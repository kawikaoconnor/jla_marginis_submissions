import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor
import Mathlib.Init.Data.Nat.Basic

/-
We formalize some examples relating to the paper by Morenikeji Neri
and Thomas Powell:
``A computational study of a class of recursive inequalitites.''

In particualr we show that if a sequence of real numbers {μ_n} satisfies
the property that μ_{n + 1} ≤ c μ_{n} where c ∈ [0,1), then said sequence
converges to 0.

We first prove that if c ∈ [0,1), the sequence given by c^k converges to
zero.
-/


/-
The definition of a recursive sequence, as given in the paper.
-/

def recursiveSeq (f : ℕ -> ℝ) (c : ℝ): (Prop) :=
  (0 ≤ c ∧ c < 1) ∧ (∀ n : ℕ, 0 ≤ f n ∧ f (n + 1) ≤ c * (f (n)))

/-
The following is a proof that c^k converges to zero, using the typical
ε-N definition.
-/

lemma cToZero (c : ℝ) : 0 ≤ c ∧ c < 1 → ∀ ε > 0, ∃ N : ℕ, ∀ k : ℕ, (k ≥ N) → c^k < ε := by
  intro h
  intro ε
  intro hε
  by_cases hc : (c = 0)
  .
    use 1
    subst hc
    intro k
    intro nk
    rw [zero_pow]
    exact hε
    exact Nat.not_eq_zero_of_lt nk
  .
    push_neg at hc
    have cGreaterZero : (0 < c) := by
      rw [lt_iff_le_and_ne]
      exact And.imp_right (fun _ => id (Ne.symm hc)) h
    by_cases simpEps : (ε < 1)
    .
      let myN := Int.ceil (Real.log ε/Real.log c)
      have cLogNeg : (Real.log c < 0) := by exact Real.log_neg cGreaterZero h.2
      use (myN.toNat + 1)
      intro k
      intro hk
      have kgtLogQuot : ((Real.log ε/Real.log c) < k) := by
        exact Nat.lt_of_ceil_lt hk
      have flipLogQuot : (k * Real.log c < Real.log ε) := by
        exact (div_lt_iff_of_neg cLogNeg).mp kgtLogQuot
      rw [← Real.log_pow] at flipLogQuot
      rw [Real.log_lt_log_iff] at flipLogQuot
      exact flipLogQuot
      exact pow_pos cGreaterZero k
      exact hε
    .
      push_neg at simpEps
      use 1
      intro k
      intro hk
      have cLtEps :  (c < ε) := by
        have splitEps : (ε = 1 ∨ 1 < ε) := by exact LE.le.eq_or_gt simpEps
        cases splitEps with
        | inl tacOne =>
          have cltone : (c < 1) := h.2
          exact lt_of_lt_of_eq cltone (id (Eq.symm tacOne))
        | inr tacTwo =>
          exact lt_trans (h.2) (tacTwo)
      have ctokLtC : (c^k ≤ c) := by
        refine pow_le_of_le_one ?h₀ ?h₁ ?hn
        exact h.1
        rw [le_iff_eq_or_lt]
        refine Or.inr ?h₁.h
        exact h.2
        exact Nat.not_eq_zero_of_lt hk
      exact lt_of_le_of_lt ctokLtC cLtEps


/-
The following is a proof that a recurisve sequence converges to zero.
-/

example : (recursiveSeq f c) → (∀ ε > 0, ∃ N : ℕ, ∀ k : ℕ, (k ≥ N) → f k < ε) := by
  unfold recursiveSeq
  intro h
  by_contra hc
  push_neg at hc
  obtain ⟨ε_0, hε_0⟩ := hc

  have ⟨my_c_assump, my_seq_assump⟩ := h
  have ⟨my_ε_0_assump, my_Nε_0_assump⟩ := hε_0

  have εfK_assump : (∃ k ≥ 1, ε_0 ≤ f k) := by exact my_Nε_0_assump 1
  obtain ⟨k_0, εk_0⟩ := εfK_assump

  have seqDecreasing : (∀ n : ℕ, f (n + 1) ≤ f n) := by
    intro n
    have cLeq1 : (c ≤ 1) := by
      rw [le_iff_eq_or_lt]
      tauto
    exact le_trans ((my_seq_assump (n)).2) (mul_le_of_le_one_of_le_of_nonneg cLeq1 (Preorder.le_refl (f n)) (my_seq_assump n).1)

  have seqGenerallyDecreasing : (∀ n : ℕ, ∀ k ≥ n, f k ≤ f n) := by
    intro n
    intro k
    induction k with
    | zero =>
      intro nAssump
      rw [ge_iff_le] at nAssump
      rw [Nat.le_zero] at nAssump
      subst nAssump
      exact Preorder.le_refl (f 0)
    | succ k hk =>
      intro assumpOnK
      by_cases myCase : (k ≥ n)
      .
        exact Preorder.le_trans (f (k + 1)) (f k) (f n) (seqDecreasing k) (hk myCase)
      .
        push_neg at myCase
        rw [ge_iff_le] at assumpOnK
        have nEqkPlusOne : (n = (k + 1)) := by
          exact Nat.le_antisymm assumpOnK myCase
        subst n
        rfl

  have mStepsEps : (∀ m : ℕ, ε_0 ≤ f (k_0 + m)) := by
    intro m
    obtain ⟨K, KAssump⟩ := my_Nε_0_assump ((k_0 + m))
    exact le_trans (KAssump.2) ((seqGenerallyDecreasing (k_0 + m) (K) (KAssump.1)))

  have mStepsSeq : (∀ m : ℕ, f (k_0 + m) ≤ (c^m)*f k_0) := by
    intro m
    induction m with
    | zero =>
      simp
    | succ m hm =>
      have almostStatement : (c * f (k_0 + m) ≤ c * (c^m * f k_0)) := by
        exact mul_le_mul (le_refl c) (hm) ((my_seq_assump (k_0 + m)).1) (my_c_assump.1)
      have relToInduction : (c*f (k_0 + m) ≤ c^(m + 1)*f k_0) := by
        simp at almostStatement
        rw [← mul_assoc (c) (c^m) (f k_0)] at almostStatement
        rw [← pow_succ'] at almostStatement
        exact almostStatement
      exact le_trans ((my_seq_assump (k_0 + m)).2) (relToInduction)

  have repeatFirstStepContra : (∀ m :ℕ, ε_0 ≤ f (k_0 + m) ∧ f (k_0 + m) ≤ (c^m) * f k_0) := by
    intro m
    exact ⟨mStepsEps m, mStepsSeq m⟩

  have getContra : (∀ m : ℕ, (0 < f k_0) → (ε_0/(f k_0)) ≤ c^m) := by
    intro m
    have epsRelTofkm : (ε_0 ≤ c^m *f (k_0)) := by
      exact le_trans ((repeatFirstStepContra (m)).1) ((repeatFirstStepContra (m)).2)
    intro fk0StrictgtZero
    rw [← div_le_iff (fk0StrictgtZero)] at epsRelTofkm
    exact epsRelTofkm

  by_cases fk0EqZero : ((f k_0) = 0)
  .
    linarith
  .
    have fk0StrictgtZero : (0 < (f k_0)) := by
      linarith

    have applyLemma : (∃ N : ℕ, ∀ k : ℕ, (k ≥ N) → c^k < (ε_0/(f k_0))) := by
      exact cToZero (c) (my_c_assump) (ε_0/(f k_0)) (div_pos (my_ε_0_assump) (fk0StrictgtZero))

    obtain ⟨myN, myNAssump⟩ := applyLemma

    have leftSideContra : (ε_0/(f k_0) ≤ c^myN) := by
      exact getContra (myN) (fk0StrictgtZero)

    have rightSideContra : (c^myN < ε_0/(f k_0)) := by
      exact myNAssump (myN) (Nat.le_refl myN)
    linarith



example (μ : ℕ → NNReal) (c : Set.Ico 0 (1:ℝ))
  (h : ∀ n, μ (n + 1) ≤ c.1 * μ n)     (n : ℕ):
            μ n ≤ c.1^n * μ 0 := by
  induction n with
  |zero => simp only [pow_zero, one_mul, le_refl]
  |succ n hn =>
    calc
    μ (n+1)   ≤ c.1 * μ n := h n
    _ ≤ c.1^(n+1) * μ 0 := by
      ring_nf;
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hn c.2.1

/-
For the inequality to hold we do not need to use the type
`NNReal` but can also use `Real`; and we can generalize `c` as well:
-/

example (μ : ℕ → Real) (c : NNReal)
  (h : ∀ n, μ (n + 1) ≤ c * μ n) (n : ℕ):
  μ n ≤ c^n * μ 0 := by
  induction n with
  |zero => simp only [pow_zero, one_mul, le_refl]
  |succ n hn =>
    calc
    _ ≤ c * μ n := h n
    _ ≤ _ := by
      ring_nf;
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hn c.2

/- Using rationals and nonnegative rationals works with the same proof: -/

example (μ : ℕ → Rat) (c : NNRat)
  (h : ∀ n, μ (n + 1) ≤ c * μ n) (n : ℕ):
  μ n ≤ c^n * μ 0 := by
  induction n with
  |zero => simp only [pow_zero, one_mul, le_refl]
  |succ n hn =>
    calc
    _ ≤ c * μ n := h n
    _ ≤ _ := by
      ring_nf;
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hn c.2
