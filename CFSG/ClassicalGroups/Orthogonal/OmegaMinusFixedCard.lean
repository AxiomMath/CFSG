module

public import CFSG.ClassicalGroups.Orthogonal.OmegaMinusType
public import CFSG.ClassicalGroups.Orthogonal.OmegaMinusFour

public section

namespace CFSG.ClassicalGroups.Orthogonal

open CFSG.ClassicalGroups CFSG.ClassicalGroups.F2Fixed QuadraticMap Module

universe uV uM

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem omegaMinus_card_eq_pow_aux :
    ∀ m : ℕ, 2 ≤ m → ∀ {V : Type uV} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (Q : QuadraticForm K V), IsMinus Q m →
      ∀ {M : Type uM} [AddCommGroup M] [Finite M], (∀ x : M, x + x = 0) →
      ∀ [DistribMulAction (Gom Q) M] (Ph : HypPair Q),
      IsCompl (fixedSub M (Lom Q Ph.e : Set (Gom Q))) (fixedSub M (Lom Q Ph.f : Set (Gom Q))) →
      ∃ n : ℕ, Nat.card M = Nat.card K ^ (2 ^ m * n) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro V _ _ _ Q h M _ _ h2 _ Ph hdec
    obtain ⟨n, hn⟩ := omegaMinus4_card_eq_pow Q h.nondeg (by simpa using h.finrank_eq)
      (fun U hU => h.noTS U hU) h2 Ph.Q_e Ph.Q_f (by rw [Ph.polar_ef]; exact one_ne_zero) hdec
    exact ⟨n, by simpa using hn⟩
  | succ m hm ih =>
    intro V _ _ _ Q h M _ _ h2 _ Ph hdec
    have hperp : IsMinus (Q.restrict Ph.perp) m := h.perp Ph
    obtain ⟨x₁, x₁', w, hx₁, hx₁', hxx, hw₁, hw₂, hQw⟩ := exists_minus_data hm hperp
    have hxx' : polar Q (x₁ : V) (x₁' : V) = 1 := by
      rw [← polar_restrict]; exact hxx
    obtain ⟨n, hn⟩ := omega_step h.nondeg Ph x₁ x₁' w hx₁ hx₁' hxx'
      (by rw [← polar_restrict]; exact hw₁) (by rw [← polar_restrict]; exact hw₂) hQw
      (e := 2 ^ m)
      (fun M' _ _ h2' _ hdec' =>
        ih (Q.restrict Ph.perp) hperp h2' ⟨x₁, x₁', hx₁, hx₁', hxx⟩ hdec')
      h2 hdec
    exact ⟨n, by rw [hn]; congr 2; ring⟩

end CFSG.ClassicalGroups.Orthogonal
