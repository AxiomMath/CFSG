module

public import CFSG.GroupTheory.CoprimeCentralizerCover
public import CFSG.GroupTheory.PGroup.CardCoprime

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G] [Finite G]

theorem commutator_eq_self_of_inf_centralizer_eq_bot {A B : Subgroup G} {p r : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hrp : r ≠ p) (hAp : IsPGroup r A)
    (hB : IsPGroup p B) (hBA : B ≤ Subgroup.normalizer (A : Set G))
    (hcent : A ⊓ Subgroup.centralizer (B : Set G) = ⊥) :
    ⁅A, B⁆ = A := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  have hJle : (⁅A, B⁆ : Subgroup G) ≤ A :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hBA
  have hJp : IsPGroup r (⁅A, B⁆ : Subgroup G) := hAp.to_le hJle
  have hJnotp : ¬ p ∣ Nat.card (⁅A, B⁆ : Subgroup G) :=
    not_dvd_card_of_isPGroup hJp hp hrp.symm
  have hsup : A ⊓ Subgroup.centralizer (B : Set G) ⊔ (⁅A, B⁆ : Subgroup G) = A :=
    inf_centralizer_sup_eq_of_commutator_le
      (p := p) (X := A) (N := (⁅A, B⁆ : Subgroup G)) (R := B)
      hJle hBA (Subgroup.normalizer_commutator_ge_right A B) hB hJnotp le_rfl
  rw [hcent, bot_sup_eq] at hsup
  exact hsup

end CFSG.GroupTheory
