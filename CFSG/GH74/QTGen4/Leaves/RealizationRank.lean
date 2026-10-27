module

public import CFSG.GH74.SectionalRank

public section

namespace CFSG.GH74.QTGen4

open CFSG.GH74 CFSG.Open

theorem finrank_realization_le_four {G : Type} [Group G] [Finite G] (hG : Gen4 G)
    {U : Subgroup G} {A : Type} [AddCommGroup A] [Module (ZMod 2) A]
    (β : ↥U →* Multiplicative A) (hsurj : Function.Surjective β) :
    Module.finrank (ZMod 2) A ≤ 4 := by
  classical
  have hU : SectionalTwoRankLE ↥U 4 := SectionalTwoRankLE.subgroup U hG
  have hY : SectionalTwoRankLE (Multiplicative A) 4 :=
    SectionalTwoRankLE.of_surjective β hsurj hU
  have hE : IsElemAbelian 2 (⊤ : Subgroup (Multiplicative A)) := by
    refine ⟨inferInstance, fun x _ => ?_⟩
    have hv : ∀ v : A, v + v = 0 := fun v => by
      rw [← two_smul (ZMod 2) v]
      have h2 : (2 : ZMod 2) = 0 := by decide
      rw [h2, zero_smul]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, two_nsmul]
    exact hv _
  have hc := hY.card_le_of_elementary ⊤ hE
  have : Finite (Multiplicative A) := Finite.of_surjective β hsurj
  have : Finite A := Finite.of_surjective Multiplicative.toAdd Multiplicative.toAdd.surjective
  have : Fintype A := Fintype.ofFinite A
  rw [Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card] at hc
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hc

end CFSG.GH74.QTGen4
