module

public import CFSG.GF2Type.Smith1979.WidthFourKP.TriPlus.RmodN
public import CFSG.LargeExtraspecial.S14C10Alt2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.OmegaPlus

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.GroupTheory.WeirSylow CFSG.Timmesfeld.ClassicalOrders CFSG.LieType.Universal.Spin

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem exists_le_Rbar_card_nine (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (h4 : finrank (ZMod 2) (Vt S g t) = 4)
    (hplus : PlusTypeAt S g ht) : ∃ P : Subgroup S.O, P ≤ Rbar S g t ∧ Nat.card P = 9 := by
  have h9R : 9 ∣ Nat.card (Rbar S g t) := by
    rw [S14.card_Rbar_eq H.conj_mem t,
      CFSG.GF2Type.Smith1979.TriPlus.card_RmodN_eq_thirtysix H C ht ht1 hVQ hΩ h4 hplus]
    exact dvd_mul_of_dvd_right (by norm_num : 9 ∣ 36) _
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨P, hPcard⟩ :=
    Sylow.exists_subgroup_card_pow_prime (G := Rbar S g t) 3 (n := 2) h9R
  refine ⟨P.map (Rbar S g t).subtype, Subgroup.map_subtype_le P, ?_⟩
  rw [Subgroup.card_subtype (Rbar S g t) P, hPcard]
  norm_num

end CFSG.GF2Type.Smith1979.OmegaPlus

end
