module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth23Test

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.TwoE6

open Subgroup CFSG.Monster.B.TwoA.Amalgam

@[expose] def Stroth23Inner :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    centralizer (L : Set G) = (center L).map L.subtype → ∀ _ι : L ≃* commutator Eam,
      ∃ x ∈ normalizer (L : Set G), x ∉ L

theorem stroth23_of_inputs
    (hU : DoubleCoverUnique) (hO : CoverOuterLeTwo) (h22 : Stroth22)
    (hI : Stroth23Inner) : Stroth23 := by
  intro G _ _ L hset hc hB hZ
  obtain ⟨ι⟩ := hU L hset.standard.1 hc ((lieModel_twistedE6_two_iff _).1 hB)
  obtain ⟨-, g, -, hg1, hg2⟩ := h22 G L hset hZ ι
  have hzu : ∀ y : center L, y ≠ 1 → y = ⟨ι.symm cD, symm_cD_mem_center ι⟩ := by
    obtain ⟨w, -, hw⟩ := (Nat.card_eq_two_iff' (1 : center L)).1 hc
    intro y hy
    have h1 : (⟨ι.symm cD, symm_cD_mem_center ι⟩ : center L) ≠ 1 := fun h =>
      xD_ne_cD (by
        have h' : ι.symm cD = 1 := congrArg Subtype.val h
        rw [MulEquiv.symm_apply_eq, map_one] at h'
        exact absurd h' (fun h2 => by
          have := congrArg (fun u : commutator Eam => (u : Eam)) h2
          simp only [coe_cD, OneMemClass.coe_one] at this
          exact CFSG.Monster.B.TwoA.Amalgam.cE'_ne_one this))
    rw [hw y hy, hw _ h1]
  have hCd : ∀ w ∈ centralizer (L : Set G), w = 1 ∨ w = ((ι.symm cD : L) : G) := by
    intro w hw
    rw [hZ] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    by_cases h1 : (⟨w', hw'⟩ : center L) = 1
    · left
      have : w' = 1 := congrArg Subtype.val h1
      rw [this]
      rfl
    · right
      have := congrArg (fun y : center L => ((y : L) : G)) (hzu _ h1)
      exact this
  have hdN := centralizer_eq_normalizer hset.standard hzu (orderOf_dOf ι)
  exact exists_outer_involution_of_rootElevenTest hO ι (centralizer_le_of_eq hZ)
    (d := ι.symm cD) (z := ι.symm xD) (by rw [MulEquiv.apply_symm_apply]; rfl)
    (MulEquiv.apply_symm_apply ι xD) xD_ne_one rootElevenTest_xhatEam hCd hdN (hI G L hset hZ ι)
    hg1 hg2

end CFSG.EvenSmallLie.TwoE6
