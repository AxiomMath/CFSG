module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.RankTwoE
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.M23FusionData
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinM23

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.QuasithinUnique.Unc25G2.M2x
  CFSG.EvenSporadicStandard.Wong77.M23Sylow

theorem m23_rankFour
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (hL : IsSporadic L .M23) : RankFour L := by
  obtain ⟨e⟩ := hL
  let φ : Carrier .M23 →* G := L.subtype.comp e.symm.toMonoidHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp e.symm.injective
  have hrange : φ.range = L := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact (e.symm x).2
    · intro hg
      exact ⟨e ⟨g, hg⟩, by simp [φ]⟩
  have hS := (Certificates.certificate24160).1
  have hP : IsPGroup 2 sylowS := IsPGroup.of_card (card_sylowS hS)
  have h2E : TwoEAt sylowS := twoE_M23.exists_at hP sylowS_index_odd
  exact hrange ▸ rankFour_range_of_twoEAt hP sylowS_index_odd h2E hφ

end CFSG.EvenSporadicStandard.M23Std
