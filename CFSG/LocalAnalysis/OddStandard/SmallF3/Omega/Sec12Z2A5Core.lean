module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5Quot
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5Swap
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5J1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5M12
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5A7
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5L225
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5L35
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5U35
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5Der
public import CFSG.Quasithin.EmptyFaithful.S152He9W

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.EvenSporadicStandard.SolomonRed CFSG.LocalAnalysis.EvenBN.GMSK

variable {Y : Type} [Group Y] {τ : Y}

theorem z2a5_fixedK
    [Finite Y] (hSel : FixedRootSelector fun D _ => Catalog D)
    (hK : CFSG.SectionRank.IsKGroupCat Y) (h : Z2A5Hyp Y τ) {S : Subgroup Y}
    (hS : FixedData Y S) : BenderL34Socle Y := by
  have hT : LieModel ↥S .PSL 2 2 4 ∨ LieModel ↥S .PSU 3 2 2 ∨ LieModel ↥S .PSL 3 2 2 := by
    rcases z2a5_fixed_survivors hSel hK h hS with h1 | h1 | h1 | ⟨-, h1⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
    · rcases h1 with h1 | h1 | h1 | h1 | h1 | h1
      · exact absurd h1 (z2a5_not_J1 h hS)
      · exact absurd h1 (z2a5_not_M12 h hS)
      · exact absurd h1 (z2a5_not_A7 h hS)
      · exact absurd h1 (z2a5_not_L225 h hS)
      · exact absurd h1 (z2a5_not_L35 h hS)
      · exact absurd h1 (z2a5_not_U35 h hS)
    · omega
  exact ⟨S, hS.normal, hS.simple, hS.cent, z2a5_derived_le hS hT, hT⟩

theorem z2a5_coreK
    [Finite Y] (hSel : FixedRootSelector fun D _ => Catalog D)
    (hK : CFSG.SectionRank.IsKGroupCat Y) (h : Z2A5Hyp Y τ) (hO : oddCore Y = ⊥) :
    IsO4Plus4 Y ∨ BenderL34Socle Y := by
  obtain ⟨e⟩ := h.2.1
  have hZ := z2a5_zstar h hO
  rcases dichotomy (setting_of_equiv sec128_A5_noncomm h.1 hZ e) with
    ⟨S, hS⟩ | ⟨S₁, S₂, hs⟩
  · exact Or.inr (z2a5_fixedK hSel hK h hS)
  · exact Or.inl (z2a5_swap h hZ e hs)

theorem asc82Z2A5K_of
    (hSel : FixedRootSelector fun D _ => Catalog D) :
    Asc82Z2A5K :=
  fun _ _ _ _ hK h =>
    z2a5_coreK hSel (z2a5_kgroup_quot hK) (z2a5Hyp_quot h) z2a5_oddCore_quot

end CFSG.OddStandard.SmallF3.Omega
