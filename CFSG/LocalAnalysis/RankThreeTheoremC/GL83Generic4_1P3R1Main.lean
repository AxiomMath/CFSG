module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1End
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1Struct
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1L45
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1L44

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem m11_false_of_plane (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (hInn : KFactInnerAction) (hWC : KFactWeakClosure)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    {p : ℕ} (hp : p ∈ rankThreeSigmaA G) (hp3 : p = 3) {P : Sylow p G} {M : Subgroup G}
    (hM : IsCoreMaxLocal p P M) {x : G} (hgen : IsGenericPoint p P M x)
    {J : Subgroup G} (hJ : IsM11Normal M x J) (hplane : M11PlaneData p P M x) : False := by
  subst hp3
  obtain ⟨⟨hPab, hwc⟩, h42, U, hUP, hU, hUc, hxU, hL43⟩ := hplane
  have hC := h42 U hUP hU hUc hxU
  obtain ⟨hxP, ⟨-, hx1, hx3, -, -⟩, -, -⟩ := id hgen
  have hUJ := m11_inf_ne_bot hS hU0 hKM hKA hp hM hgen hJ hU hUc hUP hxU
  have hL45 := m11_exists_maximal_not_le hS hU0 hKA hp hM hgen hJ hU hUc hUP hxU hUJ
  have hD3 := m11_reducedCentralizer_isPGroup hS hU0 hKM hKA hp hM hgen hJ
  have hL44 := m11_not_two_dvd_card hS hU0 hD1 hKM hp hM hgen hJ hD3
  exact false_three_of_plane hS hU0 hD1 hInn hWC hp hM hxP hx1 hx3 hPab hwc hU hUc hUP hxU hC
    hL43 hL45 hL44

end CFSG.LocalAnalysis.RankThreeTheoremC
