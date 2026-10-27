module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6Plane
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6L44
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6L45
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3End

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem a6_false_of_config (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (hInn : KFactInnerAction) (hWC : KFactWeakClosure) (hK1 : A6SylowData)
    (hK2 : KFactA6TwoSignalizer) (hK3 : A6BorelCore) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsA6Normal M x J)
    (hR1 : A6Prop34 3 P J x) {U : Subgroup G} (hV : A6InV 3 P J x U)
    (h42 : ∀ u ∈ U, u ∉ zpowers x → centralizer ({u} : Set G) ≤ M)
    (h43 : ∀ Y : Subgroup G, IsPGroup 2 Y → Y ≤ M → U ≤ normalizer (Y : Set G) →
      IsSylowOf 2 (Y ⊓ GLBPrimeCore 3 M) (GLBPrimeCore 3 M) → normalizer (Y : Set G) ≤ M) :
    False := by
  have hxJ : x ∉ J := a6_x_not_mem_J hS hU0 hp hM hgen hJ
  have hgen' := hgen
  obtain ⟨hxP, ⟨-, hx1, hx3, -, -⟩, -, -⟩ := hgen'
  have hV' := hV
  obtain ⟨hUQ, hUel, hUc, hxU, -⟩ := hV'
  have hUP : U ≤ (P : Subgroup G) := hUQ.trans inf_le_left
  exact u3end_false_three_of_plane hS hU0 hD1 hInn hWC hp hM hxP hx1 hx3 hUel hUc hUP hxU
    (a6plane_hF hgen hJ hxJ hR1 hV) h42 h43
    (a6_exists_maximal_not_le_of_plane hS hU0 hK2 hp hM hgen hJ hxJ hUel hUc hUP hxU
      (a6plane_inf_ne_bot hJ hxJ hR1 hV))
    (a6_not_two_dvd_card hS hU0 hD1 hK1 hK3 hp hM hgen hJ)

end CFSG.LocalAnalysis.RankThreeTheoremC
