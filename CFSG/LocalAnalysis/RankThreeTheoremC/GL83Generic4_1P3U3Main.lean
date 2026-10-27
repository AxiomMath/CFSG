module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Residues
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Plane
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Q
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3HF2
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3L44
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3End

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem u3_false_of_config (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (hInn : KFactInnerAction) (hWC : KFactWeakClosure) (hK1 : U3SylowData)
    (hK2 : KFactU3TwoSignalizer) (hK3 : U3BorelCore) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsU3Normal M x J)
    (hR1 : U3Prop34 3 P J x)
    (h42 : ∀ u ∈ u3VPlane (P : Subgroup G) J x, u ∉ zpowers x → centralizer ({u} : Set G) ≤ M)
    (h43 : U3PointLemma43 3 P M J x) : False := by
  have hgen' := hgen
  obtain ⟨hxP, ⟨-, hx1, hx3, -, -⟩, -, -⟩ := hgen'
  have hxJ : x ∉ J := by
    intro hxJ
    obtain ⟨-, -, -, -, ⟨Z, -, hxZ, -, hTZ, -⟩, -⟩ := hR1
    have : x ∈ ((P : Subgroup G) ⊓ J) ⊓ Z := ⟨⟨hxP, hxJ⟩, hxZ⟩
    rw [hTZ, Subgroup.mem_bot] at this
    exact hx1 this
  obtain ⟨hU, hUc, hUP, hxU, -, -⟩ := u3plane_facts hgen hR1 hxJ
  exact u3end_false_three_of_plane hS hU0 hD1 hInn hWC hp hM hxP hx1 hx3 hU hUc hUP hxU
    (u3_hF hJ hgen hR1) h42 h43 (u3_exists_maximal_not_le hS hU0 hK2 hp hM hgen hJ hxJ hR1)
    (u3_not_two_dvd_card hS hU0 hD1 hK1 hK3 hp hM hgen hJ)

theorem GL83GenericPrimeThreeU3Prop34.of_fusion (hS : Setting G) (hU0 : FullCoreLocal G)
    (hK1 : U3SylowData) (hK2 : U3AutData) (h : GL83GenericPrimeThreeU3Fusion G) :
    GL83GenericPrimeThreeU3Prop34 G := by
  intro p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hQ
  subst hp3
  have hJ : IsU3Normal M x J :=
    ⟨hJC, hCJ, hperf, hnot, hlt, hmin, Q, inferInstance, ψ, hψ, hker, hQ⟩
  have hf := h 3 hp P M hM hfail hIH x hgen rfl J hJC hCJ hperf hlt hmin hnot Q ψ hψ hker hQ
  exact u3_prop34_of_fusion hS hU0 hK1 hK2 hp hM hgen hJ hf.1 hf.2

end CFSG.LocalAnalysis.RankThreeTheoremC
