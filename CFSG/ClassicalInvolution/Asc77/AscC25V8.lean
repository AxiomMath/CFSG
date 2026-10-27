module

public import CFSG.ClassicalInvolution.Asc77.AscC25V7
public import CFSG.ClassicalInvolution.Asc77.AscC25V3
public import CFSG.ClassicalInvolution.Asc77.AscC25V6
public import CFSG.ClassicalInvolution.Asc77.AscT7U8

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section Main

variable {p f : ℕ} [Fact p.Prime]


theorem false_of_ff (h11 : C25_11 p f) (hff : FF25 p f) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G}
    {R R' : Subgroup G} {z t u₁ u₂ : G} (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {e : G}
    (heS : e ∈ (S : Subgroup G)) (he2 : e * e = 1) (hFe : IsFAut R e) (hFe' : IsFAut R' e) :
    False := by
  by_cases hZ : z ∈ zStarOf (Subgroup.centralizer ({e} : Set G))
  · exact false_of_zStar_ff h11 hyp heS he2 hFe hFe' hZ
  · obtain ⟨t', h, hcyc, hfus⟩ :=
      hff G Ω K K' W S R R' z t u₁ u₂ hyp e heS he2 hFe hFe' hZ
    exact false_of_cyc_fus h heS he2 hFe' hcyc hfus

theorem c25_16inv_of_parts (h11 : C25_11 p f) (hmix : Mix25 p f) (hff : FF25 p f) :
    T7U.C25_16inv p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hF'
  rcases hmix G Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hF' with hin | ⟨r, hrR, ha'2, hFa'⟩
  · obtain ⟨e, heS, he2, hFe, hFe'⟩ := exists_ff_of_inner h11 hyp haS ha2 hF' hin
    exact false_of_ff h11 hff hyp heS he2 hFe hFe'
  · obtain ⟨t₀, h₀⟩ := T7T.exists_hyp25T hyp
    have ha'S : a * r ∈ (S : Subgroup G) := S.mul_mem haS (h₀.hRS hrR)
    have hF'a' : IsFAut R' (a * r) :=
      T7U.isFAut_mul_of_centralizes (fun x hx => h₀.hcomm r hrR x hx) hF'
    exact false_of_ff h11 hff hyp ha'S ha'2 hFa' hF'a'

theorem c25_16invEven_of_parts (h11 : C25_11 p f) (hmix : Mix25 p f) (hff : FF25 p f) :
    Even f → T7U.C25_16inv p f :=
  fun _ => c25_16inv_of_parts h11 hmix hff

end Main

end CFSG.ClassicalInvolution.Asc77.C25V
