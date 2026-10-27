module

public import CFSG.GH74.GLS.C3.Layer1.BkP85SpJ2
public import CFSG.GH74.GLS.C3.Layer1.BkP85SpIdx2

public section

namespace CFSG.GH74.GLS

open CFSG.GH74.GLS.Th2.P85

theorem b_thm2_p85_spor_of
    (hb : B_thm2_p88b) (h89 : B_thm2_p89_J2) :
    B_thm2_p85_spor := by
  intro G _ _ x y K T S M L hs hspor
  obtain ⟨hK5, hcases⟩ := hspor
  have hsetup := hs.toP85Setup
  have hG : IsSimpleGroup G := hsetup.hG.kproper.1
  have hnab : ∃ a b : G, a * b ≠ b * a := hsetup.hG.kproper.2.1
  have hxM : x ∈ M := Th2.P85.Sp.x_mem_M hs
  have hx2 : orderOf x = 2 := hsetup.choice.std.orderOf_x
  have hCx : Subgroup.centralizer ({x} : Set G) ≤ M :=
    centralizer_le_M_of_p88b hb hs
  have hgam : gammaK 2 (T ⊓ CxK x K) 1 ≤ M := gammaK_le_M_of_p88b hb hs
  rcases hcases with ⟨hM12, hcard⟩ | ⟨hJ2, hLtop | hcard⟩
  · have cfg := Th2.P85.Sp.sporAutCfg_of_P85 hs hK5 hcard (Or.inl hM12) hxM
    exact Th2.P85.Sp.p85_index_two_false hG hnab hxM hx2 hs.Qelem hCx hgam cfg
  · exact Th2.P85.Sp.p85_J2_top_false hb h89 hs hK5 hJ2 hLtop
  · have cfg := Th2.P85.Sp.sporAutCfg_of_P85 hs hK5 hcard (Or.inr hJ2) hxM
    exact Th2.P85.Sp.p85_index_two_false hG hnab hxM hx2 hs.Qelem hCx hgam cfg

end CFSG.GH74.GLS
