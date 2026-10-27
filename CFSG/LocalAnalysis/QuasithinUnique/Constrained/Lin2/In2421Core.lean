module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421B2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421LQ7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421ZEq
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.L2_4_21

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

theorem lemma2_4_21_core_of_hyp0 (E : Lin2Hyp0) (hLQ : Lemma2421LQ) : Lemma2_4_21_core := by
  intro G _ _ T M H S L D n hcfg q hq g hqT
  by_contra haR
  obtain ⟨x, hx, hxS⟩ := hcfg.exists_mem_T_not_mem_S
  obtain ⟨hUe, -, -⟩ := E.elemU hcfg hx hxS
  have hq2 : q ^ 2 = 1 := hUe.2 q hq
  have ha2 : (g⁻¹ * q * g) ^ 2 = 1 := by
    have : (g⁻¹ * q * g) ^ 2 = g⁻¹ * q ^ 2 * g := by simp only [pow_two]; group
    rw [this, hq2]; group
  obtain ⟨ℓ, -, hw⟩ := E.exists_conj_mem_centerOf_R hcfg hq
  have hg : g⁻¹ * q * g = (ℓ * g)⁻¹ * (ℓ * q * ℓ⁻¹) * (ℓ * g) := by group
  have hw1 : ℓ * q * ℓ⁻¹ ≠ 1 := by
    intro h
    apply haR
    have : g⁻¹ * q * g = 1 := by rw [hg, h]; group
    rw [this]; exact one_mem _
  by_cases hc : centerOf L = ⊥
  · have hZR : lin2Z L (thompsonJ S) = centerOf (thompsonJ S) :=
      ((lin2Z_cases (Z := lin2Z L (thompsonJ S)) rfl).resolve_right fun h => h.1 hc).2
    exact E.false_of_ZLeq1 hcfg hLQ hc hqT haR ha2 (hZR ▸ hw) hw1 hg
  · exact E.false_of_ZLne1 hcfg (lemma2421B2_of_hyp0 E) hc hx hxS hqT haR ha2 hw hg

theorem lemma2_4_21_core_of_residual (h8 : Lemma2_4_8) (h11 : Lemma2_4_11) (h12 : Lemma2_4_12)
    (h14 : Lemma2_4_14) (hLQ : Lemma2421LQ) : Lemma2_4_21_core :=
  lemma2_4_21_core_of_hyp0 ⟨h8, h11, h12, h14⟩ hLQ

theorem lemma2421LQ_of_hyp0 (E : Lin2Hyp0) : Lemma2421LQ := by
  intro G _ _ T M H S L D n hcfg hc a haT haS ha2 hacent g z hz _ hg
  obtain ⟨x, hx, hxS⟩ := hcfg.exists_mem_T_not_mem_S
  exact E.false_of_LQ hcfg hc hx hxS haT haS ha2 hacent hz hg

theorem lemma2_4_21_core_proved (h8 : Lemma2_4_8) (h11 : Lemma2_4_11) (h12 : Lemma2_4_12)
    (h14 : Lemma2_4_14) : Lemma2_4_21_core :=
  lemma2_4_21_core_of_residual h8 h11 h12 h14 (lemma2421LQ_of_hyp0 ⟨h8, h11, h12, h14⟩)

end CFSG.QuasithinUnique.Lin2
