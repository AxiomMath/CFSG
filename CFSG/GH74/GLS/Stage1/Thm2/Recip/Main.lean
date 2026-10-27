module

public import CFSG.GH74.GLS.Stage1.Thm2.Recip.L289

public section

namespace CFSG.GH74.GLS.Stage1.Thm2.Recip

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage1.Thm6
open scoped commutatorElement

theorem b_reciprocity_of_background : IG_balance_fAut → II4_44 → II4_Aut → IG_3_27 → B_reciprocity := by
  intro hBal h44 hAut h327 G _ _ hG x y hx hy hcomm L J hL hJ
  have cfg : RecipCfg G x y L J := ⟨hG, hx, hy, hcomm, hL, hJ⟩
  refine ⟨fun hxJ => lemma_28_7 hBal h44 hAut h327 G x y L J cfg hxJ,
    fun hxJ a haJ ha2 hay hax => ?_⟩
  by_contra haL
  classical
  have hex : ∃ n : ℕ, ∃ b ∈ J, IsPGroup 2 ↥(zpowers b) ∧ b ∉ zpowers y ∧ Commute b x ∧
      b ∉ normalizer (L : Set G) ∧ orderOf b = n := ⟨orderOf a, a, haJ, ha2, hay, hax, haL, rfl⟩
  obtain ⟨b, hbJ, hb2, hby, hbx, hbL, hbord⟩ := Nat.find_spec hex
  have hmin : ∀ c ∈ J, IsPGroup 2 ↥(zpowers c) → c ∉ zpowers y → Commute c x →
      c ∉ normalizer (L : Set G) → orderOf b ≤ orderOf c := by
    intro c hc hc2 hcy hcx hcL
    rw [hbord]
    exact Nat.find_min' hex ⟨c, hc, hc2, hcy, hcx, hcL, rfl⟩
  have hFB : FailB G x y L J b := ⟨cfg, hxJ, hbJ, hb2, hby, hbx, hbL, hmin⟩
  obtain ⟨Py, P, w, hs⟩ := exists_setup hBal h44 hAut h327 hFB
  obtain ⟨u, hu⟩ : ∃ u : G, u = w * (b⁻¹ * w * b) := ⟨_, rfl⟩
  have hu2 : orderOf u = 2 := by rw [hu]; exact hs.hu2 h44
  have hux : u * x = x * u := by rw [hu]; exact mem_centralizer_singleton_iff.mp hs.hu_cx
  have huy : u * y = y * u := by rw [hu]; exact mem_centralizer_singleton_iff.mp hs.hu_cy
  have huN : u ∈ normalizer (L : Set G) := by rw [hu]; exact hs.hu_N
  have hunJ : u ∉ normalizer (J : Set G) := by rw [hu]; exact hs.hu_not_mem_normalizer_J
  obtain ⟨g, hg⟩ := lemma_28_9_b hBal h44 hAut h327 hs
  rw [← hu] at hg
  have hH : IsIntrinsic u (J.map (MulAut.conj g⁻¹).toMonoidHom) := by
    have h := isIntrinsic_map_conj hJ g⁻¹
    rwa [show g⁻¹ * y * g⁻¹⁻¹ = u by rw [inv_inv]; exact hg] at h
  have cfg₁ : RecipCfg G u x (J.map (MulAut.conj g⁻¹).toMonoidHom) L :=
    ⟨hG, hu2, hx, hux, hH, hL⟩
  have hxH : x ∈ normalizer ((J.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) : Set G) :=
    lemma_28_7 hBal h44 hAut h327 G u x _ L cfg₁ huN
  have hyxH : y * x ∈ normalizer ((J.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) : Set G) :=
    lemma_28_9_c h44 h327 hs (by rw [← hu]; exact hH)
  have hyH : y ∈ normalizer ((J.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) : Set G) := by
    have := mul_mem hyxH (inv_mem hxH)
    rwa [show y * x * x⁻¹ = y by group] at this
  have cfg₂ : RecipCfg G y u J (J.map (MulAut.conj g⁻¹).toMonoidHom) :=
    ⟨hG, hy, hu2, huy.symm, hJ, hH⟩
  exact hunJ (lemma_28_7 hBal h44 hAut h327 G y u J _ cfg₂ hyH)

end CFSG.GH74.GLS.Stage1.Thm2.Recip
