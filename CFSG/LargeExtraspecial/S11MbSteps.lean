module

public import CFSG.LargeExtraspecial.S11MbComm
public import CFSG.LargeExtraspecial.S11MbBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u_G

theorem add_mem_span_singleton_of_not_mem {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {a b x y : V} (hx : x ∈ Submodule.span (ZMod 2) {a, b})
    (hy : y ∈ Submodule.span (ZMod 2) {a, b}) (hxa : x ∉ (ZMod 2) ∙ a)
    (hya : y ∉ (ZMod 2) ∙ a) : x + y ∈ (ZMod 2) ∙ a := by
  obtain ⟨r, s, rfl⟩ := Submodule.mem_span_pair.mp hx
  obtain ⟨r', s', rfl⟩ := Submodule.mem_span_pair.mp hy
  have ha : ∀ c : ZMod 2, c • a ∈ (ZMod 2) ∙ a := fun c =>
    Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)
  rcases zmod2_eq_zero_or_eq_one s with rfl | rfl
  · exact absurd (by rw [zero_smul, add_zero]; exact ha r) hxa
  rcases zmod2_eq_zero_or_eq_one s' with rfl | rfl
  · exact absurd (by rw [zero_smul, add_zero]; exact ha r') hya
  have e : r • a + (1 : ZMod 2) • b + (r' • a + (1 : ZMod 2) • b) = (r + r') • a := by
    rw [one_smul, add_smul]
    calc r • a + b + (r' • a + b) = r • a + r' • a + (b + b) := by abel
      _ = r • a + r' • a := by rw [vec_add_self, add_zero]
  rw [e]
  exact ha _

variable {G : Type u_G} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O} {τ : S.M}
  {u : G}

omit [Finite G] in
theorem commutator_mem_QG_of_mem_M {σ w : G} (hσM : σ ∈ S.M) (hw : w ∈ S.QG) :
    w * σ * w⁻¹ * σ⁻¹ ∈ S.QG := by
  rw [show w * σ * w⁻¹ * σ⁻¹ = w * (σ * w⁻¹ * σ⁻¹) by group]
  exact S.QG.mul_mem hw (S.conj_mem_QG hσM (S.QG.inv_mem hw))

variable (hy : Hyp S g) (K : Conf S g t τ u) (hm : finrank (ZMod 2) (Vt S g t) = 2) {kb : G}
  (hb : kb * S.z * kb⁻¹ ∈ S.QG ⊓ S.Qa u)
  (hbs : S.cl (kb * S.z * kb⁻¹) ∉ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹))
  (hCE : CentralExtInput.{u_G})
include hy K hm hb hbs hCE

theorem YData.cases (hn : 7 ≤ S.width) {σ u₁ kd : G} (Y : YData S g t τ u kb σ u₁)
    (hkd : kd * S.z * kd⁻¹ = (τ : G) * (kb * S.z * kb⁻¹)) :
    (∀ w ∈ S.QG, S.cl w ∈ Wt S g t →
      S.cl (w * σ * w⁻¹ * σ⁻¹) ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹)) ∨
    (∀ w ∈ S.QG, S.cl w ∈ Wt S g t → (w * σ * w⁻¹ * σ⁻¹ ∈ S.Qa u ↔
      S.cl (w * σ * w⁻¹ * σ⁻¹) ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹))) := by
  have hV : ∀ w ∈ S.QG, S.cl w ∈ Wt S g t → w * σ * w⁻¹ * σ⁻¹ ∈ V S g t := fun w hw hwW =>
    S.mem_clPre.mpr ⟨commutator_mem_QG_of_mem_M Y.mem_M hw,
      by rw [S.cl_commutator' Y.mem_M hw]; exact Y.apply_sub_mem _ hwW⟩
  have haσ : g * S.z * g⁻¹ ∈ S.Qa u₁ := Y.a_mem
  have hfwd : ∀ w ∈ S.QG, S.cl w ∈ Wt S g t → w * σ * w⁻¹ * σ⁻¹ ∈ S.Qa u →
      S.cl (w * σ * w⁻¹ * σ⁻¹) ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
    intro w hw hwW hc
    have hcE : w * σ * w⁻¹ * σ⁻¹ ∈ S.QG ⊓ S.Qa u :=
      mem_inf.mpr ⟨commutator_mem_QG_of_mem_M Y.mem_M hw, hc⟩
    have hcσ : w * σ * w⁻¹ * σ⁻¹ ∈ S.Qa u₁ := by
      by_contra h
      refine Y.ne_conj_mul hy K hb hCE hn hkd hcE h w ?_
      calc w * σ * w⁻¹ = (w * σ * w⁻¹ * σ⁻¹) * σ := by group
        _ = σ * (w * σ * w⁻¹ * σ⁻¹) := (Y.comm _ hcE).symm
    rcases K.mem_E_cases hy hm hb hbs hcE with h | h | h | h
    · rw [h, S.cl_one]
      exact zero_mem _
    · rw [h]
      exact Submodule.mem_span_singleton_self _
    · exact absurd (h ▸ hcσ) Y.b_not_mem
    · exfalso
      apply Y.b_not_mem
      have h2 : g * S.z * g⁻¹ * (kb * S.z * kb⁻¹) ∈ S.Qa u₁ := h ▸ hcσ
      have := mul_mem (inv_mem haσ) h2
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
  by_cases hcase : ∀ w ∈ S.QG, S.cl w ∈ Wt S g t →
      S.cl (w * σ * w⁻¹ * σ⁻¹) ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹)
  · exact Or.inl hcase
  right
  push Not at hcase
  obtain ⟨w₀, hw₀, hw₀W, hw₀a⟩ := hcase
  intro w hw hwW
  refine ⟨hfwd w hw hwW, fun hwa => ?_⟩
  by_contra hcτ
  have hc₀τ : w₀ * σ * w₀⁻¹ * σ⁻¹ ∉ S.Qa u := fun h => hw₀a (hfwd w₀ hw₀ hw₀W h)
  have hz₁ : w * σ * w⁻¹ * σ⁻¹ * S.z ∈ S.QG ⊓ S.Qa u :=
    (K.mem_V_cases hy (hV w hw hwW)).resolve_left fun h => hcτ (mem_inf.mp h).2
  have hz₀ : w₀ * σ * w₀⁻¹ * σ⁻¹ * S.z ∈ S.QG ⊓ S.Qa u :=
    (K.mem_V_cases hy (hV w₀ hw₀ hw₀W)).resolve_left fun h => hc₀τ (mem_inf.mp h).2
  have hcomm : w * (w₀ * σ * w₀⁻¹ * σ⁻¹) = (w₀ * σ * w₀⁻¹ * σ⁻¹) * w := by
    have h1 := mem_Wt.mp hwW _ (S.mem_clPre.mp (hV w₀ hw₀ hw₀W)).2
    rw [S.polar_cl_eq_zero_iff (commutator_mem_QG_of_mem_M Y.mem_M hw₀) hw] at h1
    exact h1.symm
  have he : w * w₀ * σ * (w * w₀)⁻¹ * σ⁻¹ =
      (w₀ * σ * w₀⁻¹ * σ⁻¹ * S.z) * (w * σ * w⁻¹ * σ⁻¹ * S.z) := by
    have hzc : (w * σ * w⁻¹ * σ⁻¹) * S.z = S.z * (w * σ * w⁻¹ * σ⁻¹) :=
      S.z_comm_QG (commutator_mem_QG_of_mem_M Y.mem_M hw)
    calc w * w₀ * σ * (w * w₀)⁻¹ * σ⁻¹ =
          (w * (w₀ * σ * w₀⁻¹ * σ⁻¹)) * w⁻¹ * (w * σ * w⁻¹ * σ⁻¹) := by group
      _ = ((w₀ * σ * w₀⁻¹ * σ⁻¹) * w) * w⁻¹ * (w * σ * w⁻¹ * σ⁻¹) := by rw [hcomm]
      _ = (w₀ * σ * w₀⁻¹ * σ⁻¹) * (S.z * S.z) * (w * σ * w⁻¹ * σ⁻¹) := by
          rw [S.z_mul_z]; group
      _ = (w₀ * σ * w₀⁻¹ * σ⁻¹ * S.z) * ((S.z * (w * σ * w⁻¹ * σ⁻¹))) := by group
      _ = _ := by rw [← hzc]
  have hww₀ : w * w₀ ∈ S.QG := S.QG.mul_mem hw hw₀
  have hww₀W : S.cl (w * w₀) ∈ Wt S g t := by
    rw [S.cl_mul hw hw₀]
    exact add_mem hwW hw₀W
  have h1 := hfwd (w * w₀) hww₀ hww₀W (by rw [he]; exact mul_mem hz₀.2 hz₁.2)
  rw [he, S.cl_mul (mem_inf.mp hz₀).1 (mem_inf.mp hz₁).1,
    S.cl_mul_z (commutator_mem_QG_of_mem_M Y.mem_M hw₀),
    S.cl_mul_z (commutator_mem_QG_of_mem_M Y.mem_M hw)] at h1
  apply hw₀a
  have := sub_mem h1 hwa
  rwa [add_sub_cancel_right] at this

theorem false_of_bad (hn : 6 ≤ S.width) {σ u₁ : G} (Y : YData S g t τ u kb σ u₁)
    (hB : ∀ w ∈ S.QG, S.cl w ∈ Wt S g t → (w * σ * w⁻¹ * σ⁻¹ ∈ S.Qa u ↔
      S.cl (w * σ * w⁻¹ * σ⁻¹) ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹)))
    (hB' : ∀ w ∈ S.QG, S.cl w ∈ Wt S g t →
      (w * (σ * ((τ : G) * (kb * S.z * kb⁻¹))) * w⁻¹ * (σ * ((τ : G) * (kb * S.z * kb⁻¹)))⁻¹ ∈
        S.Qa u ↔ S.cl (w * (σ * ((τ : G) * (kb * S.z * kb⁻¹))) * w⁻¹ *
          (σ * ((τ : G) * (kb * S.z * kb⁻¹)))⁻¹) ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹))) :
    False := by
  have hVab := K.Vt_eq_span_pair hy hm hb hbs
  have hkey : ∀ w ∈ S.QG, S.cl w ∈ Wt S g t →
      S.cl (w * τ * w⁻¹ * (τ : G)⁻¹) ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
    intro w hw hwW
    set e := w * τ * w⁻¹ * (τ : G)⁻¹ with he_def
    set c := w * σ * w⁻¹ * σ⁻¹ with hc_def
    have heQ : e ∈ S.QG := (K.commutator_facts hy hw).1
    have heu : e ∈ S.Qa u := K.commutator_mem_Qa hy hCE hn hw hwW
    have hcQ : c ∈ S.QG := commutator_mem_QG_of_mem_M Y.mem_M hw
    have hwb : w * (kb * S.z * kb⁻¹) = kb * S.z * kb⁻¹ * w := by
      have hbV : S.cl (kb * S.z * kb⁻¹) ∈ Vt S g t := by
        rw [← K.timmesfeld_11_3 hy]
        exact S.cl_mem_clSub hb hb.1
      have h1 := mem_Wt.mp hwW _ hbV
      rw [S.polar_cl_eq_zero_iff hb.1 hw] at h1
      exact h1.symm
    have hσe : σ * e = e * σ := Y.comm e (mem_inf.mpr ⟨heQ, heu⟩)
    have hc' : w * (σ * ((τ : G) * (kb * S.z * kb⁻¹))) * w⁻¹ *
        (σ * ((τ : G) * (kb * S.z * kb⁻¹)))⁻¹ = c * e := by
      have h1 : (kb * S.z * kb⁻¹) * w⁻¹ * (kb * S.z * kb⁻¹)⁻¹ = w⁻¹ := by
        calc (kb * S.z * kb⁻¹) * w⁻¹ * (kb * S.z * kb⁻¹)⁻¹ =
              w⁻¹ * (w * (kb * S.z * kb⁻¹)) * w⁻¹ * (kb * S.z * kb⁻¹)⁻¹ := by group
          _ = w⁻¹ := by rw [hwb]; group
      calc w * (σ * ((τ : G) * (kb * S.z * kb⁻¹))) * w⁻¹ *
            (σ * ((τ : G) * (kb * S.z * kb⁻¹)))⁻¹ =
            w * σ * τ * ((kb * S.z * kb⁻¹) * w⁻¹ * (kb * S.z * kb⁻¹)⁻¹) * (τ : G)⁻¹ *
              σ⁻¹ := by group
        _ = w * σ * w⁻¹ * σ⁻¹ * (σ * e) * σ⁻¹ := by rw [h1, he_def]; group
        _ = c * e := by rw [hσe, hc_def]; group
    have hB₁ := hB w hw hwW
    have hB₂ := hB' w hw hwW
    rw [hc', S.cl_mul hcQ heQ] at hB₂
    have hiff : c * e ∈ S.Qa u ↔ c ∈ S.Qa u := ⟨fun h => by
      have := mul_mem h (inv_mem heu)
      rwa [mul_inv_cancel_right] at this, fun h => mul_mem h heu⟩
    rw [hiff, hB₁] at hB₂
    have hcV : S.cl c ∈ Vt S g t := by
      rw [hc_def, S.cl_commutator' Y.mem_M hw]
      exact Y.apply_sub_mem _ hwW
    have heV : S.cl e ∈ Vt S g t := by
      rw [he_def, (K.commutator_facts hy hw).2.1, ← K.timmesfeld_11_7 hy hCE]
      exact sub_mem_Tt hwW
    by_contra hne
    by_cases hca : S.cl c ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹)
    · apply hne
      have := sub_mem (hB₂.mp hca) hca
      rwa [add_sub_cancel_left] at this
    · have h1 : S.cl c + S.cl e ∉ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := fun h => hca (hB₂.mpr h)
      exact h1 (add_mem_span_singleton_of_not_mem (hVab ▸ hcV) (hVab ▸ heV) hca hne)
  have hbV : S.cl (kb * S.z * kb⁻¹) ∈ Tt S g t := by
    rw [K.timmesfeld_11_7 hy hCE, ← K.timmesfeld_11_3 hy]
    exact S.cl_mem_clSub hb hb.1
  obtain ⟨w', hw', hw'b⟩ := mem_Tt.mp hbV
  obtain ⟨w, hwQ, rfl⟩ := S.exists_cl w'
  have h1 := hkey w hwQ hw'
  rw [(K.commutator_facts hy hwQ).2.1, hw'b] at h1
  exact hbs h1

end CFSG.LargeExtraspecial.S11
