module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abAM
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abT2d

public noncomputable section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8ab
open CFSG.ComponentClassification.HSFLit.KD8ab

open KD7 Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

structure AD (S : KDBase A C) (T₁ : Subgroup X) where
  G : GData S T₁
  h₁ : G.D₁.q0 = .elem
  h₂ : G.D₂.q0 = .elem

variable (S) in
theorem d_conj_x : C.d * S.x * C.d⁻¹ = S.x⁻¹ := by
  obtain ⟨b, hb, hx⟩ := ψX_x S
  have hdx : C.d * S.x * C.d⁻¹ ∈ A.R := SD.conj_mem_R_of_mem_T C.d_mem S.x_mem
  refine SD.eq_of_ψX_eq hdx (inv_mem S.x_mem) ?_
  rw [SD.ψX_conj C.d_mem (x_mem_T S), SDKD.ψX_d C, SD.ψX_inv (x_mem_T S), hx]
  rcases hb with rfl | rfl <;> decide

namespace AD

variable (H : AD S T₁)

noncomputable def ι : MA →* X := H.G.P₁.ιA H.h₁

theorem ι_w₂ : H.ι MA.w₂ = H.G.D₁.w₂ := (IPair.ιA_spec (P := H.G.P₁) H.h₁).1

theorem ι_u : H.ι MA.u = S.x * S.y := (IPair.ιA_spec (P := H.G.P₁) H.h₁).2.1.trans H.G.hu₁

theorem ι_w₁ : H.ι MA.w₁ = H.G.V₁.w₁N := (IPair.ιA_spec (P := H.G.P₁) H.h₁).2.2.1

theorem ι_v : H.ι MA.v = H.G.V₁.vN := (IPair.ιA_spec (P := H.G.P₁) H.h₁).2.2.2.1

theorem ι_z : H.ι MA.z = S.z := (IPair.ιA_spec (P := H.G.P₁) H.h₁).2.2.2.2.1

theorem ι_y : H.ι MA.y = S.y := (IPair.ιA_spec (P := H.G.P₁) H.h₁).2.2.2.2.2.1

theorem ι_t : H.ι MA.t = t := (IPair.ιA_spec (P := H.G.P₁) H.h₁).2.2.2.2.2.2.1

theorem ι_k : H.ι MA.k = S.k := (IPair.ιA_spec (P := H.G.P₁) H.h₁).2.2.2.2.2.2.2

theorem ι_injective : Function.Injective H.ι := IPair.ιA_injective (P := H.G.P₁) H.h₁

theorem range_ι : H.ι.range = H.G.D₁.S₁ := IPair.range_ιA (P := H.G.P₁) H.h₁

theorem mem_range_of_mem_S₁ {g : X} (hg : g ∈ H.G.D₁.S₁) : ∃ a : MA, H.ι a = g := by
  rw [← H.range_ι] at hg
  exact hg

theorem ι_mem_S₁ (a : MA) : H.ι a ∈ H.G.D₁.S₁ := H.range_ι ▸ ⟨a, rfl⟩

theorem ι_uy : H.ι (MA.u * MA.y) = S.x := by
  rw [map_mul, ι_u, ι_y, mul_assoc, ← pow_two, S.y_sq, mul_one]

theorem ι_w₁_eq : H.G.V₁.w₁c = H.ι MA.w₁ := by
  rw [ι_w₁]; exact ISide.w₁c_of_elem _ H.h₁

theorem exists_zk {c : X} (hc : c ∈ (zpowers S.z ⊔ zpowers S.k : Subgroup X)) :
    ∃ c' ∈ MA.ZList, H.ι c' = c := by
  rcases H.G.V₁.eq_of_mem_zk hc with rfl | rfl | rfl | rfl
  · exact ⟨1, by simp [MA.ZList], map_one _⟩
  · exact ⟨MA.z, by simp [MA.ZList], H.ι_z⟩
  · exact ⟨MA.k, by simp [MA.ZList], H.ι_k⟩
  · exact ⟨MA.z * MA.k, by simp [MA.ZList], by rw [map_mul, ι_z, ι_k]; rfl⟩

theorem ι_dAct {g : X} {gy c₁ c₂ : MA}
    (hu : g * H.ι MA.u * g⁻¹ = H.ι (MA.y * MA.u * gy))
    (hw : g * H.ι MA.w₁ * g⁻¹ = H.ι (MA.w₁ * c₁))
    (hv : g * H.ι MA.v * g⁻¹ = H.ι (MA.v * MA.w₁ * c₂))
    (hz : g * H.ι MA.z * g⁻¹ = H.ι MA.z) (hy : g * H.ι MA.y * g⁻¹ = H.ι gy)
    (ht : g * H.ι MA.t * g⁻¹ = H.ι MA.t) (hk : g * H.ι MA.k * g⁻¹ = H.ι (MA.z * MA.k))
    {a : MA} (ha : MA.inT1 a = true) : H.ι (dAct gy c₁ c₂ a) = g * H.ι a * g⁻¹ := by
  have hb := nfBits_T1 a ha
  have e1 : g * H.ι a * g⁻¹ = ((MulAut.conj g).toMonoidHom.comp H.ι) a := by simp
  rw [e1]
  conv_rhs => rw [MA.nf_spec a]
  rw [dAct, map_nfProd, map_nfProd, hb]
  simp only [MA.gens, dImgs, List.map_cons, List.map_nil, nfProd, Bool.false_eq_true,
    ite_false, one_mul, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, hu, hw, hv, hz, hy, ht, hk]

theorem d_shape : ∃ gy ∈ [MA.u, MA.z * MA.u], ∃ c₁ ∈ MA.ZList, ∃ c₂ ∈ MA.ZList,
    ∀ a, MA.inT1 a = true → H.ι (dAct gy c₁ c₂ a) = C.d * H.ι a * C.d⁻¹ := by
  obtain ⟨gy, hgy, hy⟩ : ∃ gy ∈ [MA.u, MA.z * MA.u], C.d * S.y * C.d⁻¹ = H.ι gy := by
    rcases d_conj_y S with h | h
    · exact ⟨MA.u, by simp, by rw [h, ι_u]⟩
    · exact ⟨MA.z * MA.u, by simp, by rw [h, map_mul, ι_z, ι_u]⟩
  obtain ⟨c, hc, hw⟩ := H.G.d_conj_w₁c
  obtain ⟨c₁, hc₁, rfl⟩ := H.exists_zk hc
  obtain ⟨c', hc', hv⟩ := H.G.d_conj_vN
  obtain ⟨c₂, hc₂, rfl⟩ := H.exists_zk hc'
  refine ⟨gy, hgy, c₁, hc₁, c₂, hc₂, fun a ha => H.ι_dAct ?_ ?_ ?_ ?_ ?_ ?_ ?_ ha⟩
  · have hyx : S.y * (S.x * S.y) = S.x⁻¹ := by
      rw [← S.y_inv, ← mul_assoc, show S.y⁻¹ = S.y from
        inv_eq_of_mul_eq_one_right (by rw [← pow_two, S.y_sq])]
    rw [map_mul, map_mul, ι_y, ι_u, hyx, ← hy, ← d_conj_x S]
    group
  · rw [← ι_w₁_eq, map_mul, ← ι_w₁_eq, hw]
  · rw [ι_v, hv, map_mul, map_mul, ι_v, ι_w₁_eq]
  · rw [ι_z, d_conj_z S]
  · rw [ι_y, hy]
  · rw [ι_t, d_conj_t]
  · rw [ι_k, map_mul, ι_z, ι_k]; exact H.G.d_conj_k

structure DC (H : AD S T₁) where
  d₀ : X
  e : Bool
  c₂ : MA
  hc₂ : c₂ ∈ [1, MA.z]
  mem : d₀ ∈ A.T
  sq : d₀ * d₀ = H.ι (tE e)
  conj : ∀ a, MA.inT1 a = true → H.ι (dc e c₂ a) = d₀ * H.ι a * d₀⁻¹

theorem ι_tE (e : Bool) : H.ι (tE e) * H.ι (tE e) = 1 := by
  cases e
  · simp [tE]
  · simp only [tE, ite_true, ι_t]; exact tt (A := A)

theorem nonempty_DC : Nonempty H.DC := by
  obtain ⟨gy, hgy, c₁, hc₁, c₂, hc₂, hd⟩ := H.d_shape
  obtain ⟨e, he⟩ : ∃ e : Bool, C.d * C.d = H.ι (tE e) := by
    rcases d_sq (C := C) with h | h
    · exact ⟨false, by rw [← pow_two, h]; simp [tE]⟩
    · exact ⟨true, by rw [← pow_two, h]; simp [tE, ι_t]⟩
  have hT1 : ∀ a : MA, MA.inT1 (dAct gy c₁ c₂ a) = true := dAct_T1 gy hgy c₁ hc₁ c₂ hc₂
  have hsq : SqOK e gy c₁ c₂ = true := by
    simp only [SqOK, List.all_eq_true, decide_eq_true_eq]
    intro g hg
    have hgT : MA.inT1 g = true := by
      simp only [gens7, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
    apply H.ι_injective
    rw [hd _ (hT1 g), hd _ hgT, map_mul, map_mul]
    have hinv : (H.ι (tE e))⁻¹ = H.ι (tE e) :=
      inv_eq_of_mul_eq_one_right (H.ι_tE e)
    calc C.d * (C.d * H.ι g * C.d⁻¹) * C.d⁻¹ = (C.d * C.d) * H.ι g * (C.d * C.d)⁻¹ := by group
      _ = _ := by rw [he, hinv]
  obtain ⟨r, hr, c₂', hc₂', hcan⟩ := canon_exists e gy hgy c₁ hc₁ c₂ hc₂ hsq
  simp only [CanonOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hcan
  obtain ⟨hgen, hrsq⟩ := hcan
  have hrT1 : MA.inT1 r = true := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide +kernel
  have hconj : ∀ g ∈ gens7, (C.d * H.ι r) * H.ι g * (C.d * H.ι r)⁻¹ = H.ι (dc e c₂' g) := by
    intro g hg
    have hgT : MA.inT1 g = true := by
      simp only [gens7, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
    rw [← hgen g hg, hd _ (MA.T1_normal r g hgT), map_mul, map_mul, map_inv]
    group
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := dAct_gens MA.u (cOne e) c₂'
  refine ⟨⟨C.d * H.ι r, e, c₂', hc₂', ?_, ?_, fun a ha => H.ι_dAct ?_ ?_ ?_ ?_ ?_ ?_ ?_ ha⟩⟩
  · refine mul_mem C.d_mem ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [map_one]; exact one_mem _
    · rw [ι_t]; exact A.t_mem_T
    · rw [ι_uy]; exact x_mem_T S
    · rw [map_mul, ι_uy, ι_t]; exact mul_mem (x_mem_T S) A.t_mem_T
  · calc C.d * H.ι r * (C.d * H.ι r) = (C.d * H.ι r * C.d⁻¹) * (C.d * C.d) * H.ι r := by group
      _ = H.ι (tE e) := by rw [← hd _ hrT1, he, ← map_mul, ← map_mul, hrsq]
  · rw [hconj _ (by simp [gens7]), dc, g1]
  · rw [hconj _ (by simp [gens7]), dc, g2]
  · rw [hconj _ (by simp [gens7]), dc, g3]
  · rw [hconj _ (by simp [gens7]), dc, g4]
  · rw [hconj _ (by simp [gens7]), dc, g5]
  · rw [hconj _ (by simp [gens7]), dc, g6]
  · rw [hconj _ (by simp [gens7]), dc, g7]

end AD

end KD8ab

end CFSG.OddStandard.SmallF3.L33.KD
