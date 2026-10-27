module

public import CFSG.Quasithin.H13.L32NLem14413f
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14413e

public section

namespace CFSG.Quasithin.H13.L14413

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13.A6
open CFSG.Quasithin.H13.L32A
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace XCtx_F4
open CFSG.Quasithin.H13.L14413.XCtx_F4

variable {T L V V₂ X : Subgroup G} {g : G} {C : XCtx_F4 G T L V V₂ X g} (K : C.Coords_F4)

omit [CFSG.GH74.QTGen4.Finite4 G] in

theorem conj_eq_of_comm {u w y : G} (h : u * w * u⁻¹ * w⁻¹ = y) : u * w * u⁻¹ = y * w := by
  rw [← h]; group

theorem Coords_F4.z_comm_F4 {u : G} (hu : u ∈ fsuU T V) : u * K.z = K.z * u := by
  have hz : K.z ∈ centerOf (fsuU T V) := C.zU ▸ K.hz
  exact Subgroup.mem_centralizer_iff.mp hz.2 u hu

theorem Coords_F4.comm_cases_F4 {u v : G} (hu : u ∈ fsuU T V) (hv : v ∈ fsuU T V) :
    u * v * u⁻¹ * v⁻¹ = 1 ∨ u * v * u⁻¹ * v⁻¹ = K.z :=
  K.hV1 _ (C.comm_mem_V1_F4 hu hv)

theorem exists_comm_ne_F4 (C : XCtx_F4 G T L V V₂ X g) {w : G} (hw : w ∈ fsuU T V)
    (hw1 : w ∉ fsuV1 T V) :
    ∃ u ∈ fsuU T V, u * w * u⁻¹ * w⁻¹ ≠ 1 := by
  by_contra h
  push Not at h
  apply hw1
  rw [← C.zU]
  refine ⟨hw, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
  have := h u hu
  calc u * w = (u * w * u⁻¹ * w⁻¹) * w * u := by group
    _ = w * u := by rw [this, one_mul]

theorem Coords_F4.z_sq_F4 : K.z * K.z = 1 := by
  rw [← pow_two]; exact C.W_sq_F4 (C.V1X_F4 K.hz)

theorem Coords_F4.a_mem_F4 : g⁻¹ * K.z * g ∈ V₂ := C.conj_mem_V₂_F4 (C.plane.2 K.hz)

theorem Coords_F4.exists_u_a_F4 : ∃ u ∈ fsuU T V, u * (g⁻¹ * K.z * g) * u⁻¹ * (g⁻¹ * K.z * g)⁻¹ = K.z ∧
    u * K.b * u⁻¹ * K.b⁻¹ = 1 := by
  have haU : g⁻¹ * K.z * g ∈ fsuU T V := C.VXU_F4 (C.V2X K.a_mem_F4)
  have hbU : K.b ∈ fsuU T V := C.VXU_F4 K.hb
  have haV₁ := C.conj_z_not_mem_F4 K.hz K.hz1 K.hV1
  have hbV₁ : K.b ∉ fsuV1 T V := fun h => K.hbV₂ (C.plane.2 h)
  have habV₁ : g⁻¹ * K.z * g * K.b ∉ fsuV1 T V := fun h =>
    K.hbV₂ (XCtx.mem_of_mul_mem K.a_mem_F4 (C.plane.2 h))
  exact exists_transv (fun u hu => K.z_comm_F4 hu) K.z_sq_F4 (fun u hu v hv => K.comm_cases_F4 hu hv)
    haU hbU (C.exists_comm_ne_F4 haU haV₁) (C.exists_comm_ne_F4 hbU hbV₁)
    (C.exists_comm_ne_F4 (mul_mem haU hbU) habV₁)

theorem Coords_F4.exists_u_b_F4 : ∃ u ∈ fsuU T V, u * K.b * u⁻¹ * K.b⁻¹ = K.z ∧
    u * (g⁻¹ * K.z * g) * u⁻¹ * (g⁻¹ * K.z * g)⁻¹ = 1 := by
  have haU : g⁻¹ * K.z * g ∈ fsuU T V := C.VXU_F4 (C.V2X K.a_mem_F4)
  have hbU : K.b ∈ fsuU T V := C.VXU_F4 K.hb
  have haV₁ := C.conj_z_not_mem_F4 K.hz K.hz1 K.hV1
  have hbV₁ : K.b ∉ fsuV1 T V := fun h => K.hbV₂ (C.plane.2 h)
  have hbaV₁ : K.b * (g⁻¹ * K.z * g) ∉ fsuV1 T V := by
    rw [C.W_comm_F4 K.hb (C.V2X K.a_mem_F4)]
    exact fun h => K.hbV₂ (XCtx.mem_of_mul_mem K.a_mem_F4 (C.plane.2 h))
  exact exists_transv (fun u hu => K.z_comm_F4 hu) K.z_sq_F4 (fun u hu v hv => K.comm_cases_F4 hu hv)
    hbU haU (C.exists_comm_ne_F4 hbU hbV₁) (C.exists_comm_ne_F4 haU haV₁)
    (C.exists_comm_ne_F4 (mul_mem hbU haU) hbaV₁)

theorem Coords_F4.conj_z_not_mem'_F4 : g * K.z * g⁻¹ ∉ fsuV1 T V := by
  intro h
  have h2 : Nat.card ↥(fsuV1 T V) = 2 := by simpa using C.s1282.v1.2.1
  rcases K.hV1 _ h with h1 | h1
  · apply K.hz1
    calc K.z = g⁻¹ * (g * K.z * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  · apply C.gH
    show g ∈ Subgroup.normalizer (fsuV1 T V : Set G)
    rw [normalizer_eq_centralizer_of_card_two h2 K.hz K.hz1, Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    calc K.z * g = (g * K.z * g⁻¹) * g := by rw [h1]
      _ = g * K.z := by group

theorem Coords_F4.a_comm_F4 {x : G} (hx : x ∈ CFSG.conjugate (fsuU T V) g) :
    x * (g⁻¹ * K.z * g) = (g⁻¹ * K.z * g) * x := by
  have h := K.z_comm_F4 (XCtx.mem_conjU.mp hx)
  calc x * (g⁻¹ * K.z * g) = g⁻¹ * ((g * x * g⁻¹) * K.z) * g := by group
    _ = g⁻¹ * (K.z * (g * x * g⁻¹)) * g := by rw [h]
    _ = (g⁻¹ * K.z * g) * x := by group

theorem Coords_F4.comm_cases'_F4 {x y : G} (hx : x ∈ CFSG.conjugate (fsuU T V) g)
    (hy : y ∈ CFSG.conjugate (fsuU T V) g) :
    x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = g⁻¹ * K.z * g := by
  have hc : g * (x * y * x⁻¹ * y⁻¹) * g⁻¹ =
      (g * x * g⁻¹) * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹ := by group
  rcases K.comm_cases_F4 (XCtx.mem_conjU.mp hx) (XCtx.mem_conjU.mp hy) with h | h <;> rw [← hc] at h
  · left
    calc x * y * x⁻¹ * y⁻¹ = g⁻¹ * (g * (x * y * x⁻¹ * y⁻¹) * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  · right
    calc x * y * x⁻¹ * y⁻¹ = g⁻¹ * (g * (x * y * x⁻¹ * y⁻¹) * g⁻¹) * g := by group
      _ = g⁻¹ * K.z * g := by rw [h]

theorem exists_comm_ne'_F4 (C : XCtx_F4 G T L V V₂ X g) {w : G}
    (hw : w ∈ CFSG.conjugate (fsuU T V) g) (hw1 : g * w * g⁻¹ ∉ fsuV1 T V) :
    ∃ x ∈ CFSG.conjugate (fsuU T V) g, x * w * x⁻¹ * w⁻¹ ≠ 1 := by
  obtain ⟨u, hu, hne⟩ := C.exists_comm_ne_F4 (XCtx.mem_conjU.mp hw) hw1
  refine ⟨g⁻¹ * u * g, XCtx.mem_conjU.mpr (by simpa [mul_assoc] using hu), fun h => hne ?_⟩
  calc u * (g * w * g⁻¹) * u⁻¹ * (g * w * g⁻¹)⁻¹ =
      g * ((g⁻¹ * u * g) * w * (g⁻¹ * u * g)⁻¹ * w⁻¹) * g⁻¹ := by group
    _ = 1 := by rw [h]; group

theorem Coords_F4.exists_v_F4 (c d : G) (hcd : (c = K.z ∧ d = K.b) ∨ (c = K.b ∧ d = K.z)) :
    ∃ v ∈ CFSG.conjugate (fsuU T V) g, v * c * v⁻¹ * c⁻¹ = g⁻¹ * K.z * g ∧
      v * d * v⁻¹ * d⁻¹ = 1 := by
  have hz2 : (g⁻¹ * K.z * g) * (g⁻¹ * K.z * g) = 1 := by
    rw [show g⁻¹ * K.z * g * (g⁻¹ * K.z * g) = g⁻¹ * (K.z * K.z) * g by group, K.z_sq_F4]
    group
  have hzU' : K.z ∈ CFSG.conjugate (fsuU T V) g := C.VXUg_F4 (C.V1X_F4 K.hz)
  have hbU' : K.b ∈ CFSG.conjugate (fsuU T V) g := C.VXUg_F4 K.hb
  have hz1 : g * K.z * g⁻¹ ∉ fsuV1 T V := K.conj_z_not_mem'_F4
  have hb1 : g * K.b * g⁻¹ ∉ fsuV1 T V := fun h => K.hbV₂ (by
    have := C.conj_mem_V₂_F4 (C.plane.2 h)
    simpa [mul_assoc] using this)
  have hzb1 : g * (K.z * K.b) * g⁻¹ ∉ fsuV1 T V := fun h => K.hbV₂ (by
    have := C.conj_mem_V₂_F4 (C.plane.2 h)
    exact XCtx.mem_of_mul_mem (C.plane.2 K.hz) (by simpa [mul_assoc] using this))
  have hbz1 : g * (K.b * K.z) * g⁻¹ ∉ fsuV1 T V := by
    rw [C.W_comm_F4 K.hb (C.V1X_F4 K.hz)]; exact hzb1
  rcases hcd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact exists_transv (fun x hx => K.a_comm_F4 hx) hz2 (fun x hx y hy => K.comm_cases'_F4 hx hy)
      hzU' hbU' (C.exists_comm_ne'_F4 hzU' hz1) (C.exists_comm_ne'_F4 hbU' hb1)
      (C.exists_comm_ne'_F4 (mul_mem hzU' hbU') hzb1)
  · exact exists_transv (fun x hx => K.a_comm_F4 hx) hz2 (fun x hx y hy => K.comm_cases'_F4 hx hy)
      hbU' hzU' (C.exists_comm_ne'_F4 hbU' hb1) (C.exists_comm_ne'_F4 hzU' hz1)
      (C.exists_comm_ne'_F4 (mul_mem hbU' hzU') hbz1)

theorem Coords_F4.toAdd_zW_F4 : Multiplicative.toAdd (K.e K.zW_F4) = Pi.single 0 1 := by
  rw [Coords_F4.zW_F4, K.ez, toAdd_ofAdd]

theorem Coords_F4.toAdd_aW_F4 : Multiplicative.toAdd (K.e K.aW_F4) = Pi.single 1 1 := by
  rw [Coords_F4.aW_F4, K.ea, toAdd_ofAdd]

theorem Coords_F4.toAdd_bW_F4 : Multiplicative.toAdd (K.e K.bW_F4) = Pi.single 2 1 := by
  rw [Coords_F4.bW_F4, K.eb, toAdd_ofAdd]

theorem conjW_eq'_F4 {x : G} (hx : x ∈ lOne L V₂ ⊔ X ⊔ T) {w w' : ↥⁅V₂, X⁆}
    (h : x * (w : G) * x⁻¹ = w') : conjW_F4 C ⟨x, hx⟩ w = w' := Subtype.ext h

theorem Coords_F4.ex_mem_F4 : SL3.ex ∈ K.φ_F4.range := by
  obtain ⟨u, hu, h1, h2⟩ := K.exists_u_a_F4
  have hH := C.U_le_H3_F4 hu
  refine ⟨⟨u, hH⟩, K.φ_eq_F4 _ _ ?_ ?_ ?_⟩
  · rw [conjW_eq'_F4 hH (w' := K.zW_F4)
      (show u * K.z * u⁻¹ = K.z by rw [K.z_comm_F4 hu, mul_inv_cancel_right]), K.toAdd_zW_F4]
    decide +kernel
  · rw [conjW_eq'_F4 hH (w' := K.zW_F4 * K.aW_F4)
      (show u * (g⁻¹ * K.z * g) * u⁻¹ = K.z * (g⁻¹ * K.z * g) from conj_eq_of_comm h1),
      map_mul, toAdd_mul, K.toAdd_zW_F4, K.toAdd_aW_F4]
    decide +kernel
  · rw [conjW_eq'_F4 hH (w' := K.bW_F4)
      (show u * K.b * u⁻¹ = K.b by rw [conj_eq_of_comm h2, one_mul]), K.toAdd_bW_F4]
    decide +kernel

theorem Coords_F4.ez_mem_F4 : SL3.ez ∈ K.φ_F4.range := by
  obtain ⟨u, hu, h1, h2⟩ := K.exists_u_b_F4
  have hH := C.U_le_H3_F4 hu
  refine ⟨⟨u, hH⟩, K.φ_eq_F4 _ _ ?_ ?_ ?_⟩
  · rw [conjW_eq'_F4 hH (w' := K.zW_F4)
      (show u * K.z * u⁻¹ = K.z by rw [K.z_comm_F4 hu, mul_inv_cancel_right]), K.toAdd_zW_F4]
    decide +kernel
  · rw [conjW_eq'_F4 hH (w' := K.aW_F4)
      (show u * (g⁻¹ * K.z * g) * u⁻¹ = g⁻¹ * K.z * g by rw [conj_eq_of_comm h2, one_mul]),
      K.toAdd_aW_F4]
    decide +kernel
  · rw [conjW_eq'_F4 hH (w' := K.zW_F4 * K.bW_F4)
      (show u * K.b * u⁻¹ = K.z * K.b from conj_eq_of_comm h1), map_mul, toAdd_mul,
      K.toAdd_zW_F4, K.toAdd_bW_F4]
    decide +kernel

theorem Coords_F4.t10_mem_F4 : t10 ∈ K.φ_F4.range := by
  obtain ⟨v, hv, h1, h2⟩ := K.exists_v_F4 K.z K.b (Or.inl ⟨rfl, rfl⟩)
  have hH := C.conjU_le_H3_F4 hv
  refine ⟨⟨v, hH⟩, K.φ_eq_F4 _ _ ?_ ?_ ?_⟩
  · rw [conjW_eq'_F4 hH (w' := K.aW_F4 * K.zW_F4)
      (show v * K.z * v⁻¹ = (g⁻¹ * K.z * g) * K.z from conj_eq_of_comm h1), map_mul,
      toAdd_mul, K.toAdd_zW_F4, K.toAdd_aW_F4]
    decide +kernel
  · rw [conjW_eq'_F4 hH (w' := K.aW_F4)
      (show v * (g⁻¹ * K.z * g) * v⁻¹ = g⁻¹ * K.z * g by
        rw [K.a_comm_F4 hv, mul_inv_cancel_right]), K.toAdd_aW_F4]
    decide +kernel
  · rw [conjW_eq'_F4 hH (w' := K.bW_F4)
      (show v * K.b * v⁻¹ = K.b by rw [conj_eq_of_comm h2, one_mul]), K.toAdd_bW_F4]
    decide +kernel

theorem Coords_F4.ey_mem_F4 : SL3.ey ∈ K.φ_F4.range := by
  obtain ⟨v, hv, h1, h2⟩ := K.exists_v_F4 K.b K.z (Or.inr ⟨rfl, rfl⟩)
  have hH := C.conjU_le_H3_F4 hv
  refine ⟨⟨v, hH⟩, K.φ_eq_F4 _ _ ?_ ?_ ?_⟩
  · rw [conjW_eq'_F4 hH (w' := K.zW_F4)
      (show v * K.z * v⁻¹ = K.z by rw [conj_eq_of_comm h2, one_mul]), K.toAdd_zW_F4]
    decide +kernel
  · rw [conjW_eq'_F4 hH (w' := K.aW_F4)
      (show v * (g⁻¹ * K.z * g) * v⁻¹ = g⁻¹ * K.z * g by
        rw [K.a_comm_F4 hv, mul_inv_cancel_right]), K.toAdd_aW_F4]
    decide +kernel
  · rw [conjW_eq'_F4 hH (w' := K.aW_F4 * K.bW_F4)
      (show v * K.b * v⁻¹ = (g⁻¹ * K.z * g) * K.b from conj_eq_of_comm h1), map_mul,
      toAdd_mul, K.toAdd_aW_F4, K.toAdd_bW_F4]
    decide +kernel

theorem Coords_F4.range_eq_top_F4 : K.φ_F4.range = ⊤ := by
  have hP0 : SL3.P0 ≤ K.φ_F4.range := by
    intro A hA
    have hl := mem_P0list A (Subgroup.mem_inf.mp hA).1 (Subgroup.mem_inf.mp hA).2
    have hx := K.ex_mem_F4
    have hy := K.ey_mem_F4
    have hz := K.ez_mem_F4
    simp only [SL3.P0list, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact hy
    · exact hz
    · exact mul_mem hy hz
    · exact hx
    · exact mul_mem hy hx
    · exact mul_mem hx hz
    · exact mul_mem hx hy
  rcases SL3.overgroups_SL3 _ hP0 with h | h | h | h
  · have : t10 ∈ SL3.P0 := h ▸ K.t10_mem_F4
    exact absurd (Subgroup.mem_inf.mp this).1 not_inX1_t10
  · have : t10 ∈ SL3.X1 := h ▸ K.t10_mem_F4
    exact absurd this not_inX1_t10
  · obtain ⟨x, -, hx⟩ := K.exists_not_inX2_F4
    have : K.φ_F4 x ∈ SL3.X2 := h ▸ (⟨x, rfl⟩ : K.φ_F4 x ∈ K.φ_F4.range)
    exact absurd this hx
  · exact h

theorem Coords_F4.surjective_F4 : Function.Surjective K.φ_F4 :=
  MonoidHom.range_eq_top.mp K.range_eq_top_F4

end XCtx_F4

end CFSG.Quasithin.H13.L14413
