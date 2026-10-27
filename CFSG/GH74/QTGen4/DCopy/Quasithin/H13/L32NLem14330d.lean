module

public import CFSG.Quasithin.H13.L32NLem14330d
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14328e
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14330c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14332a

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

namespace L14328

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} [IsMulCommutative ↥V]

namespace Ctx_F4

variable {g z b l : G} (C : Ctx_F4 G T L V V₂ g z b l) (D : HatModelU (fsuU T V))
include C

theorem z_zU_F4 : z ∈ centerOf (fsuU T V) := C.lt.le C.z_mem

theorem not_mem_zU_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) {v : G} (hv : v ∈ V)
    (hv1 : v ∉ fsuV1 T V) : v ∉ centerOf (fsuU T V) := fun h => hv1 (by
  rw [← lemma12_8_8_three_F4 h1222 h12213 C.setting]
  exact ⟨hv, h⟩)

theorem pi_ne_zero_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) {v : G} (hv : v ∈ V)
    (hv1 : v ∉ fsuV1 T V) : D.π v ≠ 0 := by
  rw [Ne, L128A.HatU.π_eq_zero_iff D (Ctx.V_le_U hv)]
  exact C.not_mem_zU_F4 h1222 h12213 hv hv1

theorem mem_W_F4 {u : G} (hu : u ∈ fsuU T V) (hua : u * (g⁻¹ * z * g) = (g⁻¹ * z * g) * u) :
    u ∈ fsuU T V ⊓ Subgroup.centralizer (V₂ : Set G) := by
  have huz : z * u = u * z := (Subgroup.mem_centralizer_iff.mp C.z_zU_F4.2 u hu).symm
  refine ⟨hu, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
  by_cases hv1 : v = 1
  · rw [hv1, one_mul, mul_one]
  rcases C.V2_cases_F4 hv hv1 with rfl | rfl | rfl
  · exact huz
  · exact hua.symm
  · rw [mul_assoc, ← hua, ← mul_assoc, huz, mul_assoc]

theorem mem_W'_F4 {V₂' : Subgroup G} (hmem : ∀ v, v ∈ V₂' ↔ v = 1 ∨ v = z ∨ v = z * b ∨ v = b)
    {u : G} (hu : u ∈ fsuU T V) (huzb : u * (z * b) = (z * b) * u) :
    u ∈ fsuU T V ⊓ Subgroup.centralizer (V₂' : Set G) := by
  have huz : z * u = u * z := (Subgroup.mem_centralizer_iff.mp C.z_zU_F4.2 u hu).symm
  have hzz := C.mul_self_V_F4 C.z_V_F4
  refine ⟨hu, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
  rcases (hmem v).mp hv with rfl | rfl | rfl | rfl
  · rw [one_mul, mul_one]
  · exact huz
  · exact huzb.symm
  · have e : v = z * (z * v) := by rw [← mul_assoc, hzz, one_mul]
    rw [e, mul_assoc, ← huzb, ← mul_assoc, huz, mul_assoc]

theorem pi_sup_V2_F4 {y : G} (hy : y ∈ centerOf (fsuU T V) ⊔ V₂) :
    D.π y = 0 ∨ D.π y = D.π (g⁻¹ * z * g) := by
  have hV₂U : V₂ ≤ fsuU T V := C.plane.1.1.trans Ctx.V_le_U
  have hN : V₂ ≤ Subgroup.normalizer (centerOf (fsuU T V) : Set G) := fun v hv =>
    Ctx.U_le_normalizer_zU (hV₂U hv)
  obtain ⟨y₀, hy₀, v, hv, rfl⟩ := exists_mul_of_mem_sup hN hy
  rw [Ctx.pi_mul_zU D hy₀ (hV₂U hv)]
  by_cases hv1 : v = 1
  · left
    rw [hv1, L128A.HatU.π_one]
  rcases C.V2_cases_F4 hv hv1 with rfl | rfl | rfl
  · left
    exact (L128A.HatU.π_eq_zero_iff D C.z_zU_F4.1).mpr C.z_zU_F4
  · right
    rfl
  · right
    exact Ctx.pi_mul_zU D C.z_zU_F4 (hV₂U C.a_mem_F4)

theorem pi_sup_V2'_F4 {V₂' : Subgroup G} (hmem : ∀ v, v ∈ V₂' ↔ v = 1 ∨ v = z ∨ v = z * b ∨ v = b)
    {y : G} (hy : y ∈ centerOf (fsuU T V) ⊔ V₂') : D.π y = 0 ∨ D.π y = D.π (z * b) := by
  have hzbU : z * b ∈ fsuU T V := Ctx.V_le_U (V.mul_mem C.z_V_F4 C.b_mem)
  have hbU : b ∈ fsuU T V := Ctx.V_le_U C.b_mem
  have hV₂U : V₂' ≤ fsuU T V := fun v hv => by
    rcases (hmem v).mp hv with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact C.z_zU_F4.1
    · exact hzbU
    · exact hbU
  have hN : V₂' ≤ Subgroup.normalizer (centerOf (fsuU T V) : Set G) := fun v hv =>
    Ctx.U_le_normalizer_zU (hV₂U hv)
  obtain ⟨y₀, hy₀, v, hv, rfl⟩ := exists_mul_of_mem_sup hN hy
  rw [Ctx.pi_mul_zU D hy₀ (hV₂U hv)]
  rcases (hmem v).mp hv with rfl | rfl | rfl | rfl
  · left
    exact L128A.HatU.π_one D
  · left
    exact (L128A.HatU.π_eq_zero_iff D C.z_zU_F4.1).mpr C.z_zU_F4
  · right
    rfl
  · right
    rw [Ctx.pi_mul_zU D C.z_zU_F4 hbU]

theorem B_ab_F4 : D.B (D.π (g⁻¹ * z * g)) (D.π (z * b)) = 0 :=
  (D.B_spec _ (Ctx.V_le_U C.a_V_F4) _ (Ctx.V_le_U (V.mul_mem C.z_V_F4 C.b_mem))).mpr (by
    rw [C.mul_comm_V_F4 C.a_V_F4 (V.mul_mem C.z_V_F4 C.b_mem)]
    group)

theorem zb_nmem_F4 : z * b ∉ fsuV1 T V := fun h => C.b_nmem (by
  rw [show b = z * (z * b) by rw [← mul_assoc, C.mul_self_V_F4 C.z_V_F4, one_mul]]
  exact V₂.mul_mem C.z_V₂_F4 (C.plane.2 h))

theorem pi_a_ne_pi_zb_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) :
    D.π (g⁻¹ * z * g) ≠ D.π (z * b) := by
  intro h
  rw [D.π_eq_iff _ (Ctx.V_le_U C.a_V_F4) _ (Ctx.V_le_U (V.mul_mem C.z_V_F4 C.b_mem))] at h
  have hV : (g⁻¹ * z * g)⁻¹ * (z * b) ∈ V := V.mul_mem (V.inv_mem C.a_V_F4) (V.mul_mem C.z_V_F4 C.b_mem)
  have h1' : (g⁻¹ * z * g)⁻¹ * (z * b) ∈ fsuV1 T V := by
    rw [← lemma12_8_8_three_F4 h1222 h12213 C.setting]
    exact ⟨hV, h⟩
  apply C.b_nmem
  rw [show b = z⁻¹ * ((g⁻¹ * z * g) * ((g⁻¹ * z * g)⁻¹ * (z * b))) by group]
  exact V₂.mul_mem (V₂.inv_mem C.z_V₂_F4) (V₂.mul_mem C.a_mem_F4 (C.plane.2 h1'))

theorem exists_dual_ab_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) :
    ∃ ua ub : D.V, D.B ua (D.π (g⁻¹ * z * g)) = 1 ∧ D.B ub (D.π (z * b)) = 1 ∧
      D.B ub (D.π (g⁻¹ * z * g)) = 0 ∧ D.B ua (D.π (z * b)) = 0 := by
  have hnd : ∀ v, (∀ w, D.B w v = 0) → v = 0 := fun v hv =>
    L128A.HatU.B_nondegenerate D v fun w => by
      rw [L14330.B_symm D.B (L128A.HatU.B_isAlt D)]
      exact hv w
  exact L14330.exists_dual D.B hnd (C.pi_ne_zero_F4 D h1222 h12213 C.a_V_F4 C.a_nmem_F4)
    (C.pi_ne_zero_F4 D h1222 h12213 (V.mul_mem C.z_V_F4 C.b_mem) C.zb_nmem_F4)
    (C.pi_a_ne_pi_zb_F4 D h1222 h12213)

theorem exists_second_zU_F4 (h1222 : Stmt12_2_2_F4) : ∃ (T' V₂' : Subgroup G) (k : G),
    Setting1282One G T' L V 3 (fsuV1 T V) V₂' ∧
    (∀ v, v ∈ V₂' ↔ v = 1 ∨ v = z ∨ v = z * b ∨ v = b) ∧
    k⁻¹ ∈ p128 T' L V ∧ k⁻¹ ∉ Subgroup.normalizer (fsuV1 T V : Set G) ∧ k * z * k⁻¹ = z * b ∧
    CFSG.conjugate (centerOf (fsuU T V)) k⁻¹ = CFSG.conjugate (centerOf (fsuU T V)) l := by
  obtain ⟨T', V₂', k, hs', hmem', hkP, hkN, hkz, hkV⟩ := C.exists_second_F4 h1222
  refine ⟨T', V₂', k, hs', hmem', hkP, hkN, hkz, ?_⟩
  rw [C.conj_zU_F4 ((Subgroup.normalizer _).inv_mem hkV), C.conj_zU_F4 (C.L_le_F4 C.l_mem), inv_inv,
    hkz, C.l_inv_z_F4]

theorem rho_eq_F4 (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) (h12810 : Lemma12_8_10_F4)
    (h12813 : Lemma12_8_13_F4) {x : G}
    (hx : x ∈ CFSG.conjugate (centerOf (fsuU T V)) g ⊓ CFSG.conjugate (centerOf (fsuU T V)) l) :
    ∃ hxN : x ∈ Subgroup.normalizer (fsuU T V : Set G), ∃ ε : ZMod 2, ∀ v,
      D.ρ ⟨x, hxN⟩ v = v + ε • (D.B v (D.π (g⁻¹ * z * g)) • D.π (z * b) +
        D.B v (D.π (z * b)) • D.π (g⁻¹ * z * g)) := by
  have hxH : x ∈ l32nH T V := L14332.conj_zU_le_F4 h12813 C.setting C.gP C.gN hx.1
  have hxN := L14332.l32nH_le_normalizer_fsuU T V hxH
  refine ⟨hxN, ?_⟩
  obtain ⟨T', V₂', k, hs', hmem', hkP, hkN, -, hkl⟩ := C.exists_second_zU_F4 h1222
  have h4 := (h12810 G T L V 3 (fsuV1 T V) V₂ C.setting g C.gP C.gN).2.2.2.1.1
  have h4' := (h12810 G T' L V 3 (fsuV1 T V) V₂' hs' k⁻¹ hkP hkN).2.2.2.1.1
  have hxl : x ∈ CFSG.conjugate (centerOf (fsuU T V)) k⁻¹ := hkl ▸ hx.2
  set δ : D.V →ₗ[ZMod 2] D.V := (D.ρ ⟨x, hxN⟩).toLinearMap - LinearMap.id with hδ
  have hρδ : ∀ v, D.ρ ⟨x, hxN⟩ v = v + δ v := fun v => by
    simp only [hδ, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply]
    abel
  have hδπ : ∀ u ∈ fsuU T V, δ (D.π u) = D.π (x * u * x⁻¹ * u⁻¹) := fun u hu => by
    have := Ctx.rho_pi D hxN hu
    rw [hρδ] at this
    exact add_left_cancel this
  have haU : g⁻¹ * z * g ∈ fsuU T V := Ctx.V_le_U C.a_V_F4
  have hzbU : z * b ∈ fsuU T V := Ctx.V_le_U (V.mul_mem C.z_V_F4 C.b_mem)
  have hcomm_of : ∀ {u w : G}, u ∈ fsuU T V → w ∈ fsuU T V → D.B (D.π u) (D.π w) = 0 →
      u * w = w * u := fun {u w} hu hw h0 => by
    have hc := (D.B_spec u hu w hw).mp h0
    calc u * w = u * w * u⁻¹ * w⁻¹ * (w * u) := by group
      _ = w * u := by rw [hc, one_mul]
  have hinvx : ∀ {y : G} {Y : Subgroup G}, ⁅y, x⁆ ∈ Y → x * y * x⁻¹ * y⁻¹ ∈ Y :=
    fun {y Y} h => by
      have := Y.inv_mem h
      rw [commutatorElement_def] at this
      convert this using 1
      group

  have h1 : ∀ v, D.B v (D.π (g⁻¹ * z * g)) = 0 → δ v ∈ (ZMod 2) ∙ D.π (g⁻¹ * z * g) := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := D.π_surj v
    have hW := C.mem_W_F4 hu (hcomm_of hu haU hv)
    have hmem := hinvx (h4 (Subgroup.commutator_mem_commutator hW hx.1))
    rw [hδπ u hu, L14330.mem_span_singleton_zmod2]
    exact C.pi_sup_V2_F4 D hmem

  have h2 : ∀ v, D.B v (D.π (z * b)) = 0 → δ v ∈ (ZMod 2) ∙ D.π (z * b) := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := D.π_surj v
    have hW' := C.mem_W'_F4 hmem' hu (hcomm_of hu hzbU hv)
    have hmem := hinvx (h4' (Subgroup.commutator_mem_commutator hW' hxl))
    rw [hδπ u hu, L14330.mem_span_singleton_zmod2]
    exact C.pi_sup_V2'_F4 D hmem' hmem
  obtain ⟨ua, ub, hα₁, hβ₁, hα₂, hβ₂⟩ := C.exists_dual_ab_F4 D h1222 h12213
  refine L14330.delta_eq_of_inv D.B (L128A.HatU.B_isAlt D) hα₁ hβ₁ hα₂ hβ₂ (C.B_ab_F4 D) h1 h2
    (fun u v => ?_) |>.imp fun ε hε v => by rw [hρδ, hε]
  have := L128A.HatU.B_rho D ⟨x, hxN⟩ u v
  rwa [hρδ, hρδ] at this

end Ctx_F4

end L14328

end CFSG.Quasithin.H13
