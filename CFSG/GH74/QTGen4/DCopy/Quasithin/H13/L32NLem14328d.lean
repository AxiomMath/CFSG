module

public import CFSG.Quasithin.H13.L32NLem14328d
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14328c

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L14328

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} [IsMulCommutative ↥V]

namespace Ctx_F4

variable {g z b l : G} (C : Ctx_F4 G T L V V₂ g z b l)
include C

theorem P_le_F4 : p128 T L V ≤ Subgroup.normalizer (V : Set G) :=
  L128P.p128_le_normalizer (i := 3) (by norm_num)
    ⟨le_rfl, C.S.card_V_F4, C.S.TV_F4⟩

theorem L_le_F4 : L ≤ Subgroup.normalizer (V : Set G) := C.S.LV_F4

theorem V1_eq_F4 : fsuV1 T V = Subgroup.zpowers z := by
  have h2 : z ^ 2 = 1 := by rw [pow_two]; exact C.S.mul_self_V_F4 C.z_V_F4
  have ho : orderOf z = 2 := orderOf_eq_prime h2 C.z_ne
  refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr C.z_mem) ?_).symm
  rw [Nat.card_zpowers, ho, C.S.card_V1_F4]

theorem zU_eq_F4 : centerOf (fsuU T V) = zv V z := by
  rw [zv, ← C.V1_eq_F4]

theorem conj_zU_F4 {x : G} (hx : x ∈ Subgroup.normalizer (V : Set G)) :
    CFSG.conjugate (centerOf (fsuU T V)) x = zv V (x⁻¹ * z * x) := by
  rw [C.zU_eq_F4, conjugate_zv hx]

theorem zI_za_F4 : centerOf (i128 T L V (fsuV1 T V)) = zv V z ⊓ zv V (g⁻¹ * z * g) := by
  rw [C.zI, C.conj_zU_F4 (C.P_le_F4 C.gP), C.zU_eq_F4]

theorem mul_comm_V_F4 {v w : G} (hv : v ∈ V) (hw : w ∈ V) : v * w = w * v := C.S.comm_V_F4 hv hw

theorem mul_self_V_F4 {v : G} (hv : v ∈ V) : v * v = 1 := C.S.mul_self_V_F4 hv

theorem V2_cases_F4 {v : G} (hv : v ∈ V₂) (hv1 : v ≠ 1) :
    v = z ∨ v = g⁻¹ * z * g ∨ v = z * (g⁻¹ * z * g) := by
  rcases C.S.mem_V2_F4 C.a_mem_F4 C.a_nmem_F4 hv with h | h
  · rcases C.S.eq_of_mem_V1_F4 C.z_mem C.z_ne h with h1 | h1
    · exact absurd h1 hv1
    · exact Or.inl h1
  · have haa := C.mul_self_V_F4 C.a_V_F4
    rcases C.S.eq_of_mem_V1_F4 C.z_mem C.z_ne h with h1 | h1
    · right; left
      calc v = (g⁻¹ * z * g) * ((g⁻¹ * z * g) * v) := by rw [← mul_assoc, haa, one_mul]
        _ = g⁻¹ * z * g := by rw [h1, mul_one]
    · right; right
      calc v = (g⁻¹ * z * g) * ((g⁻¹ * z * g) * v) := by rw [← mul_assoc, haa, one_mul]
        _ = (g⁻¹ * z * g) * z := by rw [h1]
        _ = z * (g⁻¹ * z * g) := C.mul_comm_V_F4 C.a_V_F4 C.z_V_F4

theorem exists_k_F4 (h1222 : Stmt12_2_2_F4) : ∃ k ∈ p128 T L V, k * z * k⁻¹ = g⁻¹ * z * g ∧
    k * (g⁻¹ * z * g) * k⁻¹ = z * (g⁻¹ * z * g) := by
  obtain ⟨k, hk, hkz, hka, -⟩ := L128P.exists_rotation_mem_F4 h1222 C.setting.hyp C.setting.v1
    C.setting.v2 C.setting.le C.z_mem C.z_ne C.a_mem_F4 C.a_nmem_F4
  exact ⟨k, oTwoUpper_le _ hk, hkz, hka⟩

theorem zI_pairs_F4 (h1222 : Stmt12_2_2_F4) :
    centerOf (i128 T L V (fsuV1 T V)) = zv V z ⊓ zv V (g⁻¹ * z * g) ∧
    centerOf (i128 T L V (fsuV1 T V)) = zv V (g⁻¹ * z * g) ⊓ zv V (z * (g⁻¹ * z * g)) ∧
    centerOf (i128 T L V (fsuV1 T V)) = zv V (z * (g⁻¹ * z * g)) ⊓ zv V z := by
  obtain ⟨k, hkP, hkz, hka⟩ := C.exists_k_F4 h1222
  have hkN := C.P_le_F4 hkP
  have hkN' : k⁻¹ ∈ Subgroup.normalizer (V : Set G) := (Subgroup.normalizer _).inv_mem hkN
  have hkzz : k * (z * (g⁻¹ * z * g)) * k⁻¹ = z := by
    rw [show k * (z * (g⁻¹ * z * g)) * k⁻¹ = (k * z * k⁻¹) * (k * (g⁻¹ * z * g) * k⁻¹) by group,
      hkz, hka, ← mul_assoc, C.mul_comm_V_F4 C.a_V_F4 C.z_V_F4, mul_assoc, C.mul_self_V_F4 C.a_V_F4, mul_one]
  have h1 := C.zI_za_F4
  have h2 : centerOf (i128 T L V (fsuV1 T V)) =
      zv V (g⁻¹ * z * g) ⊓ zv V (z * (g⁻¹ * z * g)) := by
    have := congrArg (fun X => CFSG.conjugate X k⁻¹) h1
    rw [Ctx.conj_zI ((p128 T L V).inv_mem hkP), conjugate_inf, conjugate_zv hkN', conjugate_zv hkN',
      inv_inv, hkz, hka] at this
    exact this
  have h3 : centerOf (i128 T L V (fsuV1 T V)) = zv V (z * (g⁻¹ * z * g)) ⊓ zv V z := by
    have := congrArg (fun X => CFSG.conjugate X k⁻¹) h2
    rw [Ctx.conj_zI ((p128 T L V).inv_mem hkP), conjugate_inf, conjugate_zv hkN', conjugate_zv hkN',
      inv_inv, hka, hkzz] at this
    exact this
  exact ⟨h1, h2, h3⟩

theorem zI_pair_F4 (h1222 : Stmt12_2_2_F4) {v w : G} (hv : v ∈ V₂) (hw : w ∈ V₂) (hv1 : v ≠ 1)
    (hw1 : w ≠ 1) (hvw : v ≠ w) :
    zv V v ⊓ zv V w = centerOf (i128 T L V (fsuV1 T V)) := by
  obtain ⟨h1, h2, h3⟩ := C.zI_pairs_F4 h1222
  rcases C.V2_cases_F4 hv hv1 with rfl | rfl | rfl <;> rcases C.V2_cases_F4 hw hw1 with rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hvw
    | exact h1.symm
    | exact h2.symm
    | exact h3.symm
    | (rw [inf_comm]; exact h1.symm)
    | (rw [inf_comm]; exact h2.symm)
    | (rw [inf_comm]; exact h3.symm)

theorem zI_le_F4 (h1222 : Stmt12_2_2_F4) {v : G} (hv : v ∈ V₂) (hv1 : v ≠ 1) :
    centerOf (i128 T L V (fsuV1 T V)) ≤ zv V v := by
  obtain ⟨h1, h2, h3⟩ := C.zI_pairs_F4 h1222
  rcases C.V2_cases_F4 hv hv1 with rfl | rfl | rfl
  · rw [h1]; exact inf_le_left
  · rw [h2]; exact inf_le_left
  · rw [h3]; exact inf_le_left

theorem zv_inf_le_F4 (h1222 : Stmt12_2_2_F4) {x u w : G} (hx : x ∈ Subgroup.normalizer (V : Set G))
    (hu : x * u * x⁻¹ ∈ V₂) (hw : x * w * x⁻¹ ∈ V₂) (hu1 : u ≠ 1) (hw1 : w ≠ 1) (huw : u ≠ w) :
    zv V u ⊓ zv V w ≤ zv V (u * w) := by
  have hu1' : x * u * x⁻¹ ≠ 1 := fun h => hu1 (by
    calc u = x⁻¹ * (x * u * x⁻¹) * x := by group
      _ = 1 := by rw [h]; group)
  have hw1' : x * w * x⁻¹ ≠ 1 := fun h => hw1 (by
    calc w = x⁻¹ * (x * w * x⁻¹) * x := by group
      _ = 1 := by rw [h]; group)
  have huw' : x * u * x⁻¹ ≠ x * w * x⁻¹ := fun h => huw (by simpa using h)
  have huwV₂ : x * u * x⁻¹ * (x * w * x⁻¹) ∈ V₂ := V₂.mul_mem hu hw
  have huw1 : x * u * x⁻¹ * (x * w * x⁻¹) ≠ 1 := by
    intro h
    apply huw'
    have hwV := C.plane.1.1 hw
    calc x * u * x⁻¹ = x * u * x⁻¹ * ((x * w * x⁻¹) * (x * w * x⁻¹)) := by
          rw [C.mul_self_V_F4 hwV, mul_one]
      _ = x * u * x⁻¹ * (x * w * x⁻¹) * (x * w * x⁻¹) := by group
      _ = x * w * x⁻¹ := by rw [h, one_mul]
  have key := (C.zI_pair_F4 h1222 hu hw hu1' hw1' huw').le.trans (C.zI_le_F4 h1222 huwV₂ huw1)
  have hc := conjugate_mono key x
  rw [conjugate_inf, conjugate_zv hx, conjugate_zv hx, conjugate_zv hx] at hc
  convert hc using 2 <;> group

end Ctx_F4

end L14328

end CFSG.Quasithin.H13
