module

public import CFSG.Quasithin.H13.L32NLem14411e
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14411d

public section

namespace CFSG.Quasithin.H13.L14411

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open Mat8Cert S7Cert L1442M
open scoped commutatorElement

variable {G : Type} [Group G] {T V : Subgroup G}

variable [CFSG.GH74.QTGen4.Finite4 G] {L V₂ : Subgroup G} {g : G}
  {D : HatModelU (fsuU T V)} {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)}

namespace Ctx_F4
open CFSG.Quasithin.H13.L14411.Ctx_F4

variable (C : Ctx_F4 G T L V V₂ g D e)
include C

theorem e_pi_comm_F4 {a x : G} (ha : a ∈ V₂) (hx : x ∈ l32nH T V) :
    e (D.π (a * x * a⁻¹ * x⁻¹)) =
      ((matOf e (D.ρ ⟨x, HN hx⟩) : GL (Fin 8) (ZMod 2)) :
        Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (e (D.π a)) + e (D.π a) := by
  have haU := C.V2U_F4 ha
  have hc : a * x * a⁻¹ * x⁻¹ = (x * a * x⁻¹ * a⁻¹)⁻¹ := by group
  have hcU : x * a * x⁻¹ * a⁻¹ ∈ fsuU T V :=
    Subgroup.mul_mem _ (L128A.HatU.conj_mem (HN hx) haU) (Subgroup.inv_mem _ haU)
  rw [hc, L128A.HatU.π_inv D hcU, ← L128A.HatU.rho_sub_π D (HN hx) haU, neg_sub, sub_eq_add_neg,
    neg_eq_self_zmod2, map_add, matOf_mulVec, add_comm]

theorem comm_mem_U_F4 {a x : G} (ha : a ∈ V₂) (hx : x ∈ l32nH T V) :
    a * x * a⁻¹ * x⁻¹ ∈ fsuU T V := by
  rw [show a * x * a⁻¹ * x⁻¹ = a * (x * a⁻¹ * x⁻¹) by group]
  exact Subgroup.mul_mem _ (C.V2U_F4 ha) (L128A.HatU.conj_mem (HN hx) (Subgroup.inv_mem _ (C.V2U_F4 ha)))

theorem V2E_F4 : V₂ ≤ l32nE T V V₂ g := by
  obtain ⟨_, S⟩ := C.set14_F4
  have hW : V₂ ≤ l32nW T V V₂ := fun v hv => ⟨C.V2U_F4 hv, Subgroup.mem_centralizer_iff.mpr
    fun w hw => S.comm_V_F4 (C.plane.1.1 hw) (C.plane.1.1 hv)⟩
  refine le_inf hW fun v hv => ?_
  rw [show CFSG.conjugate (l32nW T V V₂) g = rconj (l32nW T V V₂) g from rfl, mem_rconj]
  exact hW ((Subgroup.mem_normalizer_iff.mp C.gV₂_F4 v).mp hv)

end Ctx_F4

section Cert


namespace Ctx_F4
open CFSG.Quasithin.H13.L14411.Ctx_F4

variable (C : Ctx_F4 G T L V V₂ g D e)
include C

theorem vec_mem_F4 {k : ℕ} (hk : k = 1 ∨ k = 2) {a x : G} (ha : a ∈ V₂) (haV : a ∉ fsuV1 T V)
    (hx : x ∈ xk D e k) :
    e (D.π (a * x * a⁻¹ * x⁻¹)) ∈ ({0, vec8 (oWs.getD k (0, 0)).1, vec8 (oWs.getD k (0, 0)).2,
      vec8 (oWs.getD k (0, 0)).1 + vec8 (oWs.getD k (0, 0)).2} : Set (Fin 8 → ZMod 2)) := by
  have hxH := xk_le_H k hx
  rw [C.e_pi_comm_F4 ha hxH, C.e_pi_a_F4 ha haV]
  refine O7_vec hk ?_
  rw [← C.img_xk_F4 (by omega : k < 3)]
  exact (mem_img8 D e).mpr ⟨x, hx, _, rfl⟩

theorem commutator_le_preP_F4 {k : ℕ} (hk : k = 1 ∨ k = 2) :
    ⁅V₂, xk D e k⁆ ≤ preP D (planeK e k) := by
  obtain ⟨_, S⟩ := C.set14_F4
  obtain ⟨a, ha, haV⟩ := C.abs.exists_mem_not_mem
  rw [Subgroup.commutator_le]
  intro v hv x hx
  have hxH := xk_le_H k hx
  have hcen : ∀ z ∈ fsuV1 T V, z * x = x * z := fun z hz =>
    (Subgroup.mem_centralizer_iff.mp (C.abs.normalizer_eq_centralizer ▸ hxH) z hz)
  rw [commutatorElement_def]
  rcases S.mem_V2_F4 ha haV hv with h1 | h1
  · rw [show v * x * v⁻¹ * x⁻¹ = (v * x) * v⁻¹ * x⁻¹ from rfl, hcen v h1,
      show x * v * v⁻¹ * x⁻¹ = 1 by group]
    exact one_mem _
  · have haa : a * a = 1 := S.mul_self_V_F4 (C.plane.1.1 ha)
    have hv' : v = a * (a * v) := by rw [← mul_assoc, haa, one_mul]
    have he : v * x * v⁻¹ * x⁻¹ = a * x * a⁻¹ * x⁻¹ := by
      rw [hv']
      calc a * (a * v) * x * (a * (a * v))⁻¹ * x⁻¹
          = a * ((a * v) * x) * (a * v)⁻¹ * a⁻¹ * x⁻¹ := by group
        _ = a * (x * (a * v)) * (a * v)⁻¹ * a⁻¹ * x⁻¹ := by rw [hcen _ h1]
        _ = a * x * a⁻¹ * x⁻¹ := by group
    rw [he]
    exact ⟨C.comm_mem_U_F4 ha hxH, mem_planeK (C.vec_mem_F4 hk ha haV hx)⟩

theorem V1_le_commutator_F4 {k : ℕ} (hk : k = 1 ∨ k = 2) : fsuV1 T V ≤ ⁅V₂, xk D e k⁆ := by
  obtain ⟨a, ha, haV⟩ := C.abs.exists_mem_not_mem
  have haU := C.V2U_F4 ha
  have hk3 : k < 3 := by omega
  have himg : ∀ y ∈ O7 k, ∃ x ∈ xk D e k, ∃ hx : x ∈ Subgroup.normalizer (fsuU T V : Set G),
      matOf e (D.ρ ⟨x, hx⟩) = y := fun y hy =>
    (mem_img8 D e).mp (by rw [C.img_xk_F4 hk3]; exact hy)

  obtain ⟨y, hy, hyw⟩ := (O7_vec_eq hk).1
  obtain ⟨x, hx, hxN, rfl⟩ := himg y hy
  have hxH := xk_le_H k hx
  set s := a * x * a⁻¹ * x⁻¹ with hs
  have hsA : s ∈ ⁅V₂, xk D e k⁆ := by
    rw [hs, ← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator ha hx
  have hsU : s ∈ fsuU T V := C.comm_mem_U_F4 ha hxH
  have hes : e (D.π s) = vec8 (oWs.getD k (0, 0)).1 := by
    rw [hs, C.e_pi_comm_F4 ha hxH, C.e_pi_a_F4 ha haV, ← hyw]

  obtain ⟨y', hy', v, hv⟩ := O7_b4 hk
  obtain ⟨x', hx', hx'N, rfl⟩ := himg y' hy'
  obtain ⟨u, hu, hue⟩ := D.π_surj (e.symm (vec8 v))
  set r := x' * u * x'⁻¹ * u⁻¹ with hr
  have hrU : r ∈ fsuU T V :=
    Subgroup.mul_mem _ (L128A.HatU.conj_mem hx'N hu) (Subgroup.inv_mem _ hu)
  have hrX : r ∈ xk D e k := by
    rw [hr, show x' * u * x'⁻¹ * u⁻¹ = x' * (u * x'⁻¹ * u⁻¹) by group]
    exact Subgroup.mul_mem _ hx' ((Subgroup.mem_normalizer_iff.mp
      (C.U_le_normalizer_xk_F4 k hu) _).mp (Subgroup.inv_mem _ hx'))
  have hB : D.B (D.π r) (D.π s) = 1 := by
    rw [C.form, hes, hr, ← L128A.HatU.rho_sub_π D hx'N hu, sub_eq_add_neg, neg_eq_self_zmod2,
      map_add, ← matOf_mulVec, hue, LinearEquiv.apply_symm_apply]
    exact hv

  have hc1 : r * s * r⁻¹ * s⁻¹ ≠ 1 := fun h => by
    have := (D.B_spec r hrU s hsU).mpr h
    rw [hB] at this
    exact one_ne_zero this
  have hcV1 : r * s * r⁻¹ * s⁻¹ ∈ fsuV1 T V := by
    rw [← C.zU]
    exact C.comm_center_F4 r hrU s hsU
  have hcA : r * s * r⁻¹ * s⁻¹ ∈ ⁅V₂, xk D e k⁆ := by
    refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ hsA)
    exact (Subgroup.mem_normalizer_iff.mp
      (L14413.le_normalizer_commutator_right V₂ (xk D e k) hrX) s).mp hsA
  intro z hz
  obtain ⟨_, S⟩ := C.set14_F4
  rcases S.eq_of_mem_V1_F4 hcV1 hc1 hz with rfl | rfl
  · exact one_mem _
  · exact hcA

theorem exists_s_F4 {k : ℕ} (hk : k = 1 ∨ k = 2) {y : GL (Fin 8) (ZMod 2)} (hy : y ∈ O7 k) :
    ∃ s ∈ ⁅V₂, xk D e k⁆, s ∈ fsuU T V ∧
      e (D.π s) = (y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 vStar) + vec8 vStar := by
  obtain ⟨a, ha, haV⟩ := C.abs.exists_mem_not_mem
  obtain ⟨x, hx, hxN, rfl⟩ := (mem_img8 D e).mp (by rw [C.img_xk_F4 (by omega : k < 3)]; exact hy)
  have hxH := xk_le_H k hx
  refine ⟨a * x * a⁻¹ * x⁻¹, ?_, C.comm_mem_U_F4 ha hxH, ?_⟩
  · rw [← commutatorElement_def]
    exact Subgroup.commutator_mem_commutator ha hx
  · rw [C.e_pi_comm_F4 ha hxH, C.e_pi_a_F4 ha haV]

theorem hat_commutator_F4 {k : ℕ} (hk : k = 1 ∨ k = 2) : D.hat ⁅V₂, xk D e k⁆ = planeK e k := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨t, ⟨ht, -⟩, rfl⟩
    exact (C.commutator_le_preP_F4 hk ht).2
  · obtain ⟨y₁, hy₁, hy₁w⟩ := (O7_vec_eq hk).1
    obtain ⟨y₂, hy₂, hy₂w⟩ := (O7_vec_eq hk).2
    obtain ⟨s₁, hs₁, hs₁U, hs₁e⟩ := C.exists_s_F4 hk hy₁
    obtain ⟨s₂, hs₂, hs₂U, hs₂e⟩ := C.exists_s_F4 hk hy₂
    refine sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr ?_)
      ((Submodule.span_singleton_le_iff_mem _ _).mpr ?_)
    · rw [← hy₁w, ← hs₁e, LinearEquiv.symm_apply_apply]
      exact L128A.HatU.π_mem_hat D hs₁ hs₁U
    · rw [← hy₂w, ← hs₂e, LinearEquiv.symm_apply_apply]
      exact L128A.HatU.π_mem_hat D hs₂ hs₂U

theorem commutator_le_U_F4 {k : ℕ} (hk : k = 1 ∨ k = 2) : ⁅V₂, xk D e k⁆ ≤ fsuU T V :=
  fun _ ht => (C.commutator_le_preP_F4 hk ht).1

theorem card_commutator_F4 {k : ℕ} (hk : k = 1 ∨ k = 2) : Nat.card ↥⁅V₂, xk D e k⁆ = 8 := by
  obtain ⟨_, S⟩ := C.set14_F4
  have hU := C.commutator_le_U_F4 hk
  have h := D.card_eq_mul_range hU
  rw [← L14323.card_hat_eq D hU, C.hat_commutator_F4 hk, L14323.card_submodule,
    finrank_planeK hk, C.zU, inf_eq_right.mpr (C.V1_le_commutator_F4 hk), S.card_V1_F4] at h
  rw [h]
  norm_num

theorem commutator_le_E_F4 {k : ℕ} (hk : k = 1 ∨ k = 2) : ⁅V₂, xk D e k⁆ ≤ l32nE T V V₂ g := by
  have hhat : planeK e k ≤ D.hat (l32nE T V V₂ g) := by
    have hw := oWs_mem hk ((D.hat (l32nE T V V₂ g)).map e.toLinearMap) C.mem_hatE_F4
    have key : ∀ w ∈ (D.hat (l32nE T V V₂ g)).map e.toLinearMap,
        e.symm w ∈ D.hat (l32nE T V V₂ g) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      exact hx
    exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr (key _ hw.1))
      ((Submodule.span_singleton_le_iff_mem _ _).mpr (key _ hw.2))
  intro s hs
  have hsU := C.commutator_le_U_F4 hk hs
  obtain ⟨t, htE, htU, hts⟩ := (L128A.HatU.mem_hat D).mp (hhat (C.commutator_le_preP_F4 hk hs).2)
  have h1 : t⁻¹ * s ∈ fsuV1 T V := by
    rw [← C.zU]
    exact (D.π_eq_iff t htU s hsU).mp hts
  rw [show s = t * (t⁻¹ * s) by group]
  exact Subgroup.mul_mem _ htE (C.V2E_F4 (C.plane.2 h1))

end Ctx_F4

end Cert

end CFSG.Quasithin.H13.L14411
