module

public import CFSG.Quasithin.H13.L32NLem144Bc
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem144Ba

public section

namespace CFSG.Quasithin.H13.L144B

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin L14411 Mat8Cert
open scoped commutatorElement

variable {G : Type} [Group G] {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)}

variable [CFSG.GH74.QTGen4.Finite4 G]

namespace Base_F4
open CFSG.Quasithin.H13.L144B.Base_F4

variable (C : Base_F4 G T L V V₂ g)
include C

theorem Q_le_preM_F4 (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) (M : Subgroup (GL (Fin 8) (ZMod 2))) :
    pCoreOf 2 (l32nH T V) ≤ preM D e M := fun q hq => by
  have hqH : q ∈ l32nH T V := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hq
  rw [mem_preM hqH, (C.matOf_eq_one_iff_F4 D e hqH).mpr hq]
  exact one_mem _

theorem T_le_preM_F4 {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)} {M : Subgroup (GL (Fin 8) (ZMod 2))}
    (hTM : img8 D e T ≤ M) : T ≤ preM D e M := fun t ht =>
  (mem_preM (C.TH_F4 ht)).mpr (hTM ((mem_img8 D e).mpr ⟨t, ht, _, rfl⟩))

theorem T_le_normalizer_xM_F4 {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)}
    {M : Subgroup (GL (Fin 8) (ZMod 2))} (hTM : img8 D e T ≤ M) :
    T ≤ Subgroup.normalizer (xM D e M : Set G) :=
  (C.T_le_preM_F4 hTM).trans (le_normalizer_oTwoUpper _)

theorem U_le_normalizer_xM_F4 (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2))
    (M : Subgroup (GL (Fin 8) (ZMod 2))) :
    fsuU T V ≤ Subgroup.normalizer (xM D e M : Set G) :=
  ((C.UQ_F4 D).trans (C.Q_le_preM_F4 e M)).trans (le_normalizer_oTwoUpper _)

theorem relIndex_xM_F4 {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)} {M O : Subgroup (GL (Fin 8) (ZMod 2))}
    (hXO : img8 D e (xM D e M) = O) (hO3 : (CFSG.Open.pCore 2 ↥O).index = 3) :
    (pCoreOf 2 (xM D e M)).relIndex (xM D e M) = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXN := (xM_le_H (D := D) e M).trans HN
  let f : ↥(xM D e M) →* ↥O := (hom8 D e hXN).codRestrict O fun x => by
    rw [← hXO, ← range_hom8 D e hXN]
    exact ⟨x, rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨γ, hγ⟩
    rw [← hXO, ← range_hom8 D e hXN] at hγ
    obtain ⟨x, rfl⟩ := hγ
    exact ⟨x, rfl⟩
  have hker : IsPGroup 2 f.ker := by
    rintro ⟨x, hx⟩
    have hx1 : hom8 D e hXN x = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      simpa [f] using this
    have hxQ : (x : G) ∈ pCoreOf 2 (l32nH T V) :=
      (C.matOf_eq_one_iff_F4 D e (xM_le_H e M x.2)).mp hx1
    obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (l32nH T V) ⟨x, hxQ⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hn
  have hidx : (CFSG.Open.pCore 2 ↥(xM D e M)).index = 3 := by
    rw [pCore_eq_comap_of_surj f hf hker, Subgroup.index_comap_of_surjective _ hf, hO3]
  have hsub : ((CFSG.Open.pCore 2 ↥(xM D e M)).map (xM D e M).subtype).subgroupOf (xM D e M) =
      CFSG.Open.pCore 2 ↥(xM D e M) :=
    Subgroup.comap_map_eq_self_of_injective (xM D e M).subtype_injective _
  unfold Subgroup.relIndex pCoreOf
  rw [hsub, hidx]

theorem comm_mem_U_F4 {a x : G} (ha : a ∈ V₂) (hx : x ∈ l32nH T V) :
    a * x * a⁻¹ * x⁻¹ ∈ fsuU T V := by
  rw [show a * x * a⁻¹ * x⁻¹ = a * (x * a⁻¹ * x⁻¹) by group]
  exact Subgroup.mul_mem _ (C.V2U_F4 ha)
    (L128A.HatU.conj_mem (HN hx) (Subgroup.inv_mem _ (C.V2U_F4 ha)))

theorem e_pi_comm_F4 (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) {a x : G} (ha : a ∈ V₂)
    (hx : x ∈ l32nH T V) :
    e (D.π (a * x * a⁻¹ * x⁻¹)) =
      ((matOf e (D.ρ ⟨x, HN hx⟩) : GL (Fin 8) (ZMod 2)) :
        Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (e (D.π a)) + e (D.π a) := by
  have haU := C.V2U_F4 ha
  have hc : a * x * a⁻¹ * x⁻¹ = (x * a * x⁻¹ * a⁻¹)⁻¹ := by group
  have hcU : x * a * x⁻¹ * a⁻¹ ∈ fsuU T V :=
    Subgroup.mul_mem _ (L128A.HatU.conj_mem (HN hx) haU) (Subgroup.inv_mem _ haU)
  rw [hc, L128A.HatU.π_inv D hcU, ← L128A.HatU.rho_sub_π D (HN hx) haU, neg_sub,
    sub_eq_add_neg, neg_eq_self_zmod2, map_add, matOf_mulVec, add_comm]

variable {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)} {M : Subgroup (GL (Fin 8) (ZMod 2))} {a : G}
  {w₁ w₂ : Fin 8 → ZMod 2}

theorem commutator_le_preP_F4 (hM : M ≤ img8 D e (l32nH T V)) (ha : a ∈ V₂)
    (haV : a ∉ fsuV1 T V) (hP : PlaneData V₂ g D e a (oTwoUpper M) w₁ w₂) :
    ⁅V₂, xM D e M⁆ ≤ L14411.preP D (planeOf e w₁ w₂) := by
  obtain ⟨_, S⟩ := C.set14_F4
  rw [Subgroup.commutator_le]
  intro v hv x hx
  have hxH := xM_le_H e M hx
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
    refine ⟨C.comm_mem_U_F4 ha hxH, mem_planeOf ?_⟩
    rw [C.e_pi_comm_F4 e ha hxH]
    refine hP.vec _ ?_
    rw [← img_xM hM]
    exact (mem_img8 D e).mpr ⟨x, hx, _, rfl⟩

theorem exists_s_F4 (hM : M ≤ img8 D e (l32nH T V)) (ha : a ∈ V₂) {y : GL (Fin 8) (ZMod 2)}
    (hy : y ∈ oTwoUpper M) :
    ∃ s ∈ ⁅V₂, xM D e M⁆, s ∈ fsuU T V ∧
      e (D.π s) = (y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (e (D.π a)) + e (D.π a) := by
  obtain ⟨x, hx, hxN, rfl⟩ := (mem_img8 D e).mp (by rw [img_xM hM]; exact hy)
  have hxH := xM_le_H e M hx
  refine ⟨a * x * a⁻¹ * x⁻¹, ?_, C.comm_mem_U_F4 ha hxH, C.e_pi_comm_F4 e ha hxH⟩
  rw [← commutatorElement_def]
  exact Subgroup.commutator_mem_commutator ha hx

theorem V1_le_commutator_F4 (hM : M ≤ img8 D e (l32nH T V)) (ha : a ∈ V₂)
    (hP : PlaneData V₂ g D e a (oTwoUpper M) w₁ w₂) : fsuV1 T V ≤ ⁅V₂, xM D e M⁆ := by
  obtain ⟨_, S⟩ := C.set14_F4
  obtain ⟨y, hy, hyw⟩ := hP.att₁
  obtain ⟨s, hsA, hsU, hes⟩ := C.exists_s_F4 hM ha hy
  rw [hyw] at hes
  obtain ⟨y', hy', v, hv⟩ := hP.nonorth
  obtain ⟨x', hx', hx'N, rfl⟩ := (mem_img8 D e).mp (by rw [img_xM hM]; exact hy')
  obtain ⟨u, hu, hue⟩ := D.π_surj (e.symm v)
  set r := x' * u * x'⁻¹ * u⁻¹ with hr
  have hrU : r ∈ fsuU T V :=
    Subgroup.mul_mem _ (L128A.HatU.conj_mem hx'N hu) (Subgroup.inv_mem _ hu)
  have hrX : r ∈ xM D e M := by
    rw [hr, show x' * u * x'⁻¹ * u⁻¹ = x' * (u * x'⁻¹ * u⁻¹) by group]
    exact Subgroup.mul_mem _ hx' ((Subgroup.mem_normalizer_iff.mp
      (C.U_le_normalizer_xM_F4 e M hu) _).mp (Subgroup.inv_mem _ hx'))
  have hB : D.B (D.π r) (D.π s) ≠ 0 := by
    have h1 : D.π r = e.symm (((matOf e (D.ρ ⟨x', hx'N⟩) : GL (Fin 8) (ZMod 2)) :
        Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v + v) := by
      apply e.injective
      rw [LinearEquiv.apply_symm_apply, hr, ← L128A.HatU.rho_sub_π D hx'N hu, sub_eq_add_neg,
        neg_eq_self_zmod2, map_add, ← matOf_mulVec, hue, LinearEquiv.apply_symm_apply]
    have h2 : D.π s = e.symm w₁ := by rw [← hes, LinearEquiv.symm_apply_apply]
    rw [h1, h2]
    exact hv
  have hc1 : r * s * r⁻¹ * s⁻¹ ≠ 1 := fun h => hB ((D.B_spec r hrU s hsU).mpr h)
  have hcV1 : r * s * r⁻¹ * s⁻¹ ∈ fsuV1 T V := by
    rw [← C.zU]
    exact C.comm_center_F4 r hrU s hsU
  have hcA : r * s * r⁻¹ * s⁻¹ ∈ ⁅V₂, xM D e M⁆ := by
    refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ hsA)
    exact (Subgroup.mem_normalizer_iff.mp
      (L14413.le_normalizer_commutator_right V₂ (xM D e M) hrX) s).mp hsA
  intro z hz
  rcases S.eq_of_mem_V1_F4 hcV1 hc1 hz with rfl | rfl
  · exact one_mem _
  · exact hcA

theorem commutator_le_U_F4 (hM : M ≤ img8 D e (l32nH T V)) (ha : a ∈ V₂) (haV : a ∉ fsuV1 T V)
    (hP : PlaneData V₂ g D e a (oTwoUpper M) w₁ w₂) : ⁅V₂, xM D e M⁆ ≤ fsuU T V :=
  fun _ ht => (C.commutator_le_preP_F4 hM ha haV hP ht).1

theorem hat_commutator_F4 (hM : M ≤ img8 D e (l32nH T V)) (ha : a ∈ V₂) (haV : a ∉ fsuV1 T V)
    (hP : PlaneData V₂ g D e a (oTwoUpper M) w₁ w₂) :
    D.hat ⁅V₂, xM D e M⁆ = planeOf e w₁ w₂ := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨t, ⟨ht, -⟩, rfl⟩
    exact (C.commutator_le_preP_F4 hM ha haV hP ht).2
  · obtain ⟨y₁, hy₁, hy₁w⟩ := hP.att₁
    obtain ⟨y₂, hy₂, hy₂w⟩ := hP.att₂
    obtain ⟨s₁, hs₁, hs₁U, hs₁e⟩ := C.exists_s_F4 hM ha hy₁
    obtain ⟨s₂, hs₂, hs₂U, hs₂e⟩ := C.exists_s_F4 hM ha hy₂
    refine sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr ?_)
      ((Submodule.span_singleton_le_iff_mem _ _).mpr ?_)
    · rw [← hy₁w, ← hs₁e, LinearEquiv.symm_apply_apply]
      exact L128A.HatU.π_mem_hat D hs₁ hs₁U
    · rw [← hy₂w, ← hs₂e, LinearEquiv.symm_apply_apply]
      exact L128A.HatU.π_mem_hat D hs₂ hs₂U

theorem card_commutator_xM_F4 (hM : M ≤ img8 D e (l32nH T V)) (ha : a ∈ V₂) (haV : a ∉ fsuV1 T V)
    (hP : PlaneData V₂ g D e a (oTwoUpper M) w₁ w₂) : Nat.card ↥⁅V₂, xM D e M⁆ = 8 := by
  obtain ⟨_, S⟩ := C.set14_F4
  have hU := C.commutator_le_U_F4 hM ha haV hP
  have h := D.card_eq_mul_range hU
  rw [← L14323.card_hat_eq D hU, C.hat_commutator_F4 hM ha haV hP, L14323.card_submodule,
    finrank_planeOf hP.w₁_ne hP.w₂_ne hP.w₁₂_ne, C.zU,
    inf_eq_right.mpr (C.V1_le_commutator_F4 hM ha hP), S.card_V1_F4] at h
  rw [h]
  norm_num

theorem commutator_le_E_xM_F4 (hM : M ≤ img8 D e (l32nH T V)) (ha : a ∈ V₂) (haV : a ∉ fsuV1 T V)
    (hP : PlaneData V₂ g D e a (oTwoUpper M) w₁ w₂) :
    ⁅V₂, xM D e M⁆ ≤ l32nE T V V₂ g := by
  have hhat : planeOf e w₁ w₂ ≤ D.hat (l32nE T V V₂ g) :=
    sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hP.E₁)
      ((Submodule.span_singleton_le_iff_mem _ _).mpr hP.E₂)
  intro s hs
  have hsU := C.commutator_le_U_F4 hM ha haV hP hs
  obtain ⟨t, htE, htU, hts⟩ :=
    (L128A.HatU.mem_hat D).mp (hhat (C.commutator_le_preP_F4 hM ha haV hP hs).2)
  have h1 : t⁻¹ * s ∈ fsuV1 T V := by
    rw [← C.zU]
    exact (D.π_eq_iff t htU s hsU).mp hts
  rw [show s = t * (t⁻¹ * s) by group]
  exact Subgroup.mul_mem _ htE (C.V2E_F4 (C.plane.2 h1))

end Base_F4

end CFSG.Quasithin.H13.L144B
