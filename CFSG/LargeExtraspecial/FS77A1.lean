module

public import CFSG.LargeExtraspecial.S12DWSetting

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.FS77

open Subgroup Module QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

structure CaseA (S : Setting G) where
  g : G
  haQ : g * S.z * g⁻¹ ∈ S.QG
  hne : g * S.z * g⁻¹ ≠ S.z
  P : HypPair S.q
  hP : P.e = S.cl (g * S.z * g⁻¹)
  hΩ : S.Mbar.map S.O.subtype = CFSG.Open.timmesfeldOmega S.q
  hw : 4 ≤ S.width

namespace CaseA

variable (D : CaseA S)

@[expose] def a : G := D.g * S.z * D.g⁻¹

theorem a_mem_QG : D.a ∈ S.QG := D.haQ

theorem a_ne_z : D.a ≠ S.z := D.hne

theorem a_mem_M : D.a ∈ S.M := S.QG_le_M D.haQ

theorem a_mul_a : D.a * D.a = 1 := by
  have h := S.z_mul_z
  calc D.a * D.a = D.g * (S.z * S.z) * D.g⁻¹ := by simp only [a]; group
    _ = 1 := by rw [h]; group

theorem a_ne_one : D.a ≠ 1 := by
  intro h
  apply S.z_ne_one
  have : S.z = D.g⁻¹ * D.a * D.g := by simp only [a]; group
  rw [this, h, mul_one, inv_mul_cancel]

theorem a_comm_z : D.a * S.z = S.z * D.a := S.z_comm_QG D.haQ

theorem cl_a : S.cl D.a = D.P.e := D.hP.symm

@[expose] def X : Subgroup G := S.M ⊓ centralizer ({D.a} : Set G)

theorem mem_X {x : G} : x ∈ D.X ↔ x * S.z = S.z * x ∧ x * D.a = D.a * x := by
  rw [X, mem_inf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]

theorem X_le_M : D.X ≤ S.M := inf_le_left

theorem conj_a_of_mem_X {x : G} (hx : x ∈ D.X) : x * D.a * x⁻¹ = D.a := by
  rw [(D.mem_X.mp hx).2]
  group

@[expose] noncomputable def toM : D.X →* S.M := inclusion D.X_le_M

@[simp] theorem coe_toM (x : D.X) : ((D.toM x : S.M) : G) = x := rfl

@[expose] noncomputable def ρX : D.X →* S.O := S.ρ.comp D.toM

theorem ρX_apply_cl (x : D.X) {y : G} (hy : y ∈ S.QG) :
    ((D.ρX x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl y) = S.cl ((x : G) * y * (x : G)⁻¹) :=
  S.ρ_cl (D.toM x) hy

theorem ρX_e (x : D.X) : ((D.ρX x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) D.P.e = D.P.e := by
  rw [← D.cl_a, D.ρX_apply_cl x D.a_mem_QG, D.conj_a_of_mem_X x.2]

theorem polar_ρX (x : D.X) (u v : S.Qt) :
    polar S.q (((D.ρX x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u)
      (((D.ρX x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = polar S.q u v :=
  polar_map_of_mem (D.ρX x).2 u v

theorem q_ρX (x : D.X) (u : S.Qt) :
    S.q (((D.ρX x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u) = S.q u :=
  map_of_mem (D.ρX x).2 u

noncomputable abbrev N : Submodule (ZMod 2) S.Qt := D.P.perp

@[expose] noncomputable def projLin : S.Qt →ₗ[ZMod 2] S.Qt where
  toFun x := D.P.proj x
  map_add' x y := by
    simp only [HypPair.proj, polar_add_left, add_smul]
    abel
  map_smul' c x := by
    simp only [HypPair.proj, polar_smul_left, smul_eq_mul, mul_smul, RingHom.id_apply, smul_sub]

theorem projLin_apply (x : S.Qt) : D.projLin x = D.P.proj x := rfl

theorem proj_mem_N (x : S.Qt) : D.P.proj x ∈ D.N := D.P.proj_mem_perp x

theorem mem_N_iff {x : S.Qt} : x ∈ D.N ↔ polar S.q D.P.e x = 0 ∧ polar S.q D.P.f x = 0 :=
  HypPair.mem_perp

theorem polar_e_of_mem_N {x : S.Qt} (hx : x ∈ D.N) : polar S.q x D.P.e = 0 := by
  rw [polar_comm]
  exact (D.mem_N_iff.mp hx).1

theorem polar_f_of_mem_N {x : S.Qt} (hx : x ∈ D.N) : polar S.q x D.P.f = 0 := by
  rw [polar_comm]
  exact (D.mem_N_iff.mp hx).2

theorem proj_of_mem_N {x : S.Qt} (hx : x ∈ D.N) : D.P.proj x = x := by
  rw [HypPair.proj, D.polar_e_of_mem_N hx, D.polar_f_of_mem_N hx, zero_smul, zero_smul,
    sub_zero, sub_zero]

theorem proj_e : D.P.proj D.P.e = 0 := by
  rw [HypPair.proj, D.P.polar_ee, D.P.polar_ef, one_smul, zero_smul, sub_self, sub_zero]

theorem proj_f : D.P.proj D.P.f = 0 := by
  rw [HypPair.proj, D.P.polar_fe, D.P.polar_ff, one_smul, zero_smul, sub_zero, sub_self]

theorem proj_of_polar_e {x : S.Qt} (hx : polar S.q x D.P.e = 0) :
    D.P.proj x = x - polar S.q x D.P.f • D.P.e := by
  rw [HypPair.proj, hx, zero_smul, sub_zero]

theorem eq_proj_add_of_polar_e {x : S.Qt} (hx : polar S.q x D.P.e = 0) :
    x = D.P.proj x + polar S.q x D.P.f • D.P.e := by
  rw [D.proj_of_polar_e hx]
  abel

theorem q_proj_of_polar_e {x : S.Qt} (hx : polar S.q x D.P.e = 0) :
    S.q (D.P.proj x) = S.q x := by
  rw [D.proj_of_polar_e hx, sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add S.q,
    map_smul_eq_sq, D.P.Q_e, polar_smul_right_eq, hx]
  ring

theorem polar_proj_of_mem_N {x y : S.Qt} (hy : y ∈ D.N) :
    polar S.q (D.P.proj x) y = polar S.q x y := by
  rw [HypPair.proj, polar_sub_left, polar_sub_left, polar_smul_left_eq, polar_smul_left_eq,
    (D.mem_N_iff.mp hy).1, (D.mem_N_iff.mp hy).2, mul_zero, mul_zero, sub_zero, sub_zero]

theorem eq_add_proj (x : S.Qt) :
    x = polar S.q x D.P.f • D.P.e + polar S.q x D.P.e • D.P.f + D.P.proj x :=
  D.P.eq_add_proj x

theorem polar_ρX_e_of_mem_N (x : D.X) {v : S.Qt} (hv : v ∈ D.N) :
    polar S.q (((D.ρX x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) D.P.e = 0 := by
  conv_lhs => rw [← D.ρX_e x]
  rw [D.polar_ρX, D.polar_e_of_mem_N hv]

@[expose] noncomputable def ρNlin (x : D.X) : D.N →ₗ[ZMod 2] D.N :=
  (D.projLin.comp (((D.ρX x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) ∘ₗ
    D.N.subtype).codRestrict D.N fun _ => D.proj_mem_N _

theorem coe_ρNlin (x : D.X) (v : D.N) :
    ((D.ρNlin x v : D.N) : S.Qt) = D.P.proj (((D.ρX x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := rfl

theorem ρX_eq_ρNlin_add (x : D.X) (v : D.N) :
    ((D.ρX x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
      (D.ρNlin x v : S.Qt) +
        polar S.q (((D.ρX x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) D.P.f • D.P.e := by
  rw [D.coe_ρNlin]
  exact D.eq_proj_add_of_polar_e (D.polar_ρX_e_of_mem_N x v.2)

theorem ρNlin_mul (x y : D.X) : D.ρNlin (x * y) = D.ρNlin x ∘ₗ D.ρNlin y := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  set w := ((D.ρX y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v with hw
  have hw' := D.eq_proj_add_of_polar_e (D.polar_ρX_e_of_mem_N y v.2)
  rw [← hw] at hw'
  rw [LinearMap.comp_apply, D.coe_ρNlin, D.coe_ρNlin, D.coe_ρNlin, map_mul, Subgroup.coe_mul,
    LinearEquiv.mul_apply, ← hw]
  conv_lhs => rw [hw']
  rw [map_add, map_smul, D.ρX_e, ← D.projLin_apply, map_add, map_smul, D.projLin_apply,
    D.projLin_apply, D.proj_e, smul_zero, add_zero]

theorem ρNlin_one : D.ρNlin 1 = LinearMap.id := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  rw [D.coe_ρNlin, map_one]
  exact D.proj_of_mem_N v.2

@[expose] noncomputable def ρN : D.X →* (D.N ≃ₗ[ZMod 2] D.N) where
  toFun x := LinearEquiv.ofLinearMap (D.ρNlin x) (D.ρNlin x⁻¹)
    (by rw [← D.ρNlin_mul, mul_inv_cancel, D.ρNlin_one])
    (by rw [← D.ρNlin_mul, inv_mul_cancel, D.ρNlin_one])
  map_one' := LinearEquiv.ext fun v => by
    change D.ρNlin 1 v = v
    rw [D.ρNlin_one]
    rfl
  map_mul' x y := LinearEquiv.ext fun v => by
    change D.ρNlin (x * y) v = D.ρNlin x (D.ρNlin y v)
    rw [D.ρNlin_mul]
    rfl

theorem coe_ρN_apply (x : D.X) (v : D.N) :
    ((D.ρN x v : D.N) : S.Qt) = D.P.proj (((D.ρX x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := rfl

theorem ρX_eq_ρN_add (x : D.X) (v : D.N) :
    ((D.ρX x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
      (D.ρN x v : S.Qt) +
        polar S.q (((D.ρX x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) D.P.f • D.P.e :=
  D.ρX_eq_ρNlin_add x v

theorem proj_ρX_of_polar_e (x : D.X) {u : S.Qt} (hu : polar S.q u D.P.e = 0) :
    D.P.proj (((D.ρX x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u) =
      (D.ρN x ⟨D.P.proj u, D.proj_mem_N u⟩ : S.Qt) := by
  rw [D.coe_ρN_apply]
  conv_lhs => rw [D.eq_proj_add_of_polar_e hu]
  rw [map_add, map_smul, D.ρX_e, ← D.projLin_apply, map_add, map_smul, D.projLin_apply,
    D.projLin_apply, D.proj_e, smul_zero, add_zero]

@[expose] noncomputable def qN : QuadraticForm (ZMod 2) D.N := S.q.comp D.N.subtype

theorem qN_apply (v : D.N) : D.qN v = S.q v := rfl

theorem polar_qN (v w : D.N) : polar D.qN v w = polar S.q v w := by
  simp only [polar, qN_apply, Submodule.coe_add]

theorem qN_nondegenerate : (polarBilin D.qN).Nondegenerate := by
  have hN := D.P.polarNondegOn_perp S.q_nondegenerate
  have hrefl : (polarBilin D.qN).IsRefl := fun v w h => by
    rw [polarBilin_apply_apply] at h ⊢
    rwa [polar_comm]
  rw [hrefl.nondegenerate_iff_separatingLeft]
  intro v hv
  apply Subtype.ext
  refine hN v v.2 fun w hw => ?_
  have := hv ⟨w, hw⟩
  rwa [polarBilin_apply_apply, D.polar_qN] at this

theorem ρN_mem_orthogonalGroup (x : D.X) :
    D.ρN x ∈ TauCeti.QuadraticMap.orthogonalGroup D.qN := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
  rw [D.qN_apply, D.qN_apply, D.coe_ρN_apply, D.q_proj_of_polar_e (D.polar_ρX_e_of_mem_N x v.2),
    D.q_ρX]

theorem finrank_N_add_two : finrank (ZMod 2) D.N + 2 = finrank (ZMod 2) S.Qt := by
  set φ : S.Qt →ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
    LinearMap.pi ![polarBilin S.q D.P.e, polarBilin S.q D.P.f] with hφ
  have hker : LinearMap.ker φ = D.N := by
    ext v
    simp only [LinearMap.mem_ker, D.mem_N_iff, hφ, funext_iff, LinearMap.pi_apply,
      Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, polarBilin_apply_apply,
      Pi.zero_apply]
  have hsurj : LinearMap.range φ = ⊤ := by
    refine eq_top_iff.mpr fun c _ => ?_
    refine ⟨c 1 • D.P.e + c 0 • D.P.f, ?_⟩
    funext i
    fin_cases i <;>
      simp [hφ, polar_add_right, polar_smul_right, D.P.polar_ee, D.P.polar_ef, D.P.polar_fe,
        D.P.polar_ff]
  have h := LinearMap.finrank_range_add_finrank_ker φ
  rw [hker, hsurj, finrank_top, Module.finrank_fin_fun] at h
  omega

theorem finrank_N : finrank (ZMod 2) D.N = 2 * S.width - 2 := by
  have h := D.finrank_N_add_two
  rw [S.finrank_Qt_eq_two_mul_width] at h
  omega

theorem proj_proj (y : S.Qt) : D.P.proj (D.P.proj y) = D.P.proj y :=
  D.proj_of_mem_N (D.proj_mem_N y)

theorem proj_sub_proj (y : S.Qt) : D.P.proj (y - D.P.proj y) = 0 := by
  rw [← D.projLin_apply, map_sub, D.projLin_apply, D.projLin_apply, D.proj_proj, sub_self]

theorem polar_sub_proj_of_mem_N (y : S.Qt) {v : S.Qt} (hv : v ∈ D.N) :
    polar S.q (y - D.P.proj y) v = 0 := by
  rw [polar_sub_left, D.polar_proj_of_mem_N hv, sub_self]

@[expose] noncomputable def projN : S.Qt →ₗ[ZMod 2] D.N :=
  D.projLin.codRestrict D.N fun y => D.proj_mem_N y

theorem coe_projN (y : S.Qt) : (D.projN y : S.Qt) = D.P.proj y := rfl

@[expose] noncomputable def extLin (h : D.N →ₗ[ZMod 2] D.N) : S.Qt →ₗ[ZMod 2] S.Qt :=
  D.N.subtype ∘ₗ h ∘ₗ D.projN + (LinearMap.id - D.projLin)

theorem extLin_apply (h : D.N →ₗ[ZMod 2] D.N) (y : S.Qt) :
    D.extLin h y = (h (D.projN y) : S.Qt) + (y - D.P.proj y) := rfl

theorem proj_extLin (h : D.N →ₗ[ZMod 2] D.N) (y : S.Qt) :
    D.P.proj (D.extLin h y) = (h (D.projN y) : S.Qt) := by
  rw [D.extLin_apply, ← D.projLin_apply, map_add, D.projLin_apply, D.projLin_apply,
    D.proj_of_mem_N (h (D.projN y)).2, D.proj_sub_proj, add_zero]

theorem projN_extLin (h : D.N →ₗ[ZMod 2] D.N) (y : S.Qt) :
    D.projN (D.extLin h y) = h (D.projN y) :=
  Subtype.ext (D.proj_extLin h y)

theorem extLin_sub_proj (h : D.N →ₗ[ZMod 2] D.N) (y : S.Qt) :
    D.extLin h y - D.P.proj (D.extLin h y) = y - D.P.proj y := by
  rw [D.proj_extLin, D.extLin_apply]
  abel

theorem extLin_comp (h h' : D.N →ₗ[ZMod 2] D.N) :
    D.extLin h ∘ₗ D.extLin h' = D.extLin (h ∘ₗ h') := by
  refine LinearMap.ext fun y => ?_
  rw [LinearMap.comp_apply, D.extLin_apply h, D.projN_extLin, D.extLin_sub_proj, D.extLin_apply]
  rfl

theorem extLin_id : D.extLin LinearMap.id = LinearMap.id := by
  refine LinearMap.ext fun y => ?_
  rw [D.extLin_apply, LinearMap.id_apply, LinearMap.id_apply, D.coe_projN]
  abel

@[expose] noncomputable def ext (h : D.N ≃ₗ[ZMod 2] D.N) : S.Qt ≃ₗ[ZMod 2] S.Qt :=
  LinearEquiv.ofLinearMap (D.extLin h) (D.extLin h.symm)
    (by
      rw [D.extLin_comp, ← LinearEquiv.coe_trans, LinearEquiv.symm_trans_self,
        LinearEquiv.refl_toLinearMap, D.extLin_id])
    (by
      rw [D.extLin_comp, ← LinearEquiv.coe_trans, LinearEquiv.self_trans_symm,
        LinearEquiv.refl_toLinearMap, D.extLin_id])

theorem ext_apply (h : D.N ≃ₗ[ZMod 2] D.N) (y : S.Qt) :
    D.ext h y = (h (D.projN y) : S.Qt) + (y - D.P.proj y) := rfl

theorem ext_of_mem_N (h : D.N ≃ₗ[ZMod 2] D.N) {v : S.Qt} (hv : v ∈ D.N) :
    D.ext h v = (h ⟨v, hv⟩ : S.Qt) := by
  have hp : D.projN v = ⟨v, hv⟩ := Subtype.ext (D.proj_of_mem_N hv)
  rw [D.ext_apply, hp, D.proj_of_mem_N hv, sub_self, add_zero]

theorem ext_e (h : D.N ≃ₗ[ZMod 2] D.N) : D.ext h D.P.e = D.P.e := by
  have hp : D.projN D.P.e = 0 := Subtype.ext D.proj_e
  rw [D.ext_apply, hp, map_zero, D.proj_e, Submodule.coe_zero, zero_add, sub_zero]

theorem ext_mem_orthogonalGroup {h : D.N ≃ₗ[ZMod 2] D.N}
    (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup D.qN) :
    D.ext h ∈ TauCeti.QuadraticMap.orthogonalGroup S.q := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun y => ?_
  have hq : ∀ v : D.N, S.q (h v) = S.q v := fun v => by
    rw [← D.qN_apply, ← D.qN_apply, map_of_mem hh]
  rw [D.ext_apply, QuadraticMap.map_add S.q, hq, polar_comm,
    D.polar_sub_proj_of_mem_N y (h (D.projN y)).2, add_zero]
  conv_rhs => rw [show y = D.P.proj y + (y - D.P.proj y) by abel]
  rw [QuadraticMap.map_add S.q, polar_comm, D.polar_sub_proj_of_mem_N y (D.proj_mem_N y),
    add_zero, D.coe_projN]

theorem commSpace_ext (h : D.N ≃ₗ[ZMod 2] D.N) :
    CFSG.RankThree.OrthogonalInvolutions.commSpace (D.ext h) =
      (CFSG.RankThree.OrthogonalInvolutions.commSpace h).map D.N.subtype := by
  ext x
  simp only [CFSG.RankThree.OrthogonalInvolutions.mem_commSpace, Submodule.mem_map,
    Submodule.subtype_apply]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨h (D.projN y) - D.projN y, ⟨D.projN y, rfl⟩, ?_⟩
    rw [Submodule.coe_sub, D.ext_apply, D.coe_projN]
    abel
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    refine ⟨v, ?_⟩
    rw [D.ext_of_mem_N h v.2, Submodule.coe_sub]

theorem ext_mem_omegaGroup {h : D.N ≃ₗ[ZMod 2] D.N}
    (hh : h ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup D.qN D.qN_nondegenerate) :
    D.ext h ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup S.q S.q_nondegenerate := by
  rw [CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup] at hh ⊢
  refine ⟨D.ext_mem_orthogonalGroup hh.1, ?_⟩
  rw [D.commSpace_ext, Submodule.finrank_map_subtype_eq]
  exact hh.2

theorem exists_mem_X_of_cl (m : S.M) (hm : S.cl ((m : G) * D.a * (m : G)⁻¹) = S.cl D.a) :
    ∃ x : D.X, D.ρX x = S.ρ m := by
  have hconj : (m : G) * D.a * (m : G)⁻¹ ∈ S.QG := S.conj_mem_QG m.2 D.a_mem_QG
  rcases (S.cl_eq_cl_iff D.a_mem_QG hconj).mp hm.symm with h2 | h2
  · have hx : (m : G) ∈ D.X := by
      refine D.mem_X.mpr ⟨S.z_comm m.2, ?_⟩
      calc (m : G) * D.a = (m : G) * D.a * (m : G)⁻¹ * m := by group
        _ = D.a * m := by rw [h2]
    exact ⟨⟨m, hx⟩, rfl⟩
  · obtain ⟨r, hrQ, hr⟩ := S.exists_conj_eq_mul_z D.a_mem_QG D.a_ne_one D.a_ne_z
    have hrM : r ∈ S.M := S.QG_le_M hrQ
    have hrz : r * S.z = S.z * r := S.z_comm hrM
    have hx : r * (m : G) ∈ D.X := by
      refine D.mem_X.mpr ⟨?_, ?_⟩
      · rw [mul_assoc, S.z_comm m.2, ← mul_assoc, hrz, mul_assoc]
      · have h3 : r * (m : G) * D.a * (r * (m : G))⁻¹ = D.a := by
          calc r * (m : G) * D.a * (r * (m : G))⁻¹ = r * ((m : G) * D.a * (m : G)⁻¹) * r⁻¹ := by
                group
            _ = r * D.a * r⁻¹ * (r * S.z * r⁻¹) := by rw [h2]; group
            _ = D.a * S.z * S.z := by rw [hr, hrz]; group
            _ = D.a := by rw [mul_assoc, S.z_mul_z, mul_one]
        calc r * (m : G) * D.a = r * (m : G) * D.a * (r * (m : G))⁻¹ * (r * m) := by group
          _ = D.a * (r * m) := by rw [h3]
    refine ⟨⟨r * m, hx⟩, ?_⟩
    have hρr : S.ρ ⟨r, hrM⟩ = 1 := (S.ρ_eq_one_iff _).mpr hrQ
    change S.ρ (⟨r, hrM⟩ * m) = S.ρ m
    rw [map_mul, hρr, one_mul]

theorem mem_range_ρN {h : D.N ≃ₗ[ZMod 2] D.N}
    (hh : h ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup D.qN D.qN_nondegenerate) :
    ∃ x : D.X, D.ρN x = h := by
  have h1 := D.ext_mem_omegaGroup hh
  rw [← s12_timmesfeldOmega_eq S.q S.q_nondegenerate, ← D.hΩ] at h1
  obtain ⟨σ, ⟨m, rfl⟩, hσh⟩ := h1
  have hρm : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = D.ext h := hσh
  have hcl : S.cl ((m : G) * D.a * (m : G)⁻¹) = S.cl D.a := by
    rw [← S.ρ_cl m D.a_mem_QG, hρm, D.cl_a, D.ext_e]
  obtain ⟨x, hx⟩ := D.exists_mem_X_of_cl m hcl
  refine ⟨x, LinearEquiv.ext fun v => Subtype.ext ?_⟩
  rw [D.coe_ρN_apply, hx, hρm, D.ext_of_mem_N h v.2, D.proj_of_mem_N (h ⟨v, v.2⟩).2]

end CaseA

end CFSG.LargeExtraspecial.FS77
