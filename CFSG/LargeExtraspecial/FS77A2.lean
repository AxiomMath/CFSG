module

public import CFSG.LargeExtraspecial.FS77A1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.FS77

open Subgroup Module QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

namespace CaseA

variable (D : CaseA S)

theorem neg_zmod2 (c : ZMod 2) : -c = c := by
  revert c
  decide

theorem sub_zmod2 (c d : ZMod 2) : c - d = c + d := by
  rw [sub_eq_add_neg, neg_zmod2]

omit [Finite G] in
theorem add_self_Qt (x : S.Qt) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem eichler_f {u : S.Qt} (hu : u ∈ D.N) :
    eichler S.q D.P.e u D.P.f = D.P.f + u + S.q u • D.P.e := by
  rw [eichler_apply D.P.Q_e (D.mem_N_iff.mp hu).1, D.P.polar_fe, (D.mem_N_iff.mp hu).2,
    zero_add, mul_one, one_smul, sub_eq_add_neg, ← neg_smul, neg_zmod2]

theorem proj_eichler_f {u : S.Qt} (hu : u ∈ D.N) :
    D.P.proj (eichler S.q D.P.e u D.P.f) = u := by
  rw [D.eichler_f hu, ← D.projLin_apply, map_add, map_add, map_smul, D.projLin_apply,
    D.projLin_apply, D.projLin_apply, D.proj_f, D.proj_e, D.proj_of_mem_N hu, smul_zero,
    zero_add, add_zero]

theorem eichler_of_mem_N {u v : S.Qt} (hu : u ∈ D.N) (hv : v ∈ D.N) :
    eichler S.q D.P.e u v = v + polar S.q u v • D.P.e := by
  rw [eichler_apply D.P.Q_e (D.mem_N_iff.mp hu).1, D.polar_e_of_mem_N hv, zero_smul, add_zero,
    mul_zero, add_zero, sub_eq_add_neg, ← neg_smul, neg_zmod2, polar_comm]

@[expose] noncomputable def K : Subgroup D.X := D.ρN.ker

theorem mem_K {x : D.X} : x ∈ D.K ↔ D.ρN x = 1 := MonoidHom.mem_ker

@[expose] noncomputable def ψ (x : D.X) : D.N :=
  D.projN (((D.ρX x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) D.P.f)

theorem coe_ψ (x : D.X) :
    (D.ψ x : S.Qt) = D.P.proj (((D.ρX x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) D.P.f) := rfl

theorem ψ_one : D.ψ 1 = 0 := by
  apply Subtype.ext
  rw [D.coe_ψ, map_one]
  exact D.proj_f

theorem ρX_of_mem_K {x : D.X} (hx : x ∈ D.K) (v : D.N) :
    ((D.ρX x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v =
      v + polar S.q (((D.ρX x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) D.P.f • D.P.e := by
  conv_lhs => rw [D.ρX_eq_ρN_add x v, D.mem_K.mp hx]
  rfl

theorem ρX_eq_eichler {x : D.X} (hx : x ∈ D.K) :
    ((D.ρX x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = eichler S.q D.P.e (D.ψ x) := by
  set g := ((D.ρX x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) with hg
  set p : S.Qt := (D.ψ x : S.Qt) with hp
  have hpN : p ∈ D.N := (D.ψ x).2
  have hge : g D.P.e = D.P.e := D.ρX_e x
  have hgfe : polar S.q (g D.P.f) D.P.e = 1 := by
    conv_lhs => rw [← hge]
    rw [hg, D.polar_ρX, D.P.polar_fe]
  have hgf : g D.P.f = polar S.q (g D.P.f) D.P.f • D.P.e + D.P.f + p := by
    rw [hp, D.coe_ψ, ← hg]
    conv_lhs => rw [D.eq_add_proj (g D.P.f)]
    rw [hgfe, one_smul]
  have hep : polar S.q D.P.e p = 0 := (D.mem_N_iff.mp hpN).1
  have hfp : polar S.q D.P.f p = 0 := (D.mem_N_iff.mp hpN).2
  have hpe : polar S.q p D.P.e = 0 := by rw [polar_comm]; exact hep
  have hpf : polar S.q p D.P.f = 0 := by rw [polar_comm]; exact hfp
  have hμ : polar S.q (g D.P.f) D.P.f = S.q p := by
    have h1 : S.q (g D.P.f) = 0 := by rw [hg, D.q_ρX, D.P.Q_f]
    rw [hgf] at h1
    simp only [QuadraticMap.map_add, map_smul_eq_sq, D.P.Q_e, D.P.Q_f, polar_add_left,
      polar_smul_left_eq, D.P.polar_ef, hep, hfp, mul_zero, add_zero, zero_add, mul_one] at h1
    rw [← sub_eq_zero, sub_zmod2]
    exact h1
  have hgv : ∀ v : D.N, g v = v + polar S.q p v • D.P.e := by
    intro v
    have h1 := D.ρX_of_mem_K hx v
    rw [← hg] at h1
    have h2 : polar S.q (g D.P.f) (g v) = 0 := by
      rw [hg, D.polar_ρX, (D.mem_N_iff.mp v.2).2]
    rw [h1, hgf, polar_add_left, polar_add_left, polar_add_right, polar_add_right,
      polar_add_right, polar_smul_left_eq, polar_smul_right_eq, polar_smul_left_eq,
      polar_smul_right_eq, polar_smul_right_eq, D.P.polar_ee, D.P.polar_fe,
      (D.mem_N_iff.mp v.2).1, (D.mem_N_iff.mp v.2).2, polar_comm S.q p D.P.e,
      (D.mem_N_iff.mp hpN).1] at h2
    rw [h1]
    congr 2
    rw [← sub_eq_zero, sub_zmod2]
    linear_combination h2
  refine LinearEquiv.ext fun y => ?_
  rw [D.eq_add_proj y, map_add, map_add, map_smul, map_smul, map_add, map_add, map_smul,
    map_smul, hge, eichler_apply_self, D.eichler_f hpN, hgf, hμ,
    hgv ⟨D.P.proj y, D.proj_mem_N y⟩, D.eichler_of_mem_N hpN (D.proj_mem_N y)]
  abel_nf

theorem ψ_mul {x y : D.X} (hx : x ∈ D.K) (hy : y ∈ D.K) : D.ψ (x * y) = D.ψ x + D.ψ y := by
  have hxy : x * y ∈ D.K := mul_mem hx hy
  have h1 := D.ρX_eq_eichler hxy
  rw [map_mul, Subgroup.coe_mul, D.ρX_eq_eichler hx, D.ρX_eq_eichler hy,
    eichler_mul (D.mem_N_iff.mp (D.ψ x).2).1 (D.mem_N_iff.mp (D.ψ y).2).1] at h1
  apply Subtype.ext
  rw [Submodule.coe_add, ← D.proj_eichler_f (D.ψ (x * y)).2, ← h1,
    D.proj_eichler_f (add_mem (D.ψ x).2 (D.ψ y).2)]

theorem ψ_eq_zero_iff {x : D.X} (hx : x ∈ D.K) : D.ψ x = 0 ↔ (x : G) ∈ S.QG := by
  refine Iff.trans ?_ (S.ρ_eq_one_iff (D.toM x))
  change D.ψ x = 0 ↔ D.ρX x = 1
  constructor
  · intro h
    apply Subtype.ext
    rw [D.ρX_eq_eichler hx, h, Submodule.coe_zero, eichler_zero_right]
    rfl
  · intro h
    apply Subtype.ext
    rw [D.coe_ψ, h]
    exact D.proj_f

theorem isPGroup_K : IsPGroup 2 D.K := by
  intro k
  have hk := k.2
  have h2 : D.ρX (k * k : D.X) = 1 := by
    apply Subtype.ext
    rw [map_mul, Subgroup.coe_mul, D.ρX_eq_eichler hk,
      eichler_mul (D.mem_N_iff.mp (D.ψ k).2).1 (D.mem_N_iff.mp (D.ψ k).2).1,
      add_self_Qt, eichler_zero_right]
    rfl
  have hQ : ((k * k : D.X) : G) ∈ S.QG := (S.ρ_eq_one_iff (D.toM (k * k))).mp h2
  refine ⟨3, Subtype.ext (Subtype.ext ?_)⟩
  have h4 := S.pow_four_eq_one hQ
  simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_one] at h4 ⊢
  calc ((k : D.X) : G) ^ 2 ^ 3 = ((k : D.X) * (k : D.X) : G) ^ 4 := by
        rw [← _root_.sq, ← pow_mul]
        norm_num
    _ = 1 := h4

theorem ψ_conj (m : D.X) {k : D.X} (hk : k ∈ D.K) : D.ψ (m * k * m⁻¹) = D.ρN m (D.ψ k) := by
  have hKn : D.K.Normal := D.ρN.normal_ker
  have hk' : m * k * m⁻¹ ∈ D.K := hKn.conj_mem k hk m
  have h1 : ((D.ρX (m * k * m⁻¹) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      eichler S.q D.P.e ((D.ρN m (D.ψ k) : S.Qt) +
        polar S.q (((D.ρX m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (D.ψ k)) D.P.f • D.P.e) := by
    rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      D.ρX_eq_eichler hk, eichler_conj (D.ρX m).2, D.ρX_e, ← D.ρX_eq_ρN_add]
  apply Subtype.ext
  rw [D.coe_ψ, h1, eichler_add_smul_self D.P.Q_e, D.proj_eichler_f (D.ρN m (D.ψ k)).2]

end CaseA

end CFSG.LargeExtraspecial.FS77
