module

public import CFSG.LocalAnalysis.QuasithinUnique.BenderBranchBasic
public import CFSG.LocalAnalysis.QuasithinUnique.ONanLemma

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

namespace BenderBranch

section ConjAut

variable {G : Type*} [Group G] {U M : Subgroup G}

@[expose] def conjAut (hM : M ≤ Subgroup.normalizer (U : Set G)) (m : M) : U ≃* U where
  toFun x := ⟨m * x * m⁻¹, (Subgroup.mem_normalizer_iff.mp (hM m.2) x).mp x.2⟩
  invFun x := ⟨m⁻¹ * x * m, by
    simpa using (Subgroup.mem_normalizer_iff.mp (hM (M.inv_mem m.2)) x).mp x.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem coe_conjAut (hM : M ≤ Subgroup.normalizer (U : Set G)) (m : M) (x : U) :
    ((conjAut hM m x : U) : G) = m * x * m⁻¹ := rfl

end ConjAut

section Linear

variable {G : Type*} [Group G] (U : Subgroup G)

instance instIsMulCommutativeOfFact [hU : Fact (IsElemAbelian 2 U)] : IsMulCommutative ↥U :=
  hU.out.1

instance instCommGroupOfFact [Fact (IsElemAbelian 2 U)] : CommGroup ↥U :=
  IsMulCommutative.instCommGroup

theorem sq_eq_one_of_fact [hU : Fact (IsElemAbelian 2 U)] (x : U) : x ^ 2 = 1 :=
  Subtype.ext (by simpa using hU.out.2 x x.2)

instance instModuleZMod2 [Fact (IsElemAbelian 2 U)] : Module (ZMod 2) (Additive ↥U) :=
  AddCommGroup.zmodModule fun x => by
    have := sq_eq_one_of_fact U (Additive.toMul x)
    apply Additive.toMul.injective
    simpa [toMul_nsmul] using this

variable {U} [Fact (IsElemAbelian 2 U)] {M : Subgroup G}

@[expose] def rho (hM : M ≤ Subgroup.normalizer (U : Set G)) :
    M →* (Additive U ≃ₗ[ZMod 2] Additive U) where
  toFun m := AddEquiv.toLinearEquiv (MulEquiv.toAdditive (conjAut hM m))
    (fun c x => ZMod.map_smul (MulEquiv.toAdditive (conjAut hM m)) c x)
  map_one' := LinearEquiv.ext fun v => by
    apply Additive.toMul.injective
    apply Subtype.ext
    simp [coe_conjAut]
  map_mul' a b := LinearEquiv.ext fun v => by
    apply Additive.toMul.injective
    apply Subtype.ext
    simp [coe_conjAut, mul_assoc]

theorem coe_toMul_rho (hM : M ≤ Subgroup.normalizer (U : Set G)) (m : M) (v : Additive U) :
    ((Additive.toMul (rho hM m v) : U) : G) = m * (Additive.toMul v : U) * m⁻¹ := rfl

@[expose] def ofSub (U : Subgroup G) [Fact (IsElemAbelian 2 U)] (H : Subgroup G) :
    Submodule (ZMod 2) (Additive U) :=
  AddSubgroup.toZModSubmodule 2
    { carrier := {v | ((Additive.toMul v : U) : G) ∈ H}
      add_mem' := fun {a b} ha hb => by simpa using H.mul_mem ha hb
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by simpa using H.inv_mem ha }

theorem mem_ofSub {H : Subgroup G} {v : Additive U} :
    v ∈ ofSub U H ↔ ((Additive.toMul v : U) : G) ∈ H := Iff.rfl

theorem map_ofSub_rho (hM : M ≤ Subgroup.normalizer (U : Set G)) (m : M) (H : Subgroup G) :
    (ofSub U H).map (rho hM m : Additive U →ₗ[ZMod 2] Additive U) =
      ofSub U (CFSG.conjugate H (m : G)⁻¹) := by
  ext v
  rw [Submodule.mem_map, mem_ofSub, mem_conjugate_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_ofSub] at hx
    simpa [coe_toMul_rho, mul_assoc] using hx
  · intro hv
    refine ⟨Additive.ofMul (conjAut hM (m⁻¹) (Additive.toMul v)), ?_, ?_⟩
    · rw [mem_ofSub]
      simp [coe_conjAut, mul_assoc] at hv ⊢
      exact hv
    · apply Additive.toMul.injective
      apply Subtype.ext
      simp [coe_toMul_rho, coe_conjAut, mul_assoc]

theorem ofSub_eq_ofSub_iff {K₁ K₂ : Subgroup G} :
    ofSub U K₁ = ofSub U K₂ ↔ U ⊓ K₁ = U ⊓ K₂ := by
  constructor
  · intro h
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hxU, hx⟩
      refine ⟨hxU, ?_⟩
      have := (SetLike.ext_iff.mp h (Additive.ofMul ⟨x, hxU⟩)).mp hx
      simpa [mem_ofSub] using this
    · rintro ⟨hxU, hx⟩
      refine ⟨hxU, ?_⟩
      have := (SetLike.ext_iff.mp h (Additive.ofMul ⟨x, hxU⟩)).mpr hx
      simpa [mem_ofSub] using this
  · intro h
    ext v
    rw [mem_ofSub, mem_ofSub]
    have := SetLike.ext_iff.mp h ((Additive.toMul v : U) : G)
    simp only [Subgroup.mem_inf] at this
    constructor
    · intro hv
      exact (this.mp ⟨(Additive.toMul v : U).2, hv⟩).2
    · intro hv
      exact (this.mpr ⟨(Additive.toMul v : U).2, hv⟩).2

abbrev subspaceAction (hM : M ≤ Subgroup.normalizer (U : Set G)) :
    MulAction M (Submodule (ZMod 2) (Additive U)) where
  smul m D := D.map (rho hM m : Additive U →ₗ[ZMod 2] Additive U)
  one_smul D := by
    show D.map ((rho hM 1 : Additive U ≃ₗ[ZMod 2] Additive U) :
      Additive U →ₗ[ZMod 2] Additive U) = D
    rw [map_one]
    exact Submodule.map_id D
  mul_smul a b D := by
    show D.map ((rho hM (a * b) : Additive U ≃ₗ[ZMod 2] Additive U) :
        Additive U →ₗ[ZMod 2] Additive U) = (D.map (rho hM b :
          Additive U →ₗ[ZMod 2] Additive U)).map (rho hM a : Additive U →ₗ[ZMod 2] Additive U)
    rw [map_mul, ← Submodule.map_comp]
    rfl

theorem index_normalizer_eq_ncard_orbit (hM : M ≤ Subgroup.normalizer (U : Set G))
    (H : Subgroup G) :
    ((M ⊓ Subgroup.normalizer ((U ⊓ H : Subgroup G) : Set G)).subgroupOf M).index =
      (ONan.orbit (rho hM).range (ofSub U H)).ncard := by
  let _ := subspaceAction hM
  have hstab : MulAction.stabilizer M (ofSub U H) =
      (M ⊓ Subgroup.normalizer ((U ⊓ H : Subgroup G) : Set G)).subgroupOf M := by
    ext m
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    have hsm : m • ofSub U H =
        (ofSub U H).map (rho hM m : Additive U →ₗ[ZMod 2] Additive U) := rfl
    rw [hsm, map_ofSub_rho, ofSub_eq_ofSub_iff]
    have hconj : CFSG.conjugate U (m : G)⁻¹ = U :=
      conjugate_eq_iff_mem_normalizer.mpr (hM (M.inv_mem m.2))
    have h1 : U ⊓ CFSG.conjugate H (m : G)⁻¹ = CFSG.conjugate (U ⊓ H) (m : G)⁻¹ := by
      rw [conjugate_inf, hconj]
    rw [h1, conjugate_eq_iff_mem_normalizer, inv_mem_iff]
    simp only [m.2, true_and]
  have horb : MulAction.orbit M (ofSub U H) = ONan.orbit (rho hM).range (ofSub U H) := by
    ext D
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨rho hM m, ⟨m, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨m, rfl⟩, rfl⟩
      exact ⟨m, rfl⟩
  rw [← hstab, MulAction.index_stabilizer, horb]

end Linear

end BenderBranch

end CFSG.QuasithinUnique
