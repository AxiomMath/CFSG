module

public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryHermitian

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019.SpBlock

open scoped commutatorElement
open CFSG.LocalAnalysis.ComponentInitial

section General

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

@[expose] def ModelPair (Γ : Subgroup (LinearMap.GeneralLinearGroup R M)) : Prop :=
  ∃ d ∈ Γ, ∃ τ ∈ Γ, ∃ τ' ∈ Γ,
    (((⁅d, τ⁆ : LinearMap.GeneralLinearGroup R M) : M →ₗ[R] M) - 1) ^ 2 = 0 ∧
    ∃ m : M, ((⁅d, τ⁆ * ⁅d, τ'⁆ : LinearMap.GeneralLinearGroup R M) : M →ₗ[R] M) m ≠
        ((⁅d, τ'⁆ * ⁅d, τ⁆ : LinearMap.GeneralLinearGroup R M) : M →ₗ[R] M) m ∧
      ((⁅d, τ⁆ * ⁅d, τ'⁆ : LinearMap.GeneralLinearGroup R M) : M →ₗ[R] M) m ≠
        -((⁅d, τ'⁆ * ⁅d, τ⁆ : LinearMap.GeneralLinearGroup R M) : M →ₗ[R] M) m

theorem commutator_val_of_conj {d τ : LinearMap.GeneralLinearGroup R M} {N : M →ₗ[R] M} {c : R}
    (hτ : (τ : M →ₗ[R] M) = 1 + N) (hN : N * N = 0)
    (hd : (d : M →ₗ[R] M) * N = c • (N * (d : M →ₗ[R] M))) :
    ((⁅d, τ⁆ : LinearMap.GeneralLinearGroup R M) : M →ₗ[R] M) = 1 + (c - 1) • N := by
  have hτinv : ((τ⁻¹ : LinearMap.GeneralLinearGroup R M) : M →ₗ[R] M) = 1 - N := by
    have h1 : (τ : M →ₗ[R] M) * (1 - N) = 1 := by
      rw [hτ, add_mul, one_mul, mul_sub, mul_one, hN, sub_zero, sub_add_cancel]
    calc ((τ⁻¹ : LinearMap.GeneralLinearGroup R M) : M →ₗ[R] M)
        = ((τ⁻¹ : LinearMap.GeneralLinearGroup R M) : M →ₗ[R] M) * ((τ : M →ₗ[R] M) * (1 - N)) := by
          rw [h1, mul_one]
      _ = 1 - N := by rw [← mul_assoc, Units.inv_mul, one_mul]
  have hdd : (d : M →ₗ[R] M) * N * ((d⁻¹ : LinearMap.GeneralLinearGroup R M) : M →ₗ[R] M) =
      c • N := by
    rw [hd, smul_mul_assoc, mul_assoc, Units.mul_inv, mul_one]
  rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul, hτinv, hτ, mul_add,
    mul_one, add_mul, Units.mul_inv, hdd, add_mul, one_mul, mul_sub, mul_one, smul_mul_assoc, hN,
    smul_zero, sub_zero, sub_smul, one_smul]
  abel

end General

section Alt

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M] {B : LinearMap.BilinForm K M}

@[expose] def nv (B : LinearMap.BilinForm K M) (v : M) : M →ₗ[K] M := (B v).smulRight v

theorem nv_apply (v z : M) : nv B v z = B v z • v := rfl

theorem nv_mul_self (hB : B.IsAlt) (v : M) : nv B v * nv B v = 0 := by
  refine LinearMap.ext fun z => ?_
  rw [Module.End.mul_apply, nv_apply, nv_apply, map_smul, hB.self_eq_zero, smul_zero, zero_smul,
    LinearMap.zero_apply]

theorem nv_skew (hB : B.IsAlt) (v z z' : M) : B z (nv B v z') + B (nv B v z) z' = 0 := by
  simp only [nv_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [← hB.neg v z]
  ring

@[expose] def tv (hB : B.IsAlt) (c : K) (v : M) : LinearMap.GeneralLinearGroup K M where
  val := 1 + c • nv B v
  inv := 1 - c • nv B v
  val_inv := by
    rw [add_mul, one_mul, mul_sub, mul_one, smul_mul_smul, nv_mul_self hB, smul_zero, sub_zero,
      sub_add_cancel]
  inv_val := by
    rw [sub_mul, one_mul, mul_add, mul_one, smul_mul_smul, nv_mul_self hB, smul_zero, add_zero,
      add_sub_cancel_right]

theorem tv_val (hB : B.IsAlt) (c : K) (v : M) :
    ((tv hB c v : LinearMap.GeneralLinearGroup K M) : M →ₗ[K] M) = 1 + c • nv B v := rfl

theorem tv_mem (hB : B.IsAlt) (c : K) (v : M) : tv hB c v ∈ sesqUnitaryGroup B := by
  intro z z'
  rw [tv_val]
  simp only [LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply, nv_apply, map_add,
    map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hB.self_eq_zero,
    RingHom.id_apply]
  have h := hB.neg v z
  rw [← h]
  ring

@[expose] def torusMap (B : LinearMap.BilinForm K M) (l : K) (v w : M) : M →ₗ[K] M :=
  1 - (l - 1) • nv' B w v + (l⁻¹ - 1) • nv' B v w
where
  nv' (B : LinearMap.BilinForm K M) (a b : M) : M →ₗ[K] M := (B a).smulRight b

theorem torusMap_apply (l : K) (v w z : M) :
    torusMap B l v w z = z - (l - 1) • (B w z • v) + (l⁻¹ - 1) • (B v z • w) := rfl

variable {v w : M}

theorem B_torusMap_v (hB : B.IsAlt) (hvw : B v w = 1) (l : K) (z : M) :
    B v (torusMap B l v w z) = l⁻¹ * B v z := by
  rw [torusMap_apply]
  simp only [map_add, map_sub, map_smul, smul_eq_mul, hB.self_eq_zero, hvw]
  ring

theorem B_torusMap_w (hB : B.IsAlt) (hvw : B v w = 1) (l : K) (z : M) :
    B w (torusMap B l v w z) = l * B w z := by
  have hwv : B w v = -1 := by rw [← hB.neg, hvw]
  rw [torusMap_apply]
  simp only [map_add, map_sub, map_smul, smul_eq_mul, hB.self_eq_zero, hwv]
  ring

theorem torusMap_v (hB : B.IsAlt) (hvw : B v w = 1) (l : K) : torusMap B l v w v = l • v := by
  have hwv : B w v = -1 := by rw [← hB.neg, hvw]
  rw [torusMap_apply, hwv, hB.self_eq_zero]
  module

theorem torusMap_w (hB : B.IsAlt) (hvw : B v w = 1) (l : K) : torusMap B l v w w = l⁻¹ • w := by
  rw [torusMap_apply, hB.self_eq_zero, hvw]
  module

theorem torusMap_comp (hB : B.IsAlt) (hvw : B v w = 1) {l : K} (hl : l ≠ 0) :
    torusMap B l v w * torusMap B l⁻¹ v w = 1 := by
  refine LinearMap.ext fun z => ?_
  rw [Module.End.mul_apply, Module.End.one_apply]
  conv_lhs => rw [torusMap_apply]
  rw [B_torusMap_w hB hvw, B_torusMap_v hB hvw, torusMap_apply, inv_inv]
  match_scalars <;> field_simp <;> ring

@[expose] def torus (hB : B.IsAlt) (hvw : B v w = 1) {l : K} (hl : l ≠ 0) :
    LinearMap.GeneralLinearGroup K M where
  val := torusMap B l v w
  inv := torusMap B l⁻¹ v w
  val_inv := torusMap_comp hB hvw hl
  inv_val := by
    have h := torusMap_comp (B := B) hB hvw (inv_ne_zero hl)
    rwa [inv_inv] at h

theorem torus_val (hB : B.IsAlt) (hvw : B v w = 1) {l : K} (hl : l ≠ 0) :
    ((torus hB hvw hl : LinearMap.GeneralLinearGroup K M) : M →ₗ[K] M) = torusMap B l v w := rfl

theorem torus_mem (hB : B.IsAlt) (hvw : B v w = 1) {l : K} (hl : l ≠ 0) :
    torus hB hvw hl ∈ sesqUnitaryGroup B := by
  intro z z'
  rw [torus_val]
  have hwv : B w v = -1 := by rw [← hB.neg, hvw]
  conv_lhs => rw [torusMap_apply, torusMap_apply]
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, hB.self_eq_zero, hvw, hwv, RingHom.id_apply]
  have h1 := hB.neg z v
  have h2 := hB.neg z w
  rw [← h1, ← h2]
  field_simp
  ring

theorem torus_mul_nv (hB : B.IsAlt) (hvw : B v w = 1) {l : K} (hl : l ≠ 0) :
    torusMap B l v w * nv B v = (l ^ 2) • (nv B v * torusMap B l v w) := by
  refine LinearMap.ext fun z => ?_
  rw [Module.End.mul_apply, LinearMap.smul_apply, Module.End.mul_apply, nv_apply, nv_apply,
    map_smul, torusMap_v hB hvw, B_torusMap_v hB hvw, smul_smul, smul_smul]
  congr 1
  field_simp

theorem torus_mul_nw (hB : B.IsAlt) (hvw : B v w = 1) {l : K} (hl : l ≠ 0) :
    torusMap B l v w * nv B w = (l⁻¹ ^ 2) • (nv B w * torusMap B l v w) := by
  refine LinearMap.ext fun z => ?_
  rw [Module.End.mul_apply, LinearMap.smul_apply, Module.End.mul_apply, nv_apply, nv_apply,
    map_smul, torusMap_w hB hvw, B_torusMap_w hB hvw, smul_smul, smul_smul]
  congr 1
  field_simp

theorem modelPair_alt (hB : B.IsAlt) (h2 : (2 : K) ≠ 0) (hvw : B v w = 1) {l : K} (hl : l ≠ 0)
    (hl2 : l ^ 2 ≠ 1) : ModelPair (sesqUnitaryGroup B) := by
  have hwv : B w v = -1 := by rw [← hB.neg, hvw]
  set d := torus hB hvw hl
  set τ := tv hB 1 v
  set τ' := tv hB 1 w
  have hu : ((⁅d, τ⁆ : LinearMap.GeneralLinearGroup K M) : M →ₗ[K] M) =
      1 + (l ^ 2 - 1) • nv B v :=
    commutator_val_of_conj (by rw [tv_val, one_smul]) (nv_mul_self hB v) (torus_mul_nv hB hvw hl)
  have hu' : ((⁅d, τ'⁆ : LinearMap.GeneralLinearGroup K M) : M →ₗ[K] M) =
      1 + (l⁻¹ ^ 2 - 1) • nv B w :=
    commutator_val_of_conj (by rw [tv_val, one_smul]) (nv_mul_self hB w) (torus_mul_nw hB hvw hl)
  have hc : l ^ 2 - 1 ≠ 0 := sub_ne_zero.2 hl2
  have hc' : l⁻¹ ^ 2 - 1 ≠ 0 := by
    rw [inv_pow]
    intro h
    apply hl2
    have h' : (l ^ 2)⁻¹ = 1 := sub_eq_zero.1 h
    rw [inv_eq_one] at h'
    exact h'
  refine ⟨d, torus_mem hB hvw hl, τ, tv_mem hB 1 v, τ', tv_mem hB 1 w, ?_, w, ?_, ?_⟩
  · rw [hu, add_sub_cancel_left, sq, smul_mul_smul, nv_mul_self hB, smul_zero]
  · rw [Units.val_mul, Units.val_mul, hu, hu', Module.End.mul_apply, Module.End.mul_apply]
    intro h
    have h' := congrArg (B v) h
    simp only [LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply, nv_apply, map_add,
      map_smul, smul_eq_mul, hB.self_eq_zero, hvw, hwv] at h'
    apply mul_ne_zero hc hc'
    linear_combination h'
  · rw [Units.val_mul, Units.val_mul, hu, hu', Module.End.mul_apply, Module.End.mul_apply]
    intro h
    have h' := congrArg (B w) h
    simp only [LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply, nv_apply, map_add,
      map_smul, map_neg, smul_eq_mul, hB.self_eq_zero, hvw, hwv] at h'
    apply mul_ne_zero h2 hc
    linear_combination -h'

end Alt

section Lin

variable {E M : Type*} [Field E] [AddCommGroup M] [Module E M] {ι : Type*} [DecidableEq ι]

@[expose] noncomputable def nb (b : Module.Basis ι E M) (i j : ι) : M →ₗ[E] M :=
  (b.coord j).smulRight (b i)

theorem nb_apply (b : Module.Basis ι E M) (i j : ι) (z : M) : nb b i j z = b.coord j z • b i := rfl

private theorem coord_self (b : Module.Basis ι E M) (i : ι) : b.coord i (b i) = 1 := by
  rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]

private theorem coord_ne (b : Module.Basis ι E M) {i j : ι} (hij : i ≠ j) :
    b.coord j (b i) = 0 := by
  rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, if_neg hij]

theorem nb_mul_self (b : Module.Basis ι E M) {i j : ι} (hij : i ≠ j) : nb b i j * nb b i j = 0 := by
  refine LinearMap.ext fun z => ?_
  rw [Module.End.mul_apply, nb_apply, nb_apply, map_smul, coord_ne b hij, smul_zero, zero_smul,
    LinearMap.zero_apply]

@[expose] noncomputable def unipotentUnit (N : M →ₗ[E] M) (hN : N * N = 0) :
    LinearMap.GeneralLinearGroup E M where
  val := 1 + N
  inv := 1 - N
  val_inv := by rw [add_mul, one_mul, mul_sub, mul_one, hN, sub_zero, sub_add_cancel]
  inv_val := by rw [sub_mul, one_mul, mul_add, mul_one, hN, add_zero, add_sub_cancel_right]

theorem unipotentUnit_val (N : M →ₗ[E] M) (hN : N * N = 0) :
    ((unipotentUnit N hN : LinearMap.GeneralLinearGroup E M) : M →ₗ[E] M) = 1 + N := rfl

@[expose] noncomputable def diagMap (b : Module.Basis ι E M) (i j : ι) (l : E) : M →ₗ[E] M :=
  1 + (l - 1) • nb b i i + (l⁻¹ - 1) • nb b j j

theorem diagMap_apply (b : Module.Basis ι E M) (i j : ι) (l : E) (z : M) :
    diagMap b i j l z = z + (l - 1) • (b.coord i z • b i) + (l⁻¹ - 1) • (b.coord j z • b j) := rfl

variable (b : Module.Basis ι E M) {i j : ι}

theorem coord_diagMap_i (hij : i ≠ j) (l : E) (z : M) :
    b.coord i (diagMap b i j l z) = l * b.coord i z := by
  rw [diagMap_apply]
  simp only [map_add, map_smul, coord_self, coord_ne b (Ne.symm hij), smul_eq_mul]
  ring

theorem coord_diagMap_j (hij : i ≠ j) (l : E) (z : M) :
    b.coord j (diagMap b i j l z) = l⁻¹ * b.coord j z := by
  rw [diagMap_apply]
  simp only [map_add, map_smul, coord_self, coord_ne b hij, smul_eq_mul]
  ring

theorem diagMap_bi (hij : i ≠ j) (l : E) : diagMap b i j l (b i) = l • b i := by
  rw [diagMap_apply, coord_self, coord_ne b hij]
  module

theorem diagMap_bj (hij : i ≠ j) (l : E) : diagMap b i j l (b j) = l⁻¹ • b j := by
  rw [diagMap_apply, coord_self, coord_ne b (Ne.symm hij)]
  module

theorem diagMap_comp (hij : i ≠ j) {l : E} (hl : l ≠ 0) :
    diagMap b i j l * diagMap b i j l⁻¹ = 1 := by
  refine LinearMap.ext fun z => ?_
  rw [Module.End.mul_apply, Module.End.one_apply]
  conv_lhs => rw [diagMap_apply]
  rw [coord_diagMap_i b hij, coord_diagMap_j b hij, diagMap_apply, inv_inv]
  match_scalars <;> field_simp <;> ring

@[expose] noncomputable def diagUnit (hij : i ≠ j) {l : E} (hl : l ≠ 0) :
    LinearMap.GeneralLinearGroup E M where
  val := diagMap b i j l
  inv := diagMap b i j l⁻¹
  val_inv := diagMap_comp b hij hl
  inv_val := by
    have h := diagMap_comp b hij (inv_ne_zero hl)
    rwa [inv_inv] at h

theorem diagUnit_val (hij : i ≠ j) {l : E} (hl : l ≠ 0) :
    ((diagUnit b hij hl : LinearMap.GeneralLinearGroup E M) : M →ₗ[E] M) = diagMap b i j l := rfl

theorem diagMap_mul_nb (hij : i ≠ j) {l : E} (hl : l ≠ 0) :
    diagMap b i j l * nb b i j = (l ^ 2) • (nb b i j * diagMap b i j l) := by
  refine LinearMap.ext fun z => ?_
  rw [Module.End.mul_apply, LinearMap.smul_apply, Module.End.mul_apply, nb_apply, nb_apply,
    map_smul, diagMap_bi b hij, coord_diagMap_j b hij, smul_smul, smul_smul]
  congr 1
  field_simp

theorem diagMap_mul_nb' (hij : i ≠ j) {l : E} (hl : l ≠ 0) :
    diagMap b i j l * nb b j i = (l⁻¹ ^ 2) • (nb b j i * diagMap b i j l) := by
  refine LinearMap.ext fun z => ?_
  rw [Module.End.mul_apply, LinearMap.smul_apply, Module.End.mul_apply, nb_apply, nb_apply,
    map_smul, diagMap_bj b hij, coord_diagMap_i b hij, smul_smul, smul_smul]
  congr 1
  field_simp

theorem modelPair_lin (b : Module.Basis ι E M) (h2 : (2 : E) ≠ 0) (hij : i ≠ j) {l : E}
    (hl : l ≠ 0) (hl2 : l ^ 2 ≠ 1) :
    ModelPair (⊤ : Subgroup (LinearMap.GeneralLinearGroup E M)) := by
  set d := diagUnit b hij hl
  set τ := unipotentUnit (nb b i j) (nb_mul_self b hij)
  set τ' := unipotentUnit (nb b j i) (nb_mul_self b (Ne.symm hij))
  have hu : ((⁅d, τ⁆ : LinearMap.GeneralLinearGroup E M) : M →ₗ[E] M) =
      1 + (l ^ 2 - 1) • nb b i j :=
    commutator_val_of_conj (unipotentUnit_val _ _) (nb_mul_self b hij) (diagMap_mul_nb b hij hl)
  have hu' : ((⁅d, τ'⁆ : LinearMap.GeneralLinearGroup E M) : M →ₗ[E] M) =
      1 + (l⁻¹ ^ 2 - 1) • nb b j i :=
    commutator_val_of_conj (unipotentUnit_val _ _) (nb_mul_self b (Ne.symm hij))
      (diagMap_mul_nb' b hij hl)
  have hc : l ^ 2 - 1 ≠ 0 := sub_ne_zero.2 hl2
  have hc' : l⁻¹ ^ 2 - 1 ≠ 0 := by
    rw [inv_pow]
    intro h
    apply hl2
    have h' : (l ^ 2)⁻¹ = 1 := sub_eq_zero.1 h
    rwa [inv_eq_one] at h'
  refine ⟨d, Subgroup.mem_top _, τ, Subgroup.mem_top _, τ', Subgroup.mem_top _, ?_, b j, ?_, ?_⟩
  · rw [hu, add_sub_cancel_left, sq, smul_mul_smul, nb_mul_self b hij, smul_zero]
  · rw [Units.val_mul, Units.val_mul, hu, hu', Module.End.mul_apply, Module.End.mul_apply]
    intro h
    have h' := congrArg (b.coord j) h
    simp only [LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply, nb_apply, map_add,
      map_smul, smul_eq_mul, coord_self, coord_ne b hij, coord_ne b (Ne.symm hij)] at h'
    apply mul_ne_zero hc hc'
    linear_combination -h'
  · rw [Units.val_mul, Units.val_mul, hu, hu', Module.End.mul_apply, Module.End.mul_apply]
    intro h
    have h' := congrArg (b.coord i) h
    simp only [LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply, nb_apply, map_add,
      map_smul, map_neg, smul_eq_mul, coord_self, coord_ne b hij, coord_ne b (Ne.symm hij)] at h'
    apply mul_ne_zero h2 hc
    linear_combination h'

end Lin

section Herm

variable {E M : Type*} [Field E] [AddCommGroup M] [Module E M] {σ : E →+* E}
  {H : M →ₛₗ[σ] M →ₗ[E] E}

@[expose] def nh (H : M →ₛₗ[σ] M →ₗ[E] E) (v : M) : M →ₗ[E] M := (H v).smulRight v

theorem nh_apply (v z : M) : nh H v z = H v z • v := rfl

theorem nh_mul_self {v : M} (hv : H v v = 0) : nh H v * nh H v = 0 := by
  refine LinearMap.ext fun z => ?_
  rw [Module.End.mul_apply, nh_apply, nh_apply, map_smul, hv, smul_zero, zero_smul,
    LinearMap.zero_apply]

variable {v w : M}

@[expose] def htorusMap (H : M →ₛₗ[σ] M →ₗ[E] E) (l : E) (v w : M) : M →ₗ[E] M :=
  1 + (l - 1) • (H w).smulRight v + (l⁻¹ - 1) • (H v).smulRight w

theorem htorusMap_apply (l : E) (z : M) :
    htorusMap H l v w z = z + (l - 1) • (H w z • v) + (l⁻¹ - 1) • (H v z • w) := rfl

variable (hH : H.IsSymm) (hv : H v v = 0) (hw : H w w = 0) (hvw : H v w = 1)
include hH hv hw hvw

theorem hwv_eq : H w v = 1 := by rw [← hH.eq v w, hvw, map_one]

theorem H_htorusMap_v (l : E) (z : M) : H v (htorusMap H l v w z) = l⁻¹ * H v z := by
  rw [htorusMap_apply]
  simp only [map_add, map_smul, smul_eq_mul, hv, hvw]
  ring

theorem H_htorusMap_w (l : E) (z : M) : H w (htorusMap H l v w z) = l * H w z := by
  have hwv := hwv_eq hH hv hw hvw
  rw [htorusMap_apply]
  simp only [map_add, map_smul, smul_eq_mul, hw, hwv]
  ring

theorem htorusMap_v (l : E) : htorusMap H l v w v = l • v := by
  have hwv := hwv_eq hH hv hw hvw
  rw [htorusMap_apply, hwv, hv]
  module

theorem htorusMap_w (l : E) : htorusMap H l v w w = l⁻¹ • w := by
  rw [htorusMap_apply, hw, hvw]
  module

theorem htorusMap_comp {l : E} (hl : l ≠ 0) : htorusMap H l v w * htorusMap H l⁻¹ v w = 1 := by
  refine LinearMap.ext fun z => ?_
  rw [Module.End.mul_apply, Module.End.one_apply]
  conv_lhs => rw [htorusMap_apply]
  rw [H_htorusMap_w hH hv hw hvw, H_htorusMap_v hH hv hw hvw, htorusMap_apply, inv_inv]
  match_scalars <;> field_simp <;> ring

@[expose] noncomputable def htorus {l : E} (hl : l ≠ 0) : LinearMap.GeneralLinearGroup E M where
  val := htorusMap H l v w
  inv := htorusMap H l⁻¹ v w
  val_inv := htorusMap_comp hH hv hw hvw hl
  inv_val := by
    have h := htorusMap_comp hH hv hw hvw (inv_ne_zero hl)
    rwa [inv_inv] at h

theorem htorus_val {l : E} (hl : l ≠ 0) :
    ((htorus hH hv hw hvw hl : LinearMap.GeneralLinearGroup E M) : M →ₗ[E] M) =
      htorusMap H l v w := rfl

theorem htorus_mem {l : E} (hl : l ≠ 0) (hσl : σ l = l) :
    htorus hH hv hw hvw hl ∈ sesqUnitaryGroup H := by
  have hwv := hwv_eq hH hv hw hvw
  intro z z'
  rw [htorus_val]
  conv_lhs => rw [htorusMap_apply, htorusMap_apply]
  have hσl' : σ l⁻¹ = l⁻¹ := by rw [map_inv₀, hσl]
  simp only [map_add, map_smulₛₗ, LinearMap.map_smulₛₗ₂, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, map_sub, map_one, hσl, hσl', hv, hw, hvw, hwv, map_mul,
    RingHom.id_apply]
  rw [hH.eq w z, hH.eq v z]
  field_simp
  ring

theorem htv_mem {η : E} (hη : σ η = -η) (u : M) (hu : H u u = 0) :
    unipotentUnit (η • nh H u) (by rw [smul_mul_smul, nh_mul_self hu, smul_zero]) ∈
      sesqUnitaryGroup H := by
  intro z z'
  rw [unipotentUnit_val]
  simp only [LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply, nh_apply, map_add,
    map_smul, map_smulₛₗ, LinearMap.map_smulₛₗ₂, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, hu, map_mul, hη, RingHom.id_apply]
  rw [hH.eq u z]
  ring

theorem htorus_mul_nh {l : E} (hl : l ≠ 0) (η : E) :
    htorusMap H l v w * (η • nh H v) = (l ^ 2) • ((η • nh H v) * htorusMap H l v w) := by
  refine LinearMap.ext fun z => ?_
  simp only [Module.End.mul_apply, LinearMap.smul_apply, nh_apply, map_smul,
    htorusMap_v hH hv hw hvw, H_htorusMap_v hH hv hw hvw, smul_smul]
  congr 1
  field_simp

theorem htorus_mul_nh' {l : E} (hl : l ≠ 0) (η : E) :
    htorusMap H l v w * (η • nh H w) = (l⁻¹ ^ 2) • ((η • nh H w) * htorusMap H l v w) := by
  refine LinearMap.ext fun z => ?_
  simp only [Module.End.mul_apply, LinearMap.smul_apply, nh_apply, map_smul,
    htorusMap_w hH hv hw hvw, H_htorusMap_w hH hv hw hvw, smul_smul]
  congr 1
  field_simp

theorem modelPair_herm (h2 : (2 : E) ≠ 0) {l : E} (hl : l ≠ 0) (hl2 : l ^ 2 ≠ 1) (hσl : σ l = l)
    {η : E} (hη0 : η ≠ 0) (hη : σ η = -η) : ModelPair (sesqUnitaryGroup H) := by
  have hwv := hwv_eq hH hv hw hvw
  set d := htorus hH hv hw hvw hl
  set τ := unipotentUnit (η • nh H v) (by rw [smul_mul_smul, nh_mul_self hv, smul_zero])
  set τ' := unipotentUnit (η • nh H w) (by rw [smul_mul_smul, nh_mul_self hw, smul_zero])
  have hNv : (η • nh H v) * (η • nh H v) = 0 := by rw [smul_mul_smul, nh_mul_self hv, smul_zero]
  have hNw : (η • nh H w) * (η • nh H w) = 0 := by rw [smul_mul_smul, nh_mul_self hw, smul_zero]
  have hu : ((⁅d, τ⁆ : LinearMap.GeneralLinearGroup E M) : M →ₗ[E] M) =
      1 + (l ^ 2 - 1) • (η • nh H v) :=
    commutator_val_of_conj (unipotentUnit_val _ _) hNv (htorus_mul_nh hH hv hw hvw hl η)
  have hu' : ((⁅d, τ'⁆ : LinearMap.GeneralLinearGroup E M) : M →ₗ[E] M) =
      1 + (l⁻¹ ^ 2 - 1) • (η • nh H w) :=
    commutator_val_of_conj (unipotentUnit_val _ _) hNw (htorus_mul_nh' hH hv hw hvw hl η)
  have hc : l ^ 2 - 1 ≠ 0 := sub_ne_zero.2 hl2
  have hc' : l⁻¹ ^ 2 - 1 ≠ 0 := by
    rw [inv_pow]
    intro h
    apply hl2
    have h' : (l ^ 2)⁻¹ = 1 := sub_eq_zero.1 h
    rwa [inv_eq_one] at h'
  refine ⟨d, htorus_mem hH hv hw hvw hl hσl, τ, htv_mem hH hv hw hvw hη v hv, τ',
    htv_mem hH hv hw hvw hη w hw, ?_, w, ?_, ?_⟩
  · rw [hu, add_sub_cancel_left, sq, smul_mul_smul, hNv, smul_zero]
  · rw [Units.val_mul, Units.val_mul, hu, hu', Module.End.mul_apply, Module.End.mul_apply]
    intro h
    have h' := congrArg (H v) h
    simp only [LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply, nh_apply, map_add,
      map_smul, smul_eq_mul, hv, hw, hvw, hwv] at h'
    apply mul_ne_zero (mul_ne_zero hc hc') (mul_ne_zero hη0 hη0)
    linear_combination -h'
  · rw [Units.val_mul, Units.val_mul, hu, hu', Module.End.mul_apply, Module.End.mul_apply]
    intro h
    have h' := congrArg (H w) h
    simp only [LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply, nh_apply, map_add,
      map_smul, map_neg, smul_eq_mul, hv, hw, hvw, hwv] at h'
    apply mul_ne_zero (mul_ne_zero h2 hc) hη0
    linear_combination h'

end Herm

end CFSG.LocalAnalysis.GLTheoremA.S2019.SpBlock
