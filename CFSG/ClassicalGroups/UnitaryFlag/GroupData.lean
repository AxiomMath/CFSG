module

public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
public import CFSG.LinearAlgebra.LinearGroups.UnitaryBasics
public import CFSG.LinearAlgebra.LinearGroups.UnitaryFourOrder
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel

public section

namespace CFSG.ClassicalGroups.UnitaryFlag

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups CFSG.Assembly.LowTwoRank
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K]

theorem norm_mul_eq (h : UnitaryFieldData p f K) (a b : K) :
    h.norm (a * b) = h.norm a * h.norm b := by
  simp only [UnitaryFieldData.norm, map_mul]
  ring

theorem norm_inv_eq (h : UnitaryFieldData p f K) (a : K) : h.norm a⁻¹ = (h.norm a)⁻¹ := by
  simp only [UnitaryFieldData.norm, map_inv₀, mul_inv]

theorem stdHermForm_eq_gramForm (h : UnitaryFieldData p f K) (n : ℕ) :
    stdHermForm h n = gramForm h (1 : Matrix (Fin n) (Fin n) K) :=
  LinearMap.ext fun x => LinearMap.ext fun y => by
    simp [stdHermForm_apply, gramForm_apply, dotProduct]

variable (p f K) in
abbrev unitarySU (n : ℕ) : Subgroup (GL (Fin n) K) :=
  StatedSU n (p ^ f) K

theorem mem_unitarySU_iff (h : UnitaryFieldData p f K) {n : ℕ} {A : GL (Fin n) K} :
    A ∈ unitarySU p f K n ↔ (A : Matrix (Fin n) (Fin n) K).det = 1 ∧
      ((A : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * A = 1 := by
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.finite
  have : CharP K p := h.charP
  rw [unitarySU, ← CFSG.LieType.Universal.Unitary.SUid_eq_statedSU h.card_eq_sq n,
    CFSG.LieType.Universal.Unitary.mem_SUid]
  have hσ : (⇑(CFSG.LieType.BorelTits.unitaryInvolution K p f) : K → K) = ⇑h.bar :=
    funext fun c => by rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, h.bar_apply]
  simp only [CFSG.LieType.Universal.Unitary.conjTr, hσ]

theorem unitarySU_eq_gramSU (h : UnitaryFieldData p f K) (n : ℕ) :
    unitarySU p f K n = gramSU h (1 : Matrix (Fin n) (Fin n) K) := by
  ext A
  rw [mem_unitarySU_iff h, mem_gramSU, Matrix.mul_one, and_comm]

theorem mem_unitarySU_iff_isometry (h : UnitaryFieldData p f K) {n : ℕ} {A : GL (Fin n) K} :
    A ∈ unitarySU p f K n ↔ (A : Matrix (Fin n) (Fin n) K).det = 1 ∧
      ∀ x y, stdHermForm h n ((A : Matrix (Fin n) (Fin n) K) *ᵥ x)
        ((A : Matrix (Fin n) (Fin n) K) *ᵥ y) = stdHermForm h n x y := by
  rw [unitarySU_eq_gramSU h, mem_gramSU_iff_isometry, stdHermForm_eq_gramForm, and_comm]

theorem stdHermForm_smul_smul (h : UnitaryFieldData p f K) {n : ℕ} (g : unitarySU p f K n)
    (x y : Fin n → K) : stdHermForm h n (g • x) (g • y) = stdHermForm h n x y :=
  ((mem_unitarySU_iff_isometry h).mp g.2).2 x y

section Scalars

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem commute_scalar (c : Kˣ) (g : GL ι K) : Commute g (GeneralLinearGroup.scalar ι c) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar]
  exact ((Matrix.scalar_commute (c : K) (fun r => Commute.all (c : K) r) _)).eq.symm

@[expose] def normOneScalars (h : UnitaryFieldData p f K) (H : Subgroup (GL ι K)) (m : ℕ) :
    Subgroup H where
  carrier := {g | ∃ c : Kˣ, h.norm (c : K) = 1 ∧ c ^ m = 1 ∧
    (g : GL ι K) = GeneralLinearGroup.scalar ι c}
  one_mem' := ⟨1, by simp [UnitaryFieldData.norm], one_pow m, by simp⟩
  mul_mem' := by
    rintro g g' ⟨c, hc, hcn, hg⟩ ⟨c', hc', hcn', hg'⟩
    refine ⟨c * c', ?_, by rw [mul_pow, hcn, hcn', one_mul], ?_⟩
    · rw [Units.val_mul, norm_mul_eq h, hc, hc', one_mul]
    · rw [Subgroup.coe_mul, hg, hg', map_mul]
  inv_mem' := by
    rintro g ⟨c, hc, hcn, hg⟩
    refine ⟨c⁻¹, ?_, by rw [inv_pow, hcn, inv_one], ?_⟩
    · rw [Units.val_inv_eq_inv_val, norm_inv_eq h, hc, inv_one]
    · rw [Subgroup.coe_inv, hg, map_inv]

theorem mem_normOneScalars {h : UnitaryFieldData p f K} {H : Subgroup (GL ι K)} {m : ℕ}
    {g : H} : g ∈ normOneScalars h H m ↔ ∃ c : Kˣ, h.norm (c : K) = 1 ∧ c ^ m = 1 ∧
      (g : GL ι K) = GeneralLinearGroup.scalar ι c :=
  Iff.rfl

instance normOneScalars_normal (h : UnitaryFieldData p f K) (H : Subgroup (GL ι K)) (m : ℕ) :
    (normOneScalars h H m).Normal where
  conj_mem g hg x := by
    obtain ⟨c, hc, hcn, hg⟩ := hg
    refine ⟨c, hc, hcn, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hg, (commute_scalar c _).eq,
      mul_inv_cancel_right]

theorem normOneScalars_le_center (h : UnitaryFieldData p f K) (H : Subgroup (GL ι K)) (m : ℕ) :
    normOneScalars h H m ≤ Subgroup.center H := by
  rintro g ⟨c, -, -, hg⟩
  rw [Subgroup.mem_center_iff]
  intro x
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hg]
  exact (commute_scalar c _).eq

theorem scalar_smul_submodule (c : Kˣ) (L : Submodule K (ι → K)) :
    GeneralLinearGroup.scalar ι c • L = L := by
  have hmv : ∀ x : ι → K, (GeneralLinearGroup.scalar ι c : GL ι K) • x = (c : K) • x :=
    fun x => by
      change ((GeneralLinearGroup.scalar ι c : GL ι K) : Matrix ι ι K) *ᵥ x = _
      rw [GeneralLinearGroup.coe_scalar, scalar_apply]
      funext i
      simp [mulVec_diagonal]
  refine le_antisymm (fun x hx => ?_) fun x hx => ?_
  · obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x _ L).mp hx
    rw [hmv]
    exact L.smul_mem _ hy
  · refine (Submodule.mem_smul_pointwise_iff_exists x _ L).mpr ⟨(c⁻¹ : Kˣ) • x, ?_, ?_⟩
    · exact L.smul_mem _ hx
    · rw [hmv, Units.smul_def, smul_smul, Units.mul_inv, one_smul]

theorem smul_submodule_of_mem_normOneScalars {h : UnitaryFieldData p f K}
    {H : Subgroup (GL ι K)} {m : ℕ} {g : H} (hg : g ∈ normOneScalars h H m)
    (L : Submodule K (ι → K)) : g • L = L := by
  obtain ⟨c, -, -, hg⟩ := hg
  rw [Subgroup.smul_def, hg, scalar_smul_submodule]

end Scalars

abbrev unitaryScalars (h : UnitaryFieldData p f K) (n : ℕ) : Subgroup (unitarySU p f K n) :=
  normOneScalars h (unitarySU p f K n) n

theorem mem_unitaryScalars {h : UnitaryFieldData p f K} {n : ℕ} {g : unitarySU p f K n} :
    g ∈ unitaryScalars h n ↔ ∃ c : Kˣ, h.norm (c : K) = 1 ∧ c ^ n = 1 ∧
      (g : GL (Fin n) K) = GeneralLinearGroup.scalar (Fin n) c :=
  Iff.rfl

theorem unitaryScalars_le_center (h : UnitaryFieldData p f K) (n : ℕ) :
    unitaryScalars h n ≤ Subgroup.center (unitarySU p f K n) :=
  normOneScalars_le_center h _ n

theorem scalar_mem_unitarySU (h : UnitaryFieldData p f K) {n : ℕ} (hn : 1 ≤ n) {c : Kˣ}
    (hc : h.norm (c : K) = 1) (hcn : c ^ n = 1) :
    GeneralLinearGroup.scalar (Fin n) c ∈ unitarySU p f K n := by
  refine (scalar_mem_statedSU_iff h.prime h.card_eq_sq hn c).mpr ⟨hcn, ?_⟩
  rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, ← h.norm_eq_pow, hc]

theorem unitaryScalars_eq (h : UnitaryFieldData p f K) {n : ℕ} (hn : 1 ≤ n) :
    unitaryScalars h n = (StatedScalars (Fin n) K).subgroupOf (unitarySU p f K n) := by
  ext g
  rw [mem_unitaryScalars, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
  constructor
  · rintro ⟨c, -, -, hg⟩
    exact ⟨c, hg.symm⟩
  · rintro ⟨c, hc⟩
    have hmem := (scalar_mem_statedSU_iff h.prime h.card_eq_sq hn c).mp (hc ▸ g.2)
    refine ⟨c, ?_, hmem.1, hc.symm⟩
    rw [h.norm_eq_pow, ← Units.val_pow_eq_pow_val, hmem.2, Units.val_one]

theorem card_unitaryScalars (h : UnitaryFieldData p f K) {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (unitaryScalars h n) = Nat.gcd n (p ^ f + 1) := by
  rw [unitaryScalars_eq h hn]
  exact (unitary_scalar_kernel h.prime h.card_eq_sq hn).2.2

abbrev unitaryPSU (h : UnitaryFieldData p f K) (n : ℕ) : Type :=
  unitarySU p f K n ⧸ unitaryScalars h n

@[expose] def unitaryProj (h : UnitaryFieldData p f K) (n : ℕ) :
    unitarySU p f K n →* unitaryPSU h n :=
  QuotientGroup.mk' _

theorem unitaryProj_surjective (h : UnitaryFieldData p f K) (n : ℕ) :
    Function.Surjective (unitaryProj h n) :=
  QuotientGroup.mk'_surjective _

theorem ker_unitaryProj (h : UnitaryFieldData p f K) (n : ℕ) :
    (unitaryProj h n).ker = unitaryScalars h n :=
  QuotientGroup.ker_mk' _

@[expose] noncomputable def unitaryPSUEquiv (h : UnitaryFieldData p f K) {n : ℕ} (hn : 1 ≤ n) :
    unitaryPSU h n ≃* StatedProj (StatedSU n (p ^ f) K) :=
  QuotientGroup.quotientMulEquivOfEq (unitaryScalars_eq h hn)

theorem unitaryPSUEquiv_unitaryProj (h : UnitaryFieldData p f K) {n : ℕ} (hn : 1 ≤ n)
    (g : unitarySU p f K n) :
    unitaryPSUEquiv h hn (unitaryProj h n g) = (QuotientGroup.mk g : StatedProj _) :=
  QuotientGroup.quotientMulEquivOfEq_mk _ _

@[expose] def isotropicLines (h : UnitaryFieldData p f K) (n : ℕ) :
    SubMulAction (unitarySU p f K n) (Submodule K (Fin n → K)) where
  carrier := {L | Module.finrank K L = 1 ∧ ∀ a ∈ L, stdHermForm h n a a = 0}
  smul_mem' g L hL := by
    refine ⟨?_, fun a ha => ?_⟩
    · rw [← hL.1]
      exact LinearEquiv.finrank_map_eq (DistribMulAction.toLinearEquiv K (Fin n → K) g) L
    · obtain ⟨b, hb, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists a g L).mp ha
      rw [stdHermForm_smul_smul]
      exact hL.2 b hb

theorem mem_isotropicLines {h : UnitaryFieldData p f K} {n : ℕ} {L : Submodule K (Fin n → K)} :
    L ∈ isotropicLines h n ↔ Module.finrank K L = 1 ∧ ∀ a ∈ L, stdHermForm h n a a = 0 :=
  Iff.rfl

theorem smul_eq_map {ι : Type} [Fintype ι] [DecidableEq ι] (g : GL ι K)
    (L : Submodule K (ι → K)) : g • L = L.map (mulVecLin (g : Matrix ι ι K)) :=
  rfl

@[expose] def isotropicTransvectionGroup (h : UnitaryFieldData p f K) (n : ℕ)
    (L : Submodule K (Fin n → K)) : Subgroup (unitarySU p f K n) :=
  Subgroup.closure {g | ∃ a ∈ L, ∃ c ∈ h.traceZero,
    mulVecLin ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      hermTransvection (stdHermForm h n) a c}

@[expose] def projIsotropicTransvectionGroup (h : UnitaryFieldData p f K) (n : ℕ)
    (L : Submodule K (Fin n → K)) : Subgroup (unitaryPSU h n) :=
  (isotropicTransvectionGroup h n L).map (unitaryProj h n)

theorem exists_mem_unitarySU_hermTransvection (h : UnitaryFieldData p f K) {n : ℕ}
    {a : Fin n → K} (ha : stdHermForm h n a a = 0) {c : K} (hc : c ∈ h.traceZero) :
    ∃ g : unitarySU p f K n, mulVecLin ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      hermTransvection (stdHermForm h n) a c := by
  set T := hermTransvection (stdHermForm h n) a c
  set M : Matrix (Fin n) (Fin n) K := LinearMap.toMatrix' T
  have hMT : mulVecLin M = T := by
    rw [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']
  have hdet : M.det = 1 := by
    rw [← LinearMap.det_toLin', Matrix.toLin'_toMatrix']
    exact det_hermTransvection _ ha c
  let A : GL (Fin n) K := GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact one_ne_zero)
  have hc' : c + h.bar c = 0 := (h.mem_traceZero).mp hc
  have hA : A ∈ unitarySU p f K n := by
    refine (mem_unitarySU_iff_isometry h).mpr ⟨hdet, fun x y => ?_⟩
    have hx : (A : Matrix (Fin n) (Fin n) K) *ᵥ x = T x := by
      rw [← hMT]
      rfl
    have hy : (A : Matrix (Fin n) (Fin n) K) *ᵥ y = T y := by
      rw [← hMT]
      rfl
    rw [hx, hy]
    exact hermTransvection_isometry (stdHermForm_isSymm h n) ha hc' x y
  exact ⟨⟨A, hA⟩, hMT⟩

theorem exists_mem_isotropicTransvectionGroup (h : UnitaryFieldData p f K) {n : ℕ}
    {L : Submodule K (Fin n → K)} (hL : L ∈ isotropicLines h n) {a : Fin n → K} (haL : a ∈ L)
    {c : K} (hc : c ∈ h.traceZero) :
    ∃ g ∈ isotropicTransvectionGroup h n L,
      mulVecLin ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        hermTransvection (stdHermForm h n) a c := by
  obtain ⟨g, hg⟩ := exists_mem_unitarySU_hermTransvection h (hL.2 a haL) hc
  exact ⟨g, Subgroup.subset_closure ⟨a, haL, c, hc, hg⟩, hg⟩

end CFSG.ClassicalGroups.UnitaryFlag
