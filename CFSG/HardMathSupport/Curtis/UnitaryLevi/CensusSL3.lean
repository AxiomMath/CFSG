module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.CensusNodes

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.AGLEmbedding.UnitaryLevi
open scoped Pointwise

variable {f : ℕ} {K : Type} [Field K]

@[expose] def dg3Mat (u : Kˣ) : Matrix (Fin 3) (Fin 3) K :=
  diagonal ![(u : K), ((u⁻¹ : Kˣ) : K), 1]

theorem det_dg3Mat (u : Kˣ) : (dg3Mat u).det = 1 := by
  simp [dg3Mat, det_diagonal, Fin.prod_univ_three]

@[expose] def dg3 (u : Kˣ) : Matrix.SpecialLinearGroup (Fin 3) K := ⟨dg3Mat u, det_dg3Mat u⟩

@[expose] def dg3Hom : Kˣ →* Matrix.SpecialLinearGroup (Fin 3) K where
  toFun := dg3
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg3, dg3Mat]
  map_mul' u v := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul]
    show dg3Mat (u * v) = dg3Mat u * dg3Mat v
    simp only [dg3Mat, diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_comm]

theorem coe_dg3Hom (u : Kˣ) :
    ((dg3Hom u : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = dg3Mat u :=
  rfl

@[expose] def cycMat : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem det_cycMat : (cycMat : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [cycMat, Matrix.det_fin_three]

@[expose] def cyc : Matrix.SpecialLinearGroup (Fin 3) K := ⟨cycMat, det_cycMat⟩

theorem coe_cyc :
    ((cyc : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = cycMat :=
  rfl

theorem cyc_pow_three : (cyc : Matrix.SpecialLinearGroup (Fin 3) K) ^ 3 = 1 := by
  apply Subtype.ext
  rw [pow_succ, pow_two, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  show cycMat * cycMat * cycMat = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cycMat, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] def scl3 (ω : Kˣ) (hω : ω ^ 3 = 1) : Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨diagonal ![(ω : K), ω, ω], by
    simp only [det_diagonal, Fin.prod_univ_three]
    simp
    have := congrArg Units.val hω
    simpa [pow_succ] using this⟩

theorem scl3_central (ω : Kˣ) (hω : ω ^ 3 = 1) (A : Matrix.SpecialLinearGroup (Fin 3) K) :
    scl3 ω hω * A = A * scl3 ω hω := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  show diagonal ![(ω : K), ω, ω] * (A : Matrix (Fin 3) (Fin 3) K) =
    (A : Matrix (Fin 3) (Fin 3) K) * diagonal ![(ω : K), ω, ω]
  ext i j
  rw [diagonal_mul, mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [mul_comm]

theorem scl3_pow_three (ω : Kˣ) (hω : ω ^ 3 = 1) : scl3 ω hω ^ 3 = 1 := by
  apply Subtype.ext
  rw [pow_succ, pow_two, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  show diagonal ![(ω : K), ω, ω] * diagonal ![(ω : K), ω, ω] * diagonal ![(ω : K), ω, ω] = 1
  simp only [diagonal_mul_diagonal]
  have h3 : (ω : K) ^ 3 = 1 := by
    have := congrArg Units.val hω
    simpa using this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [one_apply] <;> linear_combination h3

theorem dg3_mul_cyc (ω : Kˣ) (hω : ω ^ 3 = 1) :
    dg3Hom ω * cyc = scl3 ω hω * (cyc * dg3Hom ω) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  show dg3Mat ω * cycMat = diagonal ![(ω : K), ω, ω] * (cycMat * dg3Mat ω)
  have h3 : ((ω⁻¹ : Kˣ) : K) = (ω : K) ^ 2 := by
    have : ω⁻¹ = ω ^ 2 := by
      rw [inv_eq_iff_eq_inv]
      calc ω = ω ^ 3 * (ω ^ 2)⁻¹ := by group
        _ = (ω ^ 2)⁻¹ := by rw [hω, one_mul]
    rw [this]
    simp
  have hω3 : (ω : K) ^ 3 = 1 := by
    have := congrArg Units.val hω
    simpa using this
  ext i j
  rw [diagonal_mul, mul_apply, mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [dg3Mat, cycMat, diagonal_apply, h3] <;>
    first | ring1 | linear_combination hω3 | linear_combination -hω3

section Witness

variable (h : UnitaryFieldData 2 f K)

theorem mem_normalizer_zpowers {G : Type*} [Group G] {g z : G} (hc : Commute g z) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
  have key : ∀ y ∈ Subgroup.zpowers z, g * y * g⁻¹ = y := by
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [(hc.zpow_right n).eq, mul_inv_cancel_right]
  have key' : ∀ y ∈ Subgroup.zpowers z, g⁻¹ * y * g = y := by
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [(hc.inv_left.zpow_right n).eq, inv_mul_cancel_right]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rwa [key x hx]
  · intro hx
    have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [this, key' _ hx]
    exact hx

theorem pow_three_of_mem_zpowers {G : Type*} [Group G] {x : G} (hx : x ^ 3 = 1) :
    ∀ y ∈ Subgroup.zpowers x, y ^ 3 = 1 := by
  intro y hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hx, _root_.one_zpow]

theorem coe_ρ3_inl (A : Matrix.SpecialLinearGroup (Fin 3) K) (i j : Fin 3) :
    (((leviSLHom (ε := 0) h 3 A : hypSU h 3 0) : GL (HypIndex 3 0) K) :
      Matrix (HypIndex 3 0) (HypIndex 3 0) K) (.inl i) (.inl j) =
      (A : Matrix (Fin 3) (Fin 3) K) i j := by
  rw [coe_leviSLHom]
  simp [levi]

theorem sl3_scalar {A : Matrix.SpecialLinearGroup (Fin 3) K}
    (hA : leviSLHom (ε := 0) h 3 A ∈ hypScalars h 3 0) :
    ∃ c : Kˣ, ∀ i j : Fin 3, (A : Matrix (Fin 3) (Fin 3) K) i j = if i = j then (c : K) else 0 := by
  obtain ⟨c, hc⟩ := exists_scalar_entry hA
  refine ⟨c, fun i j => ?_⟩
  rw [← coe_ρ3_inl h, hc]
  simp

theorem exists_sl3_witness {I : Set ℕ} (hI : I ⊆ {3}) :
    ∃ V : Subgroup (hypSU h 3 0), V ≤ flagStabilizer h 3 0 I ∧ ⁅V, V⁆ = V ∧
      ∃ A : Subgroup (hypSU h 3 0), A ≤ V ∧ IsPGroup 3 A ∧
        ¬ IsCyclic (A.map (hypProj h 3 0)) := by
  obtain ⟨ω, hω3, hω1⟩ := exists_unit_cube_root h
  have := h.finite
  set ρ : Matrix.SpecialLinearGroup (Fin 3) K →* hypSU h 3 0 := leviSLHom (ε := 0) h 3 with hρ
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (le_refl 3)
  refine ⟨ρ.range, ?_, commutator_range_self ρ, ?_⟩
  · rintro _ ⟨A, rfl⟩
    rw [mem_flagStabilizer]
    intro i hi
    have : i = 3 := hI hi
    subst this
    exact leviSLHom_smul_hypFlag_top h A
  set t : hypSU h 3 0 := ρ (dg3Hom ω) with ht
  set c : hypSU h 3 0 := ρ cyc with hc
  set z : hypSU h 3 0 := ρ (scl3 ω hω3) with hz
  have ht3 : t ^ 3 = 1 := by
    rw [ht, ← map_pow, ← map_pow, hω3, map_one, map_one]
  have hc3 : c ^ 3 = 1 := by rw [hc, ← map_pow, cyc_pow_three, map_one]
  have hz3 : z ^ 3 = 1 := by rw [hz, ← map_pow, scl3_pow_three, map_one]
  have hzt : Commute z t := Commute.map (scl3_central ω hω3 (dg3Hom ω) : Commute _ _) ρ
  have hzc : Commute z c := Commute.map (scl3_central ω hω3 cyc : Commute _ _) ρ
  have R : t * c = z * (c * t) := by
    rw [ht, hc, hz, ← map_mul, ← map_mul, ← map_mul, dg3_mul_cyc ω hω3]
  set E : Subgroup (hypSU h 3 0) := Subgroup.zpowers t ⊔ Subgroup.zpowers z with hE
  have htE : t ∈ E := Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hzE : z ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hEp : IsPGroup 3 E := by
    refine IsPGroup.to_sup_of_normal_right'
      (isPGroup_three_of_pow_three _ (pow_three_of_mem_zpowers ht3))
      (isPGroup_three_of_pow_three _ (pow_three_of_mem_zpowers hz3)) ?_
    refine Subgroup.zpowers_le.mpr ?_
    exact mem_normalizer_zpowers hzt.symm
  have hzc' : c⁻¹ * z * c = z := by
    calc c⁻¹ * z * c = c⁻¹ * (z * c) := by group
      _ = c⁻¹ * (c * z) := by rw [hzc.eq]
      _ = z := by group
  have hct : c * t * c⁻¹ = z⁻¹ * t := by
    calc c * t * c⁻¹ = z⁻¹ * (z * (c * t)) * c⁻¹ := by group
      _ = z⁻¹ * (t * c) * c⁻¹ := by rw [← R]
      _ = z⁻¹ * t := by group
  have hct' : c⁻¹ * t * c = z * t := by
    calc c⁻¹ * t * c = c⁻¹ * (t * c) := by group
      _ = c⁻¹ * (z * (c * t)) := by rw [R]
      _ = (c⁻¹ * z * c) * t := by group
      _ = z * t := by rw [hzc']
  have hconj : ∀ g : hypSU h 3 0, g * t * g⁻¹ ∈ E → g * z * g⁻¹ ∈ E →
      ∀ x ∈ E, g * x * g⁻¹ ∈ E := by
    intro g h1 h2 x hx
    have : E ≤ E.comap (MulAut.conj g).toMonoidHom :=
      sup_le (Subgroup.zpowers_le.mpr (by simpa [MulAut.conj_apply] using h1))
        (Subgroup.zpowers_le.mpr (by simpa [MulAut.conj_apply] using h2))
    exact this hx
  have hcn : c ∈ Subgroup.normalizer (E : Set (hypSU h 3 0)) := by
    have h1 : c * t * c⁻¹ ∈ E := by
      rw [hct]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hzE) htE
    have h2 : c * z * c⁻¹ ∈ E := by
      have e : c * z * c⁻¹ = z := by
        calc c * z * c⁻¹ = z * c * c⁻¹ := by rw [hzc.symm.eq]
          _ = z := by group
      rw [e]
      exact hzE
    have h1' : c⁻¹ * t * c⁻¹⁻¹ ∈ E := by
      rw [inv_inv, hct']
      exact Subgroup.mul_mem _ hzE htE
    have h2' : c⁻¹ * z * c⁻¹⁻¹ ∈ E := by
      rw [inv_inv, hzc']
      exact hzE
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => hconj c h1 h2 x hx
    · intro hx
      have := hconj c⁻¹ h1' h2' _ hx
      simpa [mul_assoc] using this
  set Q : Subgroup (hypSU h 3 0) := Subgroup.zpowers c ⊔ E with hQ
  have hQp : IsPGroup 3 Q :=
    IsPGroup.to_sup_of_normal_right'
      (isPGroup_three_of_pow_three _ (pow_three_of_mem_zpowers hc3)) hEp
      (Subgroup.zpowers_le.mpr hcn)
  have hQV : Q ≤ ρ.range := by
    refine sup_le (Subgroup.zpowers_le.mpr ⟨cyc, rfl⟩) (sup_le ?_ ?_)
    · exact Subgroup.zpowers_le.mpr ⟨dg3Hom ω, rfl⟩
    · exact Subgroup.zpowers_le.mpr ⟨scl3 ω hω3, rfl⟩
  have htQ : t ∈ Q := Subgroup.mem_sup_right htE
  have hcQ : c ∈ Q := Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  refine ⟨Q, hQV, hQp, ?_⟩
  set π := hypProj h 3 0 with hπ
  have hker : ∀ g : hypSU h 3 0, π g = 1 → g ∈ hypScalars h 3 0 := fun g hg => by
    rw [← ker_hypProj]; exact hg
  set x : ↥(Q.map π) := ⟨π t, Subgroup.mem_map_of_mem _ htQ⟩ with hx
  set y : ↥(Q.map π) := ⟨π c, Subgroup.mem_map_of_mem _ hcQ⟩ with hy
  refine not_isCyclic_of_two_cubes (x := x) (y := y) ?_ ?_ ?_ ?_
  · apply Subtype.ext
    show π t ^ 3 = 1
    rw [← map_pow, ht3, map_one]
  · apply Subtype.ext
    show π c ^ 3 = 1
    rw [← map_pow, hc3, map_one]
  · intro e
    have e' : π t = 1 := congrArg Subtype.val e
    obtain ⟨c', hc'⟩ := sl3_scalar h (hker _ e')
    have h0 := hc' 0 0
    have h1 := hc' 1 1
    simp [coe_dg3Hom, dg3Mat] at h0 h1
    have : ((ω⁻¹ : Kˣ) : K) = ω := by rw [Units.val_inv_eq_inv_val, h1, h0]
    have hω' : ω⁻¹ = ω := Units.ext this
    apply hω1
    have h2 : ω ^ 2 = 1 := by
      calc ω ^ 2 = ω * ω := by rw [pow_two]
        _ = ω * ω⁻¹ := by rw [hω']
        _ = 1 := mul_inv_cancel ω
    calc ω = ω ^ 3 * (ω ^ 2)⁻¹ := by group
      _ = 1 := by rw [hω3, h2]; simp
  · intro hyx
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hyx
    have hm' : π (t ^ m) = π c := by
      have := congrArg Subtype.val hm
      simpa [hx, hy, map_zpow] using this
    have hker' : (t ^ m)⁻¹ * c ∈ hypScalars h 3 0 := by
      apply hker
      rw [map_mul, map_inv, hm', inv_mul_cancel]
    have hrep : (t ^ m)⁻¹ * c = ρ ((dg3Hom (ω ^ m))⁻¹ * cyc) := by
      simp only [map_mul, map_inv, map_zpow, ht, hc]
    rw [hrep] at hker'
    obtain ⟨c', hc'⟩ := sl3_scalar h hker'
    have h10 := hc' 1 0
    have e : (dg3Hom (ω ^ m))⁻¹ = dg3Hom (ω ^ m)⁻¹ := (map_inv dg3Hom _).symm
    rw [e, Matrix.SpecialLinearGroup.coe_mul, coe_dg3Hom, coe_cyc] at h10
    simp [dg3Mat, cycMat, Matrix.mul_apply, Fin.sum_univ_three] at h10
    exact zpow_ne_zero _ ω.ne_zero h10

end Witness

end CFSG.HardMathSupport.Curtis.UnitaryLevi
