module

public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.Rank2GLAbelian
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.TotallySplit

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner

open scoped MatrixGroups

section Nonab

variable {F : Type} [Field F]

theorem det_scal (c : Fˣ) : Matrix.GeneralLinearGroup.det (scal c : GL (Fin 3) F) = c ^ 3 := by
  apply Units.ext
  simp

theorem cube_eq_one_of_commutator {x z : GL (Fin 3) F} {ω : Fˣ} (h : x * z = scal ω * (z * x)) :
    ω ^ 3 = 1 := by
  have h1 := congrArg Matrix.GeneralLinearGroup.det h
  simp only [map_mul, det_scal] at h1
  have h2 : ω ^ 3 * (Matrix.GeneralLinearGroup.det z * Matrix.GeneralLinearGroup.det x) =
      1 * (Matrix.GeneralLinearGroup.det z * Matrix.GeneralLinearGroup.det x) := by
    rw [one_mul, ← h1, mul_comm]
  exact mul_right_cancel h2

theorem isPrimitiveRoot_of_pow_three {ω : Fˣ} (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) :
    IsPrimitiveRoot (ω : F) 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf ω = 3 := orderOf_eq_prime h3 h1
  have : IsPrimitiveRoot ω 3 := hord ▸ IsPrimitiveRoot.orderOf ω
  exact IsPrimitiveRoot.coe_units_iff.mpr this

theorem exists_scal_commutator (A : Subgroup (GL (Fin 3) F))
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y * x⁻¹ * y⁻¹ ∈ sc F) {x y : GL (Fin 3) F} (hx : x ∈ A)
    (hy : y ∈ A) : ∃ ω : Fˣ, x * y = scal ω * (y * x) := by
  obtain ⟨ω, hω⟩ := mem_sc_iff.mp (hcomm x hx y hy)
  refine ⟨ω, ?_⟩
  rw [← hω]
  group

theorem scal_injective : Function.Injective (scal : Fˣ → GL (Fin 3) F) := by
  intro a b h
  apply Units.ext
  have := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 0 0) h
  simpa [coe_scal, Matrix.scalar_apply] using this

theorem eq_monomial_mul_scal [Finite F] (A : Subgroup (GL (Fin 3) F))
    (hidx : ((sc F).subgroupOf A).index = 9) {x z : GL (Fin 3) F} (hx : x ∈ A) (hz : z ∈ A)
    {ω : Fˣ} (hω : IsPrimitiveRoot (ω : F) 3) (hxz : x * z = scal ω * (z * x)) :
    ∀ w ∈ A, ∃ (i j : Fin 3) (c : Fˣ), w = x ^ (i : ℕ) * z ^ (j : ℕ) * scal c := by
  intro w hw
  have hs : scal ω ∈ Subgroup.center (GL (Fin 3) F) := sc_mem_center (scal_mem_sc ω)
  let f : Fin 3 × Fin 3 → A := fun p => ⟨x ^ (p.1 : ℕ) * z ^ (p.2 : ℕ),
    A.mul_mem (A.pow_mem hx _) (A.pow_mem hz _)⟩
  have hinj : ∀ p q, (f p)⁻¹ * f q ∈ (sc F).subgroupOf A → p = q := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hmem
    rw [Subgroup.mem_subgroupOf] at hmem
    obtain ⟨c, hc⟩ := mem_sc_iff.mp hmem
    have hc' : ((x ^ (i : ℕ) * z ^ (j : ℕ))⁻¹ * (x ^ (i' : ℕ) * z ^ (j' : ℕ)) : GL (Fin 3) F) =
        scal c := hc
    have hu' : x ^ (i' : ℕ) * z ^ (j' : ℕ) = (x ^ (i : ℕ) * z ^ (j : ℕ)) * scal c := by
      rw [inv_mul_eq_iff_eq_mul] at hc'
      exact hc'
    obtain ⟨hR1, hR2⟩ := monomial_commute x z (scal ω) hs hxz i j
    obtain ⟨hR1', hR2'⟩ := monomial_commute x z (scal ω) hs hxz i' j'
    rw [hu'] at hR1' hR2'
    have hcc : scal c ∈ Subgroup.center (GL (Fin 3) F) := sc_mem_center (scal_mem_sc c)
    have e1 := eq_of_pair_right _ _ z _ _ hcc hR1 hR1'
    have e2 := eq_of_pair_left _ _ x _ _ hcc hR2 hR2'
    rw [← map_pow, ← map_pow] at e1 e2
    have f1 := scal_injective e1
    have f2 := scal_injective e2
    have g1 : (ω : F) ^ (i : ℕ) = (ω : F) ^ (i' : ℕ) := by
      have := congrArg (fun u : Fˣ => (u : F)) f1
      simpa using this
    have g2 : (ω : F) ^ (j : ℕ) = (ω : F) ^ (j' : ℕ) := by
      have := congrArg (fun u : Fˣ => (u : F)) f2
      simpa using this
    exact Prod.ext (Fin.ext (hω.pow_inj i.2 i'.2 g1)) (Fin.ext (hω.pow_inj j.2 j'.2 g2))
  have hcard : Nat.card (Fin 3 × Fin 3) = ((sc F).subgroupOf A).index := by
    simp [hidx]
  obtain ⟨⟨i, j⟩, hij⟩ :=
    exists_mem_of_injective_of_index A ((sc F).subgroupOf A) f hinj hcard ⟨w, hw⟩
  rw [Subgroup.mem_subgroupOf] at hij
  obtain ⟨c, hc⟩ := mem_sc_iff.mp hij
  refine ⟨i, j, c, ?_⟩
  have hc' : ((x ^ (i : ℕ) * z ^ (j : ℕ))⁻¹ * w : GL (Fin 3) F) = scal c := hc
  rw [inv_mul_eq_iff_eq_mul] at hc'
  exact hc'

theorem normal_form {y w : GL (Fin 3) F} {ω b : Fˣ}
    (hω : IsPrimitiveRoot (ω : F) 3) (hyw : y * w = scal ω * (w * y))
    (hw3 : w ^ 3 = scal b) {v : Fin 3 → F} (hv : v ≠ 0)
    (hyv : (y : Matrix (Fin 3) (Fin 3) F).mulVec v = v) :
    ∃ g : GL (Fin 3) F, g * y * g⁻¹ = diagGL F 1 ω (ω ^ 2) ∧ g * w * g⁻¹ = monomGL F b := by
  set Y : Matrix (Fin 3) (Fin 3) F := (y : Matrix (Fin 3) (Fin 3) F) with hY
  set W : Matrix (Fin 3) (Fin 3) F := (w : Matrix (Fin 3) (Fin 3) F) with hW
  have hYW : Y * W = Matrix.scalar (Fin 3) (ω : F) * (W * Y) := by
    rw [hY, hW, ← Units.val_mul, ← Units.val_mul, hyw, Units.val_mul, coe_scal]
  have hYWv : ∀ u : Fin 3 → F, Y.mulVec (W.mulVec u) = (ω : F) • W.mulVec (Y.mulVec u) := by
    intro u
    have : (Matrix.scalar (Fin 3) (ω : F) * (W * Y)).mulVec u = (ω : F) • (W * Y).mulVec u := by
      rw [← Matrix.mulVec_mulVec]
      ext i
      simp [Matrix.mulVec, dotProduct, Matrix.scalar_apply, Matrix.diagonal_apply]
    rw [Matrix.mulVec_mulVec, hYW, this, Matrix.mulVec_mulVec]
  have hWinj : ∀ u : Fin 3 → F, W.mulVec u = 0 → u = 0 := by
    intro u hu
    have h1 : ((w⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * W = 1 := by
      rw [hW, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have := congrArg (((w⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec) hu
    rwa [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, Matrix.mulVec_zero] at this
  let vec : Fin 3 → Fin 3 → F := ![v, W.mulVec v, W.mulVec (W.mulVec v)]
  let μ : Fin 3 → F := fun i => (ω : F) ^ (i : ℕ)
  have hvne : ∀ i, vec i ≠ 0 := by
    intro i
    fin_cases i
    · exact hv
    · exact fun h => hv (hWinj _ h)
    · exact fun h => hv (hWinj _ (hWinj _ h))
  have hY1 : Y.mulVec (W.mulVec v) = (ω : F) • W.mulVec v := by rw [hYWv, hyv]
  have hY2 : Y.mulVec (W.mulVec (W.mulVec v)) = (ω : F) ^ 2 • W.mulVec (W.mulVec v) := by
    rw [hYWv, hY1, Matrix.mulVec_smul, smul_smul, pow_two]
  have hYvec : ∀ i, Y.mulVec (vec i) = μ i • vec i := by
    intro i
    fin_cases i
    · simpa [vec, μ] using hyv
    · simpa [vec, μ] using hY1
    · simpa [vec, μ] using hY2
  have hμ : Function.Injective μ := fun i j h => Fin.ext (hω.pow_inj i.2 j.2 h)
  have hind : LinearIndependent F vec := by
    refine Module.End.eigenvectors_linearIndependent' (Matrix.toLin' Y) μ hμ vec fun i => ?_
    refine ⟨?_, hvne i⟩
    rw [Module.End.mem_eigenspace_iff]
    simpa [Matrix.toLin'_apply] using hYvec i
  let B : Matrix (Fin 3) (Fin 3) F := Matrix.of fun i j => vec j i
  have hB : IsUnit B := Matrix.linearIndependent_cols_iff_isUnit.mp hind
  have hYB : Y * B = B * Matrix.diagonal ![1, (ω : F), (ω : F) ^ 2] := by
    ext i j
    have h1 : (Y * B) i j = (Y.mulVec (vec j)) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, B]
    rw [h1, hYvec j, Matrix.mul_diagonal]
    fin_cases j <;> simp [B, μ, vec, mul_comm]
  have hW3 : W ^ 3 = Matrix.scalar (Fin 3) (b : F) := coe_pow_eq_scalar hw3
  have hW3v : W.mulVec (W.mulVec (W.mulVec v)) = (b : F) • v := by
    have : W.mulVec (W.mulVec (W.mulVec v)) = (W ^ 3).mulVec v := by
      simp [pow_succ, ← Matrix.mulVec_mulVec]
    rw [this, hW3]
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.scalar_apply, Matrix.diagonal_apply]
  have hWB : W * B = B * !![0, 0, (b : F); 1, 0, 0; 0, 1, 0] := by
    ext i j
    have h1 : (W * B) i j = (W.mulVec (vec j)) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, B]
    rw [h1]
    fin_cases j
    · simp [vec, B, Matrix.mul_apply, Fin.sum_univ_three]
    · simp [vec, B, Matrix.mul_apply, Fin.sum_univ_three]
    · have := congrFun hW3v i
      simp [vec, B, Matrix.mul_apply, Fin.sum_univ_three, mul_comm] at this ⊢
      exact this
  let Bu : GL (Fin 3) F := hB.unit
  have hBu : (Bu : Matrix (Fin 3) (Fin 3) F) = B := rfl
  refine ⟨Bu⁻¹, ?_, ?_⟩
  · rw [inv_inv, mul_assoc, inv_mul_eq_iff_eq_mul]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hBu]
    simpa [diagGL] using hYB
  · rw [inv_inv, mul_assoc, inv_mul_eq_iff_eq_mul]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hBu]
    simpa [monomGL] using hWB

theorem monomial_mem_sc {x z : GL (Fin 3) F} {ω : Fˣ} (hω : IsPrimitiveRoot (ω : F) 3)
    (hxz : x * z = scal ω * (z * x)) (i j : Fin 3) (c : Fˣ)
    (h : x ^ (i : ℕ) * z ^ (j : ℕ) * scal c ∈ sc F) : i = 0 ∧ j = 0 := by
  have hs : scal ω ∈ Subgroup.center (GL (Fin 3) F) := sc_mem_center (scal_mem_sc ω)
  have hu : x ^ (i : ℕ) * z ^ (j : ℕ) ∈ sc F := by
    have := (sc F).mul_mem h (scal_mem_sc c⁻¹)
    rwa [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one] at this
  have hc := sc_mem_center hu
  obtain ⟨hR1, hR2⟩ := monomial_commute x z (scal ω) hs hxz i j
  have e1 : (x ^ (i : ℕ) * z ^ (j : ℕ)) * z = z * (x ^ (i : ℕ) * z ^ (j : ℕ)) :=
    (Subgroup.mem_center_iff.mp hc z).symm
  have e2 : x * (x ^ (i : ℕ) * z ^ (j : ℕ)) = (x ^ (i : ℕ) * z ^ (j : ℕ)) * x :=
    Subgroup.mem_center_iff.mp hc x
  rw [e1] at hR1
  rw [e2] at hR2
  have h1 : scal ω ^ (i : ℕ) = 1 := by
    have := hR1.symm
    exact (mul_eq_right.mp this)
  have h2 : scal ω ^ (j : ℕ) = 1 := by
    have := hR2.symm
    exact (mul_eq_right.mp this)
  have h1' : scal (ω ^ (i : ℕ)) = (scal (1 : Fˣ) : GL (Fin 3) F) := by rw [scal_pow, h1, scal_one]
  have h2' : scal (ω ^ (j : ℕ)) = (scal (1 : Fˣ) : GL (Fin 3) F) := by rw [scal_pow, h2, scal_one]
  have g1 := scal_injective h1'
  have g2 := scal_injective h2'
  have k1 : (ω : F) ^ (i : ℕ) = 1 := by
    have := congrArg (fun u : Fˣ => (u : F)) g1
    simpa using this
  have k2 : (ω : F) ^ (j : ℕ) = 1 := by
    have := congrArg (fun u : Fˣ => (u : F)) g2
    simpa using this
  have d1 := (hω.pow_eq_one_iff_dvd _).mp k1
  have d2 := (hω.pow_eq_one_iff_dvd _).mp k2
  have hi := i.2
  have hj := j.2
  exact ⟨Fin.ext (by simp; omega), Fin.ext (by simp; omega)⟩

theorem pow_ne_one_of_ne_zero {ω : Fˣ} (hω : IsPrimitiveRoot (ω : F) 3) {i : Fin 3} (hi : i ≠ 0) :
    ω ^ (i : ℕ) ≠ 1 := by
  intro h
  have h' : (ω : F) ^ (i : ℕ) = 1 := by simpa using congrArg (fun u : Fˣ => (u : F)) h
  have hd := (hω.pow_eq_one_iff_dvd _).mp h'
  have h2 := i.2
  apply hi
  apply Fin.ext
  simp
  omega

theorem exists_partner [Finite F] (A : Subgroup (GL (Fin 3) F))
    (hidx : ((sc F).subgroupOf A).index = 9) {x z : GL (Fin 3) F} (hx : x ∈ A) (hz : z ∈ A)
    {ω : Fˣ} (hω : IsPrimitiveRoot (ω : F) 3) (hxz : x * z = scal ω * (z * x)) {u : GL (Fin 3) F}
    (hu : u ∈ A) (hn : u ∉ sc F) :
    ∃ w ∈ A, ∃ ω' : Fˣ, IsPrimitiveRoot (ω' : F) 3 ∧ u * w = scal ω' * (w * u) := by
  obtain ⟨i, j, c, rfl⟩ := eq_monomial_mul_scal A hidx hx hz hω hxz u hu
  have hs : scal ω ∈ Subgroup.center (GL (Fin 3) F) := sc_mem_center (scal_mem_sc ω)
  have hcc : scal c ∈ Subgroup.center (GL (Fin 3) F) := sc_mem_center (scal_mem_sc c)
  obtain ⟨hR1, hR2⟩ := monomial_commute x z (scal ω) hs hxz i j
  have hne : ¬ (i = 0 ∧ j = 0) := fun h => hn (by
    obtain ⟨rfl, rfl⟩ := h
    simpa using scal_mem_sc c)
  have hω3 : ω ^ 3 = 1 := cube_eq_one_of_commutator hxz
  by_cases hi : i = 0
  · have hj : j ≠ 0 := fun hj => hne ⟨hi, hj⟩
    refine ⟨x, hx, (ω ^ (j : ℕ))⁻¹, ?_, ?_⟩
    · refine isPrimitiveRoot_of_pow_three ?_ ?_
      · rw [inv_pow, ← pow_mul, mul_comm, pow_mul, hω3, one_pow, inv_one]
      · rw [Ne, inv_eq_one]
        exact pow_ne_one_of_ne_zero hω hj
    · have := central_swap_left (x ^ (i : ℕ) * z ^ (j : ℕ)) (scal c) x (scal ω ^ (j : ℕ)) hcc hR2
      rw [this, scal_inv, scal_pow]
  · refine ⟨z, hz, ω ^ (i : ℕ), ?_, ?_⟩
    · refine isPrimitiveRoot_of_pow_three ?_ (pow_ne_one_of_ne_zero hω hi)
      rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]
    · have := central_swap_right (x ^ (i : ℕ) * z ^ (j : ℕ)) (scal c) z (scal ω ^ (i : ℕ)) hcc hR1
      rw [this, scal_pow]

theorem exists_cubeone_noncentral [Finite F] (h3 : 3 ∣ Nat.card F - 1)
    (A : Subgroup (GL (Fin 3) F)) (hS : sc F ≤ A) (hcube : ∀ x ∈ A, x ^ 3 ∈ sc F)
    {x z : GL (Fin 3) F} (hx : x ∈ A) (hz : z ∈ A) {ω : Fˣ} (hω : IsPrimitiveRoot (ω : F) 3)
    (hxz : x * z = scal ω * (z * x)) :
    ∃ y ∈ A, y ^ 3 = 1 ∧ y ∉ sc F := by
  have hs : scal ω ∈ Subgroup.center (GL (Fin 3) F) := sc_mem_center (scal_mem_sc ω)
  have hω3 : ω ^ 3 = 1 := cube_eq_one_of_commutator hxz
  obtain ⟨a, ha⟩ := mem_sc_iff.mp (hcube x hx)
  obtain ⟨b, hb⟩ := mem_sc_iff.mp (hcube z hz)
  by_cases hbc : ∃ d : Fˣ, b = d ^ 3
  · obtain ⟨d, hd⟩ := hbc
    refine ⟨z * scal d⁻¹, A.mul_mem hz (hS (scal_mem_sc _)), ?_, ?_⟩
    · have c1 : Commute z (scal d⁻¹) := Subgroup.mem_center_iff.mp (sc_mem_center (scal_mem_sc _)) z
      rw [c1.mul_pow, hb, ← scal_pow, ← scal_mul, hd, inv_pow, mul_inv_cancel, scal_one]
    · intro hy
      have := monomial_mem_sc hω hxz 0 1 d⁻¹ (by simpa using hy)
      exact absurd this.2 (by decide)
  · push Not at hbc
    obtain ⟨k, d, hkd⟩ := exists_cube_mul_pow h3 hbc a
    refine ⟨x * z ^ (k : ℕ) * scal d⁻¹,
      A.mul_mem (A.mul_mem hx (A.pow_mem hz _)) (hS (scal_mem_sc _)), ?_, ?_⟩
    · have c1 : Commute (x * z ^ (k : ℕ)) (scal d⁻¹) :=
        Subgroup.mem_center_iff.mp (sc_mem_center (scal_mem_sc _)) _
      have hsk : scal ω ^ (k : ℕ) ∈ Subgroup.center (GL (Fin 3) F) := Subgroup.pow_mem _ hs _
      have hsk3 : (scal ω ^ (k : ℕ)) ^ 3 = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, ← scal_pow, hω3, scal_one, one_pow]
      have hc := mul_pow_three_of_central x (z ^ (k : ℕ)) _ hsk hsk3
        (mul_pow_of_central x z (scal ω) hs hxz k)
      rw [c1.mul_pow, hc, ha, ← pow_mul, mul_comm, pow_mul, hb, ← scal_pow, ← scal_pow, ← scal_mul,
        ← scal_mul, hkd, inv_pow, mul_inv_cancel, scal_one]
    · intro hy
      have := monomial_mem_sc hω hxz 1 k d⁻¹ (by simpa using hy)
      exact absurd this.1 (by decide)

theorem det_conj (g h : GL (Fin 3) F) :
    Matrix.GeneralLinearGroup.det (g * h * g⁻¹) = Matrix.GeneralLinearGroup.det h := by
  rw [map_mul, map_mul, map_inv, mul_comm (Matrix.GeneralLinearGroup.det g), mul_assoc,
    mul_inv_cancel, mul_one]

theorem det_monomGL (b : Fˣ) : Matrix.GeneralLinearGroup.det (monomGL F b) = b := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  simp [monomGL, Matrix.det_fin_three]

theorem det_diagGL (a b c : Fˣ) :
    Matrix.GeneralLinearGroup.det (diagGL F a b c) = a * b * c := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  simp [diagGL, Matrix.det_diagonal, Fin.prod_univ_three]

theorem nonabelian_heisenberg [Finite F] (h3 : 3 ∣ Nat.card F - 1) (A : Subgroup (GL (Fin 3) F))
    (hS : sc F ≤ A) (hcube : ∀ x ∈ A, x ^ 3 ∈ sc F)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y * x⁻¹ * y⁻¹ ∈ sc F)
    (hidx : ((sc F).subgroupOf A).index = 9)
    (hout : ∃ x ∈ A, ∀ c : Fˣ, (x : Matrix (Fin 3) (Fin 3) F).det ≠ (c : F) ^ 3)
    {x₀ z₀ : GL (Fin 3) F} (hx₀ : x₀ ∈ A) (hz₀ : z₀ ∈ A) (hne : x₀ * z₀ ≠ z₀ * x₀) :
    ∃ (g : GL (Fin 3) F) (lam ω : Fˣ), IsPrimitiveRoot (ω : F) 3 ∧ (∀ c : Fˣ, lam ≠ c ^ 3) ∧
      A.map (MulAut.conj g).toMonoidHom = heisenbergThree F lam ω := by
  obtain ⟨ω₀, hxz⟩ := exists_scal_commutator A hcomm hx₀ hz₀
  have hω₀3 : ω₀ ^ 3 = 1 := cube_eq_one_of_commutator hxz
  have hω₀1 : ω₀ ≠ 1 := by
    rintro rfl
    apply hne
    rw [hxz, scal_one, one_mul]
  have hω₀ : IsPrimitiveRoot (ω₀ : F) 3 := isPrimitiveRoot_of_pow_three hω₀3 hω₀1
  obtain ⟨y, hyA, hy3, hyn⟩ := exists_cubeone_noncentral h3 A hS hcube hx₀ hz₀ hω₀ hxz
  obtain ⟨v, hv, ε, hyv⟩ := exists_eigenvector_of_pow_three h3 y hy3
  have hε : ε ≠ 0 := by
    rintro rfl
    apply hv
    have h1 : ((y⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (y : Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have := congrArg (((y⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec) hyv
    rwa [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, zero_smul, Matrix.mulVec_zero] at this
  set e : Fˣ := Units.mk0 ε hε with he
  set y₁ : GL (Fin 3) F := y * scal e⁻¹ with hy₁
  have hy₁A : y₁ ∈ A := A.mul_mem hyA (hS (scal_mem_sc _))
  have hy₁n : y₁ ∉ sc F := by
    intro h
    apply hyn
    have := (sc F).mul_mem h (scal_mem_sc e)
    rwa [hy₁, mul_assoc, ← scal_mul, inv_mul_cancel, scal_one, mul_one] at this
  have hy₁v : (y₁ : Matrix (Fin 3) (Fin 3) F).mulVec v = v := by
    rw [hy₁, Units.val_mul, ← Matrix.mulVec_mulVec, coe_scal]
    have : (Matrix.scalar (Fin 3) ((e⁻¹ : Fˣ) : F)).mulVec v = ((e⁻¹ : Fˣ) : F) • v := by
      ext i
      simp [Matrix.mulVec, dotProduct, Matrix.scalar_apply, Matrix.diagonal_apply]
    rw [this, Matrix.mulVec_smul, hyv, smul_smul]
    simp [he]
    rw [inv_mul_cancel₀ hε, one_smul]
  obtain ⟨w, hwA, ω', hω', hyw⟩ := exists_partner A hidx hx₀ hz₀ hω₀ hxz hy₁A hy₁n
  obtain ⟨b, hb⟩ := mem_sc_iff.mp (hcube w hwA)
  obtain ⟨g, hg1, hg2⟩ := normal_form hω' hyw hb hv hy₁v
  have hgen := eq_monomial_mul_scal A hidx hy₁A hwA hω' hyw
  have hω'3 : ω' ^ 3 = 1 := cube_eq_one_of_commutator hyw
  have hdy : Matrix.GeneralLinearGroup.det y₁ = 1 := by
    have := det_conj g y₁
    rw [hg1, det_diagGL] at this
    rw [← this, one_mul, ← pow_succ', hω'3]
  have hdw : Matrix.GeneralLinearGroup.det w = b := by
    have := det_conj g w
    rw [hg2, det_monomGL] at this
    exact this.symm
  have hbnc : ∀ c : Fˣ, b ≠ c ^ 3 := by
    obtain ⟨w', hw'A, hw'⟩ := hout
    obtain ⟨i, j, c, rfl⟩ := hgen w' hw'A
    intro e he
    apply hw' (e ^ (j : ℕ) * c)
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    have : Matrix.GeneralLinearGroup.det (y₁ ^ (i : ℕ) * w ^ (j : ℕ) * scal c) =
        (e ^ (j : ℕ) * c) ^ 3 := by
      rw [map_mul, map_mul, map_pow, map_pow, hdy, hdw, det_scal, he, one_pow, one_mul, mul_pow,
        ← pow_mul, ← pow_mul, mul_comm 3 (j : ℕ)]
    rw [this]
    simp
  refine ⟨g, b, ω', hω', hbnc, ?_⟩
  have hcen : ∀ s ∈ sc F, g * s * g⁻¹ = s := by
    intro s hs
    rw [Subgroup.mem_center_iff.mp (sc_mem_center hs) g, mul_assoc, mul_inv_cancel, mul_one]
  have e1 : (MulAut.conj g).toMonoidHom y₁ = diagGL F 1 ω' (ω' ^ 2) := by
    simpa [MulAut.conj_apply] using hg1
  have e2 : (MulAut.conj g).toMonoidHom w = monomGL F b := by
    simpa [MulAut.conj_apply] using hg2
  have hD : diagGL F 1 ω' (ω' ^ 2) ∈ heisenbergThree F b ω' :=
    Subgroup.subset_closure (by simp)
  have hZ : monomGL F b ∈ heisenbergThree F b ω' := Subgroup.subset_closure (by simp)
  have hSc : ∀ s ∈ sc F, s ∈ heisenbergThree F b ω' := fun s hs =>
    Subgroup.subset_closure (Or.inl hs)
  apply le_antisymm
  · rintro _ ⟨w', hw'A, rfl⟩
    obtain ⟨i, j, c, rfl⟩ := hgen w' hw'A
    have e3 : (MulAut.conj g).toMonoidHom (scal c) = scal c := hcen _ (scal_mem_sc c)
    rw [map_mul, map_mul, map_pow, map_pow, e1, e2, e3]
    exact (heisenbergThree F b ω').mul_mem
      ((heisenbergThree F b ω').mul_mem ((heisenbergThree F b ω').pow_mem hD _)
        ((heisenbergThree F b ω').pow_mem hZ _)) (hSc _ (scal_mem_sc c))
  · rw [heisenbergThree, Subgroup.closure_le]
    refine Set.union_subset ?_ ?_
    · intro s hs
      exact ⟨s, hS hs, hcen s hs⟩
    · intro u hu
      rcases hu with rfl | rfl
      · exact ⟨w, hwA, e2⟩
      · exact ⟨y₁, hy₁A, e1⟩

end Nonab

end CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner
