module

public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.Rank2GUSetup
public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.Rank2GLAbelian

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.RankTwoGU

open scoped MatrixGroups
open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.KFacts
open CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner

section Scalars

variable {K : Type} [Field K]

theorem sc_normal (K : Type) [Field K] : (sc K).Normal :=
  ⟨fun s hs g => by
    rw [Subgroup.mem_center_iff.mp (sc_mem_center hs) g, mul_inv_cancel_right]
    exact hs⟩

theorem scal_comm (c : Kˣ) (g : GL (Fin 3) K) : g * scal c = scal c * g :=
  Subgroup.mem_center_iff.mp (sc_mem_center (scal_mem_sc c)) g

theorem mem_sup_sc {A : Subgroup (GL (Fin 3) K)} {x : GL (Fin 3) K} :
    x ∈ A ⊔ sc K ↔ ∃ a ∈ A, ∃ c : Kˣ, x = a * scal c := by
  have := sc_normal K
  rw [Subgroup.mem_sup_of_normal_right]
  constructor
  · rintro ⟨a, ha, z, hz, rfl⟩
    obtain ⟨c, rfl⟩ := mem_sc_iff.mp hz
    exact ⟨a, ha, c, rfl⟩
  · rintro ⟨a, ha, c, rfl⟩
    exact ⟨a, ha, scal c, scal_mem_sc c, rfl⟩

theorem comm_central {G : Type*} [Group G] (a b u v : G) (hu : u ∈ Subgroup.center G)
    (hv : v ∈ Subgroup.center G) :
    (a * u) * (b * v) * (a * u)⁻¹ * (b * v)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have hu' : ∀ g, u * g = g * u := fun g => (Subgroup.mem_center_iff.mp hu g).symm
  have hv' : ∀ g, v * g = g * v := fun g => (Subgroup.mem_center_iff.mp hv g).symm
  have c1 : ∀ g, (a * u) * g * (a * u)⁻¹ = a * g * a⁻¹ := by
    intro g
    calc (a * u) * g * (a * u)⁻¹ = a * (u * g) * u⁻¹ * a⁻¹ := by simp only [_root_.mul_inv_rev, mul_assoc]
      _ = a * (g * u) * u⁻¹ * a⁻¹ := by rw [hu' g]
      _ = a * g * a⁻¹ := by simp only [mul_assoc, mul_inv_cancel, mul_one]
  rw [c1 (b * v), _root_.mul_inv_rev]
  calc a * (b * v) * a⁻¹ * (v⁻¹ * b⁻¹) = a * b * (v * a⁻¹) * (v⁻¹ * b⁻¹) := by simp only [mul_assoc]
    _ = a * b * (a⁻¹ * v) * (v⁻¹ * b⁻¹) := by rw [hv' a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by simp only [mul_assoc, mul_inv_cancel_left]

end Scalars

section SupSc

variable {K : Type} [Field K] {A : Subgroup (GL (Fin 3) K)}

theorem sup_cube (hcube : ∀ x ∈ A, x ^ 3 ∈ sc K) : ∀ x ∈ A ⊔ sc K, x ^ 3 ∈ sc K := by
  intro x hx
  obtain ⟨a, ha, c, rfl⟩ := mem_sup_sc.mp hx
  have hcom : Commute a (scal c) := scal_comm c a
  rw [hcom.mul_pow, ← scal_pow]
  exact (sc K).mul_mem (hcube a ha) (scal_mem_sc _)

theorem sup_comm (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y * x⁻¹ * y⁻¹ ∈ sc K) :
    ∀ x ∈ A ⊔ sc K, ∀ y ∈ A ⊔ sc K, x * y * x⁻¹ * y⁻¹ ∈ sc K := by
  intro x hx y hy
  obtain ⟨a, ha, c, rfl⟩ := mem_sup_sc.mp hx
  obtain ⟨a', ha', c', rfl⟩ := mem_sup_sc.mp hy
  rw [comm_central a a' _ _ (sc_mem_center (scal_mem_sc c)) (sc_mem_center (scal_mem_sc c'))]
  exact hcomm a ha a' ha'

theorem sup_abelian (hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    ∀ x ∈ A ⊔ sc K, ∀ y ∈ A ⊔ sc K, x * y = y * x := by
  intro x hx y hy
  obtain ⟨a, ha, c, rfl⟩ := mem_sup_sc.mp hx
  obtain ⟨a', ha', c', rfl⟩ := mem_sup_sc.mp hy
  have hc1 : Commute a (scal c') := scal_comm c' a
  have hc2 : Commute (scal c) a' := (scal_comm c a').symm
  have hc3 : Commute (scal c) (scal c') := scal_comm c' (scal c)
  have hc0 : Commute a a' := hab a ha a' ha'
  exact (hc0.mul_right hc1).mul_left (hc2.mul_right hc3)

theorem sup_index (hrank : Nat.card (A ⧸ (sc K).subgroupOf A) = 9) :
    ((sc K).subgroupOf (A ⊔ sc K)).index = 9 := by
  have := sc_normal K
  exact (Subgroup.relIndex_sup_right A (sc K)).trans hrank

end SupSc

section Unitary

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem conjTr_scalar (σ : K ≃+* K) (a : K) :
    conjTr σ (Matrix.scalar (Fin 3) a) = Matrix.scalar (Fin 3) (σ a) := by
  ext i j
  simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply, Matrix.scalar_apply,
    Matrix.diagonal_apply]
  by_cases hij : j = i
  · subst hij; simp
  · simp [hij, Ne.symm hij]

theorem scal_mem_unitaryIsom3_iff {c : Kˣ} :
    scal c ∈ unitaryIsom3 h ↔ invol h c * c = 1 := by
  rw [mem_unitaryIsom3_iff, coe_scal, conjTr_scalar, ← map_mul]
  constructor
  · intro hc
    have := congrFun (congrFun hc 0) 0
    simpa [Matrix.scalar_apply] using this
  · intro hc
    rw [hc, map_one]

theorem mul_scal_mem_of_cube (h3 : 3 ∣ p ^ f + 1) {a : GL (Fin 3) K} (ha : a ∈ unitaryIsom3 h)
    (c : Kˣ) (hx : (a * scal c) ^ 3 ∈ unitaryIsom3 h) : a * scal c ∈ unitaryIsom3 h := by
  have hcom : Commute a (scal c) := scal_comm c a
  rw [hcom.mul_pow, ← scal_pow] at hx
  have h1 : scal (c ^ 3) ∈ unitaryIsom3 h := by
    have := mul_mem (inv_mem (pow_mem ha 3)) hx
    rwa [inv_mul_cancel_left] at this
  rw [scal_mem_unitaryIsom3_iff] at h1
  have hν : invol h c * c = 1 := by
    apply hF3_of_dvd h h3
    · rw [map_mul, (isUnitaryInvolution_invol h).invol, mul_comm]
    · rw [mul_pow, ← map_pow]
      simpa using h1
  exact mul_mem ha ((scal_mem_unitaryIsom3_iff h).mpr hν)

theorem mem_of_mem_sup_unitary {A : Subgroup (GL (Fin 3) K)} (hA : A ≤ unitaryIsom3 h)
    (hS : sc K ⊓ unitaryIsom3 h ≤ A) {x : GL (Fin 3) K} (hx : x ∈ A ⊔ sc K)
    (hxU : x ∈ unitaryIsom3 h) : x ∈ A := by
  obtain ⟨a, ha, c, rfl⟩ := mem_sup_sc.mp hx
  have hs : scal c ∈ unitaryIsom3 h := by
    have := mul_mem (inv_mem (hA ha)) hxU
    rwa [inv_mul_cancel_left] at this
  have := hS ⟨scal_mem_sc c, hs⟩
  exact A.mul_mem ha this

end Unitary

section Abelian

variable {p f : ℕ} {K : Type} [Field K]

theorem span_cols_eq_top (g : GL (Fin 3) K) :
    Submodule.span K (Set.range fun i : Fin 3 =>
      ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single i 1 : Fin 3 → K))) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x = (g : Matrix (Fin 3) (Fin 3) K) *ᵥ (((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      *ᵥ x) := by
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  rw [hx]
  set y := ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x
  have : y = ∑ i, y i • (Pi.single i 1 : Fin 3 → K) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [this, mulVec_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [mulVec_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem abelian_case (h : UnitaryFieldData p f K) (h3 : 3 ∣ p ^ f + 1)
    (A : Subgroup (GL (Fin 3) K)) (hA : A ≤ unitaryIsom3 h) (hcube : ∀ x ∈ A, x ^ 3 ∈ sc K)
    (hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hrank : Nat.card (A ⧸ (sc K).subgroupOf A) = 9) :
    ∃ g ∈ unitaryIsom3 h, A.map (MulAut.conj g).toMonoidHom ≤ torusThree K := by
  have := h.finite
  have h3K := three_dvd_card_sub_one h h3
  have hσ := isUnitaryInvolution_invol h
  have hF3 := hF3_of_dvd h h3
  have hS' : sc K ≤ A ⊔ sc K := le_sup_right
  have hcube' := sup_cube hcube
  have hab' := sup_abelian hab
  have hidx' := sup_index hrank
  have hcubes := abelian_cubes h3K (A ⊔ sc K) hS' hcube' hab' hidx'
  obtain ⟨g₀, hg₀⟩ := abelian_torus h3K (A ⊔ sc K) hS' hcube' hab' hidx'
  let 𝒯 : Set (Matrix (Fin 3) (Fin 3) K) := {T | ∃ a ∈ A, T = (a : Matrix (Fin 3) (Fin 3) K)}
  have hiso : ∀ T ∈ 𝒯, conjTr (invol h) T * T = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    exact (mem_unitaryIsom3_iff h).mp (hA ha)
  have hsep : ∀ T ∈ 𝒯, EigSep (invol h) T := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨c, hc⟩ := mem_sc_iff.mp (hcube a ha)
    exact eigSep_of_pow_three hσ hF3 (s := (c : K)) (by
      rw [← Units.val_pow_eq_pow_val, hc, coe_scal])
  have hSe : ∀ w ∈ Set.range (fun i : Fin 3 =>
      (((g₀⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single i 1 : Fin 3 → K))),
      IsEig 𝒯 w := by
    rintro _ ⟨i, rfl⟩ T ⟨a, ha, rfl⟩
    obtain ⟨x, y, z, -, -, hD⟩ := hg₀ ⟨a, Subgroup.mem_sup_left ha, rfl⟩
    have hD'' : g₀ * a * g₀⁻¹ = diagGL K x y z := hD
    have hD' : a * g₀⁻¹ = g₀⁻¹ * diagGL K x y z := by
      calc a * g₀⁻¹ = g₀⁻¹ * (g₀ * a * g₀⁻¹) := by group
        _ = _ := by rw [hD'']
    refine ⟨![(x : K), y, z] i, ?_⟩
    have e1 : (diagGL K x y z : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single i 1 : Fin 3 → K) =
        ![(x : K), y, z] i • (Pi.single i 1 : Fin 3 → K) := by
      ext j
      simp only [diagGL, mulVec_diagonal, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      by_cases hij : j = i
      · subst hij; simp
      · simp [hij]
    rw [mulVec_mulVec, ← Units.val_mul, hD', Units.val_mul, ← mulVec_mulVec, e1, mulVec_smul]
  obtain ⟨M, hMu, hMD⟩ := exists_unitary_eig_matrix hσ hiso hsep (span_cols_eq_top g₀⁻¹) hSe
  let gM : GL (Fin 3) K := ⟨M, conjTr (invol h) M, mul_eq_one_comm.mp hMu, hMu⟩
  have hgM : gM ∈ unitaryIsom3 h := (mem_unitaryIsom3_iff h).mpr hMu
  refine ⟨gM⁻¹, inv_mem hgM, ?_⟩
  rintro _ ⟨x, hxA, rfl⟩
  obtain ⟨c, hc⟩ := hcubes x (Subgroup.mem_sup_left hxA)
  obtain ⟨D, hD⟩ := hMD _ ⟨x, hxA, rfl⟩
  refine mem_torusThree_of_diag_cube (c := c) ?_ ?_
  · intro i j hij
    have e : (((MulAut.conj gM⁻¹).toMonoidHom x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        Matrix.diagonal D := by
      have : (((MulAut.conj gM⁻¹).toMonoidHom x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          conjTr (invol h) M * (x : Matrix (Fin 3) (Fin 3) K) * M := by
        simp [MulAut.conj_apply, gM]
      rw [this, mul_assoc, hD, ← mul_assoc, hMu, one_mul]
    rw [e, diagonal_apply_ne _ hij]
  · rw [← map_pow, hc]
    show gM⁻¹ * scal (c ^ 3) * gM⁻¹⁻¹ = scal (c ^ 3)
    rw [mul_assoc, ← scal_comm (c ^ 3) gM⁻¹⁻¹, mul_inv_cancel_left]

end Abelian

section Heis

variable {p f : ℕ} {K : Type} [Field K]

theorem coe_diagHeis (ω : Kˣ) :
    ((diagGL K 1 ω (ω ^ 2) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![1, (ω : K), (ω : K) ^ 2] := by
  show Matrix.diagonal ![((1 : Kˣ) : K), (ω : K), ((ω ^ 2 : Kˣ) : K)] = _
  simp

theorem coe_monomGL (lam : Kˣ) :
    ((monomGL K lam : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![0, 0, (lam : K); 1, 0, 0; 0, 1, 0] := rfl

theorem diagGL_one_one_one : (diagGL K 1 1 1 : GL (Fin 3) K) = 1 := by
  apply Units.ext
  simp only [diagGL, Units.val_one]
  rw [← Matrix.diagonal_one]
  congr 1
  ext k
  fin_cases k <;> simp

theorem diagHeis_cube {ω : Kˣ} (hω : ω ^ 3 = 1) : (diagGL K 1 ω (ω ^ 2)) ^ 3 = 1 := by
  rw [pow_succ, pow_two, diagGL_mul, diagGL_mul]
  have e1 : ω * ω * ω = 1 := by
    have := hω
    rw [pow_succ, pow_two] at this
    exact this
  have e2 : ω ^ 2 * ω ^ 2 * ω ^ 2 = 1 := by
    calc ω ^ 2 * ω ^ 2 * ω ^ 2 = (ω ^ 3) ^ 2 := by group
      _ = 1 := by rw [hω, one_pow]
  rw [e1, e2, one_mul, one_mul]
  exact diagGL_one_one_one

theorem monom_cube (lam : Kˣ) : (monomGL K lam) ^ 3 = scal lam := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_monomGL, coe_scal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

theorem diag_monom (lam ω : Kˣ) (hω : ω ^ 3 = 1) :
    diagGL K 1 ω (ω ^ 2) * monomGL K lam = scal ω * (monomGL K lam * diagGL K 1 ω (ω ^ 2)) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_scal, coe_diagHeis, coe_monomGL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_mul, Matrix.vecMul_diagonal, Matrix.scalar_apply]
  all_goals first
    | (have h3 : (ω : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hω, Units.val_one]
       linear_combination (-(lam : K)) * h3)
    | ring

theorem diagHeis_fix (ω : Kˣ) :
    (diagGL K 1 ω (ω ^ 2) : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single 0 1 : Fin 3 → K) =
      Pi.single 0 1 := by
  rw [coe_diagHeis]
  ext j
  fin_cases j <;> simp [Matrix.mulVec_diagonal]

theorem conj_scal (g : GL (Fin 3) K) (c : Kˣ) : g * scal c * g⁻¹ = scal c := by
  rw [scal_comm c g, mul_inv_cancel_right]

end Heis

end CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.RankTwoGU

