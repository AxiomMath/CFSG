module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OutI

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix QuadraticAlgebra
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSp4

theorem kaICyc_cyc_of_inj_normOne {F : Type} [Field F] (h2 : (2 : F) ≠ 0) {a : F} (ha : a ≠ 0)
    {G : Type} [Group G] [Finite G] (ν : G →* QuadraticAlgebra F a 0)
    (hν : Function.Injective ν) (hn : ∀ g, star (ν g) * ν g = 1) : IsCyclic G := by
  by_cases hsq : IsSquare a
  · obtain ⟨r, hr⟩ := hsq
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact ha (by simpa using hr)
    let φ : QuadraticAlgebra F a 0 →ₐ[F] F :=
      QuadraticAlgebra.lift ⟨r, by simp [hr]⟩
    refine isCyclic_of_injective_ringHom
      (((φ : QuadraticAlgebra F a 0 →+* F) : QuadraticAlgebra F a 0 →* F).comp ν) ?_
    rw [injective_iff_map_eq_one]
    intro g hg
    have h1 : (ν g).re + (ν g).im * r = 1 := by
      simpa [φ, MonoidHom.comp_apply, QuadraticAlgebra.lift_apply_apply] using hg
    have h3 := congrArg QuadraticAlgebra.re (hn g)
    simp at h3
    have hv : 2 * r * (ν g).im = 0 := by
      linear_combination (1 + ((ν g).re - (ν g).im * r)) * h1 - h3 - (ν g).im ^ 2 * hr
    have hv0 : (ν g).im = 0 :=
      (mul_eq_zero.mp hv).resolve_left (mul_ne_zero h2 hr0)
    have hu : (ν g).re = 1 := by
      rw [hv0] at h1
      simpa using h1
    apply hν
    rw [map_one]
    exact QuadraticAlgebra.ext (by simpa using hu) (by simpa using hv0)
  · have : Fact (¬ IsSquare a) := ⟨hsq⟩
    exact isCyclic_of_injective_ringHom ν hν

theorem kaICyc_eq_zero_of_neg_comm_t {R : Type} [CommRing R] (h2 : IsUnit (2 : R))
    {Z : Matrix (Fin 2) (Fin 2) R}
    (ht : Z * !![1, 1; 0, 1] = -(!![1, 1; 0, 1] * Z)) : Z = 0 := by
  have e00 := congrFun (congrFun ht 0) 0
  have e01 := congrFun (congrFun ht 0) 1
  have e10 := congrFun (congrFun ht 1) 0
  have e11 := congrFun (congrFun ht 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.cons_val_one] at e00 e01 e10 e11
  have h10 : Z 1 0 = 0 := h2.mul_right_eq_zero.mp (by linear_combination e10)
  have h00 : Z 0 0 = 0 := h2.mul_right_eq_zero.mp (by linear_combination e00 - h10)
  have h11 : Z 1 1 = 0 := h2.mul_right_eq_zero.mp (by linear_combination e11 - h10)
  have h01 : Z 0 1 = 0 :=
    h2.mul_right_eq_zero.mp (by linear_combination e01 - h00 - h11)
  ext i j
  fin_cases i <;> fin_cases j <;> simpa

theorem kaICyc_eq_zero_of_neg_comm_s {R : Type} [CommRing R] (h2 : IsUnit (2 : R))
    {Z : Matrix (Fin 2) (Fin 2) R}
    (hs : Z * !![1, 0; 1, 1] = -(!![1, 0; 1, 1] * Z)) : Z = 0 := by
  have e00 := congrFun (congrFun hs 0) 0
  have e01 := congrFun (congrFun hs 0) 1
  have e10 := congrFun (congrFun hs 1) 0
  have e11 := congrFun (congrFun hs 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.cons_val_one] at e00 e01 e10 e11
  have h01 : Z 0 1 = 0 := h2.mul_right_eq_zero.mp (by linear_combination e01)
  have h00 : Z 0 0 = 0 := h2.mul_right_eq_zero.mp (by linear_combination e00 - h01)
  have h11 : Z 1 1 = 0 := h2.mul_right_eq_zero.mp (by linear_combination e11 - h01)
  have h10 : Z 1 0 = 0 :=
    h2.mul_right_eq_zero.mp (by linear_combination e10 - h11 - h00)
  ext i j
  fin_cases i <;> fin_cases j <;> simpa

theorem kaICyc_scalar_of_comm_transvections {R : Type} [CommRing R] (h2 : IsUnit (2 : R))
    {Z : Matrix (Fin 2) (Fin 2) R} (hZ : Z ≠ 0)
    (ht : Z * !![1, 1; 0, 1] = !![1, 1; 0, 1] * Z ∨
      Z * !![1, 1; 0, 1] = -(!![1, 1; 0, 1] * Z))
    (hs : Z * !![1, 0; 1, 1] = !![1, 0; 1, 1] * Z ∨
      Z * !![1, 0; 1, 1] = -(!![1, 0; 1, 1] * Z)) :
    Z 0 1 = 0 ∧ Z 1 0 = 0 ∧ Z 1 1 = Z 0 0 := by
  rcases ht with ht | ht
  · rcases hs with hs | hs
    · have t00 := congrFun (congrFun ht 0) 0
      have t01 := congrFun (congrFun ht 0) 1
      have s00 := congrFun (congrFun hs 0) 0
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
        Matrix.cons_val_one] at t00 t01 s00
      exact ⟨by linear_combination s00, by linear_combination -t00,
        by linear_combination -t01⟩
    · exact absurd (kaICyc_eq_zero_of_neg_comm_s h2 hs) hZ
  · exact absurd (kaICyc_eq_zero_of_neg_comm_t h2 ht) hZ

section Blocks

variable {F : Type} [Field F] {a : F}

theorem kaICyc_qBlock_neg (Z : Matrix (Fin 2) (Fin 2) (QuadraticAlgebra F a 0)) :
    qBlock a (-Z) = -qBlock a Z := by
  simp [qBlock, Matrix.fromBlocks_neg]

theorem kaICyc_bAinv_gI_bA (ha : a ≠ 0) (k : Matrix.SpecialLinearGroup (Fin 2) F) :
    bAinv a * (((gI ha k : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * bA a =
        kron (k : Matrix (Fin 2) (Fin 2) F) 1 := by
  rw [coe_gI]
  simp only [Matrix.mul_assoc]
  rw [bAinv_mul_bA ha, Matrix.mul_one, ← Matrix.mul_assoc, bAinv_mul_bA ha, Matrix.one_mul]

theorem kaICyc_bAinv_conj_mul (ha : a ≠ 0) (M N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) :
    bAinv a * M * bA a * (bAinv a * N * bA a) = bAinv a * (M * N) * bA a := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (bA a) (bAinv a), bA_mul_bAinv ha, Matrix.one_mul]

theorem kaICyc_blocksI_injective (ha : a ≠ 0) {g h : fixI a ha}
    (e : blocksI ha g = blocksI ha h) : g = h := by
  have h1 := qBlock_blocksI ha g
  have h2 := qBlock_blocksI ha h
  rw [e, h2] at h1
  have h3 : bA a * (bAinv a * ((h : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) * bA a) * bAinv a =
      bA a * (bAinv a * ((g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) * bA a) * bAinv a := by
    rw [h1]
  have h4 : ∀ M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F,
      bA a * (bAinv a * M * bA a) * bAinv a = M := fun M => by
    simp only [Matrix.mul_assoc, bA_mul_bAinv ha, Matrix.mul_one]
    rw [← Matrix.mul_assoc, bA_mul_bAinv ha, Matrix.one_mul]
  rw [h4, h4] at h3
  exact Subtype.ext (sp_ext h3.symm)

theorem kaICyc_blocksI_comm (ha : a ≠ 0) (g : fixI a ha) (k : Matrix.SpecialLinearGroup (Fin 2) F)
    (h : proj 2 F (g : StatedSp 2 F) * proj 2 F (gI ha k) =
      proj 2 F (gI ha k) * proj 2 F (g : StatedSp 2 F)) :
    blocksI ha g * (k : Matrix (Fin 2) (Fin 2) F).map (algebraMap F (QuadraticAlgebra F a 0)) =
        (k : Matrix (Fin 2) (Fin 2) F).map (algebraMap F (QuadraticAlgebra F a 0)) *
          blocksI ha g ∨
      blocksI ha g * (k : Matrix (Fin 2) (Fin 2) F).map (algebraMap F (QuadraticAlgebra F a 0)) =
        -((k : Matrix (Fin 2) (Fin 2) F).map (algebraMap F (QuadraticAlgebra F a 0)) *
          blocksI ha g) := by
  rw [← map_mul, ← map_mul] at h
  have hk := kaICyc_bAinv_gI_bA ha k
  have hg := qBlock_blocksI ha g
  rcases eq_or_eq_neg_of_proj_eq h with e | e
  · left
    apply qBlock_injective a
    rw [qBlock_mul, qBlock_mul, qBlock_map, hg, ← hk, kaICyc_bAinv_conj_mul ha,
      kaICyc_bAinv_conj_mul ha]
    simp only [Subgroup.coe_mul, Units.val_mul] at e
    rw [e]
  · right
    apply qBlock_injective a
    rw [qBlock_mul, kaICyc_qBlock_neg, qBlock_mul, qBlock_map, hg, ← hk, kaICyc_bAinv_conj_mul ha,
      kaICyc_bAinv_conj_mul ha]
    simp only [Subgroup.coe_mul, Units.val_mul] at e
    rw [e, Matrix.mul_neg, Matrix.neg_mul, neg_neg]

theorem kaICyc_blocksI_scalar (h2 : (2 : F) ≠ 0) (ha : a ≠ 0) (g : fixI a ha)
    (hc : ∀ l ∈ JI ha, proj 2 F (g : StatedSp 2 F) * l = l * proj 2 F (g : StatedSp 2 F)) :
    blocksI ha g 0 1 = 0 ∧ blocksI ha g 1 0 = 0 ∧ blocksI ha g 1 1 = blocksI ha g 0 0 := by
  have h2E : IsUnit (2 : QuadraticAlgebra F a 0) := by
    have := (isUnit_iff_ne_zero.mpr h2 : IsUnit (2 : F)).map
      (algebraMap F (QuadraticAlgebra F a 0))
    rwa [map_ofNat] at this
  have hZ : blocksI ha g ≠ 0 := by
    intro h0
    have h1 : blocksI ha g * blocksI ha g⁻¹ = 1 := by
      rw [← blocksI_mul, mul_inv_cancel, blocksI_one]
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  let t : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  let s : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  have ht := kaICyc_blocksI_comm ha g t (hc _ ⟨gI ha t, ⟨t, rfl⟩, rfl⟩)
  have hs := kaICyc_blocksI_comm ha g s (hc _ ⟨gI ha s, ⟨s, rfl⟩, rfl⟩)
  have et : (t : Matrix (Fin 2) (Fin 2) F).map (algebraMap F (QuadraticAlgebra F a 0)) =
      !![1, 1; 0, 1] := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [t]
  have es : (s : Matrix (Fin 2) (Fin 2) F).map (algebraMap F (QuadraticAlgebra F a 0)) =
      !![1, 0; 1, 1] := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [s]
  rw [et] at ht
  rw [es] at hs
  exact kaICyc_scalar_of_comm_transvections h2E hZ ht hs

theorem kaICyc_blocksI_norm (ha : a ≠ 0) (g : fixI a ha) (h01 : blocksI ha g 0 1 = 0)
    (h10 : blocksI ha g 1 0 = 0) (h11 : blocksI ha g 1 1 = blocksI ha g 0 0) :
    star (blocksI ha g 0 0) * blocksI ha g 0 0 = 1 := by
  have hsym : (blocksI ha g)ᴴ * jE a * blocksI ha g = jE a := by
    rw [← qBlock_symplectic_iff ha, qBlock_blocksI]
    exact bAinv_conj_twisted ha g
  have e := congrFun (congrFun hsym 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, jE, Matrix.conjTranspose_apply, h01, h10, h11] at e
  exact e

theorem kaICyc_exists_hom (h2 : (2 : F) ≠ 0) (ha : a ≠ 0)
    (X : Subgroup (StatedProj (StatedSp 2 F)))
    (hXc : ∀ x ∈ X, ∀ l ∈ JI ha, x * l = l * x) :
    ∃ ν : (X.comap ((proj 2 F).comp (fixI a ha).subtype)) →* QuadraticAlgebra F a 0,
      Function.Injective ν ∧ ∀ g, star (ν g) * ν g = 1 := by
  have hsc : ∀ g : X.comap ((proj 2 F).comp (fixI a ha).subtype),
      blocksI ha g.1 0 1 = 0 ∧ blocksI ha g.1 1 0 = 0 ∧
        blocksI ha g.1 1 1 = blocksI ha g.1 0 0 := fun g =>
    kaICyc_blocksI_scalar h2 ha g.1 (fun l hl => hXc _ g.2 l hl)
  have hnorm : ∀ g : X.comap ((proj 2 F).comp (fixI a ha).subtype),
      star (blocksI ha g.1 0 0) * blocksI ha g.1 0 0 = 1 := fun g =>
    kaICyc_blocksI_norm ha g.1 (hsc g).1 (hsc g).2.1 (hsc g).2.2
  have hone : ∀ g : X.comap ((proj 2 F).comp (fixI a ha).subtype),
      blocksI ha g.1 0 0 = 1 → g = 1 := by
    intro g hg
    obtain ⟨h01, h10, h11⟩ := hsc g
    have : blocksI ha g.1 = blocksI ha 1 := by
      rw [blocksI_one]
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp [h01, h10, h11, hg]
    exact Subtype.ext ((kaICyc_blocksI_injective ha this).trans (Subgroup.coe_one _).symm)
  refine ⟨{ toFun := fun g => blocksI ha g.1 0 0
            map_one' := ?_
            map_mul' := ?_ }, ?_, hnorm⟩
  · show blocksI ha (1 : fixI a ha) 0 0 = 1
    rw [blocksI_one]
    simp
  · intro g h
    show blocksI ha (g.1 * h.1) 0 0 = blocksI ha g.1 0 0 * blocksI ha h.1 0 0
    rw [blocksI_mul, Matrix.mul_apply, Fin.sum_univ_two, (hsc g).1, zero_mul, add_zero]
  · rw [injective_iff_map_eq_one]
    exact hone

end Blocks

theorem kaSp4I_cyc {F : Type} [Field F] [Finite F] (hodd : ringChar F ≠ 2) {a : F} (ha : a ≠ 0)
    (X : Subgroup (StatedProj (StatedSp 2 F))) (hXle : X ≤ (fixI a ha).map (proj 2 F))
    (hXc : ∀ x ∈ X, ∀ l ∈ JI ha, x * l = l * x) : IsCyclic ↥X := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hodd
  obtain ⟨ν, hν, hn⟩ := kaICyc_exists_hom h2 ha X hXc
  have hG := kaICyc_cyc_of_inj_normOne h2 ha ν hν hn
  let ψ : ↥(X.comap ((proj 2 F).comp (fixI a ha).subtype)) →* ↥X :=
    (((proj 2 F).comp (fixI a ha).subtype).comp
      (X.comap ((proj 2 F).comp (fixI a ha).subtype)).subtype).codRestrict X (fun g => g.2)
  have hψ : Function.Surjective ψ := by
    rintro ⟨x, hx⟩
    obtain ⟨s, hs, rfl⟩ := hXle hx
    exact ⟨⟨⟨s, hs⟩, hx⟩, rfl⟩
  exact isCyclic_of_surjective ψ hψ

theorem kaSp4I_hcyc {F : Type} [Field F] [Finite F] (hodd : ringChar F ≠ 2)
    (_h5 : 5 ≤ Nat.card F) {a : F} (ha : a ≠ 0) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ X : Subgroup (StatedProj (StatedSp 2 F)), IsPGroup p ↥X →
      X ≤ (fixI a ha).map (proj 2 F) → (∀ x ∈ X, ∀ l ∈ JI ha, x * l = l * x) →
        IsCyclic ↥X :=
  fun _ _ _ X _ hXle hXc => kaSp4I_cyc hodd ha X hXle hXc

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
