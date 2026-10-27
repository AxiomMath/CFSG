module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL5Out
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAProjFix

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped MatrixGroups commutatorElement

section Defs

variable (F : Type) [Field F]

@[expose] def kaL5B4Mat : Matrix (Fin 5) (Fin 5) F :=
  Matrix.diagonal fun i : Fin 5 => if (i : ℕ) < 4 then (1 : F) else -1

theorem kaL5B4Mat_mul_self : kaL5B4Mat F * kaL5B4Mat F = 1 := by
  rw [kaL5B4Mat, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs <;> simp

@[expose] def kaL5B4GL : GL (Fin 5) F :=
  ⟨kaL5B4Mat F, kaL5B4Mat F, kaL5B4Mat_mul_self F, kaL5B4Mat_mul_self F⟩

theorem coe_kaL5B4GL : ((kaL5B4GL F : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) = kaL5B4Mat F :=
  rfl

theorem kaL5B4GL_mul_self : kaL5B4GL F * kaL5B4GL F = 1 :=
  Units.ext (by rw [Units.val_mul, coe_kaL5B4GL, kaL5B4Mat_mul_self, Units.val_one])

theorem kaL5B4GL_inv : (kaL5B4GL F)⁻¹ = kaL5B4GL F :=
  inv_eq_of_mul_eq_one_right (kaL5B4GL_mul_self F)

@[expose] def kaL5B4E : Fin 5 → F := Pi.single 4 1

theorem kaL5B4E_apply (i : Fin 5) : kaL5B4E F i = if i = 4 then 1 else 0 := by
  simp [kaL5B4E, Pi.single_apply]

end Defs

section Frame

variable {F : Type} [Field F]

theorem kaL5B4_exists_frame (hK : ringChar F ≠ 2) {B : GL (Fin 5) F} (hB : B * B = 1)
    (h4 : Module.finrank F (LinearMap.ker (toLin' B.val - 1)) = 4) :
    ∃ P : GL (Fin 5) F, B = P * kaL5B4GL F * P⁻¹ := by
  have hBm : (B : Matrix (Fin 5) (Fin 5) F) * B = 1 := by
    rw [← Units.val_mul, hB, Units.val_one]
  obtain ⟨b, hb⟩ := exists_eigenbasis hK hBm
  obtain ⟨P, D, hPD, hD⟩ := exists_gl_inv_mul_mul_eq_toMatrix b B
  have hDd : (D : Matrix (Fin 5) (Fin 5) F) = kaL5B4Mat F := by
    rw [hD, kaL5B4Mat]
    ext a c
    rw [LinearMap.toMatrix_apply, toLin'_apply, hb c, h4, map_smul, Module.Basis.repr_self,
      Finsupp.smul_apply, Finsupp.single_apply, diagonal_apply]
    by_cases hac : a = c
    · subst hac
      simp
    · simp [hac, Ne.symm hac]
  refine ⟨P, ?_⟩
  have hDe : D = kaL5B4GL F := Units.ext hDd
  rw [← hDe, ← hPD]
  group

end Frame

section Vec

variable {F : Type} [Field F]

@[expose] def kaL5B4Has (M : Matrix (Fin 5) (Fin 5) F) (z : F) : Prop :=
  M *ᵥ kaL5B4E F = z • kaL5B4E F ∧ kaL5B4E F ᵥ* M = z • kaL5B4E F

theorem kaL5B4Has_mul {M N : Matrix (Fin 5) (Fin 5) F} {z w : F} (hM : kaL5B4Has M z)
    (hN : kaL5B4Has N w) : kaL5B4Has (M * N) (z * w) := by
  refine ⟨?_, ?_⟩
  · rw [← Matrix.mulVec_mulVec, hN.1, Matrix.mulVec_smul, hM.1, smul_smul, mul_comm]
  · rw [← Matrix.vecMul_vecMul, hM.2, Matrix.smul_vecMul, hN.2, smul_smul]

theorem kaL5B4Has_inv {M N : Matrix (Fin 5) (Fin 5) F} {z : F} (h1 : M * N = 1) (h2 : N * M = 1)
    (hM : kaL5B4Has M z) : z ≠ 0 ∧ kaL5B4Has N z⁻¹ := by
  have hrow : kaL5B4E F = z • (kaL5B4E F ᵥ* N) := by
    calc kaL5B4E F = kaL5B4E F ᵥ* (M * N) := by rw [h1, Matrix.vecMul_one]
      _ = (kaL5B4E F ᵥ* M) ᵥ* N := (Matrix.vecMul_vecMul _ _ _).symm
      _ = z • (kaL5B4E F ᵥ* N) := by rw [hM.2, Matrix.smul_vecMul]
  have hcol : kaL5B4E F = z • (N *ᵥ kaL5B4E F) := by
    calc kaL5B4E F = (N * M) *ᵥ kaL5B4E F := by rw [h2, Matrix.one_mulVec]
      _ = N *ᵥ (M *ᵥ kaL5B4E F) := (Matrix.mulVec_mulVec _ _ _).symm
      _ = z • (N *ᵥ kaL5B4E F) := by rw [hM.1, Matrix.mulVec_smul]
  have hz : z ≠ 0 := by
    rintro rfl
    have := congrFun hrow 4
    simp [kaL5B4E_apply] at this
  refine ⟨hz, ?_, ?_⟩
  · calc N *ᵥ kaL5B4E F = z⁻¹ • (z • (N *ᵥ kaL5B4E F)) := by
          rw [smul_smul, inv_mul_cancel₀ hz, one_smul]
      _ = z⁻¹ • kaL5B4E F := by rw [← hcol]
  · calc kaL5B4E F ᵥ* N = z⁻¹ • (z • (kaL5B4E F ᵥ* N)) := by
          rw [smul_smul, inv_mul_cancel₀ hz, one_smul]
      _ = z⁻¹ • kaL5B4E F := by rw [← hrow]

theorem kaL5B4Has_inv_sl {g : SL(5, F)} {z : F}
    (hg : kaL5B4Has (g : Matrix (Fin 5) (Fin 5) F) z) :
    z ≠ 0 ∧ kaL5B4Has ((g⁻¹ : SL(5, F)) : Matrix (Fin 5) (Fin 5) F) z⁻¹ := by
  refine kaL5B4Has_inv (M := (g : Matrix (Fin 5) (Fin 5) F)) ?_ ?_ hg
  · rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  · rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem kaL5B4_entries (h2 : (2 : F) ≠ 0) {c : Matrix (Fin 5) (Fin 5) F}
    (hc : c * kaL5B4Mat F = kaL5B4Mat F * c) :
    (∀ i : Fin 5, i ≠ 4 → c i 4 = 0) ∧ (∀ j : Fin 5, j ≠ 4 → c 4 j = 0) := by
  have key : ∀ x : F, -x = x → x = 0 := fun x hx => by
    have : (2 : F) * x = 0 := by linear_combination -hx
    exact (mul_eq_zero.1 this).resolve_left h2
  constructor
  · intro i hi
    have h := congrFun (congrFun hc i) 4
    rw [kaL5B4Mat, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    fin_cases i
    · exact key _ (by simpa using h)
    · exact key _ (by simpa using h)
    · exact key _ (by simpa using h)
    · exact key _ (by simpa using h)
    · exact absurd rfl hi
  · intro j hj
    have h := congrFun (congrFun hc 4) j
    rw [kaL5B4Mat, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    fin_cases j
    · exact key _ (by simpa using h.symm)
    · exact key _ (by simpa using h.symm)
    · exact key _ (by simpa using h.symm)
    · exact key _ (by simpa using h.symm)
    · exact absurd rfl hj

theorem kaL5B4_has_of_comm (h2 : (2 : F) ≠ 0) {c : Matrix (Fin 5) (Fin 5) F}
    (hc : c * kaL5B4Mat F = kaL5B4Mat F * c) : kaL5B4Has c (c 4 4) := by
  obtain ⟨hcol, hrow⟩ := kaL5B4_entries h2 hc
  refine ⟨?_, ?_⟩
  · funext i
    simp only [Matrix.mulVec, dotProduct, kaL5B4E_apply, Pi.smul_apply, smul_eq_mul]
    simp
    by_cases hi : i = 4
    · subst hi
      simp
    · rw [hcol i hi]
      simp [hi]
  · funext j
    simp only [Matrix.vecMul, dotProduct, kaL5B4E_apply, Pi.smul_apply, smul_eq_mul]
    simp
    by_cases hj : j = 4
    · subst hj
      simp
    · rw [hrow j hj]
      simp [hj]

end Vec

section Block

variable {F : Type} [Field F]

@[expose] def kaL5B4Blk (A : Matrix (Fin 4) (Fin 4) F) : Matrix (Fin 5) (Fin 5) F :=
  !![A 0 0, A 0 1, A 0 2, A 0 3, 0;
    A 1 0, A 1 1, A 1 2, A 1 3, 0;
    A 2 0, A 2 1, A 2 2, A 2 3, 0;
    A 3 0, A 3 1, A 3 2, A 3 3, 0;
    0, 0, 0, 0, 1]

theorem kaL5B4Blk_mul (A B : Matrix (Fin 4) (Fin 4) F) :
    kaL5B4Blk (A * B) = kaL5B4Blk A * kaL5B4Blk B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kaL5B4Blk, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_five]

theorem kaL5B4Blk_one : kaL5B4Blk (1 : Matrix (Fin 4) (Fin 4) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kaL5B4Blk]

theorem det_kaL5B4Blk (A : Matrix (Fin 4) (Fin 4) F) : (kaL5B4Blk A).det = A.det := by
  rw [Matrix.det_succ_column _ (Fin.last 4), Fin.sum_univ_castSucc]
  have h1 : ∀ i : Fin 4, kaL5B4Blk A i.castSucc (Fin.last 4) = 0 := by
    intro i
    fin_cases i <;> simp [kaL5B4Blk]
  have h2 : (kaL5B4Blk A).submatrix (Fin.last 4).succAbove (Fin.last 4).succAbove = A := by
    ext i j
    rw [Fin.succAbove_last]
    fin_cases i <;> fin_cases j <;> simp [kaL5B4Blk]
  simp only [h1, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, Fin.succAbove_last]
  rw [Fin.succAbove_last] at h2
  rw [h2]
  norm_num [kaL5B4Blk]

@[expose] def kaL5B4Sl (A : SL(4, F)) : SL(5, F) :=
  ⟨kaL5B4Blk (A : Matrix (Fin 4) (Fin 4) F), by rw [det_kaL5B4Blk, A.2]⟩

theorem coe_kaL5B4Sl (A : SL(4, F)) :
    ((kaL5B4Sl A : SL(5, F)) : Matrix (Fin 5) (Fin 5) F) =
      kaL5B4Blk (A : Matrix (Fin 4) (Fin 4) F) :=
  rfl

@[expose] def kaL5B4Hom : SL(4, F) →* SL(5, F) where
  toFun := kaL5B4Sl
  map_one' := by
    apply Subtype.ext
    rw [coe_kaL5B4Sl]
    exact kaL5B4Blk_one
  map_mul' A B := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_kaL5B4Sl, coe_kaL5B4Sl, coe_kaL5B4Sl,
      Matrix.SpecialLinearGroup.coe_mul]
    exact kaL5B4Blk_mul _ _

theorem coe_kaL5B4Hom (A : SL(4, F)) :
    ((kaL5B4Hom A : SL(5, F)) : Matrix (Fin 5) (Fin 5) F) =
      kaL5B4Blk (A : Matrix (Fin 4) (Fin 4) F) :=
  rfl

@[expose] def kaL5B4Phi (F : Type) [Field F] : SL(4, F) →* projectiveSL 5 F :=
  (proj 5 F).comp kaL5B4Hom

theorem kaL5B4Blk_col (A : Matrix (Fin 4) (Fin 4) F) (i : Fin 5) :
    kaL5B4Blk A i 4 = if i = 4 then 1 else 0 := by
  fin_cases i <;> simp [kaL5B4Blk]

theorem kaL5B4Blk_row (A : Matrix (Fin 4) (Fin 4) F) (j : Fin 5) :
    kaL5B4Blk A 4 j = if j = 4 then 1 else 0 := by
  fin_cases j <;> simp [kaL5B4Blk]

theorem kaL5B4Has_blk (A : Matrix (Fin 4) (Fin 4) F) : kaL5B4Has (kaL5B4Blk A) 1 := by
  refine ⟨?_, ?_⟩
  · funext i
    simp [Matrix.mulVec, dotProduct, kaL5B4E_apply, kaL5B4Blk_col]
  · funext j
    simp [Matrix.vecMul, dotProduct, kaL5B4E_apply, kaL5B4Blk_row]

theorem kaL5B4_exists_blk {k : SL(5, F)} (h : kaL5B4Has (k : Matrix (Fin 5) (Fin 5) F) 1) :
    ∃ A : SL(4, F), kaL5B4Hom A = k := by
  have hcol : ∀ i : Fin 5, (k : Matrix (Fin 5) (Fin 5) F) i 4 = if i = 4 then 1 else 0 := by
    intro i
    have := congrFun h.1 i
    simpa [Matrix.mulVec, dotProduct, kaL5B4E_apply] using this
  have hrow : ∀ j : Fin 5, (k : Matrix (Fin 5) (Fin 5) F) 4 j = if j = 4 then 1 else 0 := by
    intro j
    have := congrFun h.2 j
    simpa [Matrix.vecMul, dotProduct, kaL5B4E_apply] using this
  set A : Matrix (Fin 4) (Fin 4) F :=
    Matrix.of fun i j => (k : Matrix (Fin 5) (Fin 5) F) i.castSucc j.castSucc with hA
  have hk : (k : Matrix (Fin 5) (Fin 5) F) = kaL5B4Blk A := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [kaL5B4Blk, hA, hcol, hrow]
  have hdet : A.det = 1 := by
    rw [← det_kaL5B4Blk, ← hk]
    exact k.2
  exact ⟨(⟨A, hdet⟩ : SL(4, F)), Subtype.ext hk.symm⟩

theorem kaL5B4_blk_comm (A : Matrix (Fin 4) (Fin 4) F) :
    kaL5B4Blk A * kaL5B4Mat F = kaL5B4Mat F * kaL5B4Blk A := by
  rw [kaL5B4Mat]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [kaL5B4Blk]

end Block

section Struct

variable {F : Type} [Field F]

theorem kaL5B4_mem_cent {g : SL(5, F)} :
    g ∈ kaSlCent5 (kaL5B4GL F) ↔
      (g : Matrix (Fin 5) (Fin 5) F) * kaL5B4Mat F = kaL5B4Mat F * g := by
  rw [kaSlCent5, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    have h1 := congrArg (fun u : GL (Fin 5) F => (u : Matrix (Fin 5) (Fin 5) F))
      (h (kaL5B4GL F) (Set.mem_singleton _))
    simp only [Units.val_mul, coe_kaL5B4GL, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at h1
    exact h1.symm
  · intro h x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    apply Units.ext
    simp only [Units.val_mul, coe_kaL5B4GL, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    exact h.symm

theorem kaL5B4_blk_mem_cent (A : SL(4, F)) : kaL5B4Hom A ∈ kaSlCent5 (kaL5B4GL F) := by
  rw [kaL5B4_mem_cent, coe_kaL5B4Hom]
  exact kaL5B4_blk_comm _

theorem kaL5B4_range_le_map :
    (kaL5B4Phi F).range ≤ (kaSlCent5 (kaL5B4GL F)).map (proj 5 F) := by
  rintro _ ⟨A, rfl⟩
  exact ⟨kaL5B4Hom A, kaL5B4_blk_mem_cent A, rfl⟩

theorem kaL5B4_map_le_fix {x : projectiveSL 5 F}
    (hx : x ∈ (kaSlCent5 (kaL5B4GL F)).map (proj 5 F)) : conjAut 5 F (kaL5B4GL F) x = x := by
  obtain ⟨g, hg, rfl⟩ := hx
  have hc := kaL5B4_mem_cent.1 hg
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, kaL5B4GL_inv, coe_kaL5B4GL, ← hc, Matrix.mul_assoc,
    kaL5B4Mat_mul_self, Matrix.mul_one]

theorem kaL5B4_conj_mem_range (h2 : (2 : F) ≠ 0) {c : SL(5, F)}
    (hc : c ∈ kaSlCent5 (kaL5B4GL F)) (A : SL(4, F)) :
    ∃ A' : SL(4, F), kaL5B4Hom A' = c * kaL5B4Hom A * c⁻¹ := by
  apply kaL5B4_exists_blk
  have h1 := kaL5B4_has_of_comm h2 (kaL5B4_mem_cent.1 hc)
  obtain ⟨hz, hinv⟩ := kaL5B4Has_inv_sl h1
  have h3 := kaL5B4Has_mul (kaL5B4Has_mul h1 (kaL5B4Has_blk (A : Matrix (Fin 4) (Fin 4) F)))
    hinv
  rw [mul_one, mul_inv_cancel₀ hz] at h3
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_kaL5B4Hom]
  exact h3

theorem kaL5B4_normalizes (h2 : (2 : F) ≠ 0) :
    ∀ x ∈ (kaSlCent5 (kaL5B4GL F)).map (proj 5 F),
      x ∈ normalizer ((kaL5B4Phi F).range : Set (projectiveSL 5 F)) := by
  have key : ∀ x ∈ (kaSlCent5 (kaL5B4GL F)).map (proj 5 F), ∀ l ∈ (kaL5B4Phi F).range,
      x * l * x⁻¹ ∈ (kaL5B4Phi F).range := by
    rintro _ ⟨c, hc, rfl⟩ _ ⟨A, rfl⟩
    obtain ⟨A', hA'⟩ := kaL5B4_conj_mem_range h2 hc A
    refine ⟨A', ?_⟩
    change proj 5 F (kaL5B4Hom A') = _
    rw [hA', map_mul, map_mul, map_inv]
    rfl
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro l
  constructor
  · exact fun hl => key x hx l hl
  · intro hl
    have := key x⁻¹ (inv_mem hx) _ hl
    simpa [mul_assoc] using this

theorem kaL5B4_perfect : ⁅(kaL5B4Phi F).range, (kaL5B4Phi F).range⁆ = (kaL5B4Phi F).range := by
  have hP : Group.IsPerfect SL(4, F) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by norm_num)
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def,
    Group.isPerfect_def.mp hP]

theorem kaL5B4_quasisimple : CFSG.IsQuasisimple SL(4, F) := by
  have hperf : Group.IsPerfect SL(4, F) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by norm_num)
  obtain ⟨-, hsimple, -⟩ :=
    CFSG.LinearGroups.linear_projective_simple (K := F) (n := 4) (by omega)
      (Or.inl (by norm_num))
  refine ⟨hperf, hsimple, ?_⟩
  by_contra h
  push Not at h
  have : IsMulCommutative (SL(4, F) ⧸ Subgroup.center SL(4, F)) := ⟨⟨h⟩⟩
  exact Group.IsPerfect.not_isMulCommutative (SL(4, F) ⧸ Subgroup.center SL(4, F)) this

theorem kaL5B4_hLp [Finite F] :
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ M : Subgroup (projectiveSL 5 F), M ≤ (kaL5B4Phi F).range →
      IsPGroup p ↥M → (∀ l ∈ (kaL5B4Phi F).range, l ∈ normalizer (M : Set (projectiveSL 5 F))) →
        ∀ m ∈ M, ∀ l ∈ (kaL5B4Phi F).range, m * l = l * m :=
  fun _ hp _ M hML hMp hMn =>
    ka_central_of_quasisimple_image (kaL5B4Phi F) kaL5B4_quasisimple hp M hML hMp hMn

end Struct

section Fix

variable {F : Type} [Field F]

theorem kaL5B4_fix_scalar {n : ℕ} (A : GL (Fin n) F) (g : SL(n, F))
    (h : conjAut n F A (proj n F g) = proj n F g) :
    ∃ μ : F, (g : Matrix (Fin n) (Fin n) F) =
      μ • (A.val * (g : Matrix (Fin n) (Fin n) F) * A⁻¹.val) := by
  rw [conjAut_proj, proj_eq_proj_iff] at h
  obtain ⟨c, -, hc⟩ := mem_scalars.1 h
  refine ⟨(c : F), ?_⟩
  set S := ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F A g with hS
  have hSmat : (S : Matrix (Fin n) (Fin n) F) =
      A.val * (g : Matrix (Fin n) (Fin n) F) * A⁻¹.val := by
    rw [hS, coe_slConjugation]
  have hscal : (Matrix.scalar (Fin n) (c : F) : Matrix (Fin n) (Fin n) F) = (c : F) • 1 := by
    rw [smul_one_eq_diagonal, Matrix.scalar_apply]
  calc (g : Matrix (Fin n) (Fin n) F) = ((S * (S⁻¹ * g) : SL(n, F)) : Matrix (Fin n) (Fin n) F) :=
        congrArg Subtype.val (mul_inv_cancel_left S g).symm
    _ = (S : Matrix (Fin n) (Fin n) F) * ((S⁻¹ * g : SL(n, F)) : Matrix (Fin n) (Fin n) F) :=
        Matrix.SpecialLinearGroup.coe_mul _ _
    _ = _ := by rw [hc, hscal, hSmat, Matrix.mul_smul, Matrix.mul_one]

theorem kaL5B4_commute_single {n : ℕ} (A : GL (Fin n) F) {i j : Fin n} (hij : i ≠ j)
    (g : SL(n, F)) (hg : (g : Matrix (Fin n) (Fin n) F) = 1 + Matrix.single i j 1)
    (h : conjAut n F A (proj n F g) = proj n F g) :
    Commute (Matrix.single i j (1 : F)) A.val := by
  obtain ⟨μ, hμ⟩ := kaL5B4_fix_scalar A g h
  set N : Matrix (Fin n) (Fin n) F := Matrix.single i j 1 with hN
  have hN0 : N ≠ 0 := by
    intro h0
    have := congrFun (congrFun h0 i) j
    simp [hN] at this
  have hN2 : N * N = 0 := by
    rw [hN, Matrix.single_mul_single_of_ne (1 : F) i j i hij.symm 1]
  set Nt : Matrix (Fin n) (Fin n) F := A.val * N * A⁻¹.val with hNt
  have hNt2 : Nt * Nt = 0 := by
    calc Nt * Nt = A.val * (N * (A⁻¹.val * A.val) * N) * A⁻¹.val := by
          simp only [hNt, Matrix.mul_assoc]
      _ = 0 := by rw [Units.inv_mul, Matrix.mul_one, hN2, Matrix.mul_zero, Matrix.zero_mul]
  rw [hg, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Units.mul_inv] at hμ
  have hμ1 : μ = 1 :=
    ka_proj_scalar_eq_one N Nt hN0 hN2 hNt2 1 1 μ (by simpa only [one_smul] using hμ)
  rw [hμ1, one_smul] at hμ
  have hNN : N = Nt := add_left_cancel hμ
  show N * A.val = A.val * N
  calc N * A.val = Nt * A.val := by rw [← hNN]
    _ = A.val * N * (A⁻¹.val * A.val) := by simp only [hNt, Matrix.mul_assoc]
    _ = A.val * N := by rw [Units.inv_mul, Matrix.mul_one]

theorem kaL5B4_has_transvection {i j : Fin 5} (hi : i ≠ 4) (hj : j ≠ 4) (c : F) :
    kaL5B4Has (Matrix.transvection i j c) 1 := by
  refine ⟨?_, ?_⟩
  · rw [kaL5B4E, Matrix.mulVec_single_one, one_smul]
    funext a
    simp [Matrix.col, Matrix.transvection, Matrix.one_apply, hj, Pi.single_apply]
  · rw [kaL5B4E, Matrix.single_one_vecMul, one_smul]
    funext b
    simp [Matrix.row, Matrix.transvection, Matrix.one_apply, hi, Pi.single_apply, eq_comm]

theorem kaL5B4_root_mem {i j : Fin 5} (hij : i ≠ j) (hi : i ≠ 4) (hj : j ≠ 4) (c : F) :
    ∃ g : SL(5, F), (g : Matrix (Fin 5) (Fin 5) F) = 1 + Matrix.single i j c ∧
      proj 5 F g ∈ (kaL5B4Phi F).range := by
  let g : SL(5, F) := ⟨Matrix.transvection i j c, Matrix.det_transvection_of_ne i j hij c⟩
  obtain ⟨A, hA⟩ := kaL5B4_exists_blk (k := g) (kaL5B4_has_transvection hi hj c)
  refine ⟨g, rfl, A, ?_⟩
  change proj 5 F (kaL5B4Hom A) = proj 5 F g
  rw [hA]

theorem kaL5B4_root (c : F) : ∃ g : SL(5, F),
    (g : Matrix (Fin 5) (Fin 5) F) = 1 + c • (Matrix.single (0 : Fin 5) 1 (1 : F)) ∧
      proj 5 F g ∈ (kaL5B4Phi F).range := by
  obtain ⟨g, hg, hgL⟩ := kaL5B4_root_mem (i := 0) (j := 1) (by decide) (by decide) (by decide) c
  refine ⟨g, ?_, hgL⟩
  rw [hg, Matrix.smul_single, smul_eq_mul, mul_one]

theorem kaL5B4_diag_of_commute (M : Matrix (Fin 5) (Fin 5) F)
    (h : ∀ i j : Fin 5, i ≠ j → i ≠ 4 → j ≠ 4 → Commute (Matrix.single i j (1 : F)) M) :
    M = Matrix.diagonal ![M 0 0, M 0 0, M 0 0, M 0 0, M 4 4] := by
  have hcol : ∀ a b : Fin 5, a ≠ b → b ≠ 4 → M a b = 0 := by
    intro a b hab hb
    by_cases hb0 : b = 0
    · subst hb0
      exact Matrix.col_eq_zero_of_commute_single (h 0 1 (by decide) (by decide) (by decide)) hab
    · exact Matrix.col_eq_zero_of_commute_single (h b 0 hb0 hb (by decide)) hab
  have hrow : ∀ a b : Fin 5, a ≠ b → a ≠ 4 → M a b = 0 := by
    intro a b hab ha
    by_cases ha0 : a = 0
    · subst ha0
      exact Matrix.row_eq_zero_of_commute_single (h 1 0 (by decide) (by decide) (by decide))
        hab.symm
    · exact Matrix.row_eq_zero_of_commute_single (h 0 a (Ne.symm ha0) (by decide) ha) hab.symm
  have hdiag : ∀ a : Fin 5, a ≠ 4 → M a a = M 0 0 := by
    intro a ha
    by_cases ha0 : a = 0
    · rw [ha0]
    · exact Matrix.diag_eq_of_commute_single (h a 0 ha0 ha (by decide))
  ext a b
  by_cases hab : a = b
  · subst hab
    rw [Matrix.diagonal_apply_eq]
    fin_cases a
    · rfl
    · exact hdiag 1 (by decide)
    · exact hdiag 2 (by decide)
    · exact hdiag 3 (by decide)
    · rfl
  · rw [Matrix.diagonal_apply_ne _ hab]
    by_cases hb : b = 4
    · subst hb
      exact hrow a 4 hab hab
    · exact hcol a b hab hb

end Fix

section Torus

variable {F : Type} [Field F]

@[expose] noncomputable def kaL5B4Tor (u : Fˣ) : GL (Fin 5) F :=
  ⟨Matrix.diagonal ![(u : F), u, u, u, 1],
    Matrix.diagonal ![((u⁻¹ : Fˣ) : F), ((u⁻¹ : Fˣ) : F), ((u⁻¹ : Fˣ) : F), ((u⁻¹ : Fˣ) : F), 1],
    by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp,
    by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp⟩

theorem coe_kaL5B4Tor (u : Fˣ) :
    ((kaL5B4Tor u : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) =
      Matrix.diagonal ![(u : F), u, u, u, 1] :=
  rfl

theorem kaL5B4Tor_mul (u v : Fˣ) : kaL5B4Tor (F := F) (u * v) = kaL5B4Tor u * kaL5B4Tor v := by
  apply Units.ext
  rw [Units.val_mul, coe_kaL5B4Tor, coe_kaL5B4Tor, coe_kaL5B4Tor, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp

@[expose] noncomputable def kaL5B4TorHom : Fˣ →* GL (Fin 5) F :=
  MonoidHom.mk' kaL5B4Tor kaL5B4Tor_mul

theorem kaL5B4_conj_tor (A : GL (Fin 5) F) (l z : F)
    (hA : (A : Matrix (Fin 5) (Fin 5) F) = Matrix.diagonal ![l, l, l, l, z]) :
    ∃ u : Fˣ, conjAut 5 F A = conjAut 5 F (kaL5B4Tor u) := by
  have hdet : IsUnit (A : Matrix (Fin 5) (Fin 5) F).det := Matrix.isUnits_det_units A
  rw [hA, Matrix.det_diagonal, Fin.prod_univ_five] at hdet
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, isUnit_iff_ne_zero,
    ne_eq, mul_eq_zero, not_or] at hdet
  obtain ⟨⟨⟨⟨hl, -⟩, -⟩, -⟩, hz⟩ := hdet
  have hu : l * z⁻¹ ≠ 0 := mul_ne_zero hl (inv_ne_zero hz)
  have hAeq : A = GeneralLinearGroup.scalar (Fin 5) (Units.mk0 z hz) *
      kaL5B4Tor (Units.mk0 (l * z⁻¹) hu) := by
    apply Units.ext
    rw [Units.val_mul, hA, GeneralLinearGroup.coe_scalar, coe_kaL5B4Tor, Matrix.scalar_apply,
      Matrix.diagonal_mul_diagonal]
    have hzl : z * (l * z⁻¹) = l := by field_simp
    congr 1
    funext i
    fin_cases i <;> simp [hzl]
  refine ⟨Units.mk0 (l * z⁻¹) hu, ?_⟩
  rw [hAeq, map_mul, conjAut_scalar, one_mul]

end Torus

section Hfix

variable {F : Type} [Field F]

theorem kaL5B4_hfix [Finite F] :
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P' : Subgroup (MulAut (projectiveSL 5 F)), IsPGroup p ↥P' →
      (∀ e ∈ P', ∀ r ∈ (kaL5B4Phi F).range, e r = r) → IsCyclic ↥P' := by
  intro p hp hp2 P' hP' hfixP
  let T : Fˣ →* MulAut (projectiveSL 5 F) := (conjAut 5 F).comp kaL5B4TorHom
  have hle : P' ≤ T.range := by
    intro e he
    have hodd : Odd (orderOf e) := ka_odd_of_mem_pGroup hp hp2 hP' he
    let N : Matrix (Fin 5) (Fin 5) F := Matrix.single 0 1 1
    have hN0 : N ≠ 0 := by
      intro h0
      have := congrFun (congrFun h0 0) 1
      simp [N] at this
    have hN2 : N * N = 0 :=
      Matrix.single_mul_single_of_ne (1 : F) (0 : Fin 5) (1 : Fin 5) (0 : Fin 5) (by decide) (1 : F)
    obtain ⟨A, rfl⟩ := ka_fix_conjAut_proj (n := 5) (by norm_num) (kaL5B4Phi F).range
      N hN0 hN2 kaL5B4_root e hodd (hfixP e he)
    have hA : ∀ i j : Fin 5, i ≠ j → i ≠ 4 → j ≠ 4 →
        Commute (Matrix.single i j (1 : F)) A.val := by
      intro i j hij hi hj
      obtain ⟨g, hg, hgL⟩ := kaL5B4_root_mem hij hi hj (1 : F)
      exact kaL5B4_commute_single A hij g hg (hfixP _ he _ hgL)
    obtain ⟨u, hu⟩ := kaL5B4_conj_tor A _ _ (kaL5B4_diag_of_commute A.val hA)
    exact ⟨u, hu.symm⟩
  have : IsCyclic ↥T.range := isCyclic_of_surjective T.rangeRestrict T.rangeRestrict_surjective
  exact isCyclic_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)

end Hfix

section Main

variable {F : Type} [Field F]

theorem kaL5B4_main [Finite F] (hodd : ringChar F ≠ 2) : KAAll (conjAut 5 F (kaL5B4GL F)) := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hodd
  refine ka_all_of_torus_fix (ka_conj_inj_pl5 hodd) ((kaSlCent5 (kaL5B4GL F)).map (proj 5 F))
    (kaL5B4Phi F).range ?_ ?_ kaL5B4_range_le_map (kaL5B4_normalizes h2) kaL5B4_perfect
    kaL5B4_hLp kaL5B4_hfix (ka_outCentral_pl5 hodd (kaL5B4GL F) (kaL5B4GL_mul_self F))
  · intro y hy
    exact mem_fixSub.2 (kaL5B4_map_le_fix hy)
  · intro c hc ho
    exact ka_odd_mem_map_cent_pl5 (kaL5B4GL F) (kaL5B4GL_mul_self F) (mem_fixSub.1 hc) ho

theorem kaL5B4_congr_eq_mul {Y : Type} [Group Y] (e α : MulAut Y) :
    MulAut.congr e α = e * α * e⁻¹ := by
  ext x
  simp [MulAut.congr_apply]

end Main

theorem kaL5B4_thm : KAL5B4 := by
  intro F _ _ hodd B hB h4
  obtain ⟨P, rfl⟩ := kaL5B4_exists_frame hodd hB h4
  have h' := KAAll.of_mulEquiv (conjAut 5 F P : projectiveSL 5 F ≃* projectiveSL 5 F)
    (kaL5B4_main hodd)
  have key : MulAut.congr (conjAut 5 F P : projectiveSL 5 F ≃* projectiveSL 5 F)
      (conjAut 5 F (kaL5B4GL F)) = conjAut 5 F (P * kaL5B4GL F * P⁻¹) := by
    rw [kaL5B4_congr_eq_mul, map_mul, map_mul, map_inv]
  rwa [key] at h'

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
