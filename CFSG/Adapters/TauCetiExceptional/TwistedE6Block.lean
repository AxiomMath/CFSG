module

public import CFSG.Adapters.TauCetiExceptional.TwistedBlock
public import CFSG.Adapters.TauCetiExceptional.MinusculeClosure
public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.IntegralMatrix
public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.Generation
import all TauCeti.Algebra.Lie.E6.DoubledMinuscule.IntegralMatrix
import all TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E6.MinusculeWeight

public noncomputable section

namespace CFSG.TauCetiBridge.Twisted

open CFSG.Blueprint.Chevalley TauCeti TauCeti.DynkinType TauCeti.E6DoubledMinuscule
  TauCeti.UniversalEnvelopingAlgebra WithConv
open CFSG.TauCetiBridge.Minuscule
open scoped Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

@[expose] def e6Blk (a : Fin 54) : Fin 2 := if (matrixIndexEquiv.symm a).isLeft then 0 else 1

@[expose] def e6E (A : Type*) [CommRing A] (i : Fin 6) : Matrix (Fin 54) (Fin 54) A :=
  (rootIntMatrix (.inl i)).map (Int.cast : ℤ → A)

@[expose] def e6F (A : Type*) [CommRing A] (i : Fin 6) : Matrix (Fin 54) (Fin 54) A :=
  (rootIntMatrix (.inr i)).map (Int.cast : ℤ → A)

@[expose] def e6Wt (a : Fin 54) (i : Fin 6) : ℤ :=
  e6DoubledMinusculeWeight (matrixIndexEquiv.symm a) i

theorem e6Wt_mem (a : Fin 54) (i : Fin 6) : e6Wt a i = -1 ∨ e6Wt a i = 0 ∨ e6Wt a i = 1 := by
  rw [e6Wt]
  rcases matrixIndexEquiv.symm a with x | x
  · rw [e6DoubledMinusculeWeight_inl]
    exact e6MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one x i
  · rw [e6DoubledMinusculeWeight_inr, Pi.neg_apply]
    rcases e6MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one x i with h | h | h <;>
      rw [h] <;> norm_num

theorem e6Wt_injective : Function.Injective e6Wt := fun a b h =>
  matrixIndexEquiv.symm.injective (e6DoubledMinusculeWeight_injective (funext fun i => by
    have := congrFun h i
    simpa [e6Wt] using this))

theorem rootIntMatrix_apply' (j : Fin 6 ⊕ Fin 6) (r s : Fin 54) :
    rootIntMatrix j r s =
      if r = matrixIndexEquiv (reflection (Sum.elim id id j) (matrixIndexEquiv.symm s)) then
        (if matrixWeight s (Sum.elim id id j) = (Sum.elim (fun _ ↦ -1) (fun _ ↦ 1) j : ℤ)
          then summandSign (matrixIndexEquiv.symm s) else 0) else 0 := by
  rw [rootIntMatrix]
  exact kostantRootGeneratorIntMatrix_apply_of_eq
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice j matrixBasis (rep_rootGenerator_matrixBasis_eq_smul j s) r

theorem e6Blk_eq_iff (a b : Fin 54) : e6Blk a = e6Blk b ↔ matrixSummand a = matrixSummand b := by
  unfold e6Blk matrixSummand
  rcases matrixIndexEquiv.symm a <;> rcases matrixIndexEquiv.symm b <;> simp

theorem rootIntMatrix_isBlockDiag (j : Fin 6 ⊕ Fin 6) :
    IsBlockDiag e6Blk ℤ (rootIntMatrix j) := fun a b hab =>
  rootIntMatrix_eq_zero_of_summand_ne j fun h => hab ((e6Blk_eq_iff a b).2 h)

@[expose] def e6dRatPoints :
    Subgroup (WithConv (GeneralLinear.coordinateHopfAlgebra ℤ 54 →ₐ[ℤ] ℚ)) :=
  ((elementarySubgroup ℚ).map (points ℚ).subtype).map
    (GeneralLinear.pointsMulEquiv (R := ℤ) (A := ℚ) 54).symm.toMonoidHom

theorem e6dVanishingIdeal_le_definingIdeal :
    fracVanishingIdeal (R := ℤ) (K := ℚ) e6dRatPoints ≤ definingIdeal := by
  rw [definingIdeal_eq_kostantGeneratedDefiningIdeal]
  refine fracVanishingIdeal_le_kostantGeneratedDefiningIdeal _ _ _ _ _ _ _ _ fun j c => ?_
  rw [← coe_rootSubgroupPoints]
  exact ⟨_, ⟨_, rootSubgroupPoints_mem_elementarySubgroup ℚ j (Multiplicative.ofAdd c), rfl⟩, rfl⟩

theorem e6d_evalMat_eq_zero (P : MvPolynomial (Fin 54 × Fin 54) ℤ)
    (hP : ∀ g ∈ elementarySubgroup ℚ,
      BigCell.evalMat (((g : points ℚ) : Matrix.GeneralLinearGroup (Fin 54) ℚ) :
        Matrix (Fin 54) (Fin 54) ℚ) P = 0)
    (A : Type*) [CommRing A] (g : Matrix.GeneralLinearGroup (Fin 54) A) (hg : g ∈ points A) :
    BigCell.evalMat (g : Matrix (Fin 54) (Fin 54) A) P = 0 := by
  have hx : GeneralLinear.coordinateHopfAlgebraAlgEquiv ℤ 54
      (GeneralLinear.coordinateRingMap ℤ 54 P) ∈ fracVanishingIdeal (R := ℤ) (K := ℚ)
        e6dRatPoints := by
    refine (mem_fracVanishingIdeal _ _).mpr ?_
    rintro ⟨_, ⟨_, ⟨g', hg', rfl⟩, rfl⟩⟩
    change ((GeneralLinear.pointsMulEquiv (R := ℤ) (A := ℚ) 54).symm
      (g' : Matrix.GeneralLinearGroup (Fin 54) ℚ)).ofConv _ = 0
    rw [GeneralLinear.pointsMulEquiv_symm_apply,
      GeneralLinear.generalLinearToPoint_coordinateRingMap, aeval_eq_evalMat]
    exact hP g' hg'
  have := (mem_points_iff A g).mp hg _ (e6dVanishingIdeal_le_definingIdeal hx)
  rwa [GeneralLinear.pointsMulEquiv_symm_apply,
    GeneralLinear.generalLinearToPoint_coordinateRingMap, aeval_eq_evalMat] at this

theorem one_add_smul_isBlockDiag_e6 {A : Type*} [CommRing A] (c : A)
    {E : Matrix (Fin 54) (Fin 54) ℤ} (hE : IsBlockDiag e6Blk ℤ E) :
    IsBlockDiag e6Blk A (1 + c • E.map (Int.cast : ℤ → A)) := by
  intro a b hab
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, hE a b hab, Int.cast_zero, smul_zero,
    add_zero]
  exact isBlockDiag_one a b hab

theorem e6d_points_isBlockDiag (A : Type*) [CommRing A] (g : Matrix.GeneralLinearGroup (Fin 54) A)
    (hg : g ∈ points A) : IsBlockDiag e6Blk A (g : Matrix (Fin 54) (Fin 54) A) := by
  intro a b hab
  have hle : elementarySubgroup ℚ ≤ (blockGL e6Blk ℚ).comap (points ℚ).subtype := by
    rw [elementarySubgroup_le_iff]
    intro k u
    refine mem_blockGL_of ?_ ?_
    · rw [Subgroup.coe_subtype, coe_rootSubgroupPoints_eq_one_add_smul]
      exact one_add_smul_isBlockDiag_e6 _ (rootIntMatrix_isBlockDiag k)
    · rw [Subgroup.coe_subtype, ← Subgroup.coe_inv, ← map_inv,
        coe_rootSubgroupPoints_eq_one_add_smul]
      exact one_add_smul_isBlockDiag_e6 _ (rootIntMatrix_isBlockDiag k)
  have h := e6d_evalMat_eq_zero (MvPolynomial.X (a, b)) (fun g' hg' => ?_) A g hg
  · rwa [BigCell.evalMat_X] at h
  rw [BigCell.evalMat_X]
  exact (hle hg').1 a b hab

theorem rootIntMatrix_inl_eq (i : Fin 6) :
    rootIntMatrix (.inl i) =
      (raisingMatrix i).submatrix matrixIndexEquiv.symm matrixIndexEquiv.symm := by
  ext r s
  rw [rootIntMatrix_apply', Matrix.submatrix_apply, raisingMatrix_apply]
  simp only [Sum.elim_inl, id_eq, matrixWeight_apply]
  by_cases h1 : r = matrixIndexEquiv (reflection i (matrixIndexEquiv.symm s)) <;>
    by_cases h2 : e6DoubledMinusculeWeight (matrixIndexEquiv.symm s) i = -1 <;>
    simp [h1, h2, Equiv.symm_apply_eq]

theorem rootIntMatrix_inr_eq (i : Fin 6) :
    rootIntMatrix (.inr i) =
      (loweringMatrix i).submatrix matrixIndexEquiv.symm matrixIndexEquiv.symm := by
  ext r s
  rw [rootIntMatrix_apply', Matrix.submatrix_apply, loweringMatrix_apply]
  simp only [Sum.elim_inr, id_eq, matrixWeight_apply]
  by_cases h1 : r = matrixIndexEquiv (reflection i (matrixIndexEquiv.symm s)) <;>
    by_cases h2 : e6DoubledMinusculeWeight (matrixIndexEquiv.symm s) i = 1 <;>
    simp [h1, h2, Equiv.symm_apply_eq]

theorem map_submatrix_cartanGeneratorMatrix (L : Type*) [CommRing L] (i : Fin 6) :
    (Int.castRingHom L).mapMatrix
        ((cartanGeneratorMatrix i).submatrix matrixIndexEquiv.symm matrixIndexEquiv.symm) =
      Matrix.diagonal fun a => (e6Wt a i : L) := by
  ext a b
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply,
    cartanGeneratorMatrix_apply]
  by_cases hab : a = b
  · subst hab
    simp [e6Wt]
  · rw [ite_eq_right fun h => (hab (matrixIndexEquiv.symm.injective h)).elim,
      Matrix.diagonal_apply_ne _ hab, map_zero]

theorem e6_int_comm (i : Fin 6) :
    rootIntMatrix (.inl i) * rootIntMatrix (.inr i) -
        rootIntMatrix (.inr i) * rootIntMatrix (.inl i) =
      (cartanGeneratorMatrix i).submatrix matrixIndexEquiv.symm matrixIndexEquiv.symm := by
  have h := isSerreSystem.lie_E_F_self i
  rw [Ring.lie_def] at h
  ext a b
  rw [rootIntMatrix_inl_eq, rootIntMatrix_inr_eq, Matrix.sub_apply, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_apply, Matrix.submatrix_apply,
    Matrix.submatrix_apply, ← Matrix.sub_apply, h]

theorem e6_int_commH (i j : Fin 6) :
    (cartanGeneratorMatrix i).submatrix matrixIndexEquiv.symm matrixIndexEquiv.symm *
        rootIntMatrix (.inl j) -
      rootIntMatrix (.inl j) *
        (cartanGeneratorMatrix i).submatrix matrixIndexEquiv.symm matrixIndexEquiv.symm =
      Tag.cartan .E6 i j • rootIntMatrix (.inl j) := by
  have h := isSerreSystem.lie_H_E i j
  rw [Ring.lie_def] at h
  have hc : (CartanMatrix.E 6)ᵀ i j = Tag.cartan .E6 i j := by
    have := e6_cartan i j
    rwa [E6Minuscule.weightTable_cartanMatrix] at this
  ext a b
  rw [rootIntMatrix_inl_eq, Matrix.sub_apply, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_apply, Matrix.submatrix_apply,
    ← Matrix.sub_apply, h, Matrix.smul_apply, Matrix.smul_apply, Matrix.submatrix_apply, hc]

theorem e6E_comm (L : Type*) [CommRing L] (i : Fin 6) :
    e6E L i * e6F L i - e6F L i * e6E L i = Matrix.diagonal fun a => (e6Wt a i : L) := by
  rw [← map_submatrix_cartanGeneratorMatrix, ← e6_int_comm, map_sub, map_mul, map_mul]
  rfl

theorem e6E_commH (L : Type*) [CommRing L] (i j : Fin 6) :
    Matrix.diagonal (fun a => (e6Wt a i : L)) * e6E L j -
      e6E L j * Matrix.diagonal (fun a => (e6Wt a i : L)) =
        ((Tag.cartan .E6 i j : ℤ) : L) • e6E L j := by
  rw [← map_submatrix_cartanGeneratorMatrix]
  change (Int.castRingHom L).mapMatrix _ * (Int.castRingHom L).mapMatrix (rootIntMatrix (.inl j)) -
      (Int.castRingHom L).mapMatrix (rootIntMatrix (.inl j)) * (Int.castRingHom L).mapMatrix _ = _
  rw [← map_mul, ← map_mul, ← map_sub, e6_int_commH]
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
    eq_intCast, Int.cast_mul, e6E]

theorem e6E_ne_zero (L : Type*) [CommRing L] [Nontrivial L] (j : Fin 6) : e6E L j ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_e6MinusculeWeight_apply_eq_neg_one j
  intro h
  have e := congrArg (fun M : Matrix (Fin 54) (Fin 54) L =>
    M (matrixIndexEquiv (.inl (e6MinusculeReflection j a))) (matrixIndexEquiv (.inl a))) h
  simp only [e6E, Matrix.map_apply, rootIntMatrix_apply', Equiv.symm_apply_apply,
    reflection_inl, Sum.elim_inl, id_eq, matrixWeight_apply, e6DoubledMinusculeWeight_inl, ha,
    ite_true, summandSign_inl, Int.cast_one, Matrix.zero_apply] at e
  exact one_ne_zero e

theorem cartan_E6_off (i j : Fin 6) (hij : i ≠ j) :
    Tag.cartan .E6 i j = 0 ∨ Tag.cartan .E6 i j = -1 := by
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | (left; rfl) | (right; rfl)

theorem e6_isDiag_of_commute {L : Type*} [Field L] (h2 : (2 : L) ≠ 0)
    {z : Matrix (Fin 54) (Fin 54) L}
    (hz : ∀ i, z * Matrix.diagonal (fun a => (e6Wt a i : L)) =
      Matrix.diagonal (fun a => (e6Wt a i : L)) * z) {a b : Fin 54} (hab : a ≠ b) : z a b = 0 :=
  isDiag_of_commute_diagonal h2 e6Wt e6Wt_mem e6Wt_injective hz hab

theorem summandSign_cast_ne_zero (L : Type*) [Field L] (x : Fin 27 ⊕ Fin 27) :
    ((summandSign x : ℤ) : L) ≠ 0 := by
  cases x <;> simp

theorem e6_diag_eq_reflection {L : Type*} [Field L] {z : Matrix (Fin 54) (Fin 54) L}
    (hz : ∀ a b, a ≠ b → z a b = 0) (hE : ∀ i, z * e6E L i = e6E L i * z)
    (hF : ∀ i, z * e6F L i = e6F L i * z) (i : Fin 6) (x : Fin 27 ⊕ Fin 27) :
    z (matrixIndexEquiv x) (matrixIndexEquiv x) =
      z (matrixIndexEquiv (reflection i x)) (matrixIndexEquiv (reflection i x)) := by
  have hw := e6Wt_mem (matrixIndexEquiv x) i
  simp only [e6Wt, Equiv.symm_apply_apply] at hw
  rcases hw with h | h | h
  · refine diag_eq_of_commute hz (hE i) ?_
    simp [e6E, rootIntMatrix_apply', matrixWeight_apply, h, summandSign_cast_ne_zero]
  · have hfix : reflection i x = x := by
      cases x with
      | inl y =>
        rw [reflection_inl, (e6MinusculeReflection_eq_self_iff i y).2]
        simpa using h
      | inr y =>
        rw [reflection_inr, (e6MinusculeReflection_eq_self_iff i y).2]
        simpa using h
    rw [hfix]
  · refine diag_eq_of_commute hz (hF i) ?_
    simp [e6F, rootIntMatrix_apply', matrixWeight_apply, h, summandSign_cast_ne_zero]

theorem e6_diag_eq_of_commute {L : Type*} [Field L] {z : Matrix (Fin 54) (Fin 54) L}
    (hz : ∀ a b, a ≠ b → z a b = 0) (hE : ∀ i, z * e6E L i = e6E L i * z)
    (hF : ∀ i, z * e6F L i = e6F L i * z) {a b : Fin 54} (hab : e6Blk a = e6Blk b) :
    z a a = z b b := by
  have hpath : ∀ (l : List (Fin 6)) (x : Fin 27 ⊕ Fin 27),
      z (matrixIndexEquiv x) (matrixIndexEquiv x) =
        z (matrixIndexEquiv (l.foldl (fun c i => reflection i c) x))
          (matrixIndexEquiv (l.foldl (fun c i => reflection i c) x)) := by
    intro l
    induction l with
    | nil => intro x; rfl
    | cons i l ih => intro x; rw [List.foldl_cons, ← ih, ← e6_diag_eq_reflection hz hE hF]
  have hinl : ∀ (l : List (Fin 6)) (y : Fin 27), l.foldl (fun c i => reflection i c)
      (Sum.inl y : Fin 27 ⊕ Fin 27) = .inl (l.foldl (fun c i => e6MinusculeReflection i c) y) := by
    intro l
    induction l with
    | nil => intro y; rfl
    | cons i l ih => intro y; rw [List.foldl_cons, List.foldl_cons, reflection_inl, ih]
  have hinr : ∀ (l : List (Fin 6)) (y : Fin 27), l.foldl (fun c i => reflection i c)
      (Sum.inr y : Fin 27 ⊕ Fin 27) = .inr (l.foldl (fun c i => e6MinusculeReflection i c) y) := by
    intro l
    induction l with
    | nil => intro y; rfl
    | cons i l ih => intro y; rw [List.foldl_cons, List.foldl_cons, reflection_inr, ih]
  have hl : ∀ y : Fin 27, z (matrixIndexEquiv (.inl y)) (matrixIndexEquiv (.inl y)) =
      z (matrixIndexEquiv (.inl 0)) (matrixIndexEquiv (.inl 0)) := by
    intro y
    obtain ⟨l, hl⟩ := exists_e6MinusculeReflections_eq y
    rw [hpath l (.inl 0), hinl, hl]
  have hr : ∀ y : Fin 27, z (matrixIndexEquiv (.inr y)) (matrixIndexEquiv (.inr y)) =
      z (matrixIndexEquiv (.inr 0)) (matrixIndexEquiv (.inr 0)) := by
    intro y
    obtain ⟨l, hl⟩ := exists_e6MinusculeReflections_eq y
    rw [hpath l (.inr 0), hinr, hl]
  obtain ⟨x, rfl⟩ := matrixIndexEquiv.surjective a
  obtain ⟨y, rfl⟩ := matrixIndexEquiv.surjective b
  rcases x with x | x <;> rcases y with y | y
  · rw [hl x, hl y]
  · exact absurd hab (by simp [e6Blk])
  · exact absurd hab (by simp [e6Blk])
  · rw [hr x, hr y]

theorem e6_excl_sum : ∀ π' : Equiv.Perm (Fin 6),
    (∀ ij : Fin 6 × Fin 6, Tag.cartan .E6 (π' ij.1) (π' ij.2) = Tag.cartan .E6 ij.1 ij.2) →
    (∀ x : Fin 27 ⊕ Fin 27, ∃ y : Fin 27 ⊕ Fin 27, y.isLeft = x.isLeft ∧
      ∀ j, e6DoubledMinusculeWeight y (π' j) = e6DoubledMinusculeWeight x j) → π' = 1 := by
  decide +kernel

theorem e6_excl (π' : Equiv.Perm (Fin 6))
    (hcart : ∀ ij : Fin 6 × Fin 6, Tag.cartan .E6 (π' ij.1) (π' ij.2) = Tag.cartan .E6 ij.1 ij.2)
    (h : ∀ a, ∃ b, e6Blk b = e6Blk a ∧ ∀ j, e6Wt b (π' j) = e6Wt a j) : π' = 1 := by
  refine e6_excl_sum π' hcart fun x => ?_
  obtain ⟨b, hb, hw⟩ := h (matrixIndexEquiv x)
  refine ⟨matrixIndexEquiv.symm b, ?_, fun j => ?_⟩
  · simp only [e6Blk, Equiv.symm_apply_apply] at hb
    revert hb
    cases matrixIndexEquiv.symm b <;> cases x <;> simp
  · simpa [e6Wt] using hw j

end CFSG.TauCetiBridge.Twisted
