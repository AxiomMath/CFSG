module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphParamSL
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphTorusGram

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule
open CFSG.Timmesfeld.LieEmbed (a5Root)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut slGraphAut_matrix)
open CFSG.LieType.Steinberg.TwistedE6 (sigma rho twistSign)

section Perm

variable {n : ℕ} {F : Type} [Field F]

@[expose] noncomputable def permGL (π : Equiv.Perm (Fin n)) : GL (Fin n) F where
  val := π.toPEquiv.toMatrix
  inv := π.symm.toPEquiv.toMatrix
  val_inv := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  inv_val := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self,
      Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]

theorem permGL_mul_mul_inv (π : Equiv.Perm (Fin n)) (M : Matrix (Fin n) (Fin n) F) :
    ((permGL π : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * M *
        (((permGL π)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = M.submatrix π π := by
  change π.toPEquiv.toMatrix * M * π.symm.toPEquiv.toMatrix = _
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm,
    Matrix.submatrix_submatrix]
  rfl

theorem slConjugation_permGL_transvection (π : Equiv.Perm (Fin n)) {i j : Fin n} (hij : i ≠ j)
    (c : F) :
    slConjugation n F (permGL π) (Matrix.SpecialLinearGroup.transvection hij c) =
      Matrix.SpecialLinearGroup.transvection (π.symm.injective.ne hij) c := by
  refine Subtype.ext ?_
  rw [slConjugation_matrix]
  change ((permGL π : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (1 + Matrix.single i j c) *
      (((permGL π)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
    1 + Matrix.single (π.symm i) (π.symm j) c
  rw [permGL_mul_mul_inv, show (1 + Matrix.single i j c).submatrix π π =
      (1 : Matrix (Fin n) (Fin n) F).submatrix π π + (Matrix.single i j c).submatrix π π from rfl,
    Matrix.submatrix_one_equiv, Matrix.submatrix_single_equiv]

theorem slGraphAut_transvection {i j : Fin n} (hij : i ≠ j) (c : F) :
    slGraphAut n F (Matrix.SpecialLinearGroup.transvection hij c) =
      Matrix.SpecialLinearGroup.transvection hij.symm (-c) := by
  refine Subtype.ext ?_
  rw [slGraphAut_matrix, Matrix.SpecialLinearGroup.transvection_inv]
  change Matrix.transpose (1 + Matrix.single i j (-c)) = 1 + Matrix.single j i (-c)
  rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single]

theorem map_transvection {K : Type} [Field K] (ε : F →+* K) {i j : Fin n} (hij : i ≠ j)
    (c : F) :
    Matrix.SpecialLinearGroup.map ε (Matrix.SpecialLinearGroup.transvection hij c) =
      Matrix.SpecialLinearGroup.transvection hij (ε c) := by
  refine Subtype.ext ?_
  change (1 + Matrix.single i j c).map ε = 1 + Matrix.single i j (ε c)
  rw [Matrix.map_add ε (map_add ε), Matrix.map_one ε (map_zero ε) (map_one ε), Matrix.map_single]

end Perm

section Beta

variable {F : Type} [Field F]

@[expose] def graphPairPerm : Equiv.Perm (Fin 6) :=
  ⟨![3, 4, 5, 0, 1, 2], ![3, 4, 5, 0, 1, 2], by decide, by decide⟩

@[expose] def graphSwapPerm : Equiv.Perm (Fin 6) := Equiv.swap 3 5

theorem blockSwapJ_cond_iff : ∀ i j : Fin 6,
    ((j : ℕ) = i + 3 ∨ (i : ℕ) = j + 3) ↔ graphPairPerm i = j := by
  decide

theorem graphGram6_eq_permGL : graphGram6 F = permGL graphPairPerm := by
  refine Units.ext ?_
  ext i j
  change (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.blockSwapJ 6 3 :
      Matrix (Fin 6) (Fin 6) F) i j =
    (graphPairPerm.toPEquiv.toMatrix : Matrix (Fin 6) (Fin 6) F) i j
  simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some_inj,
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.blockSwapJ, Matrix.of_apply,
    blockSwapJ_cond_iff]

theorem graphBeta6_transvection {i j : Fin 6} (hij : i ≠ j) (c : F) :
    (slConjugation 6 F (graphGram6 F) * slGraphAut 6 F)
        (Matrix.SpecialLinearGroup.transvection hij c) =
      Matrix.SpecialLinearGroup.transvection (graphPairPerm.symm.injective.ne hij.symm) (-c) := by
  rw [MulAut.mul_apply, slGraphAut_transvection, graphGram6_eq_permGL,
    slConjugation_permGL_transvection]

theorem graphSwapPerm_graphPairPerm_symm :
    ∀ k : Fin 6, graphSwapPerm.symm (graphPairPerm.symm k) = Fin.rev (graphSwapPerm.symm k) := by
  decide

end Beta

theorem intCast_eq_one_of_sign_charTwo {K : Type} [Field K] [CharP K 2] {z : ℤ}
    (h : z = 1 ∨ z = -1) : (z : K) = 1 := by
  rcases h with rfl | rfl
  · exact Int.cast_one
  · rw [Int.cast_neg, Int.cast_one, CharTwo.neg_eq]

section Param


variable (K : Type) [Field K] [Finite K] [CharP K 2] {F : Type} [Field F]

@[expose] noncomputable def graphParamHom (ε : F ≃+* K) :
    Matrix.SpecialLinearGroup (Fin 6) F →* e6Data_valid.minGroup K :=
  (slToE6Sc K).comp ((slConjugation 6 K (permGL graphSwapPerm)).toMonoidHom.comp
    (Matrix.SpecialLinearGroup.map (ε : F →+* K)))

variable {K}

theorem graphParamHom_transvection (ε : F ≃+* K) {i j : Fin 6} (hij : i ≠ j) (c : F) :
    graphParamHom K ε (Matrix.SpecialLinearGroup.transvection hij c) =
      e6Data_valid.xm K (a5Root (graphSwapPerm.symm i) (graphSwapPerm.symm j)) (ε c) := by
  rw [graphParamHom, MonoidHom.comp_apply, MonoidHom.comp_apply, map_transvection,
    MulEquiv.coe_toMonoidHom, slConjugation_permGL_transvection, slToE6Sc_transvection]
  rfl

theorem sigma_graphParamHom (ε : F ≃+* K) (g : Matrix.SpecialLinearGroup (Fin 6) F) :
    sigma K (RingHom.id K) (graphParamHom K ε g) =
      graphParamHom K ε ((slConjugation 6 F (graphGram6 F) * slGraphAut 6 F) g) := by
  have h : (sigma K (RingHom.id K)).comp (graphParamHom K ε) =
      (graphParamHom K ε).comp (slConjugation 6 F (graphGram6 F) * slGraphAut 6 F).toMonoidHom := by
    refine MonoidHom.eq_of_eqOn_dense
      (Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field) ?_
    rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
    rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk, MonoidHom.comp_apply,
      MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, graphBeta6_transvection,
      graphParamHom_transvection, graphParamHom_transvection,
      CFSG.LieType.Steinberg.TwistedE6.sigma_xm (RingHom.id K)
        (CFSG.Timmesfeld.LieEmbed.isRoot_a5Root (graphSwapPerm.symm.injective.ne hij)),
      CFSG.Timmesfeld.LieEmbed.rho_a5Root,
      intCast_eq_one_of_sign_charTwo (CFSG.LieType.Steinberg.TwistedE6.twistSign_eq_one_or _),
      one_mul, RingHom.id_apply, graphSwapPerm_graphPairPerm_symm,
      graphSwapPerm_graphPairPerm_symm, map_neg, CharTwo.neg_eq]
  exact DFunLike.congr_fun h g

theorem graphParamHom_injective (ε : F ≃+* K) : Function.Injective (graphParamHom K ε) := by
  refine slToE6Sc_injective.comp ((slConjugation 6 K (permGL graphSwapPerm)).injective.comp ?_)
  intro g h hgh
  refine Subtype.ext (Matrix.ext fun a b => ε.injective ?_)
  exact congrFun (congrFun (congrArg Subtype.val hgh) a) b

theorem range_graphParamHom (ε : F ≃+* K) :
    (graphParamHom K ε).range = e6ScLevi K e6A5Nodes := by
  have hsurj : Function.Surjective ((slConjugation 6 K (permGL graphSwapPerm)).toMonoidHom.comp
      (Matrix.SpecialLinearGroup.map (ε : F →+* K))) := by
    intro g
    refine ⟨Matrix.SpecialLinearGroup.map (ε.symm : K →+* F)
      ((slConjugation 6 K (permGL graphSwapPerm)).symm g), ?_⟩
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    have e : Matrix.SpecialLinearGroup.map (ε : F →+* K)
        (Matrix.SpecialLinearGroup.map (ε.symm : K →+* F)
          ((slConjugation 6 K (permGL graphSwapPerm)).symm g)) =
        (slConjugation 6 K (permGL graphSwapPerm)).symm g := by
      refine Subtype.ext (Matrix.ext fun a b => ?_)
      exact ε.apply_symm_apply _
    rw [e, MulEquiv.apply_symm_apply]
  rw [graphParamHom, MonoidHom.range_comp, MonoidHom.range_eq_top.2 hsurj, ← MonoidHom.range_eq_map,
    range_slToE6Sc]

variable (K) in
@[expose] noncomputable def graphParamEquiv (ε : F ≃+* K) :
    Matrix.SpecialLinearGroup (Fin 6) F ≃* e6ScLevi K e6A5Nodes :=
  (MonoidHom.ofInjective (graphParamHom_injective ε)).trans
    (MulEquiv.subgroupCongr (range_graphParamHom ε))

theorem coe_graphParamEquiv (ε : F ≃+* K) (g : Matrix.SpecialLinearGroup (Fin 6) F) :
    ((graphParamEquiv K ε g : e6ScLevi K e6A5Nodes) : e6Data_valid.minGroup K) =
      graphParamHom K ε g :=
  rfl

end Param

end CFSG.SeitzReduction.F4Pilot
