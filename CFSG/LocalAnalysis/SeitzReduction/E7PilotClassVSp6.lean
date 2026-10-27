module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassVSL6
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Timmesfeld.LieEmbed
open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.Assembly.LowTwoRank TauCeti.GLSymplecticFin

@[expose] def e7SpIdx : Fin 3 ⊕ Fin 3 ≃ Fin 6 := finSumFinEquiv.trans (Equiv.swap 3 5)

theorem spIdx_check : ∀ i : Fin 3, e7SpIdx (.inr i) = Fin.rev (e7SpIdx (.inl i)) ∧
    e7SpIdx (.inl i) = Fin.rev (e7SpIdx (.inr i)) := by
  decide

theorem spIdx_inr (i : Fin 3) : e7SpIdx (.inr i) = Fin.rev (e7SpIdx (.inl i)) := (spIdx_check i).1

theorem spIdx_inl (i : Fin 3) : e7SpIdx (.inl i) = Fin.rev (e7SpIdx (.inr i)) := (spIdx_check i).2

theorem spIdx_ne {a b : Fin 3 ⊕ Fin 3} (h : a ≠ b) : e7SpIdx a ≠ e7SpIdx b :=
  fun e => h (e7SpIdx.injective e)

variable {K : Type} [Field K]

theorem reindex_single (a b : Fin 3 ⊕ Fin 3) (x : K) :
    Matrix.reindexAlgEquiv K K e7SpIdx (Matrix.single a b x) =
      Matrix.single (e7SpIdx a) (e7SpIdx b) x := by
  rw [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_single_equiv,
    Equiv.symm_symm]

theorem transvection_mul_transvection {p q p' q' : Fin 6} (h : q ≠ p') (x y : K) :
    (1 + Matrix.single p q x) * (1 + Matrix.single p' q' y) =
      1 + Matrix.single p q x + Matrix.single p' q' y := by
  rw [add_mul, one_mul, mul_add, mul_one, Matrix.single_mul_single_of_ne (h := h), add_zero]
  abel

variable (K) in
theorem det_mat_statedSp (A : StatedSp 3 K) : (mat 3 K A).det = 1 := by
  have hsp := TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup.1
    ((Subgroup.ext_iff.1 CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic _).1 A.2)
  exact SymplecticGroup.det_eq_one hsp

variable (K) in
@[expose] noncomputable def spToSL : StatedSp 3 K →* Matrix.SpecialLinearGroup (Fin 6) K where
  toFun A := ⟨Matrix.reindexAlgEquiv K K e7SpIdx (mat 3 K A), by
    rw [Matrix.det_reindexAlgEquiv, det_mat_statedSp]⟩
  map_one' := Subtype.ext (by
    change Matrix.reindexAlgEquiv K K e7SpIdx (mat 3 K 1) = 1
    rw [map_one, map_one])
  map_mul' A B := Subtype.ext (by
    change Matrix.reindexAlgEquiv K K e7SpIdx (mat 3 K (A * B)) =
      Matrix.reindexAlgEquiv K K e7SpIdx (mat 3 K A) * Matrix.reindexAlgEquiv K K e7SpIdx (mat 3 K B)
    rw [map_mul, map_mul])

theorem coe_spToSL (A : StatedSp 3 K) :
    (spToSL K A : Matrix (Fin 6) (Fin 6) K) = Matrix.reindexAlgEquiv K K e7SpIdx (mat 3 K A) :=
  rfl

theorem coe_spToSL_elt (r : RootSubgroupIndex 3) (c : K) :
    (spToSL K (elt r c) : Matrix (Fin 6) (Fin 6) K) =
      1 + c • Matrix.reindexAlgEquiv K K e7SpIdx (E K r) := by
  rw [coe_spToSL, mat_elt, map_add, map_one, map_smul]

theorem spToSL_positiveLong (i : Fin 3) (c : K) :
    spToSL K (elt (.positiveLong i) c) =
      Matrix.SpecialLinearGroup.transvection (spIdx_ne (Sum.inl_ne_inr (a := i) (b := i))) c := by
  apply Subtype.ext
  rw [coe_spToSL_elt, Matrix.SpecialLinearGroup.transvection_coe, E, reindex_single,
    Matrix.smul_single, smul_eq_mul, mul_one]

theorem spToSL_negativeLong (i : Fin 3) (c : K) :
    spToSL K (elt (.negativeLong i) c) =
      Matrix.SpecialLinearGroup.transvection (spIdx_ne (Sum.inr_ne_inl (a := i) (b := i))) c := by
  apply Subtype.ext
  rw [coe_spToSL_elt, Matrix.SpecialLinearGroup.transvection_coe, E, reindex_single,
    Matrix.smul_single, smul_eq_mul, mul_one]

theorem spToSL_difference {i j : Fin 3} (hij : i ≠ j) (c : K) :
    spToSL K (elt (.difference i j hij) c) =
      Matrix.SpecialLinearGroup.transvection
          (spIdx_ne (a := .inl i) (b := .inl j) (by simpa using hij)) c *
        Matrix.SpecialLinearGroup.transvection
          (spIdx_ne (a := .inr j) (b := .inr i) (by simpa using hij.symm)) (-c) := by
  apply Subtype.ext
  rw [coe_spToSL_elt, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe,
    transvection_mul_transvection (spIdx_ne (a := .inl j) (b := .inr j) Sum.inl_ne_inr), E,
    map_sub, reindex_single, reindex_single, smul_sub, Matrix.smul_single, Matrix.smul_single,
    smul_eq_mul, mul_one, ← Matrix.single_neg]
  abel

theorem spToSL_positiveSum {i j : Fin 3} (hij : i < j) (c : K) :
    spToSL K (elt (.positiveSum i j hij) c) =
      Matrix.SpecialLinearGroup.transvection
          (spIdx_ne (a := .inl i) (b := .inr j) Sum.inl_ne_inr) c *
        Matrix.SpecialLinearGroup.transvection
          (spIdx_ne (a := .inl j) (b := .inr i) Sum.inl_ne_inr) c := by
  apply Subtype.ext
  rw [coe_spToSL_elt, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe,
    transvection_mul_transvection (spIdx_ne (a := .inr j) (b := .inl j) Sum.inr_ne_inl), E,
    map_add, reindex_single, reindex_single, smul_add, Matrix.smul_single, Matrix.smul_single,
    smul_eq_mul, mul_one]
  abel

theorem spToSL_negativeSum {i j : Fin 3} (hij : i < j) (c : K) :
    spToSL K (elt (.negativeSum i j hij) c) =
      Matrix.SpecialLinearGroup.transvection
          (spIdx_ne (a := .inr i) (b := .inl j) Sum.inr_ne_inl) c *
        Matrix.SpecialLinearGroup.transvection
          (spIdx_ne (a := .inr j) (b := .inl i) Sum.inr_ne_inl) c := by
  apply Subtype.ext
  rw [coe_spToSL_elt, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe,
    transvection_mul_transvection (spIdx_ne (a := .inl j) (b := .inr j) Sum.inl_ne_inr), E,
    map_add, reindex_single, reindex_single, smul_add, Matrix.smul_single, Matrix.smul_single,
    smul_eq_mul, mul_one]
  abel

variable (K) in
theorem isSimpleGroup_statedSp_three [Finite K] [CharP K 2] : IsSimpleGroup (StatedSp 3 K) := by
  have : IsSimpleGroup (StatedSp 3 K ⧸ center (StatedSp 3 K)) :=
    (CFSG.LieType.Universal.Symplectic.isQuasisimple 3 K (by norm_num)
      F4Pilot.sp6_field_condition).2.1
  exact ((QuotientGroup.quotientMulEquivOfEq
    CFSG.Timmesfeld.LieEmbed.center_statedSp_eq_bot).trans QuotientGroup.quotientBot).symm.isSimpleGroup

theorem eq_top_of_elt_mem {S : Subgroup (StatedSp 3 K)}
    (h : ∀ (r : RootSubgroupIndex 3) (c : K), elt r c ∈ S) : S = ⊤ := by
  have htop : S.comap (equivStatedSp 3 K).toMonoidHom = ⊤ :=
    eq_top_of_root_subgroups _ fun r c => h r (Multiplicative.toAdd c)
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := (equivStatedSp 3 K).surjective x
  have hy : y ∈ S.comap (equivStatedSp 3 K).toMonoidHom := by
    rw [htop]
    exact Subgroup.mem_top y
  exact hy

variable [Finite K] [CharP K 2]

variable (K) in
@[expose] noncomputable def spToAdjointE7 : StatedSp 3 K →* adjointGroup .E7 K :=
  (slToAdjointE7 K).comp (spToSL K)

theorem spToAdjointE7_positiveLong (i : Fin 3) (c : K) :
    spToAdjointE7 K (elt (.positiveLong i) c) = e7A5Elt K (e7SpIdx (.inl i)) (e7SpIdx (.inr i)) c := by
  rw [spToAdjointE7, MonoidHom.comp_apply, spToSL_positiveLong, slToAdjointE7_transvection]

theorem spToAdjointE7_negativeLong (i : Fin 3) (c : K) :
    spToAdjointE7 K (elt (.negativeLong i) c) = e7A5Elt K (e7SpIdx (.inr i)) (e7SpIdx (.inl i)) c := by
  rw [spToAdjointE7, MonoidHom.comp_apply, spToSL_negativeLong, slToAdjointE7_transvection]

theorem spToAdjointE7_difference {i j : Fin 3} (hij : i ≠ j) (c : K) :
    spToAdjointE7 K (elt (.difference i j hij) c) =
      e7A5Elt K (e7SpIdx (.inl i)) (e7SpIdx (.inl j)) c *
        e7A5Elt K (e7SpIdx (.inr j)) (e7SpIdx (.inr i)) c := by
  rw [spToAdjointE7, MonoidHom.comp_apply, spToSL_difference, map_mul, slToAdjointE7_transvection,
    slToAdjointE7_transvection, e7A5Elt_neg]

theorem spToAdjointE7_positiveSum {i j : Fin 3} (hij : i < j) (c : K) :
    spToAdjointE7 K (elt (.positiveSum i j hij) c) =
      e7A5Elt K (e7SpIdx (.inl i)) (e7SpIdx (.inr j)) c *
        e7A5Elt K (e7SpIdx (.inl j)) (e7SpIdx (.inr i)) c := by
  rw [spToAdjointE7, MonoidHom.comp_apply, spToSL_positiveSum, map_mul, slToAdjointE7_transvection,
    slToAdjointE7_transvection]

theorem spToAdjointE7_negativeSum {i j : Fin 3} (hij : i < j) (c : K) :
    spToAdjointE7 K (elt (.negativeSum i j hij) c) =
      e7A5Elt K (e7SpIdx (.inr i)) (e7SpIdx (.inl j)) c *
        e7A5Elt K (e7SpIdx (.inr j)) (e7SpIdx (.inl i)) c := by
  rw [spToAdjointE7, MonoidHom.comp_apply, spToSL_negativeSum, map_mul, slToAdjointE7_transvection,
    slToAdjointE7_transvection]

theorem e7A5Elt_ne_one (i j : Fin 6) {c : K} (hc : c ≠ 0) : e7A5Elt K i j c ≠ 1 := by
  intro h
  have h' := congrArg Subtype.val h
  rw [coe_e7A5Elt, OneMemClass.coe_one, ← pinnedX_zero .E7 K (e7A5Root i j)] at h'
  exact hc (pinnedX_injective .E7 K _ h')

theorem spToAdjointE7_injective : Function.Injective (spToAdjointE7 K) := by
  have := isSimpleGroup_statedSp_three K
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases (spToAdjointE7 K).normal_ker.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hmem : elt (.positiveLong 0) (1 : K) ∈ (spToAdjointE7 K).ker := by
      rw [h]
      exact Subgroup.mem_top _
    rw [MonoidHom.mem_ker, spToAdjointE7_positiveLong] at hmem
    exact e7A5Elt_ne_one _ _ one_ne_zero hmem

end CFSG.SeitzReduction.E7Pilot
