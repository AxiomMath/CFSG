module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddL3AutFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearHigherBIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
open CFSG.ComponentClassification
open scoped MatrixGroups

section Card

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem card_rootsOfUnity_two (h2 : (2 : F) ≠ 0) : Nat.card (rootsOfUnity 2 F) = 2 := by
  have hneg : (-1 : Fˣ) ∈ rootsOfUnity 2 F := by
    rw [mem_rootsOfUnity]
    norm_num
  rw [Nat.card_eq_two_iff]
  refine ⟨1, ⟨-1, hneg⟩, ?_, ?_⟩
  · intro h
    have h1 : (1 : Fˣ) = -1 := congrArg Subtype.val h
    have h1' : (1 : F) = -1 := by simpa using congrArg Units.val h1
    exact h2 (by linear_combination h1')
  · ext u
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    have hu : (u : Fˣ) ^ 2 = 1 := (mem_rootsOfUnity 2 (u : Fˣ)).1 u.2
    have hu' : ((u : Fˣ) : F) * ((u : Fˣ) : F) = 1 := by
      have := congrArg Units.val hu
      simpa [sq] using this
    rcases mul_self_eq_one_iff.1 hu' with h | h
    · left
      exact Subtype.ext (Units.ext (by simpa using h))
    · right
      exact Subtype.ext (Units.ext (by simpa using h))

theorem card_isometryGroup_three (hodd : ringChar F ≠ 2) (R : GL (Fin 3) F)
    (hR : (R : Matrix (Fin 3) (Fin 3) F)ᵀ = R) :
    Nat.card (CatalogueBGraphForm.isometryGroup 3 F R) =
      2 * (Nat.card F * (Nat.card F ^ 2 - 1)) := by
  have hodd' : Odd (Nat.card F) := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two F hodd
  have hnd := CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hodd R hR
  obtain ⟨d, psi, e, -⟩ :=
    CatalogueBOrthogonalThreeSimilarity.finite_odd_orthogonal_three_trace_zero_similarity hodd'
      (CatalogueBLinearHigherB.matrixQuadraticForm R) hnd (by rw [Module.finrank_fin_fun])
  obtain ⟨e', -⟩ := CatalogueBOrthogonal.trace_zero_three_full_orthogonal_isometry (K := F)
    (Ring.two_ne_zero hodd)
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hodd
  have hc1 : Nat.card (CatalogueBGraphForm.isometryGroup 3 F R) =
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup
        (CatalogueBLinearHigherB.matrixQuadraticForm R)) := by
    rw [CatalogueBLinearHigherB.orthogonalGroup_matrixQuadraticForm hodd R hR]
    exact (Nat.card_congr (CatalogueBLinearHigherB.isometryGroupEquiv R).toEquiv).symm
  rw [hc1, Nat.card_congr e.toEquiv, ← Nat.card_congr e'.toEquiv, Nat.card_prod,
    Nat.card_congr (CatalogueBLinearTwo.pglEquivCoordinateD_all_fields F).toEquiv.symm,
    card_rootsOfUnity_two h2, CFSG.GorensteinWalter.pgl2_card_formula]
  ring

omit [Finite F] in
theorem eq_one_or_eq_neg_one_of_sq_eq_one (u : Fˣ) (hu : u ^ 2 = 1) : u = 1 ∨ u = -1 := by
  have hu' : (u : F) * (u : F) = 1 := by
    have := congrArg Units.val hu
    simpa [sq] using this
  rcases mul_self_eq_one_iff.1 hu' with h | h
  · left
    exact Units.ext (by simpa using h)
  · right
    exact Units.ext (by simpa using h)

omit [Finite F] in
theorem card_soForm_mul_two (hodd : ringChar F ≠ 2) (R : GL (Fin 3) F) :
    Nat.card (soForm (R : Matrix (Fin 3) (Fin 3) F)) * 2 =
      Nat.card (CatalogueBGraphForm.isometryGroup 3 F R) := by
  classical
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hodd
  set J := CatalogueBGraphForm.isometryGroup 3 F R with hJ
  let d : J →* Fˣ := (Matrix.GeneralLinearGroup.det).comp J.subtype
  have hdR : ((R : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det ≠ 0 :=
    (Matrix.isUnits_det_units R).ne_zero
  have hsq : ∀ g : J, (d g) ^ 2 = 1 := by
    intro g
    have h1 := (CatalogueBGraphForm.mem_isometryGroup 3 F R g).1 g.2
    have h3 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h3
    apply Units.ext
    have h4 : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det *
        ((R : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det *
        ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det =
        ((R : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det := h3
    have h5 : (((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det ^ 2 - 1) *
        ((R : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 0 := by linear_combination h4
    have h6 := (mul_eq_zero.1 h5).resolve_right hdR
    change ((Matrix.GeneralLinearGroup.det (g : GL (Fin 3) F) : Fˣ) : F) ^ 2 = 1
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    linear_combination h6
  have hneg : (-1 : GL (Fin 3) F) ∈ J := by
    rw [hJ, CatalogueBGraphForm.mem_isometryGroup]
    simp
  have hrange : d.range = rootsOfUnity 2 F := by
    ext u
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨g, rfl⟩
      exact (mem_rootsOfUnity 2 _).2 (hsq g)
    · intro hu
      rcases eq_one_or_eq_neg_one_of_sq_eq_one u ((mem_rootsOfUnity 2 u).1 hu) with rfl | rfl
      · exact ⟨1, map_one d⟩
      · refine ⟨⟨-1, hneg⟩, ?_⟩
        apply Units.ext
        change ((Matrix.GeneralLinearGroup.det (-1 : GL (Fin 3) F) : Fˣ) : F) = ((-1 : Fˣ) : F)
        rw [Matrix.GeneralLinearGroup.val_det_apply]
        simp [Matrix.det_neg]
        norm_num
  have hidx : d.ker.index = 2 := by
    rw [Subgroup.index_ker, hrange]
    exact card_rootsOfUnity_two h2
  have hmem : ∀ y : soForm (R : Matrix (Fin 3) (Fin 3) F),
      Matrix.SpecialLinearGroup.toGL (y : SL(3, F)) ∈ J := by
    intro y
    rw [hJ, CatalogueBGraphForm.mem_isometryGroup]
    exact y.2
  have hdet1 : ∀ y : soForm (R : Matrix (Fin 3) (Fin 3) F),
      d ⟨Matrix.SpecialLinearGroup.toGL (y : SL(3, F)), hmem y⟩ = 1 := by
    intro y
    apply Units.ext
    change ((Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL (y : SL(3, F))) : Fˣ) :
      F) = 1
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact (y : SL(3, F)).2
  have hker : Nat.card (soForm (R : Matrix (Fin 3) (Fin 3) F)) = Nat.card d.ker := by
    refine Nat.card_eq_of_bijective
      (fun y => ⟨⟨Matrix.SpecialLinearGroup.toGL (y : SL(3, F)), hmem y⟩, hdet1 y⟩) ⟨?_, ?_⟩
    · intro y z hyz
      have h1 := congrArg (fun w : d.ker => ((w : J) : GL (Fin 3) F)) hyz
      exact Subtype.ext (Matrix.SpecialLinearGroup.toGL_injective h1)
    · rintro ⟨⟨g, hgJ⟩, hk⟩
      have hdg : (g : Matrix (Fin 3) (Fin 3) F).det = 1 := by
        have := congrArg Units.val (MonoidHom.mem_ker.1 hk)
        simpa [d, Matrix.GeneralLinearGroup.val_det_apply] using this
      have hg : (g : Matrix (Fin 3) (Fin 3) F)ᵀ * (R : Matrix (Fin 3) (Fin 3) F) *
          (g : Matrix (Fin 3) (Fin 3) F) = R := (CatalogueBGraphForm.mem_isometryGroup 3 F R g).1 hgJ
      refine ⟨⟨⟨(g : Matrix (Fin 3) (Fin 3) F), hdg⟩, hg⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact Units.ext rfl
  rw [hker, ← hidx]
  exact Subgroup.card_mul_index d.ker

theorem card_soForm (hodd : ringChar F ≠ 2) (R : GL (Fin 3) F)
    (hR : (R : Matrix (Fin 3) (Fin 3) F)ᵀ = R) :
    Nat.card (soForm (R : Matrix (Fin 3) (Fin 3) F)) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  have h1 := card_soForm_mul_two hodd R
  have h2 := card_isometryGroup_three hodd R hR
  omega

end Card

end CFSG.QuasithinUnique.Ch1
