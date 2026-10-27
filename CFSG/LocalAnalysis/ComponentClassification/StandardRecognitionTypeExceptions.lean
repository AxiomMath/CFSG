module

public import CFSG.Blueprint.RecognitionDefs
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearFourTwo
public import CFSG.GH74.Exceptional.UnitaryFourTwo
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix

public section

namespace CFSG.ComponentClassification.StandardRecognition

open Matrix CFSG.Assembly.LowTwoRank

theorem statedClassicalModel_of_modelsLieModel {X : Type} [Group X] {t : StatedLieTag}
    {n p f : ℕ} (hn : n ≠ 0) (h : Models.LieModel X t n p f) : StatedClassicalModel X t n p f :=
  h.2.resolve_right fun h' => hn h'.1

theorem modelsLieModel_of_statedClassicalModel {X : Type} [Group X] {t : StatedLieTag}
    {n p f : ℕ} (h : StatedClassicalModel X t n p f) : Models.LieModel X t n p f :=
  ⟨h.1, Or.inl h⟩

theorem blueprintLieModel_of_statedClassicalModel {X : Type} [Group X] {t : StatedLieTag}
    {n p f : ℕ} (ht : t ∈ Blueprint.classicalTags) (h : StatedClassicalModel X t n p f) :
    Blueprint.LieModel X t n p f :=
  Or.inl ⟨ht, h⟩

theorem statedClassicalModel_of_blueprintLieModel {X : Type} [Group X] {t : StatedLieTag}
    {n p f : ℕ} (hn : n ≠ 0) (h : Blueprint.LieModel X t n p f) :
    StatedClassicalModel X t n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero hn h

theorem nonempty_mulEquiv_alternating_five_of_lieModel (X : Type) [Group X]
    (h : Models.LieModel X .PSL 2 2 2) : Nonempty (X ≃* alternatingGroup (Fin 5)) :=
  LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model X
    (blueprintLieModel_of_statedClassicalModel (by decide)
      (statedClassicalModel_of_modelsLieModel (by decide) h))

theorem lieModel_PSL_two_seven_of_lieModel_PSL_three_two (X : Type) [Group X]
    (h : Models.LieModel X .PSL 3 2 1) : Models.LieModel X .PSL 2 7 1 :=
  modelsLieModel_of_statedClassicalModel (statedClassicalModel_of_blueprintLieModel (by decide)
    (LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism X
      (blueprintLieModel_of_statedClassicalModel (by decide)
        (statedClassicalModel_of_modelsLieModel (by decide) h))))

theorem nonempty_mulEquiv_alternating_eight_of_lieModel (X : Type) [Group X]
    (h : Models.LieModel X .PSL 4 2 1) : Nonempty (X ≃* alternatingGroup (Fin 8)) :=
  (SymmetricLocal.lie_model_linear_four_two_iff X).1
    (blueprintLieModel_of_statedClassicalModel (by decide)
      (statedClassicalModel_of_modelsLieModel (by decide) h))

theorem lieModel_PSp_two_three_of_lieModel_PSU_four_two (X : Type) [Group X]
    (h : Models.LieModel X .PSU 4 2 1) : Models.LieModel X .PSp 2 3 1 :=
  modelsLieModel_of_statedClassicalModel
    (GH74.Exceptional.statedClassicalModel_PSp_two_three_of_PSU_four_two
      (statedClassicalModel_of_modelsLieModel (by decide) h))

theorem lieModel_PSU_three_three_of_nonempty_mulEquiv (X : Type) [Group X]
    (h : Nonempty (X ≃* StatedProj (StatedSU 3 3 (GaloisField 3 2)))) :
    Models.LieModel X .PSU 3 3 1 :=
  modelsLieModel_of_statedClassicalModel ⟨⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩,
    GaloisField 3 2, inferInstance, inferInstance, GaloisField.card 3 2 two_ne_zero, h⟩

@[expose] def symplecticIndex : Fin 2 ⊕ Fin 2 ≃ Fin 4 where
  toFun := Sum.elim ![0, 1] ![3, 2]
  invFun := ![.inl 0, .inl 1, .inr 1, .inr 0]
  left_inv := by decide
  right_inv := by decide

theorem reindex_J :
    reindex symplecticIndex symplecticIndex (J (Fin 2) (ZMod 2)) =
      PresentationLocal.antidiagGram := by
  decide

@[expose] noncomputable def symplecticReindex :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2) ≃* Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  (reindexAlgEquiv (ZMod 2) (ZMod 2) symplecticIndex).toMulEquiv

theorem symplecticReindex_apply (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) :
    symplecticReindex A = reindex symplecticIndex symplecticIndex A :=
  rfl

theorem mem_symplecticGroup_iff_reindex (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) :
    A ∈ symplecticGroup (Fin 2) (ZMod 2) ↔
      (reindex symplecticIndex symplecticIndex A)ᵀ * PresentationLocal.antidiagGram *
        reindex symplecticIndex symplecticIndex A = PresentationLocal.antidiagGram := by
  rw [SymplecticGroup.mem_iff', ← reindex_J, transpose_reindex]
  simp only [← symplecticReindex_apply, ← map_mul, symplecticReindex.injective.eq_iff]

@[expose] noncomputable def symplecticToGL :
    symplecticGroup (Fin 2) (ZMod 2) →* GL (Fin 4) (ZMod 2) :=
  (Units.map symplecticReindex.toMonoidHom).comp
    (symplecticGroup (Fin 2) (ZMod 2)).subtype.toHomUnits

@[expose] noncomputable def symplecticToSympFour :
    symplecticGroup (Fin 2) (ZMod 2) →* PresentationLocal.sympFour :=
  symplecticToGL.codRestrict _ fun A => (mem_symplecticGroup_iff_reindex A).1 A.2

theorem symplecticToSympFour_bijective : Function.Bijective symplecticToSympFour := by
  refine ⟨fun A B h => ?_, fun h => ?_⟩
  · have h' := congrArg (fun g : PresentationLocal.sympFour =>
      ((g : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))) h
    exact Subtype.ext ((reindex symplecticIndex symplecticIndex).injective h')
  · have hmem : reindex symplecticIndex.symm symplecticIndex.symm
        ((h : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) ∈
          symplecticGroup (Fin 2) (ZMod 2) := by
      rw [mem_symplecticGroup_iff_reindex, ← reindex_symm, Equiv.apply_symm_apply]
      exact h.2
    refine ⟨⟨_, hmem⟩, Subtype.ext (Units.ext ?_)⟩
    change reindex symplecticIndex symplecticIndex (reindex symplecticIndex.symm
      symplecticIndex.symm _) = _
    rw [← reindex_symm, Equiv.apply_symm_apply]

theorem map_commutator_symplecticToSympFour :
    (commutator (symplecticGroup (Fin 2) (ZMod 2))).map symplecticToSympFour =
      commutator PresentationLocal.sympFour := by
  rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.2 symplecticToSympFour_bijective.2]

@[expose] noncomputable def symplecticCommutatorEquivAlternating :
    commutator (symplecticGroup (Fin 2) (ZMod 2)) ≃* alternatingGroup (Fin 6) :=
  (((MulEquiv.ofBijective symplecticToSympFour symplecticToSympFour_bijective).subgroupMap
    (commutator (symplecticGroup (Fin 2) (ZMod 2)))).trans
      (MulEquiv.subgroupCongr map_commutator_symplecticToSympFour)).trans
    PresentationLocal.commutatorEquivAlternating

theorem nonempty_mulEquiv_alternating_six_of_symplectic (X : Type) [Group X]
    (h : Nonempty (X ≃* commutator (symplecticGroup (Fin 2) (ZMod 2)))) :
    Nonempty (X ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨e⟩ := h
  exact ⟨e.trans symplecticCommutatorEquivAlternating⟩

theorem even_exceptions_odd_type (X : Type) [Group X]
    (h : Blueprint.Recognition.EvenStandardException X) :
    Blueprint.Recognition.OddStandardType X := by
  rcases h with h | h | h | h | h | h | h | h
  · exact Or.inl ⟨5, le_rfl, nonempty_mulEquiv_alternating_five_of_lieModel X h⟩
  · exact Or.inr (Or.inl ⟨.PSL, 2, 7, 1, by decide,
      lieModel_PSL_two_seven_of_lieModel_PSL_three_two X h⟩)
  · exact Or.inl ⟨8, by norm_num, nonempty_mulEquiv_alternating_eight_of_lieModel X h⟩
  · exact Or.inl ⟨6, by norm_num, nonempty_mulEquiv_alternating_six_of_symplectic X h⟩
  · exact Or.inr (Or.inl ⟨.PSU, 3, 3, 1, by decide,
      lieModel_PSU_three_three_of_nonempty_mulEquiv X h⟩)
  · exact Or.inr (Or.inl ⟨.PSp, 2, 3, 1, by decide,
      lieModel_PSp_two_three_of_lieModel_PSU_four_two X h⟩)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

end CFSG.ComponentClassification.StandardRecognition
