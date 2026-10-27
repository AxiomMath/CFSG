module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.Engine
public import CFSG.Adapters.ClassicalCatalogReverse
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionTypeExceptions
import CFSG.Monster.Existence.Compat.Sp8

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding TauCeti CFSG.Adapters.RankTwoModelTransports


theorem isClassicalTwoOrG2_of_fixedField_model {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : (K : Type) → [Field K] → Subgroup (GL ι K))
    (hH : ∀ {K L : Type} [Field K] [Field L] (φ : K ≃+* L),
      (H K).map (glCongr φ).toMonoidHom = H L)
    (d : ValidLieTypeIndex) (hd : IsClassicalOrG2Index d.1)
    (eT : d.Group ≃* StatedProj (H ↥d.fixedField))
    {G : Type} [Group G] {K : Type} [Field K] [Finite K] (hK : Nat.card K = d.fieldOrder)
    (θ : G ≃* StatedProj (H K)) : IsClassicalTwoOrG2 G := by
  obtain ⟨φ⟩ := CFSG.ClassicalModels.nonempty_ringEquiv_validIndex_fixedField d K hK
  exact Or.inl ⟨d, hd, ⟨(θ.trans (statedProjCongr (glCongr φ) (hH φ) (glCongr_statedScalars φ))).trans
    eT.symm⟩⟩

theorem isClassicalTwoOrG2_of_statedPSp {G : Type} [Group G] {k f : ℕ}
    (h : StatedClassicalModel G .PSp k 2 f) (hk : 3 ≤ k ∨ (k = 2 ∧ 4 ≤ 2 ^ f)) :
    IsClassicalTwoOrG2 G := by
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨θ⟩⟩ := h
  let _ := hfield
  let _ := hfinite
  let q : PrimePower := ⟨2, f, hadm.1, by have := hadm.2.1; omega⟩
  rcases hk with hk3 | ⟨rfl, h4⟩
  · have hv : (LieTypeIndex.B k q).Valid := by
      rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
        LieTypeIndex.isDuplicateRepresentative_iff]
      exact ⟨⟨by omega, fun h => by omega⟩, fun h => by omega⟩
    exact isClassicalTwoOrG2_of_fixedField_model (fun K _ => StatedSp k K)
      (fun φ => CFSG.ClassicalInvolution.Upgrade.glCongr_statedSp φ k) ⟨.B k q, hv⟩ rfl
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj k q hv rfl hk3)
      (by simp [ValidLieTypeIndex.fieldOrder, q, hK]) θ
  · have hv : (LieTypeIndex.B 2 q).Valid := by
      rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
        LieTypeIndex.isDuplicateRepresentative_iff]
      simp only [PrimePower.card_def, q]
      exact ⟨⟨by omega, by omega⟩, fun h => by omega⟩
    exact isClassicalTwoOrG2_of_fixedField_model (fun K _ => StatedSp 2 K)
      (fun φ => CFSG.ClassicalInvolution.Upgrade.glCongr_statedSp φ 2) ⟨.B 2 q, hv⟩ rfl
      (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv)
      (by simp [ValidLieTypeIndex.fieldOrder, q, hK]) θ


open CFSG.Quasithin.SmithC27 in
theorem center_sp_eq_bot {n : ℕ} {F : Type} [Field F] [CharP F 2] :
    Subgroup.center (StatedSp n F) = ⊥ := by
  rw [CFSG.LieType.Universal.Symplectic.center_eq,
    CFSG.Timmesfeld.ClassicalOrders.statedScalars_subgroupOf_statedSp_eq_bot]

open CFSG.Quasithin.SmithC27 in
theorem isChevComponent_sp {k : ℕ} {F : Type} [Field F] [Finite F]
    [CharP F 2] (hk : 3 ≤ k ∨ (k = 2 ∧ 4 ≤ Nat.card F)) :
    CFSG.IsQuasisimple (StatedSp k F) ∧
      IsClassicalTwoOrG2 (StatedSp k F ⧸ Subgroup.center (StatedSp k F)) := by
  obtain ⟨f, hf1, hfcard⟩ := CFSG.AGLEmbedding.ParabHub.exists_card_eq_two_pow F
  have hk2 : 2 ≤ k := by omega
  have hadm : StatedLieAdmissible .PSp k 2 f := by
    refine ⟨Nat.prime_two, hf1, hk2, ?_⟩
    intro h
    have h1 : k = 2 := (Prod.mk.inj h).1
    have h2 : 2 ^ f = 2 := (Prod.mk.inj h).2
    rcases hk with hk3 | ⟨-, hF4⟩
    · omega
    · rw [hfcard] at hF4; omega
  refine ⟨CFSG.LieType.Universal.Symplectic.isQuasisimple_of_admissible k F hadm hfcard, ?_⟩
  refine isClassicalTwoOrG2_of_statedPSp
    (CFSG.LieType.Universal.Symplectic.statedClassicalModel_center_quotient k F hadm hfcard) ?_
  rcases hk with hk3 | ⟨hk2', hF4⟩
  · exact Or.inl hk3
  · exact Or.inr ⟨hk2', by rw [← hfcard]; exact hF4⟩

open CFSG.Quasithin.SmithC27 in
theorem isChevComponent_sp_one {F : Type} [Field F] [Finite F]
    [CharP F 2] (hF : 4 ≤ Nat.card F) :
    CFSG.IsQuasisimple (StatedSp 1 F) ∧
      IsClassicalTwoOrG2 (StatedSp 1 F ⧸ Subgroup.center (StatedSp 1 F)) := by
  obtain ⟨h1, h2⟩ := isChevComponent_sl (F := F) (k := 2) (Or.inr ⟨rfl, hF⟩)
  let e : Matrix.SpecialLinearGroup (Fin 2) F ≃* StatedSp 1 F :=
    CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne F
  exact ⟨isQuasisimple_of_mulEquiv e h1, isClassicalTwoOrG2_of_mulEquiv (quotCenterCongr e) h2⟩


open CFSG.Quasithin.SmithC27 in
theorem isChevComponent_comm_sp_four_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    CFSG.IsQuasisimple ↥(commutator (StatedSp 2 K)) ∧
      IsClassicalTwoOrG2 (↥(commutator (StatedSp 2 K)) ⧸
        Subgroup.center ↥(commutator (StatedSp 2 K))) := by
  let e : StatedSp 2 K ≃* CFSG.ComponentClassification.PresentationLocal.sympFour :=
    (CFSG.Monster.Existence.Compat.statedSpEquiv 2 K).trans
      ((CFSG.Monster.Existence.Compat.sympMapEquiv
        (CFSG.Monster.Existence.Compat.ringEquivZMod2 hK)).trans
        (MulEquiv.ofBijective CFSG.ComponentClassification.StandardRecognition.symplecticToSympFour
          CFSG.ComponentClassification.StandardRecognition.symplecticToSympFour_bijective))
  have hmap : (commutator (StatedSp 2 K)).map e.toMonoidHom = commutator _ := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr e.surjective]
  let e6 : commutator (StatedSp 2 K) ≃* alternatingGroup (Fin 6) :=
    (e.subgroupMap _).trans ((MulEquiv.subgroupCongr hmap).trans
      CFSG.ComponentClassification.PresentationLocal.commutatorEquivAlternating)
  have h6 : 5 ≤ Nat.card (Fin 6) := by simp
  have hA0 := CFSG.ComponentClassification.CatalogueBAlternating.alternating_quasisimple h6
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup h6
  have hperf : Group.IsPerfect (alternatingGroup (Fin 6)) := Group.isPerfect_def.mpr hA0.1
  have hnt : Nontrivial (alternatingGroup (Fin 6)) := hsimple.toNontrivial
  have hnc : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact Group.IsPerfect.not_isMulCommutative (alternatingGroup (Fin 6)) ⟨⟨fun a b => h a b⟩⟩
  have hA : CFSG.IsQuasisimple (alternatingGroup (Fin 6)) := isQuasisimple_of_simple hsimple hnc
  have hZ : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
    center_eq_bot_of_quasisimple_simple hA
  refine ⟨isQuasisimple_of_mulEquiv e6.symm hA, ?_⟩
  have e1 := quotCenterCongr e6
  have e2 : alternatingGroup (Fin 6) ⧸ Subgroup.center (alternatingGroup (Fin 6)) ≃*
      alternatingGroup (Fin 6) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact isClassicalTwoOrG2_of_mulEquiv (e1.trans e2).symm
    (Or.inr (Or.inl ⟨6, Or.inr (Or.inl rfl), ⟨MulEquiv.refl _⟩⟩))

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
