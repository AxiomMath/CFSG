module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K148DownFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM6Quot
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieG2
public import CFSG.GH74.KGroups.U33
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09TD4G2A

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open scoped commutatorElement
open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.Blueprint.Chevalley (TwistTag Tag adjointGroup)
open CFSG.LieType.Chevalley (fieldActor fixSubfield ringEquiv_cube_apply_eq trialityFieldImage)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3 (fixSubgroupFieldActorEquiv)
open CFSG.HardMathSupport.Seitz.TrialityOdd.Inner (trialityFieldImageEquivRoot)


private def sfm6Pp3 : TauCeti.PrimePower := ⟨3, 1, Nat.prime_three, Nat.one_pos⟩

private theorem sfm6Pp3_card : sfm6Pp3.card = 3 := by
  rw [TauCeti.PrimePower.card_def]
  rfl

private theorem sfm6Valid_tw23 : (TauCeti.LieTypeIndex.twistedA 2 sfm6Pp3).Valid := by
  rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
  simp [sfm6Pp3]

variable {K : Type} [Field K] [Finite K]

noncomputable def sfm6TrialityFieldImageEquivG2 (σ : K ≃+* K) (h2 : (2 : fixSubfield σ) = 0) :
    ↥(trialityFieldImage σ σ) ≃* ↥(adjointGroup Tag.G2 (fixSubfield σ)) :=
  (trialityFieldImageEquivRoot σ).trans
    ((MulEquiv.subgroupCongr
      (CFSG.RankThree.PartTwo.KFacts.d4_twistedFixedGroup_id_eq_graphFixedRootGroup (K := fixSubfield σ))).symm.trans
      (CFSG.RankThree.PartTwo.KFacts.d4FixedG2Equiv (fixSubfield σ) h2))

private theorem sfm6_two_eq_zero {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2) :
    (2 : k) = 0 := by
  have : Fintype k := Fintype.ofFinite k
  have h := card_nsmul_eq_zero (G := k) (x := 1)
  rw [← Nat.card_eq_fintype_card, hk] at h
  simpa using h

theorem K148TwoG2Fact_holds : K148TwoG2Fact := by
  intro K _ _ σ hK hσ H _ e S hS Q _ φ hφ hQ
  have hK' : Nat.card K = 2 ^ 3 := by rw [hK]; norm_num
  have hσ3 : ∀ c, σ (σ (σ c)) = c := ringEquiv_cube_apply_eq hK hσ
  have hσ3' : σ ^ 3 = 1 := td4g2_sigma_cube hK hσ
  have hσ1 : σ ≠ 1 := td4g2_frob_ne_one Nat.prime_two le_rfl hK hσ
  have hord : orderOf σ = 3 := orderOf_eq_prime hσ3' hσ1
  have hF : Nat.card (fixSubfield σ) = 2 := by
    obtain ⟨-, hc⟩ :=
      CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two (by norm_num) hK' σ
    rw [hord] at hc
    simpa using hc
  have h2 : (2 : fixSubfield σ) = 0 := sfm6_two_eq_zero hF
  have hfix : CFSG.RankThree.PartTwo.Sec4.autFix (fieldActor (t := TwistTag.D4) σ σ) =
      fixSubgroup (fieldActor (t := TwistTag.D4) σ σ) := Subgroup.ext fun _ => Iff.rfl
  let e3 : H ≃* ↥(adjointGroup Tag.G2 (fixSubfield σ)) :=
    e.trans ((MulEquiv.subgroupCongr hfix).trans
      ((fixSubgroupFieldActorEquiv K σ hσ3).trans (sfm6TrialityFieldImageEquivG2 σ h2)))
  have hsimple := (CFSG.QuasithinUnique.Id2519.g2Two_derived hF).1
  haveI := hsimple
  have hS' : (S.map e3.toMonoidHom).IsSubnormal :=
    Subgroup.IsSubnormal.map (f := e3.toMonoidHom) e3.surjective hS
  let eS := Subgroup.equivMapOfInjective S e3.toMonoidHom e3.injective
  let φ' : ↥(S.map e3.toMonoidHom) →* Q := φ.comp eS.symm.toMonoidHom
  have hφ' : Function.Surjective φ' := hφ.comp eS.symm.surjective
  obtain ⟨eQ⟩ := CFSG.LocalAnalysis.GLTheoremA.CatA.SFM6.nonempty_mulEquiv_of_isSubnormal
    (D := commutator ↥(adjointGroup Tag.G2 (fixSubfield σ))) le_rfl hS' φ' hφ' hQ
  have hDM : (commutator ↥(adjointGroup Tag.G2 (fixSubfield σ))).map
      (adjointGroup Tag.G2 (fixSubfield σ)).subtype =
      ⁅adjointGroup Tag.G2 (fixSubfield σ), adjointGroup Tag.G2 (fixSubfield σ)⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  let eD : ↥(commutator ↥(adjointGroup Tag.G2 (fixSubfield σ))) ≃*
      ↥⁅adjointGroup Tag.G2 (fixSubfield σ), adjointGroup Tag.G2 (fixSubfield σ)⁆ :=
    ((commutator ↥(adjointGroup Tag.G2 (fixSubfield σ))).equivMapOfInjective _
      (adjointGroup Tag.G2 (fixSubfield σ)).subtype_injective).trans (MulEquiv.subgroupCongr hDM)
  obtain ⟨eU⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel
    (CFSG.Quasithin.EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds (fixSubfield σ) hF)
  have hT0 : CFSG.Blueprint.LieModel
      (TauCeti.CFSGIndex.lie ⟨.twistedA 2 sfm6Pp3, sfm6Valid_tw23⟩).Group .PSU 3 3 1 :=
    Or.inl ⟨by simp [CFSG.Blueprint.classicalTags],
      CFSG.StandardType.ChevTwo.statedClassicalModel_psu_three_three_of_twistedA_two sfm6Pp3
        sfm6Valid_tw23 sfm6Pp3_card (MulEquiv.refl _)⟩
  obtain ⟨eT⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel hT0
  exact ⟨TauCeti.CFSGIndex.lie ⟨.twistedA 2 sfm6Pp3, sfm6Valid_tw23⟩, sfm6Pp3_card,
    ⟨eQ.trans (eD.trans (eU.trans eT.symm))⟩⟩

end CFSG.LocalAnalysis.GLTheoremA

end
