module

public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
public import CFSG.Open.StatedZModTwo
public import CFSG.RankThree.PartTwo.Sec19.SimsItem316SmallModels
public import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCOmegaBridge
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.GLTheoremB.UniqDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.TitsIso

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Omega2401

open CFSG.Open

@[expose] def twoPP : TauCeti.PrimePower := ⟨2, 1, Nat.prime_two, Nat.one_pos⟩

theorem valid_D_of_four_le {n : ℕ} (hn : 4 ≤ n) (q : TauCeti.PrimePower) :
    (TauCeti.LieTypeIndex.D n q).Valid := by
  refine (TauCeti.LieTypeIndex.valid_iff _).mpr
    ⟨(TauCeti.LieTypeIndex.inStandardRange_iff _).mpr hn, ?_⟩
  simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]

theorem valid_twistedD_of_four_le {n : ℕ} (hn : 4 ≤ n) (q : TauCeti.PrimePower) :
    (TauCeti.LieTypeIndex.twistedD n q).Valid := by
  refine (TauCeti.LieTypeIndex.valid_iff _).mpr
    ⟨(TauCeti.LieTypeIndex.inStandardRange_iff _).mpr hn, ?_⟩
  simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]

theorem valid_twistedA_three_two : (TauCeti.LieTypeIndex.twistedA 3 twoPP).Valid := by
  refine (TauCeti.LieTypeIndex.valid_iff _).mpr ⟨?_, ?_⟩
  · rw [TauCeti.LieTypeIndex.inStandardRange_iff]
    exact ⟨by norm_num, fun hr => absurd hr (by norm_num)⟩
  · simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]

theorem nonempty_statedProj_equiv_of_bot {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] (H : Subgroup (GL ι K))
    (hbot : (StatedScalars ι K).subgroupOf H = ⊥) : Nonempty (StatedProj H ≃* H) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot⟩

theorem nonempty_statedProj_equiv_of_card_two {K : Type} [Field K] (hK : Nat.card K = 2)
    (ι : Type) [Fintype ι] [DecidableEq ι] (H : Subgroup (GL ι K)) :
    Nonempty (StatedProj H ≃* H) := by
  apply nonempty_statedProj_equiv_of_bot H
  rw [CFSG.Open.StatedAPI.statedScalars_eq_bot_of_card_two hK ι]
  ext x
  simp [Subgroup.mem_subgroupOf]

theorem nonempty_ringEquiv_zmod_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nonempty (K ≃+* ZMod 2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  exact ⟨(CFSG.ClassicalModels.finiteFieldEquivGaloisField K 2 1 Nat.one_pos h1).trans
    (GaloisField.equivZmodP 2).toRingEquiv⟩

theorem eq_one_of_irreducible_zmod_two (B C : ZMod 2)
    (h : ∀ s : ZMod 2, s ^ 2 + B * s + C ≠ 0) : B = 1 ∧ C = 1 := by
  revert B C
  decide

theorem nonempty_statedProj_of_isOmegaTwo_true {n : ℕ} {L : Type} [Group L]
    (h : CFSG.LocalAnalysis.GLTheoremB.IsOmegaTwo true n L) :
    Nonempty (L ≃* StatedProj (StatedOmega (StatedQuadPlus n (ZMod 2)))) := by
  obtain ⟨e0⟩ := h
  obtain ⟨eS⟩ := nonempty_statedProj_equiv_of_card_two (K := ZMod 2) (Nat.card_zmod 2)
    (Fin n ⊕ Fin n) (StatedOmega (StatedQuadPlus n (ZMod 2)))
  exact ⟨e0.trans eS.symm⟩

theorem nonempty_statedProj_of_isOmegaTwo_false {n : ℕ} {L : Type} [Group L]
    (h : CFSG.LocalAnalysis.GLTheoremB.IsOmegaTwo false n L) :
    Nonempty (L ≃* StatedProj (StatedOmega (StatedQuadMinus n (ZMod 2) 1 1))) := by
  obtain ⟨e0⟩ := h
  obtain ⟨eS⟩ := nonempty_statedProj_equiv_of_card_two (K := ZMod 2) (Nat.card_zmod 2)
    (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (StatedOmega (StatedQuadMinus n (ZMod 2) 1 1))
  exact ⟨e0.trans eS.symm⟩

theorem nonempty_D_of_isOmegaTwo_true {n : ℕ} (hn : 4 ≤ n) {L : Type} [Group L]
    (h : CFSG.LocalAnalysis.GLTheoremB.IsOmegaTwo true n L) :
    Nonempty (L ≃* TauCeti.ValidLieTypeIndex.Group ⟨.D n twoPP, valid_D_of_four_le hn twoPP⟩) := by
  obtain ⟨eL⟩ := nonempty_statedProj_of_isOmegaTwo_true h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eD⟩ := CFSG.RankThree.PartTwo.Census.Carrier.SpinD.nonempty_typeDGroupEquivProjOmegaPlus
    n 1 twoPP (valid_D_of_four_le hn twoPP) rfl rfl
  let φ : ZMod 2 ≃+* GaloisField 2 1 := (GaloisField.equivZmodP 2).toRingEquiv.symm
  let eT := CFSG.RankThree.PartOne.statedProjEquivOfGLEquiv
    (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin n ⊕ Fin n) φ)
    (CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.statedQuadPlus_comp φ n))
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)
    (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.projImage_statedOmegaPlus_eq_projOmegaPlus n
      (GaloisField 2 1))
  exact ⟨eL.trans (eT.trans eD.symm)⟩

theorem nonempty_twistedD_of_isOmegaTwo_false {n : ℕ} (hn : 4 ≤ n) {L : Type} [Group L]
    (h : CFSG.LocalAnalysis.GLTheoremB.IsOmegaTwo false n L) :
    Nonempty (L ≃* TauCeti.ValidLieTypeIndex.Group
      ⟨.twistedD n twoPP, valid_twistedD_of_four_le hn twoPP⟩) := by
  obtain ⟨eL⟩ := nonempty_statedProj_of_isOmegaTwo_false h
  have hv := valid_twistedD_of_four_le hn twoPP
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.twistedD n twoPP, hv⟩
  obtain ⟨b, c, hbc, ⟨eD⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj n
      twoPP hv rfl
  have hF : Nat.card (TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD n twoPP, hv⟩) = 2 := by
    rw [TauCeti.ValidLieTypeIndex.card_fixedField]
    simp [TauCeti.ValidLieTypeIndex.fieldOrder, twoPP]
  obtain ⟨φ⟩ := nonempty_ringEquiv_zmod_two hF
  obtain ⟨hb, hc⟩ := eq_one_of_irreducible_zmod_two (φ b) (φ c)
    (CFSG.ClassicalInvolution.Upgrade.irreducible_map φ hbc)
  let eT := CFSG.Adapters.RankTwoModelTransports.statedProjCongr
    (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
    (CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
      (CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp (n := n) φ hb hc))
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)
  exact ⟨eL.trans (eT.symm.trans eD.symm)⟩

theorem two_le_pRank_three_of_plus {n : ℕ} (hn : 4 ≤ n) {L : Type} [Group L] [Finite L]
    (e : L ≃* StatedProj (StatedOmega (StatedQuadPlus n (ZMod 2)))) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  have h := CFSG.SectionRank.ClassicalEven.omegaPlus_three_le_pRank_three (K := ZMod 2) hn
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
  omega

theorem two_le_pRank_three_of_minus {n : ℕ} (hn : 4 ≤ n) {L : Type} [Group L] [Finite L]
    (e : L ≃* StatedProj (StatedOmega (StatedQuadMinus n (ZMod 2) 1 1))) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
  have h := CFSG.SectionRank.ClassicalEven.omegaMinus_three_le_pRank_three (K := ZMod 2) hn 1 1
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
  omega

theorem nonempty_alt_eight_of_isOmegaTwo_true_three {L : Type} [Group L]
    (h : CFSG.LocalAnalysis.GLTheoremB.IsOmegaTwo true 3 L) :
    Nonempty (L ≃* alternatingGroup (Fin 8)) := by
  obtain ⟨e0⟩ := h
  obtain ⟨φ, -, -⟩ := CFSG.RankThree.PartTwo.Sec19.SimsItem316Small.omegaPlusTwo_three_model
  exact ⟨e0.trans ((MulEquiv.subgroupCongr
    (CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.omegaPlusTwo_eq_statedOmega 3)).symm.trans φ)⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Omega2401

end
