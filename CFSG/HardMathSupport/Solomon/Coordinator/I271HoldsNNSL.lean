module

public import CFSG.HardMathSupport.Solomon.Coordinator.I271TwistPlane
public import CFSG.HardMathSupport.Solomon.Coordinator.I271TwistRel
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsNNFacts
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsNNL34
public import CFSG.LieType.SeitzGeneration.ClassicalSeitzStatus
public import CFSG.LocalAnalysis.GLTheoremA.PartI.ExcBridge
import CFSG.Quasithin.Background.GoldschmidtListedSolv
import CFSG.ClassicalInvolution.PerfectCase.Basic
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index
public import CFSG.HardMathSupport.Solomon.Coordinator.I271TwistGlue

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2

section Cat

theorem plane_closure_cat (hIn : SeitzInnerThreeClassical) (hOut : SeitzOuterClassical)
    (d : TauCeti.ValidLieTypeIndex) (hcl : IsClassicalIndex d.1) (hD4 : ¬ IsDFourIndex d.1)
    (hchar : (3 : ℕ) ≠ d.1.characteristic) (hexc : ¬ IsD2SeitzException 3 d.1)
    (E : Subgroup (MulAut (Cat d))) (hE : IsElemAbelian 3 E) (hc : Nat.card E = 9) :
    Subgroup.closure {s : Cat d | ∃ ε ∈ E, ε ≠ 1 ∧ ε s = s} = ⊤ := by
  have hc' : Nat.card E = 3 ^ 2 := by rw [hc]; norm_num
  by_cases hin : InnerPlane d 3 E
  · exact hIn d 3 Nat.prime_three (by norm_num) hchar hexc E hE hc' ⟨hin, rfl, hcl⟩
  · exact hOut d 3 Nat.prime_three (by norm_num) hchar hexc E hE hc'
      ⟨hin, hcl, fun h => hD4 h.2⟩

theorem exists_cat_of_isSLThreeExc {X : Type} [Group X] (h : IsSLThreeExc X)
    (h4 : ¬ IsSLThreeFour X) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A 2 q).Valid), q.card ≠ 4 ∧
      ¬ 3 ∣ q.card ∧
      Nonempty (X ⧸ Subgroup.center X ≃* Cat (⟨.A 2 q, hv⟩ : TauCeti.ValidLieTypeIndex)) := by
  obtain ⟨F, hF, hfin, h9, ⟨e⟩⟩ := h
  have h3 : 3 ∣ Nat.card F - 1 := by omega
  obtain ⟨q, _, hqc, ⟨φ⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.exists_primePower_card_eq F
  have hv : (TauCeti.LieTypeIndex.A 2 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp only [hqc]
    omega
  refine ⟨q, hv, ?_, ?_, ⟨?_⟩⟩
  · intro hq4
    exact h4 ⟨F, hF, hfin, by rw [← hqc]; exact hq4, ⟨e⟩⟩
  · rw [hqc]; omega
  · let e₁ : X ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
      e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm
    exact ((QuotientGroup.congr _ _ e₁ (Subgroup.map_center_eq e₁)).trans
      (CFSG.Adapters.RankTwoModelTransports.projectiveSpecialLinearGroupCongr (Fin 3) φ)).trans
      (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv).symm

theorem exists_cat_of_isSUThreeExc {X : Type} [Group X] (hX : CFSG.Open.IsQuasisimple X)
    (h : IsSUThreeExc X) :
    ∃ (Q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA 2 Q).Valid), ¬ 3 ∣ Q.card ∧
      Nonempty (X ⧸ Subgroup.center X ≃* Cat (⟨.twistedA 2 Q, hv⟩ : TauCeti.ValidLieTypeIndex)) := by
  obtain ⟨F, hF, hfin, q, hFq, hq9, ⟨e⟩⟩ := h
  have hq2 := CFSG.Open.StatedCenterThree.two_le_of_card_eq_sq hFq
  have h3 : 3 ∣ q + 1 := by omega
  have hq3 : 3 ≤ q := by
    by_contra hlt
    obtain rfl : q = 2 := by omega
    have hs : Group.IsSolvable (StatedSU 3 (2 ^ 1) F) :=
      CFSG.Quasithin.isSolvable_statedSU_one (by simpa using hFq)
    exact CFSG.ClassicalInvolution.not_isSolvable_of_open_isQuasisimple hX
      (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)
  obtain ⟨Q, _, hQc, ⟨φ⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.exists_primePower_sq_card_eq F hFq hq2
  have hv : (TauCeti.LieTypeIndex.twistedA 2 Q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff]
    refine ⟨⟨le_rfl, fun _ => ?_⟩, fun h => h⟩
    show 3 ≤ Q.card
    rw [hQc]
    exact hq3
  have hQ' : Q.p ^ Q.exponent = q := (TauCeti.PrimePower.card_def Q).symm.trans hQc
  subst hQ'
  refine ⟨Q, hv, ?_, ⟨?_⟩⟩
  · rw [TauCeti.PrimePower.card_def]; omega
  · have hFq' : Nat.card (GaloisField Q.p (2 * Q.exponent)) = (Q.p ^ Q.exponent) ^ 2 := by
      rw [GaloisField.card _ _ (by have := Q.exponent_pos; omega), ← pow_mul, mul_comm]
    have e₃ : X ≃* StatedSU 3 (Q.p ^ Q.exponent) (GaloisField Q.p (2 * Q.exponent)) :=
      e.trans (CFSG.Open.StatedSUFieldChange.statedSUEquiv φ 3 _)
    exact ((QuotientGroup.congr _ _ e₃ (Subgroup.map_center_eq e₃)).trans
      (QuotientGroup.quotientMulEquivOfEq
        (CFSG.LocalAnalysis.GLTheoremA.center_statedSU_three_eq hFq' h3))).trans
      (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 Q hv).symm

end Cat

section Fam

theorem not_exception_A_two {q : TauCeti.PrimePower} (hq4 : q.card ≠ 4) :
    ¬ IsD2SeitzException 3 (TauCeti.LieTypeIndex.A 2 q) := by
  intro h
  rcases h with ⟨-, h⟩ | ⟨h5, -⟩
  · rcases h with ⟨q', -, -, h⟩ | ⟨q', hp, he, h⟩ | ⟨q', -, -, h⟩ | ⟨q', -, -, h | h⟩ | h
    · cases h
    · have hq : q = q' := by
        cases h
        rfl
      apply hq4
      rw [hq, TauCeti.PrimePower.card_def, hp, he]
      norm_num
    · cases h
    · cases h
    · cases h
    · cases h
  · omega

theorem not_exception_twistedA_two {Q : TauCeti.PrimePower} :
    ¬ IsD2SeitzException 3 (TauCeti.LieTypeIndex.twistedA 2 Q) := by
  intro h
  rcases h with ⟨-, h⟩ | ⟨h5, -⟩
  · rcases h with ⟨q', -, -, h⟩ | ⟨q', hp, he, h⟩ | ⟨q', -, -, h⟩ | ⟨q', -, -, h | h⟩ | h
    · cases h
    · cases h
    · cases h
    · cases h
    · cases h
    · cases h
  · omega

theorem nnExcZ_slThreeExc (hIn : SeitzInnerThreeClassical) (hOut : SeitzOuterClassical) :
    NNExcZ (fun _ _ K => IsSLThreeExc ↥K) := by
  intro X _ _ hXK K B hH hNN hidx h4 h9 hZ1 hZ2 hP
  by_cases hF : IsSLThreeFour ↥K
  · exact nnExc_slThreeFour X hXK K B hH hNN hidx h4 h9 hF
  · left
    have hBel : IsElemAbelian 3 B := hH.scp.2.1
    have hq : CFSG.Open.IsQuasisimple ↥K := i116e_isQuasisimple hH.core hH.comp
    have h9' : autOrderIn B K = 9 := by rw [h9]; norm_num
    obtain ⟨q, hv, hq4, hq3, ⟨e⟩⟩ := exists_cat_of_isSLThreeExc hP hF
    have hqp : q.p ≠ 3 := by
      intro h
      apply hq3
      rw [TauCeti.PrimePower.card_def, h]
      exact dvd_pow_self 3 q.exponent_pos.ne'
    have hplane := fun E hE hc => plane_closure_cat hIn hOut (⟨.A 2 q, hv⟩ : TauCeti.ValidLieTypeIndex)
      trivial (by rintro ⟨q', h⟩; cases h)
      (by simpa [TauCeti.LieTypeIndex.characteristic_A] using hqp.symm)
      (not_exception_A_two hq4) E hE hc
    exact nn_caseA_of_twist hH hidx (rel_of_ZJ hH hZ1 hZ2) (hgen_of_plane hBel hq.1 h9' e hplane)

theorem nnExcZ_suThreeExc (hIn : SeitzInnerThreeClassical) (hOut : SeitzOuterClassical) :
    NNExcZ (fun _ _ K => IsSUThreeExc ↥K) := by
  intro X _ _ hXK K B hH hNN hidx h4 h9 hZ1 hZ2 hP
  left
  have hBel : IsElemAbelian 3 B := hH.scp.2.1
  have hq : CFSG.Open.IsQuasisimple ↥K := i116e_isQuasisimple hH.core hH.comp
  have h9' : autOrderIn B K = 9 := by rw [h9]; norm_num
  obtain ⟨Q, hv, hQ3, ⟨e⟩⟩ := exists_cat_of_isSUThreeExc hq hP
  have hQp : Q.p ≠ 3 := by
    intro h
    apply hQ3
    rw [TauCeti.PrimePower.card_def, h]
    exact dvd_pow_self 3 Q.exponent_pos.ne'
  have hplane := fun E hE hc => plane_closure_cat hIn hOut (⟨.twistedA 2 Q, hv⟩ : TauCeti.ValidLieTypeIndex)
    trivial (by rintro ⟨q', h⟩; cases h)
    (by simpa [TauCeti.LieTypeIndex.characteristic_twistedA] using hQp.symm)
    not_exception_twistedA_two E hE hc
  exact nn_caseA_of_twist hH hidx (rel_of_ZJ hH hZ1 hZ2) (hgen_of_plane hBel hq.1 h9' e hplane)

theorem nnSLThreeExc_holds
    (T : Tables112) (TL : TableL2) (TT : Tables112Types) : NNSLThreeExc :=
  nnFor_of_excZ (fun _ _ K => IsSLThreeExc ↥K) (nnFactsZ_of_tables T TL TT _)
    (nnExcZ_slThreeExc seitzInnerThreeClassical_holds seitzOuterClassical_holds)

theorem nnSUThreeExc_holds
    (T : Tables112) (TL : TableL2) (TT : Tables112Types) : NNSUThreeExc :=
  nnFor_of_excZ (fun _ _ K => IsSUThreeExc ↥K) (nnFactsZ_of_tables T TL TT _)
    (nnExcZ_suThreeExc seitzInnerThreeClassical_holds seitzOuterClassical_holds)

end Fam

end CFSG.HardMathSupport.Solomon.Coordinator
