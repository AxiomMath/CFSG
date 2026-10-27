module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSection
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySuzukiNormalizer
public import CFSG.Quasithin.Background.SmithB42D4Main
public import CFSG.Quasithin.Background.SmithB42F4Main
public import CFSG.Quasithin.Background.SmithB42Tits
public import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Catalog
public import CFSG.Adapters.TauCetiExceptional.EvenD4
public import CFSG.RankThree.PartTwo.Sec4.Census.BridgeSuzuki
public import CFSG.Sporadic.Schreier.TitsOuter
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
public import CFSG.Adapters.TauCetiExceptional.BridgeTransport
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFFamilies
public import CFSG.HardMathSupport.Cooperstein.Proving.NineThreeTransfer
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.Reduction
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.Sporadic.Schreier.TitsOther

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator

open CFSG.Quasithin CFSG.QuasithinUnique.Setup CFSG.Blueprint CFSG.Blueprint.Chevalley TauCeti

theorem isSQTKExceptionalTwoIndex_cases {d : LieTypeIndex} (hd : IsSQTKExceptionalTwoIndex d) :
    (∃ q : PrimePower, d = .trialityD4 q ∧ q.p = 2) ∨ (∃ m : ℕ, d = .suzuki m) ∨
      (∃ m : ℕ, d = .reeF4 m) ∨ d = .tits := by
  cases d <;> simp only [IsSQTKExceptionalTwoIndex] at hd
  · exact Or.inl ⟨_, rfl, hd⟩
  · exact Or.inr (Or.inl ⟨_, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr rfl))

theorem exists_isFFStarOffender_le {W : Type} [CommGroup W] [Finite W]
    {G E : Subgroup (MulAut W)} (hEG : E ≤ G) (hE : E ≠ ⊥) (hel : IsElemAbelian2 E)
    (hoff : Nat.card W ≤ Nat.card E * Nat.card (fixV E)) :
    ∃ A : Subgroup (MulAut W), A ≤ E ∧ IsFFStarOffender G A :=
  (B1.exists_offender_below (X := G) ⟨hEG, hE, hel⟩ 0 (by simpa using hoff)).imp fun _ h =>
    ⟨h.1, h.2.1⟩

theorem card_mul_card_fixV_lt_of_dispCriterion {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)} (hperf : Group.IsPerfect ↥L)
    (hirr : X1.IsIrrOn L) {M : Type} [Group M] (e : ↥L ⧸ Subgroup.center ↥L ≃* M)
    (hM : B42Disp.DispCriterion M) (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (hE : E ≠ ⊥) (hel : IsElemAbelian2 E) :
    Nat.card E * Nat.card (fixV E) < Nat.card W := by
  have : Nontrivial W := hirr.1
  by_contra hcon
  obtain ⟨A, hAE, hA⟩ :=
    exists_isFFStarOffender_le (G := L ⊔ E) le_sup_right hE hel (not_lt.1 hcon)
  exact B42Disp.not_isFFStarOffender_of_dispCriterion hW L hperf hirr.2 e hM le_sup_left
    (hAE.trans hEN) hA

theorem chevalleyExceptionalModel_trialityD4_of_lie
    {X : Type} [Group X] {q : PrimePower} (hv : (LieTypeIndex.trialityD4 q).Valid)
    (hq : q.p = 2) (e : X ≃* (CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group) :
    ChevalleyExceptionalModel X .trialityD4 2 q.exponent := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p (q.exponent * 3)) = q.card ^ TwistTag.D4.order := by
    rw [GaloisField.card q.p (q.exponent * 3) (Nat.mul_ne_zero q.exponent_pos.ne' (by norm_num)),
      PrimePower.card_def, pow_mul]
    rfl
  have hσ : ∀ x : GaloisField q.p (q.exponent * 3),
      iterateFrobenius (GaloisField q.p (q.exponent * 3)) q.p q.exponent x = x ^ q.card :=
    fun x => by rw [iterateFrobenius_def, PrimePower.card_def]
  obtain ⟨φ⟩ := CFSG.TauCetiBridge.Even.twistedBridgeEven_trialityD4 q hv hq _ hK _ hσ
  have hcard : q.card = 2 ^ q.exponent := by rw [PrimePower.card_def, hq]
  rw [hcard] at hK hσ
  exact ⟨⟨Nat.prime_two, q.exponent_pos, rfl⟩, GaloisField q.p (q.exponent * 3), inferInstance,
    inferInstance, hK, _, hσ, ⟨e.trans φ.symm⟩⟩

theorem suzukiModel_of_lie {X : Type} [Group X] {m : ℕ} (hv : (LieTypeIndex.suzuki m).Valid)
    (e : X ≃* (CFSGIndex.lie ⟨.suzuki m, hv⟩).Group) : SuzukiModel X 2 (2 * m + 1) := by
  obtain ⟨h2, a, ha, K, i1, i2, hk, hK, ⟨f⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index m hv
  exact ⟨h2, a, ha, K, i1, i2, hk, hK, ⟨e.trans f⟩⟩

theorem reeTitsModel_reeF4_of_lie
    {X : Type} [Group X] {m : ℕ} (hv : (LieTypeIndex.reeF4 m).Valid)
    (e : X ≃* (CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group) : ReeTitsModel X .twistedF4 2 (2 * m + 1) := by
  have hfin : ∀ d : ReeF4LieIndex, Finite d.1.fixedField := fun _ => inferInstance
  have hchar : ∀ d : ReeF4LieIndex, CharP d.1.fixedField 2 := fun _ => inferInstance
  have := hfin (ReeF4LieIndex.of m hv)
  have := hchar (ReeF4LieIndex.of m hv)
  have hm : 1 ≤ m := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hhalf : (ReeF4LieIndex.of m hv).toSuzukiReeIndex.halfExponent = m :=
    SuzukiReeIndex.halfExponent_reeF4 m hv
  obtain ⟨e₁⟩ := CFSG.TauCetiBridge.ReeF4.nonempty_candidate_equiv_reeF4 (ReeF4LieIndex.of m hv)
  rw [hhalf] at e₁
  have hK := CFSG.TauCetiBridge.ReeF4.card_fixedField_reeF4 (ReeF4LieIndex.of m hv)
  rw [hhalf] at hK
  exact ⟨⟨Nat.prime_two, by omega, ⟨rfl, rfl, ⟨m, rfl⟩, by omega⟩⟩, m, rfl,
    ⟨(ReeF4LieIndex.of m hv).1.fixedField, inferInstance, inferInstance, hK,
      ⟨(e.trans e₁).trans (CFSG.TauCetiBridge.ReeF4.nativeModelEquiv m).symm⟩⟩⟩

theorem reeTitsModel_tits_of_lie
    {X : Type} [Group X] (hv : LieTypeIndex.tits.Valid)
    (e : X ≃* (CFSGIndex.lie ⟨.tits, hv⟩).Group) : ReeTitsModel X .Tits 2 1 := by
  have hfin : ∀ d : TitsLieIndex, Finite d.1.fixedField := fun _ => inferInstance
  have hchar : ∀ d : TitsLieIndex, CharP d.1.fixedField 2 := fun _ => inferInstance
  have := hfin TitsLieIndex.of
  have := hchar TitsLieIndex.of
  obtain ⟨e₁⟩ := CFSG.TauCetiBridge.ReeF4.nonempty_candidate_equiv_tits TitsLieIndex.of
  exact ⟨⟨Nat.prime_two, le_rfl, ⟨rfl, rfl, rfl⟩⟩, 0, rfl,
    ⟨TitsLieIndex.of.1.fixedField, inferInstance, inferInstance,
      (CFSG.TauCetiBridge.ReeF4.card_fixedField_tits _).trans (pow_one 2).symm,
      ⟨(e.trans e₁).trans (CFSG.TauCetiBridge.ReeF4.nativeModelEquiv 0).symm⟩⟩⟩

theorem noIrrFFOffender_suzuki
    (m : ℕ) (hv : (LieTypeIndex.suzuki m).Valid) :
    NoIrrFFOffender (CFSGIndex.lie ⟨.suzuki m, hv⟩).Group := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hEN hE hel _
  have : Nontrivial W := hirr.1
  obtain ⟨-, a, ha, K, _, _, hfa, hK, ⟨α⟩⟩ := suzukiModel_of_lie hv e
  rw [hfa] at hK
  exact (Family.suzuki_irreducible_normalizer_excludes a ha hK W hW L hq.1 hirr.2 α).2.2.2.2
    E hE hel hEN

theorem noIrrFFOffender_trialityD4
    (q : PrimePower) (hv : (LieTypeIndex.trialityD4 q).Valid) (hq : q.p = 2) :
    NoIrrFFOffender (CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group := by
  intro W _ _ hW L E hql hirr ⟨e⟩ hEN hE hel _
  obtain ⟨hf, K, _, _, σ, hK, hσ, ⟨e'⟩⟩ :=
    X6.exists_mulEquiv_triality_model (chevalleyExceptionalModel_trialityD4_of_lie hv hq e)
  exact card_mul_card_fixV_lt_of_dispCriterion hW hql.1 hirr e'
    (B42D4.dispCriterion_trialityD4 hf hK σ hσ) hEN hE hel

theorem noIrrFFOffender_reeF4
    (m : ℕ) (hv : (LieTypeIndex.reeF4 m).Valid) :
    NoIrrFFOffender (CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group := by
  intro W _ _ hW L E hql hirr ⟨e⟩ hEN hE hel _
  obtain ⟨a, K, _, _, _, ha, hfa, hK, ⟨e'⟩⟩ :=
    X6.exists_mulEquiv_largeRee_model (reeTitsModel_reeF4_of_lie hv e)
  exact card_mul_card_fixV_lt_of_dispCriterion hW hql.1 hirr e'
    (B42F4.dispCriterion_reeGamma ha (by rw [hK, hfa])) hEN hE hel

theorem noIrrFFOffender_tits
    (hv : LieTypeIndex.tits.Valid) :
    NoIrrFFOffender (CFSGIndex.lie ⟨.tits, hv⟩).Group := by
  intro W _ _ hW L E hql hirr ⟨e⟩ hEN hE hel _
  obtain ⟨e'⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv _ 2 1 (reeTitsModel_tits_of_lie hv e)
  exact card_mul_card_fixV_lt_of_dispCriterion hW hql.1 hirr e' B42Tits.titsD_dispCriterion hEN hE
    hel

theorem noIrrFFOffender_exceptional_two
    (d : TauCeti.ValidLieTypeIndex) (hd : IsSQTKExceptionalTwoIndex d.1) :
    NoIrrFFOffender (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨d, hv⟩ := d
  rcases isSQTKExceptionalTwoIndex_cases hd with ⟨q, rfl, hq⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩ | rfl
  · exact noIrrFFOffender_trialityD4 q hv hq
  · exact noIrrFFOffender_suzuki m hv
  · exact noIrrFFOffender_reeF4 m hv
  · exact noIrrFFOffender_tits hv

end CFSG.HardMathSupport.Cooperstein.Coordinator
