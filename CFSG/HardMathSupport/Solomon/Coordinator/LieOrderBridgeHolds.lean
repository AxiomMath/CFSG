module

public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieEnd
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBOdd
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd
import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Catalog
import CFSG.RankThree.PartTwo.Sec4.Census.BridgeSuzuki
import CFSG.Adapters.TauCetiExceptional.EvenB1
import CFSG.Adapters.TauCetiExceptional.ReeBridge
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
public import CFSG.Adapters.LinearCatalog
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open TauCeti CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Open
  CFSG.HardMathSupport.Solomon.Coordinator.I1420
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.CatLeafProof (card_eq_lieOrder)

section Models


private theorem card_classical {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (ht : t ∈ classicalTags) (h : StatedClassicalModel G t n p f) :
    Nat.card G = lieOrderNumerator t n (p ^ f) / lieOrderDivisor t n (p ^ f) :=
  card_eq_lieOrder h.1 (Or.inl ⟨ht, h⟩)

private theorem card_chevalley {G : Type} [Group G] {t : StatedLieTag} {p f : ℕ}
    (ht : t ∈ chevalleyExceptionalTags) (h : ChevalleyExceptionalModel G t p f) :
    Nat.card G = lieOrderNumerator t 0 (p ^ f) / lieOrderDivisor t 0 (p ^ f) :=
  card_eq_lieOrder h.1 (Or.inr (Or.inl ⟨rfl, ht, h⟩))

private theorem card_reeTits {G : Type} [Group G] {t : StatedLieTag} {p f : ℕ}
    (ht : t ∈ reeTitsTags) (h : ReeTitsModel G t p f) :
    Nat.card G = lieOrderNumerator t 0 (p ^ f) / lieOrderDivisor t 0 (p ^ f) :=
  card_eq_lieOrder h.1 (Or.inr (Or.inr (Or.inl ⟨rfl, ht, h⟩)))

private theorem card_suzuki {G : Type} [Group G] {m : ℕ} (hm : 1 ≤ m)
    (h : SuzukiModel G 2 (2 * m + 1)) :
    Nat.card G = lieOrderNumerator .twistedB2 0 (2 ^ (2 * m + 1)) /
      lieOrderDivisor .twistedB2 0 (2 ^ (2 * m + 1)) :=
  card_eq_lieOrder ⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩
    (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, h⟩)))

private theorem order_A (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.A r q).Valid) {G : Type}
    [Group G] (e : G ≃* ValidLieTypeIndex.Group ⟨.A r q, hv⟩) :
    Nat.card G = lieOrderFormula (.A r q) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hmodel : StatedClassicalModel G .PSL (r + 1) q.p q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, by omega, ?_, ?_⟩, GaloisField q.p q.exponent,
      inferInstance, inferInstance, GaloisField.card q.p q.exponent q.exponent_pos.ne',
      ⟨(e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv)).trans
        (projectiveSpecialLinearGroupEquivStatedProj (r + 1) _)⟩⟩
    · intro h
      simp only [Prod.mk.injEq] at h
      have := hrange.2 (by omega)
      simp only [PrimePower.card_def] at this
      omega
    · intro h
      simp only [Prod.mk.injEq] at h
      have := hrange.2 (by omega)
      simp only [PrimePower.card_def] at this
      omega
  rw [card_classical (by simp [classicalTags]) hmodel]
  simp only [lieOrderFormula, orderA, lieOrderNumerator, lieOrderDivisor, Nat.add_sub_cancel,
    mul_comm (r + 1) r, PrimePower.card_def]

private theorem order_twistedA (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.twistedA r q).Valid)
    {G : Type} [Group G] (e : G ≃* ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩) :
    Nat.card G = lieOrderFormula (.twistedA r q) := by
  rw [card_classical (by simp [classicalTags])
    (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e)]
  simp only [lieOrderFormula, orderTwistedA, lieOrderNumerator, lieOrderDivisor,
    Nat.add_sub_cancel, mul_comm (r + 1) r, PrimePower.card_def]

private theorem order_B (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.B r q).Valid) {G : Type}
    [Group G] (e : G ≃* ValidLieTypeIndex.Group ⟨.B r q, hv⟩) :
    Nat.card G = lieOrderFormula (.B r q) := by
  have hr : 2 ≤ r :=
    ((LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1).1
  have hpsp : StatedClassicalModel G .PSp r q.p q.exponent → Nat.card G = lieOrderFormula (.B r q) :=
    fun hm => by
      rw [card_classical (by simp [classicalTags]) hm]
      simp only [lieOrderFormula, orderBC, lieOrderNumerator, lieOrderDivisor, sq,
        PrimePower.card_def]
  rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
  · exact hpsp (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e)
  · by_cases hp : q.p = 2
    · exact hpsp (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp hr3 e)
    · rw [card_classical (by simp [classicalTags])
        (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hp hr3 e)]
      have hodd : Odd (q.p ^ q.exponent) := (q.prime_p.eq_two_or_odd'.resolve_left hp).pow
      simp only [lieOrderFormula, orderBC, lieOrderNumerator, lieOrderDivisor, sq,
        PrimePower.card_def, CFSG.ClassicalInvolution.gcd_two_sub_one_of_odd hodd]

private theorem order_C (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.C r q).Valid) {G : Type}
    [Group G] (e : G ≃* ValidLieTypeIndex.Group ⟨.C r q, hv⟩) :
    Nat.card G = lieOrderFormula (.C r q) := by
  rw [card_classical (by simp [classicalTags])
    (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv e)]
  simp only [lieOrderFormula, orderBC, lieOrderNumerator, lieOrderDivisor, sq,
    PrimePower.card_def]

private theorem order_D (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.D r q).Valid) {G : Type}
    [Group G] (e : G ≃* ValidLieTypeIndex.Group ⟨.D r q, hv⟩) :
    Nat.card G = lieOrderFormula (.D r q) := by
  rw [card_classical (by simp [classicalTags])
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e)]
  simp only [lieOrderFormula, orderD, lieOrderNumerator, lieOrderDivisor, PrimePower.card_def]

private theorem order_twistedD (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.twistedD r q).Valid)
    {G : Type} [Group G] (e : G ≃* ValidLieTypeIndex.Group ⟨.twistedD r q, hv⟩) :
    Nat.card G = lieOrderFormula (.twistedD r q) := by
  rw [card_classical (by simp [classicalTags])
    (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e)]
  simp only [lieOrderFormula, orderTwistedD, lieOrderNumerator, lieOrderDivisor,
    PrimePower.card_def]

section Exceptional


private theorem order_E6 (q : PrimePower) (hv : (LieTypeIndex.E6 q).Valid) {G : Type} [Group G]
    (e : G ≃* ValidLieTypeIndex.Group ⟨.E6 q, hv⟩) : Nat.card G = lieOrderFormula (.E6 q) := by
  have hm : ChevalleyExceptionalModel G .E6 q.p q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, ?_⟩
    by_cases hq : q.p = 2
    · exact CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.e6 q hv hq e
    · exact CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.chevalleyBridges.e6 q hv
        hq e
  rw [card_chevalley (by simp [chevalleyExceptionalTags]) hm]
  simp only [lieOrderFormula, orderE6, lieOrderNumerator, lieOrderDivisor, PrimePower.card_def]

private theorem order_E7 (q : PrimePower) (hv : (LieTypeIndex.E7 q).Valid) {G : Type} [Group G]
    (e : G ≃* ValidLieTypeIndex.Group ⟨.E7 q, hv⟩) : Nat.card G = lieOrderFormula (.E7 q) := by
  have hm : ChevalleyExceptionalModel G .E7 q.p q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, ?_⟩
    by_cases hq : q.p = 2
    · exact CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.e7 q hv hq e
    · exact CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.chevalleyBridges.e7 q hv
        hq e
  rw [card_chevalley (by simp [chevalleyExceptionalTags]) hm]
  simp only [lieOrderFormula, orderE7, lieOrderNumerator, lieOrderDivisor, PrimePower.card_def]

private theorem order_E8 (q : PrimePower) (hv : (LieTypeIndex.E8 q).Valid) {G : Type} [Group G]
    (e : G ≃* ValidLieTypeIndex.Group ⟨.E8 q, hv⟩) : Nat.card G = lieOrderFormula (.E8 q) := by
  have hm : ChevalleyExceptionalModel G .E8 q.p q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, ?_⟩
    by_cases hq : q.p = 2
    · exact CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.e8 q hv hq e
    · exact CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.chevalleyBridges.e8 q hv
        hq e
  rw [card_chevalley (by simp [chevalleyExceptionalTags]) hm]
  simp only [lieOrderFormula, orderE8, lieOrderNumerator, lieOrderDivisor, Nat.div_one,
    PrimePower.card_def]

private theorem order_F4 (q : PrimePower) (hv : (LieTypeIndex.F4 q).Valid) {G : Type} [Group G]
    (e : G ≃* ValidLieTypeIndex.Group ⟨.F4 q, hv⟩) : Nat.card G = lieOrderFormula (.F4 q) := by
  have hm : ChevalleyExceptionalModel G .F4 q.p q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, ?_⟩
    by_cases hq : q.p = 2
    · exact CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.f4 q hv hq e
    · exact CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.chevalleyBridges.f4 q hv
        hq e
  rw [card_chevalley (by simp [chevalleyExceptionalTags]) hm]
  simp only [lieOrderFormula, orderF4, lieOrderNumerator, lieOrderDivisor, Nat.div_one,
    PrimePower.card_def]

private theorem order_G2 (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid) {G : Type} [Group G]
    (e : G ≃* ValidLieTypeIndex.Group ⟨.G2 q, hv⟩) : Nat.card G = lieOrderFormula (.G2 q) := by
  have h3 : 3 ≤ q.p ^ q.exponent := by
    have h := ((LieTypeIndex.valid_iff _).1 hv).1
    simpa only [LieTypeIndex.inStandardRange_iff, PrimePower.card_def] using h
  have hm : ChevalleyExceptionalModel G .G2 q.p q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, rfl, h3⟩, ?_⟩
    by_cases hq : q.p = 2
    · exact CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.g2 q hv hq e
    · exact CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.chevalleyBridges.g2 q hv
        hq e
  rw [card_chevalley (by simp [chevalleyExceptionalTags]) hm]
  simp only [lieOrderFormula, orderG2, lieOrderNumerator, lieOrderDivisor, Nat.div_one,
    PrimePower.card_def]

private theorem order_twistedE6 (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid)
    {G : Type} [Group G] (e : G ≃* ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩) :
    Nat.card G = lieOrderFormula (.twistedE6 q) := by
  have hm : ChevalleyExceptionalModel G .twistedE6 q.p q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, ?_⟩
    by_cases hq : q.p = 2
    · exact CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.twistedE6 q hv hq (by decide) e
    · exact CFSG.TauCetiBridge.twistedModel_of_bridge
        CFSG.TauCetiBridge.Twisted.twistedBridge_twistedE6 q hv hq (by decide) e
  rw [card_chevalley (by simp [chevalleyExceptionalTags]) hm]
  simp only [lieOrderFormula, orderTwistedE6, lieOrderNumerator, lieOrderDivisor,
    PrimePower.card_def]

private theorem order_trialityD4 (q : PrimePower) (hv : (LieTypeIndex.trialityD4 q).Valid)
    {G : Type} [Group G] (e : G ≃* ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) :
    Nat.card G = lieOrderFormula (.trialityD4 q) := by
  have hm : ChevalleyExceptionalModel G .trialityD4 q.p q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, ?_⟩
    by_cases hq : q.p = 2
    · exact CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.trialityD4 q hv hq (by decide) e
    · exact CFSG.TauCetiBridge.twistedModel_of_bridge
        CFSG.TauCetiBridge.Twisted.twistedBridge_trialityD4 q hv hq (by decide) e
  rw [card_chevalley (by simp [chevalleyExceptionalTags]) hm]
  simp only [lieOrderFormula, orderTrialityD4, lieOrderNumerator, lieOrderDivisor, Nat.div_one,
    PrimePower.card_def]

end Exceptional

private theorem order_suzuki (m : ℕ) (hv : (LieTypeIndex.suzuki m).Valid) {G : Type} [Group G]
    (e : G ≃* ValidLieTypeIndex.Group ⟨.suzuki m, hv⟩) :
    Nat.card G = lieOrderFormula (.suzuki m) := by
  have hm : 1 ≤ m := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  rw [card_suzuki hm (CFSG.SectionRank.suzukiModel_of_mulEquiv e
    (CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index m hv))]
  simp only [lieOrderFormula, orderSuzuki, lieOrderNumerator, lieOrderDivisor, Nat.div_one]

private theorem order_reeG2 (a : ℕ) (hv : (LieTypeIndex.reeG2 a).Valid) {G : Type} [Group G]
    (e : G ≃* ValidLieTypeIndex.Group ⟨.reeG2 a, hv⟩) :
    Nat.card G = lieOrderFormula (.reeG2 a) := by
  have ha : 1 ≤ a := by
    have h := ((LieTypeIndex.valid_iff _).1 hv).1
    simpa [LieTypeIndex.inStandardRange_iff] using h
  have hK : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) :=
    GaloisField.card 3 (2 * a + 1) (by omega)
  obtain ⟨φ⟩ := CFSG.TauCetiBridge.reeG2Bridge a hv (GaloisField 3 (2 * a + 1)) hK
  have hm : ReeTitsModel G .twistedG2 3 (2 * a + 1) :=
    ⟨⟨Nat.prime_three, by omega, ⟨rfl, rfl, ⟨a, rfl⟩, by omega⟩⟩, a, rfl,
      ⟨GaloisField 3 (2 * a + 1), inferInstance, inferInstance, hK, ⟨e.trans φ.symm⟩⟩⟩
  rw [card_reeTits (by simp [reeTitsTags]) hm]
  simp only [lieOrderFormula, orderRee, lieOrderNumerator, lieOrderDivisor, Nat.div_one]

section Ree


private theorem order_reeF4 (m : ℕ) (hv : (LieTypeIndex.reeF4 m).Valid) {G : Type} [Group G]
    (e : G ≃* ValidLieTypeIndex.Group ⟨.reeF4 m, hv⟩) :
    Nat.card G = lieOrderFormula (.reeF4 m) := by
  have hfin : ∀ d : ReeF4LieIndex, Finite d.1.fixedField := fun _ => inferInstance
  have hchar : ∀ d : ReeF4LieIndex, CharP d.1.fixedField 2 := fun _ => inferInstance
  have := hfin (ReeF4LieIndex.of m hv)
  have := hchar (ReeF4LieIndex.of m hv)
  have hm1 : 1 ≤ m := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hhalf : (ReeF4LieIndex.of m hv).toSuzukiReeIndex.halfExponent = m :=
    SuzukiReeIndex.halfExponent_reeF4 m hv
  obtain ⟨e₁⟩ := CFSG.TauCetiBridge.ReeF4.nonempty_candidate_equiv_reeF4 (ReeF4LieIndex.of m hv)
  rw [hhalf] at e₁
  have hK := CFSG.TauCetiBridge.ReeF4.card_fixedField_reeF4 (ReeF4LieIndex.of m hv)
  rw [hhalf] at hK
  have hm : ReeTitsModel G .twistedF4 2 (2 * m + 1) :=
    ⟨⟨Nat.prime_two, by omega, ⟨rfl, rfl, ⟨m, rfl⟩, by omega⟩⟩, m, rfl,
      ⟨(ReeF4LieIndex.of m hv).1.fixedField, inferInstance, inferInstance, hK,
        ⟨(e.trans e₁).trans (CFSG.TauCetiBridge.ReeF4.nativeModelEquiv m).symm⟩⟩⟩
  rw [card_reeTits (by simp [reeTitsTags]) hm]
  simp only [lieOrderFormula, orderTwistedF4, lieOrderNumerator, lieOrderDivisor, Nat.div_one]

private theorem order_tits (hv : LieTypeIndex.tits.Valid) {G : Type} [Group G]
    (e : G ≃* ValidLieTypeIndex.Group ⟨.tits, hv⟩) :
    Nat.card G = lieOrderFormula .tits := by
  have hfin : ∀ d : TitsLieIndex, Finite d.1.fixedField := fun _ => inferInstance
  have hchar : ∀ d : TitsLieIndex, CharP d.1.fixedField 2 := fun _ => inferInstance
  have := hfin TitsLieIndex.of
  have := hchar TitsLieIndex.of
  obtain ⟨e₁⟩ := CFSG.TauCetiBridge.ReeF4.nonempty_candidate_equiv_tits TitsLieIndex.of
  have hm : ReeTitsModel G .Tits 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, ⟨rfl, rfl, rfl⟩⟩, 0, rfl,
      ⟨TitsLieIndex.of.1.fixedField, inferInstance, inferInstance,
        (CFSG.TauCetiBridge.ReeF4.card_fixedField_tits _).trans (pow_one 2).symm,
        ⟨(e.trans e₁).trans (CFSG.TauCetiBridge.ReeF4.nativeModelEquiv 0).symm⟩⟩⟩
  rw [card_reeTits (by simp [reeTitsTags]) hm]
  simp only [lieOrderFormula, orderTits, lieOrderNumerator, lieOrderDivisor, Nat.div_one]
  norm_num

end Ree

end Models

theorem lieOrderBridge_holds :
    LieOrderBridge := by
  rintro ⟨d, hv⟩ G _ _ ⟨e⟩
  cases d with
  | A r q => exact order_A r q hv e
  | twistedA r q => exact order_twistedA r q hv e
  | B r q => exact order_B r q hv e
  | C r q => exact order_C r q hv e
  | D r q => exact order_D r q hv e
  | twistedD r q => exact order_twistedD r q hv e
  | E6 q => exact order_E6 q hv e
  | E7 q => exact order_E7 q hv e
  | E8 q => exact order_E8 q hv e
  | F4 q => exact order_F4 q hv e
  | G2 q => exact order_G2 q hv e
  | twistedE6 q => exact order_twistedE6 q hv e
  | trialityD4 q => exact order_trialityD4 q hv e
  | suzuki m => exact order_suzuki m hv e
  | reeG2 a => exact order_reeG2 a hv e
  | reeF4 m => exact order_reeF4 m hv e
  | tits => exact order_tits hv e

end CFSG.HardMathSupport.Solomon.Coordinator
