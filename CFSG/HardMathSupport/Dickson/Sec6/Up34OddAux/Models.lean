module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7ToolsB
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafLieOrder
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.Models.Blueprint
public import CFSG.Adapters.TauCetiExceptional.B1Exceptional
public import CFSG.Adapters.TauCetiExceptional.ReeBridge
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open TauCeti CFSG.Assembly.LowTwoRank CFSG.Open CFSG.Yardstones.Md0ec50421ce4
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.LocalAnalysis.GLTheoremB
open CFSG.ComponentClassification.CatLeaf (lieModel_odd_card_ne_L34 lieOrderNumerator
  lieOrderDivisor)
open CFSG.ComponentClassification.CatLeafProof (lieOrderFormulasInput)

section Bridges


theorem exists_blueprint_lieModel_of_odd {G : Type} [Group G] (d : ValidLieTypeIndex)
    (hd : d.1.characteristic ≠ 2) (e : G ≃* d.Group) :
    ∃ (t : StatedLieTag) (n f : ℕ), CFSG.Blueprint.LieModel G t n d.1.characteristic f := by
  obtain ⟨d, hv⟩ := d
  change d.characteristic ≠ 2 at hd
  change ∃ (t : StatedLieTag) (n f : ℕ), CFSG.Blueprint.LieModel G t n d.characteristic f
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  cases d with
  | A r q =>
    rw [LieTypeIndex.characteristic_A]
    exact ⟨.PSL, r + 1, q.exponent, CFSG.Models.LieModel.toBlueprint
      (by simp [CFSG.Blueprint.classicalTags]) (CFSG.Models.lieModel_A r q hv e)⟩
  | twistedA r q =>
    have h := CFSG.Models.lieModel_twistedA r q hv e
    simp only [ValidLieTypeIndex.characteristic, ValidLieTypeIndex.fieldExponent] at h
    exact ⟨.PSU, r + 1, _, CFSG.Models.LieModel.toBlueprint
      (by simp [CFSG.Blueprint.classicalTags]) h⟩
  | B r q =>
    rw [LieTypeIndex.characteristic_B]
    rcases CFSG.Models.lieModel_B r q hv e with h | h
    · exact ⟨.PSp, r, q.exponent, CFSG.Models.LieModel.toBlueprint
        (by simp [CFSG.Blueprint.classicalTags]) h⟩
    · exact ⟨.POmegaOdd, r, q.exponent, CFSG.Models.LieModel.toBlueprint
        (by simp [CFSG.Blueprint.classicalTags]) h⟩
  | C r q =>
    rw [LieTypeIndex.characteristic_C]
    exact ⟨.PSp, r, q.exponent, CFSG.Models.LieModel.toBlueprint
      (by simp [CFSG.Blueprint.classicalTags]) (CFSG.Models.lieModel_C r q hv e)⟩
  | D r q =>
    rw [LieTypeIndex.characteristic_D]
    exact ⟨.POmegaPlus, r, q.exponent, CFSG.Models.LieModel.toBlueprint
      (by simp [CFSG.Blueprint.classicalTags]) (CFSG.Models.lieModel_D r q hv e)⟩
  | twistedD r q =>
    rw [LieTypeIndex.characteristic_twistedD]
    exact ⟨.POmegaMinus, r, q.exponent, CFSG.Models.LieModel.toBlueprint
      (by simp [CFSG.Blueprint.classicalTags]) (CFSG.Models.lieModel_twistedD r q hv e)⟩
  | E6 q =>
    rw [LieTypeIndex.characteristic_E6] at hd ⊢
    have hm : CFSG.Blueprint.ChevalleyExceptionalModel G .E6 q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.e6 q hv hd e⟩
    exact ⟨.E6, 0, q.exponent, Or.inr (Or.inl ⟨rfl,
      by simp [CFSG.Blueprint.chevalleyExceptionalTags], hm⟩)⟩
  | E7 q =>
    rw [LieTypeIndex.characteristic_E7] at hd ⊢
    have hm : CFSG.Blueprint.ChevalleyExceptionalModel G .E7 q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.e7 q hv hd e⟩
    exact ⟨.E7, 0, q.exponent, Or.inr (Or.inl ⟨rfl,
      by simp [CFSG.Blueprint.chevalleyExceptionalTags], hm⟩)⟩
  | E8 q =>
    rw [LieTypeIndex.characteristic_E8] at hd ⊢
    have hm : CFSG.Blueprint.ChevalleyExceptionalModel G .E8 q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.e8 q hv hd e⟩
    exact ⟨.E8, 0, q.exponent, Or.inr (Or.inl ⟨rfl,
      by simp [CFSG.Blueprint.chevalleyExceptionalTags], hm⟩)⟩
  | F4 q =>
    rw [LieTypeIndex.characteristic_F4] at hd ⊢
    have hm : CFSG.Blueprint.ChevalleyExceptionalModel G .F4 q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.f4 q hv hd e⟩
    exact ⟨.F4, 0, q.exponent, Or.inr (Or.inl ⟨rfl,
      by simp [CFSG.Blueprint.chevalleyExceptionalTags], hm⟩)⟩
  | G2 q =>
    rw [LieTypeIndex.characteristic_G2] at hd ⊢
    have h3 : 3 ≤ q.p ^ q.exponent := by
      simpa only [LieTypeIndex.inStandardRange_iff, PrimePower.card_def] using hr
    have hm : CFSG.Blueprint.ChevalleyExceptionalModel G .G2 q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl, h3⟩, CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.g2 q hv hd e⟩
    exact ⟨.G2, 0, q.exponent, Or.inr (Or.inl ⟨rfl,
      by simp [CFSG.Blueprint.chevalleyExceptionalTags], hm⟩)⟩
  | twistedE6 q =>
    rw [LieTypeIndex.characteristic_twistedE6] at hd ⊢
    have hm : CFSG.Blueprint.ChevalleyExceptionalModel G .twistedE6 q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, CFSG.TauCetiBridge.twistedModel_of_bridge
        CFSG.TauCetiBridge.Twisted.twistedBridge_twistedE6 q hv hd (by decide) e⟩
    exact ⟨.twistedE6, 0, q.exponent, Or.inr (Or.inl ⟨rfl,
      by simp [CFSG.Blueprint.chevalleyExceptionalTags], hm⟩)⟩
  | trialityD4 q =>
    rw [LieTypeIndex.characteristic_trialityD4] at hd ⊢
    have hm : CFSG.Blueprint.ChevalleyExceptionalModel G .trialityD4 q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, CFSG.TauCetiBridge.twistedModel_of_bridge
        CFSG.TauCetiBridge.Twisted.twistedBridge_trialityD4 q hv hd (by decide) e⟩
    exact ⟨.trialityD4, 0, q.exponent, Or.inr (Or.inl ⟨rfl,
      by simp [CFSG.Blueprint.chevalleyExceptionalTags], hm⟩)⟩
  | suzuki m =>
    rw [LieTypeIndex.characteristic_suzuki] at hd
    exact absurd rfl hd
  | reeG2 a =>
    rw [LieTypeIndex.characteristic_reeG2]
    have ha : 1 ≤ a := by
      simpa [LieTypeIndex.inStandardRange_iff] using hr
    have hK : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) :=
      GaloisField.card 3 (2 * a + 1) (by omega)
    obtain ⟨φ⟩ := CFSG.TauCetiBridge.reeG2Bridge a hv (GaloisField 3 (2 * a + 1)) hK
    have hm : CFSG.Blueprint.ReeTitsModel G .twistedG2 3 (2 * a + 1) :=
      ⟨⟨Nat.prime_three, by omega, ⟨rfl, rfl, ⟨a, rfl⟩, by omega⟩⟩, a, rfl,
        ⟨GaloisField 3 (2 * a + 1), inferInstance, inferInstance, hK, ⟨e.trans φ.symm⟩⟩⟩
    exact ⟨.twistedG2, 0, 2 * a + 1, Or.inr (Or.inr (Or.inl ⟨rfl,
      by simp [CFSG.Blueprint.reeTitsTags], hm⟩))⟩
  | reeF4 m =>
    rw [LieTypeIndex.characteristic_reeF4] at hd
    exact absurd rfl hd
  | tits =>
    rw [LieTypeIndex.characteristic_tits] at hd
    exact absurd rfl hd

section Orders


theorem card_ne_of_oddCatalog {G : Type} [Group G] (d : ValidLieTypeIndex)
    (hd : d.1.characteristic ≠ 2) (e : G ≃* d.Group) : Nat.card G ≠ 20160 := by
  obtain ⟨t, n, f, hm⟩ := exists_blueprint_lieModel_of_odd d hd e
  exact lieModel_odd_card_ne_L34 lieOrderFormulasInput hd hm.admissible hm

theorem card_mul_divisor_of_lieModel {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (hm : CFSG.Blueprint.LieModel X t n p f) :
    Nat.card X * lieOrderDivisor t n (p ^ f) = lieOrderNumerator t n (p ^ f) :=
  (lieOrderFormulasInput X t n p f hm.admissible hm).2.1

theorem card_ne_of_typeA_one_eight {G : Type} [Group G] (q : PrimePower)
    (hv : (LieTypeIndex.A 1 q).Valid) (hq : q.card = 8) (e : G ≃* ValidLieTypeIndex.Group ⟨.A 1 q, hv⟩) :
    Nat.card G ≠ 20160 := by
  intro hcard
  have hm := CFSG.Models.LieModel.toBlueprint (by simp [CFSG.Blueprint.classicalTags])
    (CFSG.Models.lieModel_A 1 q hv e)
  have h := card_mul_divisor_of_lieModel hm
  have h8 : q.p ^ q.exponent = 8 := (PrimePower.card_def q).symm.trans hq
  rw [h8, hcard] at h
  have h1 : lieOrderDivisor .PSL (1 + 1) 8 = 1 := by decide
  have h2 : lieOrderNumerator .PSL (1 + 1) 8 = 504 := by decide
  rw [h1, h2] at h
  omega

theorem card_ne_of_typeTwistedA_three_two {G : Type} [Group G] (q : PrimePower)
    (hv : (LieTypeIndex.twistedA 3 q).Valid) (hq : q.card = 2)
    (e : G ≃* ValidLieTypeIndex.Group ⟨.twistedA 3 q, hv⟩) : Nat.card G ≠ 20160 := by
  intro hcard
  have hm := CFSG.Models.lieModel_twistedA 3 q hv e
  have hc : ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩ = q.p :=
    LieTypeIndex.characteristic_twistedA 3 q
  have hf : ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 q, hv⟩ = q.exponent :=
    LieTypeIndex.fieldExponent_twistedA 3 q
  rw [hc, hf] at hm
  have h := card_mul_divisor_of_lieModel (CFSG.Models.LieModel.toBlueprint
    (by simp [CFSG.Blueprint.classicalTags]) hm)
  have h2 : q.p ^ q.exponent = 2 := (PrimePower.card_def q).symm.trans hq
  rw [h2, hcard] at h
  have h1 : lieOrderDivisor .PSU (3 + 1) 2 = 1 := by decide
  have h3 : lieOrderNumerator .PSU (3 + 1) 2 = 25920 := by decide
  rw [h1, h3] at h
  omega

theorem not_isChevSimple_of_isLThreeFour {r : ℕ} (hr2 : r ≠ 2) {T : Type} [Group T]
    (hT : IsLThreeFour T) : ¬ IsChevSimple r T := by
  have hcard : Nat.card T = 20160 := card_eq_of_isLThreeFour hT
  rintro (⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩)
  · cases i with
    | cyclic q hq => exact hi
    | alternating n hn => exact hi
    | sporadic s => exact hi
    | lie d =>
      have hd : d.1.characteristic = r := hi
      exact card_ne_of_oddCatalog d (hd ▸ hr2) e hcard
  · cases i with
    | cyclic q hq => exact hi
    | sporadic s => exact hi
    | alternating n hn =>
      have e' : T ≃* alternatingGroup (Fin n) := e
      haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
      have h := Nat.card_congr e'.toEquiv
      rw [hcard, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at h
      rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨-, rfl⟩
      · norm_num [Nat.factorial] at h
      · norm_num [Nat.factorial] at h
      · exact hr2 rfl
    | lie d =>
      obtain ⟨ld, hv⟩ := d
      cases ld with
      | A n q =>
        rcases n with _ | _ | n
        · exact hi.elim
        · change (q.card = 7 ∧ r = 2) ∨ (q.card = 8 ∧ r = 3) at hi
          rcases hi with ⟨-, rfl⟩ | ⟨hq, -⟩
          · exact hr2 rfl
          · exact card_ne_of_typeA_one_eight q hv hq e hcard
        · exact hi.elim
      | twistedA n q =>
        rcases n with _ | _ | _ | _ | n
        · exact hi.elim
        · exact hi.elim
        · change q.card = 3 ∧ r = 2 at hi
          exact hr2 hi.2
        · change q.card = 2 ∧ r = 3 at hi
          exact card_ne_of_typeTwistedA_three_two q hv hi.1 e hcard
        · exact hi.elim
      | B n q => exact hi.elim
      | C n q => exact hi.elim
      | D n q => exact hi.elim
      | twistedD n q => exact hi.elim
      | E6 q => exact hi.elim
      | E7 q => exact hi.elim
      | E8 q => exact hi.elim
      | F4 q => exact hi.elim
      | G2 q => exact hi.elim
      | twistedE6 q => exact hi.elim
      | trialityD4 q => exact hi.elim
      | suzuki m => exact hi.elim
      | reeG2 m => exact hi.elim
      | reeF4 m => exact hi.elim
      | tits => exact hi.elim

end Orders

end Bridges

end CFSG.HardMathSupport.Dickson.Sec6
