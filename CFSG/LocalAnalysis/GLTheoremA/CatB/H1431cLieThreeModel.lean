module

public import CFSG.Adapters.TauCetiExceptional.B1Exceptional
public import CFSG.Adapters.TauCetiExceptional.ReeBridge
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.Models.Blueprint
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open TauCeti CFSG.Assembly.LowTwoRank CFSG.Open

section Model


theorem lieS3_exists_model {G : Type} [Group G] (d : ValidLieTypeIndex)
    (hd : d.1.characteristic ≠ 2) (e : G ≃* d.Group) :
    ∃ (t : StatedLieTag) (n f : ℕ), CFSG.Blueprint.LieModel G t n d.1.characteristic f ∧
      t ≠ .Tits ∧ (t = .PSL → n = 2 →
        ∃ (q : PrimePower) (hv : (LieTypeIndex.A 1 q).Valid), d = ⟨.A 1 q, hv⟩) := by
  obtain ⟨d, hv⟩ := d
  change d.characteristic ≠ 2 at hd
  change ∃ (t : StatedLieTag) (n f : ℕ), CFSG.Blueprint.LieModel G t n d.characteristic f ∧
    t ≠ .Tits ∧ (t = .PSL → n = 2 →
      ∃ (q : PrimePower) (hv' : (LieTypeIndex.A 1 q).Valid), (⟨d, hv⟩ : ValidLieTypeIndex) =
        ⟨.A 1 q, hv'⟩)
  have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  cases d with
  | A r q =>
    rw [LieTypeIndex.characteristic_A]
    refine ⟨.PSL, r + 1, q.exponent, CFSG.Models.LieModel.toBlueprint
      (by simp [CFSG.Blueprint.classicalTags]) (CFSG.Models.lieModel_A r q hv e), by decide,
      fun _ hn => ?_⟩
    obtain rfl : r = 1 := by omega
    exact ⟨q, hv, rfl⟩
  | twistedA r q =>
    have h := CFSG.Models.lieModel_twistedA r q hv e
    simp only [ValidLieTypeIndex.characteristic, ValidLieTypeIndex.fieldExponent] at h
    exact ⟨.PSU, r + 1, _, CFSG.Models.LieModel.toBlueprint
      (by simp [CFSG.Blueprint.classicalTags]) h, by decide, fun h => absurd h (by decide)⟩
  | B r q =>
    rw [LieTypeIndex.characteristic_B]
    rcases CFSG.Models.lieModel_B r q hv e with h | h
    · exact ⟨.PSp, r, q.exponent, CFSG.Models.LieModel.toBlueprint
        (by simp [CFSG.Blueprint.classicalTags]) h, by decide, fun h => absurd h (by decide)⟩
    · exact ⟨.POmegaOdd, r, q.exponent, CFSG.Models.LieModel.toBlueprint
        (by simp [CFSG.Blueprint.classicalTags]) h, by decide, fun h => absurd h (by decide)⟩
  | C r q =>
    rw [LieTypeIndex.characteristic_C]
    exact ⟨.PSp, r, q.exponent, CFSG.Models.LieModel.toBlueprint
      (by simp [CFSG.Blueprint.classicalTags]) (CFSG.Models.lieModel_C r q hv e), by decide,
      fun h => absurd h (by decide)⟩
  | D r q =>
    rw [LieTypeIndex.characteristic_D]
    exact ⟨.POmegaPlus, r, q.exponent, CFSG.Models.LieModel.toBlueprint
      (by simp [CFSG.Blueprint.classicalTags]) (CFSG.Models.lieModel_D r q hv e), by decide,
      fun h => absurd h (by decide)⟩
  | twistedD r q =>
    rw [LieTypeIndex.characteristic_twistedD]
    exact ⟨.POmegaMinus, r, q.exponent, CFSG.Models.LieModel.toBlueprint
      (by simp [CFSG.Blueprint.classicalTags]) (CFSG.Models.lieModel_twistedD r q hv e),
      by decide, fun h => absurd h (by decide)⟩
  | E6 q =>
    rw [LieTypeIndex.characteristic_E6] at hd ⊢
    have hm : CFSG.Blueprint.ChevalleyExceptionalModel G .E6 q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.e6 q hv hd e⟩
    exact ⟨.E6, 0, q.exponent, Or.inr (Or.inl ⟨rfl,
      by simp [CFSG.Blueprint.chevalleyExceptionalTags], hm⟩), by decide,
      fun h => absurd h (by decide)⟩
  | E7 q =>
    rw [LieTypeIndex.characteristic_E7] at hd ⊢
    have hm : CFSG.Blueprint.ChevalleyExceptionalModel G .E7 q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.e7 q hv hd e⟩
    exact ⟨.E7, 0, q.exponent, Or.inr (Or.inl ⟨rfl,
      by simp [CFSG.Blueprint.chevalleyExceptionalTags], hm⟩), by decide,
      fun h => absurd h (by decide)⟩
  | E8 q =>
    rw [LieTypeIndex.characteristic_E8] at hd ⊢
    have hm : CFSG.Blueprint.ChevalleyExceptionalModel G .E8 q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.e8 q hv hd e⟩
    exact ⟨.E8, 0, q.exponent, Or.inr (Or.inl ⟨rfl,
      by simp [CFSG.Blueprint.chevalleyExceptionalTags], hm⟩), by decide,
      fun h => absurd h (by decide)⟩
  | F4 q =>
    rw [LieTypeIndex.characteristic_F4] at hd ⊢
    have hm : CFSG.Blueprint.ChevalleyExceptionalModel G .F4 q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.f4 q hv hd e⟩
    exact ⟨.F4, 0, q.exponent, Or.inr (Or.inl ⟨rfl,
      by simp [CFSG.Blueprint.chevalleyExceptionalTags], hm⟩), by decide,
      fun h => absurd h (by decide)⟩
  | G2 q =>
    rw [LieTypeIndex.characteristic_G2] at hd ⊢
    have h3 : 3 ≤ q.p ^ q.exponent := by
      simpa only [LieTypeIndex.inStandardRange_iff, PrimePower.card_def] using hr
    have hm : CFSG.Blueprint.ChevalleyExceptionalModel G .G2 q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl, h3⟩, CFSG.TauCetiBridge.untwistedModel_of_bridge
        CFSG.TauCetiBridge.chevalleyBridges.g2 q hv hd e⟩
    exact ⟨.G2, 0, q.exponent, Or.inr (Or.inl ⟨rfl,
      by simp [CFSG.Blueprint.chevalleyExceptionalTags], hm⟩), by decide,
      fun h => absurd h (by decide)⟩
  | twistedE6 q =>
    rw [LieTypeIndex.characteristic_twistedE6] at hd ⊢
    have hm : CFSG.Blueprint.ChevalleyExceptionalModel G .twistedE6 q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, CFSG.TauCetiBridge.twistedModel_of_bridge
        CFSG.TauCetiBridge.Twisted.twistedBridge_twistedE6 q hv hd (by decide) e⟩
    exact ⟨.twistedE6, 0, q.exponent, Or.inr (Or.inl ⟨rfl,
      by simp [CFSG.Blueprint.chevalleyExceptionalTags], hm⟩), by decide,
      fun h => absurd h (by decide)⟩
  | trialityD4 q =>
    rw [LieTypeIndex.characteristic_trialityD4] at hd ⊢
    have hm : CFSG.Blueprint.ChevalleyExceptionalModel G .trialityD4 q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, CFSG.TauCetiBridge.twistedModel_of_bridge
        CFSG.TauCetiBridge.Twisted.twistedBridge_trialityD4 q hv hd (by decide) e⟩
    exact ⟨.trialityD4, 0, q.exponent, Or.inr (Or.inl ⟨rfl,
      by simp [CFSG.Blueprint.chevalleyExceptionalTags], hm⟩), by decide,
      fun h => absurd h (by decide)⟩
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
      by simp [CFSG.Blueprint.reeTitsTags], hm⟩)), by decide, fun h => absurd h (by decide)⟩
  | reeF4 m =>
    rw [LieTypeIndex.characteristic_reeF4] at hd
    exact absurd rfl hd
  | tits =>
    rw [LieTypeIndex.characteristic_tits] at hd
    exact absurd rfl hd

end Model

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
