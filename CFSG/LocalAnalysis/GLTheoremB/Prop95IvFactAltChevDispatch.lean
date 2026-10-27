module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvFactAltChevOrder
public import CFSG.Adapters.LieModelOrders
public import CFSG.Adapters.TauCetiExceptional.EvenB1
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExclusionsTwo
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
public import CFSG.Models.Blueprint
public import CFSG.RankThree.PartOne.S12K.Rigidity
public import CFSG.RankThree.PartTwo.Sec16.Item166Proof

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95IvFact

open CFSG.Open CFSG.EvenSmallLie.CatalogOrders CFSG.LocalAnalysis.GLTheoremB.Prop95Parts


theorem c2_A {r f : ℕ} (hr : 1 ≤ r) (hf : 1 ≤ f) : Char2Order (ordA r (2 ^ f)) := by
  exact Or.inl ⟨r, f, hr, hf, rfl⟩

theorem c2_twistedA {r f : ℕ} (hr : 2 ≤ r) (hf : 1 ≤ f) :
    Char2Order (ordTwistedA r (2 ^ f)) := by
  exact Or.inr <| Or.inl ⟨r, f, hr, hf, rfl⟩

theorem c2_BC {r f : ℕ} (hr : 2 ≤ r) (hf : 1 ≤ f) : Char2Order (ordBC r (2 ^ f)) := by
  exact Or.inr <| Or.inr <| Or.inl ⟨r, f, hr, hf, rfl⟩

theorem c2_D {r f : ℕ} (hr : 4 ≤ r) (hf : 1 ≤ f) : Char2Order (ordD r (2 ^ f)) := by
  exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨r, f, hr, hf, rfl⟩

theorem c2_twistedD {r f : ℕ} (hr : 4 ≤ r) (hf : 1 ≤ f) :
    Char2Order (ordTwistedD r (2 ^ f)) := by
  exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨r, f, hr, hf, rfl⟩

theorem c2_E6 {f : ℕ} (hf : 1 ≤ f) : Char2Order (ordE6 (2 ^ f)) := by
  exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨f, hf, rfl⟩

theorem c2_E7 {f : ℕ} (hf : 1 ≤ f) : Char2Order (ordE7 (2 ^ f)) := by
  exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨f, hf, rfl⟩

theorem c2_E8 {f : ℕ} (hf : 1 ≤ f) : Char2Order (ordE8 (2 ^ f)) := by
  exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨f, hf, rfl⟩

theorem c2_F4 {f : ℕ} (hf : 1 ≤ f) : Char2Order (ordF4 (2 ^ f)) := by
  exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
    Or.inl ⟨f, hf, rfl⟩

theorem c2_G2 {f : ℕ} (hf : 1 ≤ f) : Char2Order (ordG2 (2 ^ f)) := by
  exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
    Or.inr <| Or.inl ⟨f, hf, rfl⟩

theorem c2_twistedE6 {f : ℕ} (hf : 1 ≤ f) : Char2Order (ordTwistedE6 (2 ^ f)) := by
  exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
    Or.inr <| Or.inr <| Or.inl ⟨f, hf, rfl⟩

theorem c2_trialityD4 {f : ℕ} (hf : 1 ≤ f) : Char2Order (ordTrialityD4 (2 ^ f)) := by
  exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
    Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨f, hf, rfl⟩

theorem c2_suzuki {a : ℕ} (ha : 1 ≤ a) : Char2Order (ordSuzuki (2 ^ (2 * a + 1))) := by
  exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
    Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨a, ha, rfl⟩

theorem c2_twistedF4 {a : ℕ} (ha : 1 ≤ a) : Char2Order (ordTwistedF4 (2 ^ (2 * a + 1))) := by
  exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
    Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨a, ha, rfl⟩

theorem c2_tits : Char2Order ordTits := by
  exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
    Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| rfl

theorem char2_A (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A r q).Valid)
    (hd : q.p = 2) {G : Type} [Group G]
    (e : G ≃* (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group) : Char2Order (Nat.card G) := by
  have hr : 1 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1).1
  have hL := CFSG.Models.lieModel_A r q hv e
  have hB := CFSG.Models.LieModel.toBlueprint (by decide) hL
  rw [hd] at hB
  rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by omega) hB]
  exact c2_A hr q.exponent_pos

theorem char2_twistedA (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (hd : q.p = 2) {G : Type} [Group G]
    (e : G ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group) : Char2Order (Nat.card G) := by
  have hr : 2 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1).1
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ = 2 :=
    (TauCeti.LieTypeIndex.characteristic_twistedA r q).trans hd
  have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩ = q.exponent :=
    TauCeti.LieTypeIndex.fieldExponent_twistedA r q
  have hL := CFSG.Models.lieModel_twistedA r q hv e
  rw [hc, hf] at hL
  have hB := CFSG.Models.LieModel.toBlueprint (by decide) hL
  rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by omega) hB]
  exact c2_twistedA hr q.exponent_pos

theorem char2_B (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.B r q).Valid)
    (hd : q.p = 2) {G : Type} [Group G]
    (e : G ≃* (TauCeti.CFSGIndex.lie ⟨.B r q, hv⟩).Group) : Char2Order (Nat.card G) := by
  have hr : 2 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1).1
  rcases CFSG.Models.lieModel_B r q hv e with hL | hL
  · have hB := CFSG.Models.LieModel.toBlueprint (by decide) hL
    rw [hd] at hB
    rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by omega) hB]
    exact c2_BC hr q.exponent_pos
  · have hB := CFSG.Models.LieModel.toBlueprint (by decide) hL
    rw [hd] at hB
    rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by omega) hB]
    exact c2_BC hr q.exponent_pos

theorem char2_D (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D r q).Valid)
    (hd : q.p = 2) {G : Type} [Group G]
    (e : G ≃* (TauCeti.CFSGIndex.lie ⟨.D r q, hv⟩).Group) : Char2Order (Nat.card G) := by
  have hr : 4 ≤ r := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have hL := CFSG.Models.lieModel_D r q hv e
  have hB := CFSG.Models.LieModel.toBlueprint (by decide) hL
  rw [hd] at hB
  rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by omega) hB]
  exact c2_D hr q.exponent_pos

theorem char2_twistedD (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid) (hd : q.p = 2) {G : Type} [Group G]
    (e : G ≃* (TauCeti.CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group) : Char2Order (Nat.card G) := by
  have hr : 4 ≤ r := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have hL := CFSG.Models.lieModel_twistedD r q hv e
  have hB := CFSG.Models.LieModel.toBlueprint (by decide) hL
  rw [hd] at hB
  rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by omega) hB]
  exact c2_twistedD hr q.exponent_pos

theorem char2_E6 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E6 q).Valid)
    (hd : q.p = 2) {G : Type} [Group G]
    (e : G ≃* (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group) : Char2Order (Nat.card G) := by
  rw [Nat.card_congr e.toEquiv, CFSG.AGLEmbedding.card_catGroup_E6_even (d := ⟨.E6 q, hv⟩) hd rfl]
  exact c2_E6 q.exponent_pos

theorem char2_E7 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E7 q).Valid)
    (hd : q.p = 2) {G : Type} [Group G]
    (e : G ≃* (TauCeti.CFSGIndex.lie ⟨.E7 q, hv⟩).Group) : Char2Order (Nat.card G) := by
  have hm : CFSG.Blueprint.ChevalleyExceptionalModel G .E7 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.e7 q hv hd e⟩
  rw [hd] at hm
  have hc : Nat.card G = CFSG.Open.ordE7 (2 ^ q.exponent) :=
    CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hm
  rw [hc]
  exact c2_E7 q.exponent_pos

theorem char2_E8 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E8 q).Valid)
    (hd : q.p = 2) {G : Type} [Group G]
    (e : G ≃* (TauCeti.CFSGIndex.lie ⟨.E8 q, hv⟩).Group) : Char2Order (Nat.card G) := by
  have hm : CFSG.Blueprint.ChevalleyExceptionalModel G .E8 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.e8 q hv hd e⟩
  rw [hd] at hm
  have hc : Nat.card G = CFSG.Open.ordE8 (2 ^ q.exponent) :=
    CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hm
  rw [hc]
  exact c2_E8 q.exponent_pos

theorem char2_F4 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.F4 q).Valid)
    (hd : q.p = 2) {G : Type} [Group G]
    (e : G ≃* (TauCeti.CFSGIndex.lie ⟨.F4 q, hv⟩).Group) : Char2Order (Nat.card G) := by
  rw [Nat.card_congr e.toEquiv, CFSG.AGLEmbedding.card_catGroup_F4_even (d := ⟨.F4 q, hv⟩) hd rfl]
  exact c2_F4 q.exponent_pos

theorem char2_G2 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid)
    (hd : q.p = 2) {G : Type} [Group G]
    (e : G ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group) : Char2Order (Nat.card G) := by
  rw [Nat.card_congr e.toEquiv, CFSG.AGLEmbedding.card_catGroup_G2_even (d := ⟨.G2 q, hv⟩) hd rfl]
  exact c2_G2 q.exponent_pos

theorem char2_twistedE6 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid)
    (hd : q.p = 2) {G : Type} [Group G]
    (e : G ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group) : Char2Order (Nat.card G) := by
  have hm : CFSG.Blueprint.ChevalleyExceptionalModel G .twistedE6 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.twistedE6 q hv hd (by decide) e⟩
  rw [hd] at hm
  have hc : Nat.card G = CFSG.Open.ordTwistedE6 (2 ^ q.exponent) :=
    CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hm
  rw [hc]
  exact c2_twistedE6 q.exponent_pos

theorem char2_trialityD4 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) (hd : q.p = 2) {G : Type} [Group G]
    (e : G ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group) : Char2Order (Nat.card G) := by
  rw [Nat.card_congr e.toEquiv,
    CFSG.AGLEmbedding.card_catGroup_trialityD4_even (d := ⟨.trialityD4 q, hv⟩) hd rfl]
  exact c2_trialityD4 q.exponent_pos

theorem char2_suzuki (m : ℕ) (hv : (TauCeti.LieTypeIndex.suzuki m).Valid) {G : Type} [Group G]
    (e : G ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki m, hv⟩).Group) : Char2Order (Nat.card G) := by
  have hm1 : 1 ≤ m := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have hS := CFSG.RankThree.PartTwo.Sec16.suzukiModel_of_mulEquiv e
    (CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index m hv)
  obtain ⟨-, -, hc⟩ := CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_suzuki hS
  rw [hc]
  exact c2_suzuki hm1

theorem char2_reeF4 (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid) {G : Type} [Group G]
    (e : G ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group) : Char2Order (Nat.card G) := by
  have hm1 : 1 ≤ m := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  rw [Nat.card_congr e.toEquiv, CFSG.AGLEmbedding.card_catGroup_reeF4 (d := ⟨.reeF4 m, hv⟩) rfl]
  exact c2_twistedF4 hm1

theorem char2_tits {G : Type} [Group G] (hv : (TauCeti.LieTypeIndex.tits).Valid)
    (e : G ≃* (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group) : Char2Order (Nat.card G) := by
  have hR : CFSG.Blueprint.ReeTitsModel G .Tits 2 1 :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.reeTitsModel_tits_of_lie hv e
  rw [CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_Tits hR]
  exact c2_tits

theorem char2Order_of_chev2 (d : TauCeti.ValidLieTypeIndex)
    (hd : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsChevIndexTwo d.1)
    (G : Type) [Group G] (e : G ≃* (TauCeti.CFSGIndex.lie d).Group) :
    Char2Order (Nat.card G) := by
  obtain ⟨x, hv⟩ := d
  cases x with
  | A r q => exact char2_A r q hv hd e
  | twistedA r q => exact char2_twistedA r q hv hd e
  | B r q => exact char2_B r q hv hd e
  | C r q =>
    exact absurd (show q.p = 2 from hd)
      (((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
        ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1).2)
  | D r q => exact char2_D r q hv hd e
  | twistedD r q => exact char2_twistedD r q hv hd e
  | E6 q => exact char2_E6 q hv hd e
  | E7 q => exact char2_E7 q hv hd e
  | E8 q => exact char2_E8 q hv hd e
  | F4 q => exact char2_F4 q hv hd e
  | G2 q => exact char2_G2 q hv hd e
  | twistedE6 q => exact char2_twistedE6 q hv hd e
  | trialityD4 q => exact char2_trialityD4 q hv hd e
  | suzuki m => exact char2_suzuki m hv e
  | reeG2 m => exact (hd : False).elim
  | reeF4 m => exact char2_reeF4 m hv e
  | tits => exact char2_tits hv e

end CFSG.LocalAnalysis.GLTheoremB.Prop95IvFact
