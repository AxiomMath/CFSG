module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieL3

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def KDLevelFiniteLie (p : ℕ) : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex,
    (p = 3 → ∀ q : TauCeti.PrimePower,
      d.1 ≠ .A 1 q ∧ d.1 ≠ .A 2 q ∧ d.1 ≠ .twistedA 2 q) →
      (k2 p (TauCeti.CFSGIndex.lie d) → DownLe p 2 (TauCeti.CFSGIndex.lie d).Group) ∧
      (k3 p (TauCeti.CFSGIndex.lie d) → DownLe p 3 (TauCeti.CFSGIndex.lie d).Group)

@[expose] def KDLieRowSp4Eight : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.B 2 q).Valid), q.card = 8 →
    DownLe 3 2 (TauCeti.CFSGIndex.lie ⟨.B 2 q, hv⟩).Group

@[expose] def KDLieRowSp6Two : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.B 3 q).Valid), q.card = 2 →
    DownLe 3 2 (TauCeti.CFSGIndex.lie ⟨.B 3 q, hv⟩).Group

@[expose] def KDLieRowOmega8PlusTwo : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D 4 q).Valid), q.card = 2 →
    DownLe 3 2 (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group

@[expose] def KDLieRowG2Eight : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid), q.card = 8 →
    DownLe 3 2 (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group

@[expose] def KDLieRowU4Eight : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA 3 q).Valid), q.card = 8 →
    DownLe 3 2 (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group

@[expose] def KDLieRowU5Two : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA 4 q).Valid), q.card = 2 →
    DownLe 3 2 (TauCeti.CFSGIndex.lie ⟨.twistedA 4 q, hv⟩).Group

@[expose] def KDLieRowU6Two : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid), q.card = 2 →
    DownLe 3 2 (TauCeti.CFSGIndex.lie ⟨.twistedA 5 q, hv⟩).Group

@[expose] def KDLieRowTD4Two : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.card = 2 →
    DownLe 3 2 (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group

@[expose] def KDLieRowTitsThree : Prop :=
  ∀ hv : (TauCeti.LieTypeIndex.tits).Valid,
    DownLe 3 2 (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group

@[expose] def KDLieRowReeF4EightThree : Prop :=
  ∀ hv : (TauCeti.LieTypeIndex.reeF4 1).Valid,
    DownLe 3 2 (TauCeti.CFSGIndex.lie ⟨.reeF4 1, hv⟩).Group

@[expose] def KDLieRowTitsFive : Prop :=
  ∀ hv : (TauCeti.LieTypeIndex.tits).Valid,
    DownLe 5 2 (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group

@[expose] def KDLieRowReeF4ThirtyTwoFive : Prop :=
  ∀ hv : (TauCeti.LieTypeIndex.reeF4 2).Valid,
    DownLe 5 2 (TauCeti.CFSGIndex.lie ⟨.reeF4 2, hv⟩).Group

@[expose] def KDLieRowSzFive : Prop :=
  ∀ hv : (TauCeti.LieTypeIndex.suzuki 2).Valid,
    DownLe 5 2 (TauCeti.CFSGIndex.lie ⟨.suzuki 2, hv⟩).Group

@[expose] def KDLieRowsOpen : Prop :=
  KDLieRowSp4Eight ∧ KDLieRowSp6Two ∧ KDLieRowOmega8PlusTwo ∧ KDLieRowG2Eight ∧
    KDLieRowU4Eight ∧ KDLieRowU5Two ∧ KDLieRowU6Two ∧ KDLieRowTD4Two ∧ KDLieRowTitsThree ∧
    KDLieRowReeF4EightThree ∧ KDLieRowTitsFive ∧ KDLieRowReeF4ThirtyTwoFive ∧ KDLieRowSzFive

private theorem kdLF_k3Lie_excluded {ld : TauCeti.LieTypeIndex} (h : k3Lie ld)
    (hx : ∀ q : TauCeti.PrimePower, ld ≠ .A 1 q ∧ ld ≠ .A 2 q ∧ ld ≠ .twistedA 2 q) : False := by
  cases ld with
  | A n q =>
    rcases n with _ | _ | _ | n
    · exact (show False from h).elim
    · exact (show False from h).elim
    · exact (hx q).2.1 rfl
    · exact (show False from h).elim
  | twistedA n q =>
    rcases n with _ | _ | _ | n
    · exact (show False from h).elim
    · exact (show False from h).elim
    · exact (hx q).2.2 rfl
    · exact (show False from h).elim
  | _ => exact (show False from h).elim

theorem kdLevelFiniteLie_of_rows (h : KDLieRowsOpen) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → KDLevelFiniteLie p := by
  obtain ⟨hSp4, hSp6, hOm8, hG2, hU4, hU5, hU6, hTD4, hT3, hR8, hT5, hR32, hSz⟩ := h
  intro p _ _ d hx
  obtain ⟨ld, hv⟩ := d
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · cases ld with
    | A n q =>
      rcases n with _ | _ | _ | n
      · exact (show False from hk).elim
      · obtain ⟨rfl, -⟩ : p = 3 ∧ ¬ 3 ∣ q.card := hk
        exact ((hx rfl q).1 rfl).elim
      · rcases (show (p = 3 ∧ q.p = 2 ∧ Even q.exponent) ∨ (p = 13 ∧ q.card = 3) from hk) with
          ⟨rfl, -⟩ | ⟨rfl, hc⟩
        · exact ((hx rfl q).2.1 rfl).elim
        · exact lieRow_A2_three_thirteen q hv hc
      · exact (show False from hk).elim
    | twistedA n q =>
      rcases n with _ | _ | _ | _ | _ | _ | n
      · exact (show False from hk).elim
      · exact (show False from hk).elim
      · obtain ⟨rfl, -⟩ : p = 3 ∧ q.p = 2 ∧ Odd q.exponent ∧ 1 < q.exponent := hk
        exact ((hx rfl q).2.2 rfl).elim
      · obtain ⟨rfl, hc⟩ : p = 3 ∧ q.card = 8 := hk
        exact hU4 q hv hc
      · obtain ⟨rfl, hc⟩ : p = 3 ∧ q.card = 2 := hk
        exact hU5 q hv hc
      · obtain ⟨rfl, hc⟩ : p = 3 ∧ q.card = 2 := hk
        exact hU6 q hv hc
      · exact (show False from hk).elim
    | B n q =>
      rcases n with _ | _ | _ | _ | n
      · exact (show False from hk).elim
      · exact (show False from hk).elim
      · obtain ⟨rfl, hc⟩ : p = 3 ∧ q.card = 8 := hk
        exact hSp4 q hv hc
      · obtain ⟨rfl, hc⟩ : p = 3 ∧ q.card = 2 := hk
        exact hSp6 q hv hc
      · exact (show False from hk).elim
    | C _ _ => exact (show False from hk).elim
    | D n q =>
      rcases n with _ | _ | _ | _ | _ | n
      · exact (show False from hk).elim
      · exact (show False from hk).elim
      · exact (show False from hk).elim
      · exact (show False from hk).elim
      · obtain ⟨rfl, hc⟩ : p = 3 ∧ q.card = 2 := hk
        exact hOm8 q hv hc
      · exact (show False from hk).elim
    | twistedD _ _ => exact (show False from hk).elim
    | E6 _ => exact (show False from hk).elim
    | E7 _ => exact (show False from hk).elim
    | E8 _ => exact (show False from hk).elim
    | F4 _ => exact (show False from hk).elim
    | G2 q =>
      obtain ⟨rfl, hc⟩ : p = 3 ∧ q.card = 8 := hk
      exact hG2 q hv hc
    | twistedE6 _ => exact (show False from hk).elim
    | trialityD4 q =>
      obtain ⟨rfl, hc⟩ : p = 3 ∧ q.card = 2 := hk
      exact hTD4 q hv hc
    | suzuki m =>
      obtain ⟨rfl, rfl⟩ : p = 5 ∧ m = 2 := hk
      exact hSz hv
    | reeG2 _ => exact (show False from hk).elim
    | reeF4 m =>
      rcases (show (p = 3 ∧ m = 1) ∨ (p = 5 ∧ m = 2) from hk) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hR8 hv
      · exact hR32 hv
    | tits =>
      rcases (show p = 3 ∨ p = 5 from hk) with rfl | rfl
      · exact hT3 hv
      · exact hT5 hv
  · obtain ⟨rfl, hc⟩ : p = 3 ∧ k3Lie ld := hk
    exact (kdLF_k3Lie_excluded hc (hx rfl)).elim

end CFSG.LocalAnalysis.GLTheoremA
