module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29Parts
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossOut
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossRank

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

@[expose] def CrossAbelianAt (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → d.1.characteristic ≠ p →
    ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L →
      Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) → ¬ IsLinearOrUnitaryAt p L →
      CFSG.Open.pRank p (⊤ : Subgroup L) = 2 → ∀ P : Sylow p L, IsMulCommutative (P : Subgroup L)

@[expose] def CrossRankAt (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → d.1.characteristic ≠ p →
    ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L →
      Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) → ¬ IsLinearOrUnitaryAt p L →
      3 ≤ CFSG.Open.pRank p (⊤ : Subgroup L) →
      ∀ y : L, orderOf y = p → 3 ≤ CFSG.Open.pRank p (centralizer ({y} : Set L))

@[expose] def CrossSylowAbelianAt (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → d.1.characteristic ≠ p →
    ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L →
      Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) → ∀ P : Sylow p L,
        IsMulCommutative (P : Subgroup L)

@[expose] def CrossAt (d : TauCeti.ValidLieTypeIndex) : Prop :=
  CrossAbelianAt d ∧ CrossRankAt d

theorem crossAt_of_sylowAbelian {d : TauCeti.ValidLieTypeIndex} (hab : CrossSylowAbelianAt d) :
    CrossAt d := by
  refine ⟨fun p hp hp5 hdp L _ _ hs hiso _ _ => hab p hp hp5 hdp L hs hiso, ?_⟩
  intro p hp hp5 hdp L _ _ hs hiso _ h3 y hy
  haveI : Fact p.Prime := ⟨hp⟩
  exact three_le_pRank_centralizer_of_sylow_abelian (hab p hp hp5 hdp L hs hiso) h3
    (hy ▸ pow_orderOf_eq_one y)

@[expose] def CrossFamLinear : Prop :=
  ∀ (m : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A m q).Valid),
    CrossAt ⟨.A m q, hv⟩

@[expose] def CrossFamUnitary : Prop :=
  ∀ (m : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA m q).Valid),
    CrossAt ⟨.twistedA m q, hv⟩

@[expose] def CrossFamB : Prop :=
  ∀ (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.B r q).Valid),
    CrossAt ⟨.B r q, hv⟩

@[expose] def CrossFamC : Prop :=
  ∀ (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.C r q).Valid),
    CrossAt ⟨.C r q, hv⟩

@[expose] def CrossFamD : Prop :=
  ∀ (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D r q).Valid),
    CrossAt ⟨.D r q, hv⟩

@[expose] def CrossFamTwistedD : Prop :=
  ∀ (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid),
    CrossAt ⟨.twistedD r q, hv⟩

@[expose] def CrossFamE6 : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E6 q).Valid), CrossAt ⟨.E6 q, hv⟩

@[expose] def CrossFamTwistedE6 : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid),
    CrossAt ⟨.twistedE6 q, hv⟩

@[expose] def CrossFamE7 : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E7 q).Valid), CrossAt ⟨.E7 q, hv⟩

@[expose] def CrossFamE8 : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E8 q).Valid), CrossAt ⟨.E8 q, hv⟩

@[expose] def CrossFamF4 : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.F4 q).Valid), CrossAt ⟨.F4 q, hv⟩

@[expose] def CrossFamG2 : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid), CrossAt ⟨.G2 q, hv⟩

@[expose] def CrossFamTrialityD4 : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
    CrossAt ⟨.trialityD4 q, hv⟩

@[expose] def CrossFamSuzuki : Prop :=
  ∀ (m : ℕ) (hv : (TauCeti.LieTypeIndex.suzuki m).Valid), CrossAt ⟨.suzuki m, hv⟩

@[expose] def CrossFamReeG2 : Prop :=
  ∀ (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeG2 m).Valid), CrossAt ⟨.reeG2 m, hv⟩

@[expose] def CrossFamReeF4 : Prop :=
  ∀ (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid), CrossAt ⟨.reeF4 m, hv⟩

@[expose] def CrossFamTits : Prop :=
  ∀ hv : TauCeti.LieTypeIndex.tits.Valid, CrossAt ⟨.tits, hv⟩

section Assembly


theorem kd29Cross_of_at (h : ∀ d : TauCeti.ValidLieTypeIndex, CrossAt d) : KD29Cross := by
  intro p hp hp5 X _ _ L _ hs hn hc ⟨d, hdp, ⟨e⟩⟩ hl hcen h3 ⟨x, hxL, hx, hxc⟩ w hw hw1 hwp
  exfalso
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hAb, hRk⟩ := h d
  exact false_of_cross_core L (pRank_quotient_le_one_of_catalog hp hp5 L hs hn hc hl hcen)
    (fun h3' y hy => hRk p hp hp5 hdp L hs ⟨e⟩ hl h3' y hy)
    (fun h2 => hAb p hp hp5 hdp L hs ⟨e⟩ hl h2) h3 hxL hx hxc

theorem kd29Cross_of_families (hA : CrossFamLinear) (htA : CrossFamUnitary) (hB : CrossFamB)
    (hC : CrossFamC) (hD : CrossFamD) (htD : CrossFamTwistedD) (hE6 : CrossFamE6)
    (htE6 : CrossFamTwistedE6) (hE7 : CrossFamE7) (hE8 : CrossFamE8) (hF4 : CrossFamF4)
    (hG2 : CrossFamG2) (htr : CrossFamTrialityD4) (hSz : CrossFamSuzuki)
    (hRG : CrossFamReeG2) (hRF : CrossFamReeF4) (hT : CrossFamTits) : KD29Cross := by
  refine kd29Cross_of_at fun d => ?_
  obtain ⟨d, hv⟩ := d
  cases d with
  | A m q => exact hA m q hv
  | twistedA m q => exact htA m q hv
  | B r q => exact hB r q hv
  | C r q => exact hC r q hv
  | D r q => exact hD r q hv
  | twistedD r q => exact htD r q hv
  | E6 q => exact hE6 q hv
  | E7 q => exact hE7 q hv
  | E8 q => exact hE8 q hv
  | F4 q => exact hF4 q hv
  | G2 q => exact hG2 q hv
  | twistedE6 q => exact htE6 q hv
  | trialityD4 q => exact htr q hv
  | suzuki m => exact hSz m hv
  | reeG2 m => exact hRG m hv
  | reeF4 m => exact hRF m hv
  | tits => exact hT hv

end Assembly

end CFSG.LocalAnalysis.RankFourTheoremC
