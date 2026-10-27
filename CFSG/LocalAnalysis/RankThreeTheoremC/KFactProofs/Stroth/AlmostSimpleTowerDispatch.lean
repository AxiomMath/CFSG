module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleSplit
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleTowerClassical
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleTowerLinear
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleA

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open CFSG.AGLEmbedding CFSG.LieType.SeitzGeneration

@[expose] def IsExceptionalLieIndex : TauCeti.LieTypeIndex → Prop
  | .E6 _ | .E7 _ | .E8 _ | .F4 _ | .G2 _ | .twistedE6 _ | .trialityD4 _
  | .suzuki _ | .reeG2 _ | .reeF4 _ | .tits => True
  | _ => False

structure ExceptionalTowers : Prop where
  sporadic : ∀ (s : TauCeti.SporadicName) (p : ℕ), p.Prime → p ≠ 2 →
    OutTowerAt (TauCeti.CFSGIndex.sporadic s).Group p
  lie : ∀ (d : TauCeti.ValidLieTypeIndex), IsExceptionalLieIndex d.1 → ∀ (p : ℕ), p.Prime →
    p ≠ 2 → OutTowerAt (TauCeti.CFSGIndex.lie d).Group p

@[expose] def LinearOuterResidual : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X) [L.Normal],
    Subgroup.centralizer (L : Set X) = ⊥ →
    (∀ E : Subgroup X, IsElemAbelian p E → Nat.card E ≤ p ^ 2) →
    ∀ (m : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A m q).Valid), 2 ≤ m →
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.lie ⟨.A m q, hv⟩).Group) →
      p ∣ Nat.totient (Nat.gcd (m + 1) (q.card - 1)) → ¬ p ∣ q.card - 1 →
      ∀ x : X, (∃ k : ℕ, x ^ (p ^ k) = 1) → x ∈ L

@[expose] def UnitaryOuterResidual : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X) [L.Normal],
    Subgroup.centralizer (L : Set X) = ⊥ →
    (∀ E : Subgroup X, IsElemAbelian p E → Nat.card E ≤ p ^ 2) →
    ∀ (m : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA m q).Valid), 2 ≤ m →
      Nonempty (↥L ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA m q, hv⟩).Group) →
      p ∣ Nat.totient (Nat.gcd (m + 1) (q.card + 1)) → ¬ p ∣ q.card + 1 →
      ∀ x : X, (∃ k : ℕ, x ^ (p ^ k) = 1) → x ∈ L

@[expose] def AlmostSimpleTowerResidual : Prop :=
  LinearOuterResidual ∧ UnitaryOuterResidual

theorem almostSimplePartA_of_inputs (hT : ExceptionalTowers) (hLin : LinearOuterResidual)
    (hUni : UnitaryOuterResidual) : AlmostSimplePartA := by
  intro p hp hp2 X _ _ L _ hs hnab hcat hnalt hC hE
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨i, ⟨e⟩⟩ := hcat
  have hrkL : RankLE2 p ↥L := rankLE2_of_subgroup L hE
  have key : OutTowerAt ↥L p ∨ (∀ x : X, (∃ k : ℕ, x ^ (p ^ k) = 1) → x ∈ L) := by
    cases i with
    | cyclic r hr =>
      exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _))
    | alternating n hn => exact absurd ⟨n, ⟨e⟩⟩ hnalt
    | sporadic s => exact Or.inl (OutTowerAt.of_mulEquiv e (hT.sporadic s p hp hp2))
    | lie d =>
      obtain ⟨d, hv⟩ := d
      have hrk : RankLE2 p (Cat ⟨d, hv⟩) := RankLE2.of_mulEquiv e hrkL
      have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
        ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
      cases d with
      | A m q =>
        have hm1 : 1 ≤ m := hrange.1
        rcases Nat.lt_or_ge m 2 with h1 | hm2
        · obtain rfl : m = 1 := by omega
          exact Or.inl (OutTowerAt.of_mulEquiv e (outTowerAt_catA_one hv))
        · rcases outTowerAt_catA_or hm2 hv hp hp2 hrk with h | ⟨hφ, hq1⟩
          · exact Or.inl (OutTowerAt.of_mulEquiv e h)
          · exact Or.inr (hLin p hp hp2 X L hC hE m q hv hm2 ⟨e⟩ hφ hq1)
      | twistedA m q =>
        rcases outTowerAt_cat_twistedA_or hv hp hp2 hrk with h | ⟨hφ, hq1⟩
        · exact Or.inl (OutTowerAt.of_mulEquiv e h)
        · exact Or.inr (hUni p hp hp2 X L hC hE m q hv
            (TauCeti.LieTypeIndex.two_le_of_twistedA_inStandardRange
              ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1) ⟨e⟩ hφ hq1)
      | B r q =>
        have hr2 : 2 ≤ r := hrange.1
        rcases Nat.lt_or_ge r 3 with hr3 | hr3
        · obtain rfl : r = 2 := by omega
          exact Or.inl (OutTowerAt.of_mulEquiv e (outTowerAt_catB_two hv))
        · by_cases hq2 : q.p = 2
          · exact Or.inl (OutTowerAt.of_mulEquiv e (outTowerAt_catB_even hr3 hq2 hv))
          · exact Or.inl (OutTowerAt.of_mulEquiv e
              (outTowerAt_catOrth (d := ⟨.B r q, hv⟩) (Or.inl ⟨r, q, rfl, hr3, hq2⟩) hp hp2 hrk))
      | C r q => exact Or.inl (OutTowerAt.of_mulEquiv e (outTowerAt_catC hv))
      | D r q =>
        exact Or.inl (OutTowerAt.of_mulEquiv e
          (outTowerAt_catOrth (d := ⟨.D r q, hv⟩) (Or.inr (Or.inl ⟨r, q, rfl⟩)) hp hp2 hrk))
      | twistedD r q =>
        exact Or.inl (OutTowerAt.of_mulEquiv e
          (outTowerAt_catOrth (d := ⟨.twistedD r q, hv⟩) (Or.inr (Or.inr ⟨r, q, rfl⟩)) hp hp2 hrk))
      | E6 q => exact Or.inl (OutTowerAt.of_mulEquiv e (hT.lie ⟨.E6 q, hv⟩ trivial p hp hp2))
      | E7 q => exact Or.inl (OutTowerAt.of_mulEquiv e (hT.lie ⟨.E7 q, hv⟩ trivial p hp hp2))
      | E8 q => exact Or.inl (OutTowerAt.of_mulEquiv e (hT.lie ⟨.E8 q, hv⟩ trivial p hp hp2))
      | F4 q => exact Or.inl (OutTowerAt.of_mulEquiv e (hT.lie ⟨.F4 q, hv⟩ trivial p hp hp2))
      | G2 q => exact Or.inl (OutTowerAt.of_mulEquiv e (hT.lie ⟨.G2 q, hv⟩ trivial p hp hp2))
      | twistedE6 q =>
        exact Or.inl (OutTowerAt.of_mulEquiv e (hT.lie ⟨.twistedE6 q, hv⟩ trivial p hp hp2))
      | trialityD4 q =>
        exact Or.inl (OutTowerAt.of_mulEquiv e (hT.lie ⟨.trialityD4 q, hv⟩ trivial p hp hp2))
      | suzuki m => exact Or.inl (OutTowerAt.of_mulEquiv e (hT.lie ⟨.suzuki m, hv⟩ trivial p hp hp2))
      | reeG2 m => exact Or.inl (OutTowerAt.of_mulEquiv e (hT.lie ⟨.reeG2 m, hv⟩ trivial p hp hp2))
      | reeF4 m => exact Or.inl (OutTowerAt.of_mulEquiv e (hT.lie ⟨.reeF4 m, hv⟩ trivial p hp hp2))
      | tits => exact Or.inl (OutTowerAt.of_mulEquiv e (hT.lie ⟨.tits, hv⟩ trivial p hp hp2))
  rcases key with hTower | hP
  · exact pClosed_of_outTower hC hTower
  · exact sylow_normal_of_pElements_mem hP

theorem almostSimplePartA_of_residual_of_towers (hT : ExceptionalTowers)
    (h : AlmostSimpleTowerResidual) : AlmostSimplePartA :=
  almostSimplePartA_of_inputs hT h.1 h.2

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
