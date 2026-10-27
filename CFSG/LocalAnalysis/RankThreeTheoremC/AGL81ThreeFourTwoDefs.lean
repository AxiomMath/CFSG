module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

@[expose] def ThreeFourTwoAt (p : ℕ) (X : Type*) [Group X] : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K Y₀ E : Subgroup Y) (R : Sylow p Y)
    (I T : Type) [Group I] [Finite I] [Group T] (σ : I →* Y) (ψ : I →* T),
    p.Prime → p ≠ 2 → K.Normal → Nonempty (K ≃* X) →
    pRank p (centralizer (K : Set Y)) ≤ 1 → centralizer (K : Set Y) ≤ Y₀ →
    (∀ L : Subgroup Y, IsComponentOf L ⊤ → L ≤ K → ¬ L ≤ Y₀) →
    E ≤ R → IsElemAbelian p E → Nat.card E = p ^ 2 →
    (if 3 ≤ pRank p (R : Subgroup Y) then GLBWeakCore p (R : Subgroup Y)
      else GLBCore p 1 E) ≤ Y₀ →
    σ.range ≤ Y₀ → IsSubnormal σ.range Y₀ → commutator I = ⊤ →
    Function.Surjective ψ → IsPGroup 2 ψ.ker → CFSG.Open.IsQuasisimple T →
    ¬ σ.range ≤ centralizer (K : Set Y) →
    ∃ iK iJ : TauCeti.CFSGIndex, IsThreeFourPair p iK iJ ∧ Nonempty (K ≃* iK.Group) ∧
      ∃ f : I →* iJ.Group, Function.Surjective f ∧ (centralizer (K : Set Y)).comap σ ≤ f.ker

@[expose] def ThreeFourTwoNoneAt (p : ℕ) (X : Type*) [Group X] : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K Y₀ E : Subgroup Y) (R : Sylow p Y)
    (I T : Type) [Group I] [Finite I] [Group T] (σ : I →* Y) (ψ : I →* T),
    p.Prime → p ≠ 2 → K.Normal → Nonempty (K ≃* X) →
    pRank p (centralizer (K : Set Y)) ≤ 1 → centralizer (K : Set Y) ≤ Y₀ →
    (∀ L : Subgroup Y, IsComponentOf L ⊤ → L ≤ K → ¬ L ≤ Y₀) →
    E ≤ R → IsElemAbelian p E → Nat.card E = p ^ 2 →
    (if 3 ≤ pRank p (R : Subgroup Y) then GLBWeakCore p (R : Subgroup Y)
      else GLBCore p 1 E) ≤ Y₀ →
    σ.range ≤ Y₀ → IsSubnormal σ.range Y₀ → commutator I = ⊤ →
    Function.Surjective ψ → IsPGroup 2 ψ.ker → CFSG.Open.IsQuasisimple T →
    σ.range ≤ centralizer (K : Set Y)

theorem ThreeFourTwoNoneAt.threeFourTwoAt {p : ℕ} {X : Type*} [Group X]
    (h : ThreeFourTwoNoneAt p X) : ThreeFourTwoAt p X := by
  intro Y _ _ K Y₀ E R I T _ _ _ σ ψ hp hp2 hK hKX hrk hC hcomp hER hE hEc hcore hσY hσs hI
    hψ hψk hT hσC
  exact absurd (h Y K Y₀ E R I T σ ψ hp hp2 hK hKX hrk hC hcomp hER hE hEc hcore hσY hσs hI hψ
    hψk hT) hσC

@[expose] def ThreeFourTwoLinTwo : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (q : TauCeti.PrimePower) (d : TauCeti.ValidLieTypeIndex),
    q.p = p → 2 ≤ q.exponent → d.1 = .A 1 q →
    ThreeFourTwoNoneAt p (TauCeti.CFSGIndex.lie d).Group

@[expose] def ThreeFourTwoUnitary : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (q : TauCeti.PrimePower) (d : TauCeti.ValidLieTypeIndex),
    q.p = p → d.1 = .twistedA 2 q → ThreeFourTwoNoneAt p (TauCeti.CFSGIndex.lie d).Group

@[expose] def ThreeFourTwoSpFour : Prop :=
  (∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (q : TauCeti.PrimePower) (d : TauCeti.ValidLieTypeIndex),
      q.p = p → q.exponent = 1 → d.1 = .B 2 q →
      ThreeFourTwoNoneAt p (TauCeti.CFSGIndex.lie d).Group) ∧
    ∀ (q : TauCeti.PrimePower) (d : TauCeti.ValidLieTypeIndex),
      q.p = 2 → q.exponent = 1 → d.1 = .twistedA 3 q →
      ThreeFourTwoNoneAt 3 (TauCeti.CFSGIndex.lie d).Group

@[expose] def ThreeFourTwoLinThree : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (q : TauCeti.PrimePower) (d : TauCeti.ValidLieTypeIndex),
    q.p = p → q.exponent = 1 → d.1 = .A 2 q →
    ThreeFourTwoNoneAt p (TauCeti.CFSGIndex.lie d).Group

@[expose] def ThreeFourTwoReeTwo : Prop :=
  ∀ (m : ℕ) (d : TauCeti.ValidLieTypeIndex), d.1 = .reeG2 m →
    ThreeFourTwoNoneAt 3 (TauCeti.CFSGIndex.lie d).Group

@[expose] def ThreeFourTwoThreeLie : Prop :=
  ∀ (q : TauCeti.PrimePower) (d : TauCeti.ValidLieTypeIndex), q.p = 2 →
    ((q.exponent = 3 ∧ d.1 = .A 1 q) ∨ (q.exponent = 2 ∧ d.1 = .A 2 q)) →
    ThreeFourTwoNoneAt 3 (TauCeti.CFSGIndex.lie d).Group

@[expose] def ThreeFourTwoThreePairs : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex,
    ((∃ q : TauCeti.PrimePower, q.p = 2 ∧
        ((q.exponent = 3 ∧ (d.1 = .G2 q ∨ d.1 = .B 2 q)) ∨ (q.exponent = 1 ∧ d.1 = .B 3 q))) ∨
      d.1 = .tits) →
    ThreeFourTwoAt 3 (TauCeti.CFSGIndex.lie d).Group

@[expose] def ThreeFourTwoThreeAlt : Prop :=
  ∀ (n : ℕ) (h : 5 ≤ n), (n = 6 ∨ n = 9) →
    ThreeFourTwoNoneAt 3 (TauCeti.CFSGIndex.alternating n h).Group

@[expose] def ThreeFourTwoThreeSporadic : Prop :=
  ∀ s : TauCeti.SporadicName, (s = .M11 ∨ s = .M12 ∨ s = .J3) →
    ThreeFourTwoNoneAt 3 (TauCeti.CFSGIndex.sporadic s).Group

@[expose] def ThreeFourTwoLTwoEightSq : Prop :=
  ∀ (q : TauCeti.PrimePower) (d : TauCeti.ValidLieTypeIndex), q.p = 2 → q.exponent = 3 →
    d.1 = .A 1 q →
    ThreeFourTwoNoneAt 3 ((TauCeti.CFSGIndex.lie d).Group × (TauCeti.CFSGIndex.lie d).Group)

@[expose] def ThreeFourTwoFiveLie : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, (d.1 = .suzuki 2 ∨ d.1 = .tits ∨ d.1 = .reeF4 2) →
    ThreeFourTwoNoneAt 5 (TauCeti.CFSGIndex.lie d).Group

@[expose] def ThreeFourTwoAltTen : Prop :=
  ∀ h : 5 ≤ 10, ThreeFourTwoAt 5 (TauCeti.CFSGIndex.alternating 10 h).Group

@[expose] def ThreeFourTwoSporadicNone : Prop :=
  (∀ s : TauCeti.SporadicName, (s = .McL ∨ s = .Ru) →
      ThreeFourTwoNoneAt 5 (TauCeti.CFSGIndex.sporadic s).Group) ∧
    ThreeFourTwoNoneAt 7 (TauCeti.CFSGIndex.sporadic .He).Group ∧
    ThreeFourTwoNoneAt 11 (TauCeti.CFSGIndex.sporadic .J4).Group

@[expose] def ThreeFourTwoSporadicPairs : Prop :=
  ThreeFourTwoAt 5 (TauCeti.CFSGIndex.sporadic .HS).Group ∧
    ∀ s : TauCeti.SporadicName, (s = .ONan ∨ s = .Fi24Prime) →
      CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic s).Group →
      ThreeFourTwoAt 7 (TauCeti.CFSGIndex.sporadic s).Group

@[expose] def ThreeFourTwoSzSq : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .suzuki 2 →
    ThreeFourTwoNoneAt 5 ((TauCeti.CFSGIndex.lie d).Group × (TauCeti.CFSGIndex.lie d).Group)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
