module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenSolvDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

@[expose] def ThreeFourSolvThreeAt (X : Type*) [Group X] : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K Y₀ E : Subgroup Y) (R : Sylow 3 Y)
    (I₀ : Type) [Group I₀] [Finite I₀] (σ : I₀ →* Y),
    K.Normal → Nonempty (K ≃* X) → Subgroup.center K = ⊥ →
    pRank 3 (⊤ : Subgroup Y) ≤ 3 →
    pRank 3 (centralizer (K : Set Y)) ≤ 1 → centralizer (K : Set Y) ≤ Y₀ →
    (∀ L : Subgroup Y, IsComponentOf L ⊤ → L ≤ K → ¬ L ≤ Y₀) →
    E ≤ R → IsElemAbelian 3 E → Nat.card E = 3 ^ 2 →
    (if 3 ≤ pRank 3 (R : Subgroup Y) then GLBWeakCore 3 (R : Subgroup Y)
      else GLBCore 3 1 E) ≤ Y₀ →
    pCoreOf 2 Y₀ ≤ centralizer (K : Set Y) →
    Nat.Coprime 3 (Nat.card σ.ker) → σ.range ≤ Y₀ → IsSubnormal σ.range Y₀ →
    IsSymThreeOrSUThreeTwo (I₀ ⧸ CFSG.pCore 2 I₀) → SolvThreeAutCond Y₀ σ →
    SolvThreeDirectCond Y₀
      ((CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).map σ) →
    ¬ (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).map σ ≤
      centralizer (K : Set Y) →
    (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).map σ ≤ K ∧
      IsSolvThreeTarget K

@[expose] def ThreeFourSolvThreeNoneAt (X : Type*) [Group X] : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K Y₀ E : Subgroup Y) (R : Sylow 3 Y)
    (I₀ : Type) [Group I₀] [Finite I₀] (σ : I₀ →* Y),
    K.Normal → Nonempty (K ≃* X) → Subgroup.center K = ⊥ →
    pRank 3 (⊤ : Subgroup Y) ≤ 3 →
    pRank 3 (centralizer (K : Set Y)) ≤ 1 → centralizer (K : Set Y) ≤ Y₀ →
    (∀ L : Subgroup Y, IsComponentOf L ⊤ → L ≤ K → ¬ L ≤ Y₀) →
    E ≤ R → IsElemAbelian 3 E → Nat.card E = 3 ^ 2 →
    (if 3 ≤ pRank 3 (R : Subgroup Y) then GLBWeakCore 3 (R : Subgroup Y)
      else GLBCore 3 1 E) ≤ Y₀ →
    pCoreOf 2 Y₀ ≤ centralizer (K : Set Y) →
    Nat.Coprime 3 (Nat.card σ.ker) → σ.range ≤ Y₀ → IsSubnormal σ.range Y₀ →
    IsSymThreeOrSUThreeTwo (I₀ ⧸ CFSG.pCore 2 I₀) → SolvThreeAutCond Y₀ σ →
    SolvThreeDirectCond Y₀
      ((CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).map σ) →
    (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).map σ ≤
      centralizer (K : Set Y)

@[expose] def ThreeFourSolvThreeLeAt (X : Type*) [Group X] : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K Y₀ E : Subgroup Y) (R : Sylow 3 Y)
    (I₀ : Type) [Group I₀] [Finite I₀] (σ : I₀ →* Y),
    K.Normal → Nonempty (K ≃* X) → Subgroup.center K = ⊥ →
    pRank 3 (⊤ : Subgroup Y) ≤ 3 →
    pRank 3 (centralizer (K : Set Y)) ≤ 1 → centralizer (K : Set Y) ≤ Y₀ →
    (∀ L : Subgroup Y, IsComponentOf L ⊤ → L ≤ K → ¬ L ≤ Y₀) →
    E ≤ R → IsElemAbelian 3 E → Nat.card E = 3 ^ 2 →
    (if 3 ≤ pRank 3 (R : Subgroup Y) then GLBWeakCore 3 (R : Subgroup Y)
      else GLBCore 3 1 E) ≤ Y₀ →
    pCoreOf 2 Y₀ ≤ centralizer (K : Set Y) →
    Nat.Coprime 3 (Nat.card σ.ker) → σ.range ≤ Y₀ → IsSubnormal σ.range Y₀ →
    IsSymThreeOrSUThreeTwo (I₀ ⧸ CFSG.pCore 2 I₀) → SolvThreeAutCond Y₀ σ →
    SolvThreeDirectCond Y₀
      ((CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).map σ) →
    ¬ (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).map σ ≤
      centralizer (K : Set Y) →
    (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).map σ ≤ K

theorem ThreeFourSolvThreeNoneAt.at {X : Type*} [Group X] (h : ThreeFourSolvThreeNoneAt X) :
    ThreeFourSolvThreeAt X := by
  intro Y _ _ K Y₀ E R I₀ _ _ σ hK hKX hZ hrk hrkC hC hcomp hER hE hEc hcore hO2 hker hσY hσs
    hb hcond hdir hJ
  exact absurd (h Y K Y₀ E R I₀ σ hK hKX hZ hrk hrkC hC hcomp hER hE hEc hcore hO2 hker hσY hσs
    hb hcond hdir) hJ

theorem ThreeFourSolvThreeLeAt.at {X : Type*} [Group X] (h : ThreeFourSolvThreeLeAt X)
    (hX : ∀ (K : Type) [Group K], Nonempty (K ≃* X) → IsSolvThreeTarget K) :
    ThreeFourSolvThreeAt X := by
  intro Y _ _ K Y₀ E R I₀ _ _ σ hK hKX hZ hrk hrkC hC hcomp hER hE hEc hcore hO2 hker hσY hσs
    hb hcond hdir hJ
  exact ⟨h Y K Y₀ E R I₀ σ hK hKX hZ hrk hrkC hC hcomp hER hE hEc hcore hO2 hker hσY hσs hb
    hcond hdir hJ, hX K hKX⟩

@[expose] def ThreeFourSolvThreeLinTwo : Prop :=
  ∀ (q : TauCeti.PrimePower) (d : TauCeti.ValidLieTypeIndex), q.p = 3 → 2 ≤ q.exponent →
    d.1 = .A 1 q → ThreeFourSolvThreeNoneAt (TauCeti.CFSGIndex.lie d).Group

@[expose] def ThreeFourSolvThreeUnitary : Prop :=
  ∀ (q : TauCeti.PrimePower) (d : TauCeti.ValidLieTypeIndex), q.p = 3 → d.1 = .twistedA 2 q →
    ThreeFourSolvThreeNoneAt (TauCeti.CFSGIndex.lie d).Group

@[expose] def ThreeFourSolvThreeLinThree : Prop :=
  ∀ (q : TauCeti.PrimePower) (d : TauCeti.ValidLieTypeIndex), q.p = 3 → q.exponent = 1 →
    d.1 = .A 2 q → ThreeFourSolvThreeNoneAt (TauCeti.CFSGIndex.lie d).Group

@[expose] def ThreeFourSolvThreeReeTwo : Prop :=
  ∀ (m : ℕ) (d : TauCeti.ValidLieTypeIndex), d.1 = .reeG2 m →
    ThreeFourSolvThreeNoneAt (TauCeti.CFSGIndex.lie d).Group

@[expose] def ThreeFourSolvThreeLie : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex,
    ((∃ q : TauCeti.PrimePower, q.p = 2 ∧
        ((q.exponent = 3 ∧ (d.1 = .A 1 q ∨ d.1 = .G2 q ∨ d.1 = .B 2 q)) ∨
          (q.exponent = 2 ∧ d.1 = .A 2 q))) ∨
      d.1 = .tits) →
    ThreeFourSolvThreeNoneAt (TauCeti.CFSGIndex.lie d).Group

@[expose] def ThreeFourSolvThreeSporadic : Prop :=
  ∀ s : TauCeti.SporadicName, (s = .M11 ∨ s = .M12 ∨ s = .J3) →
    ThreeFourSolvThreeNoneAt (TauCeti.CFSGIndex.sporadic s).Group

@[expose] def ThreeFourSolvThreeLTwoEightSq : Prop :=
  ∀ (q : TauCeti.PrimePower) (d : TauCeti.ValidLieTypeIndex), q.p = 2 → q.exponent = 3 →
    d.1 = .A 1 q →
    ThreeFourSolvThreeNoneAt ((TauCeti.CFSGIndex.lie d).Group × (TauCeti.CFSGIndex.lie d).Group)

@[expose] def ThreeFourSolvThreeTargets : Prop :=
  (∀ (n : ℕ) (h : 5 ≤ n), (n = 6 ∨ n = 9) →
      ThreeFourSolvThreeLeAt (TauCeti.CFSGIndex.alternating n h).Group) ∧
    ∀ (q : TauCeti.PrimePower) (d : TauCeti.ValidLieTypeIndex), q.p = 2 → q.exponent = 1 →
      (d.1 = .twistedA 3 q ∨ d.1 = .B 3 q) →
      ThreeFourSolvThreeLeAt (TauCeti.CFSGIndex.lie d).Group

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
