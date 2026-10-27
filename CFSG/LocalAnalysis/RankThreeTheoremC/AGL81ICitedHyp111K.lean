module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CfgData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def IsLieOver (K : Type) [Group K] (f : TauCeti.PrimePower → TauCeti.LieTypeIndex)
    (r e : ℕ) : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex,
    (∃ q : TauCeti.PrimePower, q.p = r ∧ q.exponent = e ∧ d.1 = f q) ∧
    Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def IsSzThirtyTwo (K : Type) [Group K] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, d.1 = .suzuki 2 ∧
    Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def IsSLThreeFour (K : Type) [Group K] : Prop :=
  IsQuasisimple K ∧ Nat.card (Subgroup.center K) = 3 ∧ IsLinThreeFour (K ⧸ Subgroup.center K)

@[expose] noncomputable def hyp111Star (p : ℕ) (H I : Subgroup G) :
    Subgroup (H ⧸ primeComplementCore (G := H) p) :=
  (I.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p))

@[expose] def HasNormalIndex (M : Subgroup G) (p : ℕ) : Prop :=
  ∃ N : Subgroup G, N ≤ M ∧ (N.subgroupOf M).Normal ∧ (N.subgroupOf M).index = p

@[expose] def AGL81NineEightTwo (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H₁ R₁ : Subgroup G), D1Escape p P M H₁ R₁ →
    ∀ H Q : Subgroup G, IsAGLQ p M Q → Q ≤ H → GLBIsMaxTwoLocal H → ¬ H ≤ M →
    (∃ S : Sylow p (d1KBar p M H), (S : Subgroup (d1KBar p M H)).map (d1KBar p M H).subtype =
      (Q.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓
        d1KBar p M H) →
    Hyp111B3 p H Q (d1KBar p M H) ∨
      (p = 3 ∧ ∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p),
        IsComponentOf L ⊤ ∧ ¬ L ≤ d1X0 p M H ∧
          (IsLinThreeFour L ∨ IsSLThreeFour L ∨ Nonempty (L ≃* alternatingGroup (Fin 11))))

@[expose] def AGL81EightTwo (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H₁ R₁ : Subgroup G), D1Escape p P M H₁ R₁ →
    rankThreeGamma 2 p (P : Subgroup G) ≤ M →
    (∀ a g : G, a ∈ (P : Subgroup G) → g * a * g⁻¹ ∈ (P : Subgroup G) →
      ∃ m ∈ M, m * a * m⁻¹ = g * a * g⁻¹) ∧ ¬ HasNormalIndex M p

@[expose] def AGL81TenElevenOne (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → ∀ (P : Sylow 3 G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    AGL81CfgData 3 P M H Q K → ∀ W : Sylow 3 G, (W : Subgroup G) ≤ M →
      rankThreeGamma 2 3 (W : Subgroup G) ≤ M ∨
        Nonempty ((M ⧸ primeComplementCore (G := M) 3) ≃* alternatingGroup (Fin 10)) ∨
        Nonempty ((M ⧸ primeComplementCore (G := M) 3) ≃* Equiv.Perm (Fin 10))

@[expose] def AGL81TenThirteenAt (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    p ∈ rankThreeSigmaA G → AGL81CfgData p P M H Q K →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    ∀ I₀ ∈ cZero (H ⊓ L),
      CFSG.ComponentClassification.AS76b.oUpperTwo I₀ ≤ d1PlusCore p H K ∨
        (p = 3 ∧ IsAltTwoP 3 K ∧ CFSG.ComponentClassification.AS76b.oUpperTwo I₀ ≤ hyp111Pre p H K)

@[expose] def AGL81TenSixX (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81CfgData p P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    ∀ I₀ ∈ cZero (H ⊓ L),
      CFSG.ComponentClassification.AS76b.oUpperTwo I₀ ≤ d1PlusCore p H K →
      I₀ ≤ d1PlusCore p H K ∨ (p = 3 ∧ IsLinThreeFour K)

structure AGL81ElevenNineData (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) (L W : Subgroup G) (a₀ : G) : Prop where
  data : AGL81CfgData p P M H Q K
  shape : (p = 3 ∧ IsLieOver K (.A 1) 2 3) ∨ (p = 5 ∧ IsSzThirtyTwo K)
  block : IsWeakSBlock M (pCoreOf 2 H) L
  normal : M ≤ Subgroup.normalizer (L : Set G)
  j0_le : jZero H L ≤ d1PlusCore p H K
  dvd : p ∣ Nat.card (jZero H L)
  sylow : IsPGroup p W ∧ W ≤ H ⊓ M ∧ ∀ W' : Subgroup G, IsPGroup p W' → W' ≤ H ⊓ M → W ≤ W' → W' = W
  mem : a₀ ∈ W
  order : orderOf a₀ = p
  outer : a₀ ∉ hyp111Pre p H K ⊔ d1PlusCore p H K
  not_split : ¬ ∀ g ∈ Subgroup.zpowers a₀ ⊔ (W ⊓ jZero H L),
    ∃ u ∈ W ⊓ jZero H L, ∀ j ∈ jZero H L, ⁅u⁻¹ * g, j⁆ ∈ pCoreOf 2 (jZero H L)

@[expose] def AGL81ElevenNineFieldAut (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) (L W : Subgroup G) (a₀ : G),
    AGL81ElevenNineData p P M H Q K L W a₀ → HasNormalIndex M p

@[expose] def AGL81FourSixteenAt (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → ∀ (P : Sylow 5 G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 5)) (L W : Subgroup G) (a₀ x : G),
    AGL81ElevenNineData 5 P M H Q K L W a₀ → x ∈ W ⊓ jZero H L → orderOf x = 5 →
    Open.pRank 5 (Subgroup.centralizer ({x} : Set G) ⊓ M) ≤ 3 →
    ∀ D : Subgroup G, D ≤ M → IsElemAbelian 5 D → Nat.card D = 25 →
      3 ≤ Open.pRank 5 (Subgroup.centralizer (D : Set G) ⊓ M)

@[expose] def AGL81ElevenNineGammaFive (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → ∀ (P : Sylow 5 G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 5)) (L W : Subgroup G) (a₀ : G),
    AGL81ElevenNineData 5 P M H Q K L W a₀ →
    (∀ D : Subgroup G, D ≤ M → IsElemAbelian 5 D → Nat.card D = 25 →
      3 ≤ Open.pRank 5 (Subgroup.centralizer (D : Set G) ⊓ M)) →
    ∀ V : Sylow 5 G, (V : Subgroup G) ≤ M → rankThreeGamma 2 5 (V : Subgroup G) ≤ M

@[expose] def AGL81TenNineOne (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81ElevenData p P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      IsEmpty (↥(barM M L) ≃* alternatingGroup (Fin 7))

@[expose] def AGL81TenNineOneCfg (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81CfgData p P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      IsEmpty (↥(barM M L) ≃* alternatingGroup (Fin 7))

@[expose] def AGL81FiveTwentySix (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → ∀ X T L : Subgroup G, IsSylowTwoOf T X →
    X ⊓ Subgroup.centralizer (pCoreOf 2 X : Set G) ≤ pCoreOf 2 X →
    (∀ Y : Subgroup G, Y ≤ X → IsSubnormal Y X → InClassXBlock Y → False) →
    IsTwoPrimeComponent X L → 3 ∣ Nat.card L →
    L ≤ ⨆ (B : Subgroup G) (_ : B ≤ T) (_ : B ≠ ⊥) (_ : (B.subgroupOf T).Characteristic)
      (_ : 3 ∣ Nat.card ↥(L ⊓ Subgroup.normalizer (B : Set G))),
        L ⊓ Subgroup.normalizer (B : Set G)

end CFSG.LocalAnalysis.RankThreeTheoremC
