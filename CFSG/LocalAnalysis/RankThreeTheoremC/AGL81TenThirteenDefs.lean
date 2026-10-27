module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeList
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CfgData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def IsThreeFourPair (p : ℕ) (iK iJ : TauCeti.CFSGIndex) : Prop :=
  (p = 3 ∧ ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧
    ∃ dK dJ : TauCeti.ValidLieTypeIndex, dK.1 = .B 3 q ∧ dJ.1 = .twistedA 3 q ∧
      iK = .lie dK ∧ iJ = .lie dJ) ∨
  (p = 3 ∧ ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧
    ∃ dK dJ : TauCeti.ValidLieTypeIndex, dK.1 = .G2 q ∧ dJ.1 = .twistedA 2 q ∧
      iK = .lie dK ∧ iJ = .lie dJ) ∨
  (p = 3 ∧ ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧
    ∃ dK dJ : TauCeti.ValidLieTypeIndex, dK.1 = .B 2 q ∧ dJ.1 = .A 1 q ∧
      iK = .lie dK ∧ iJ = .lie dJ) ∨
  (p = 3 ∧ ∃ q : TauCeti.PrimePower, q.p = 3 ∧ q.exponent = 1 ∧
    ∃ dK dJ : TauCeti.ValidLieTypeIndex, dK.1 = .tits ∧ dJ.1 = .A 2 q ∧
      iK = .lie dK ∧ iJ = .lie dJ) ∨
  (p = 5 ∧ ∃ h₁ h₂, iK = .alternating 10 h₁ ∧ iJ = .alternating 5 h₂) ∨
  (p = 5 ∧ ∃ q : TauCeti.PrimePower, q.p = 5 ∧ q.exponent = 1 ∧
    ∃ dJ : TauCeti.ValidLieTypeIndex, dJ.1 = .twistedA 2 q ∧ iK = .sporadic .HS ∧
      iJ = .lie dJ) ∨
  (p = 7 ∧ ∃ q : TauCeti.PrimePower, q.p = 7 ∧ q.exponent = 1 ∧
    ∃ dJ : TauCeti.ValidLieTypeIndex, dJ.1 = .A 2 q ∧ iK = .sporadic .ONan ∧
      iJ = .lie dJ) ∨
  (p = 7 ∧ iK = .sporadic .Fi24Prime ∧ iJ = .sporadic .He)

@[expose] def KFactThreeFourOne : Prop :=
  ∀ (p : ℕ) (Y : Type) [Group Y] [Finite Y] (K Y₀ E J : Subgroup Y) (R : Sylow p Y),
    p.Prime → p ≠ 2 → p ≠ 3 → K.Normal → NineThreeListGroup p K →
    pRank p (centralizer (K : Set Y)) ≤ 1 → centralizer (K : Set Y) ≤ Y₀ →
    (∀ L : Subgroup Y, IsComponentOf L ⊤ → L ≤ K → ¬ L ≤ Y₀) →
    E ≤ R → IsElemAbelian p E → Nat.card E = p ^ 2 →
    (if 3 ≤ pRank p (R : Subgroup Y) then GLBWeakCore p (R : Subgroup Y)
      else GLBCore p 1 E) ≤ Y₀ →
    J ≤ Y₀ → IsSubnormal J Y₀ → (∀ x ∈ J, x ^ 3 ∈ centralizer (K : Set Y)) →
    J ≤ centralizer (K : Set Y)

@[expose] def KFactThreeFourTwo : Prop :=
  ∀ (p : ℕ) (Y : Type) [Group Y] [Finite Y] (K Y₀ E : Subgroup Y) (R : Sylow p Y)
    (I T : Type) [Group I] [Finite I] [Group T] (σ : I →* Y) (ψ : I →* T),
    p.Prime → p ≠ 2 → CFSG.Open.IsKGroup Y → K.Normal → NineThreeListGroup p K →
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

variable (G) in
@[expose] def AGL81TenThirteenPerfect : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    p ∈ rankThreeSigmaA G → AGL81CfgData p P M H Q K →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    ∀ I₀ ∈ cZero (H ⊓ L), IsTwoPrimeComponent I₀ I₀ → ¬ I₀ ≤ d1PlusCore p H K →
    ∀ iK iJ : TauCeti.CFSGIndex, IsThreeFourPair p iK iJ → Nonempty (K ≃* iK.Group) →
    (∃ f : I₀ →* iJ.Group, Function.Surjective f ∧ (d1PlusCore p H K).subgroupOf I₀ ≤ f.ker) →
    False

variable (G) in
@[expose] def AGL81TenThirteenSolvThree : Prop :=
  Setting G → 3 ∈ rankThreeSigmaA G → ∀ (P : Sylow 3 G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
    AGL81CfgData 3 P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    ∀ I₀ ∈ cZero (H ⊓ L), IsSymThreeOrSUThreeTwo (↥I₀ ⧸ CFSG.pCore 2 ↥I₀) →
    ¬ CFSG.ComponentClassification.AS76b.oUpperTwo I₀ ≤ d1PlusCore 3 H K →
    IsAltTwoP 3 K ∧ CFSG.ComponentClassification.AS76b.oUpperTwo I₀ ≤ hyp111Pre 3 H K

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
