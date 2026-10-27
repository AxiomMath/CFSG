module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Ctx
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNBridgeB

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def HypA (G : Type) [Group G] [Finite G] : Prop :=
  (∀ p ∈ rankThreeSigmaA G, ∃ M : Subgroup G, rankThreeIsMaxTwoLocal M ∧ p ∈ sigmaM G M) ∧
    ∃ M : Subgroup G, rankThreeIsMaxTwoLocal M ∧ ∃ p ∈ sigmaM G M, ∃ H : Subgroup G,
      IsTwoLocal H ∧ 2 < CFSG.Open.pRank p (H ⊓ M) ∧ ¬ H ≤ M

@[expose] def QSet (M : Subgroup G) (p : ℕ) : Set (Subgroup G) :=
  {Q | p.Prime ∧ p ≠ 2 ∧ Q ≤ M ∧ IsPGroup p Q ∧
    ((p ∈ sigmaM G M ∧ 2 < CFSG.Open.pRank p Q) ∨
      ∃ E : Subgroup G, E ≤ Q ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
        rankThreeGamma 1 p E ≤ M)}

@[expose] def HFam (M Q : Subgroup G) : Set (Subgroup G) :=
  {H | H ≠ ⊤ ∧ Q ≤ H ∧ ¬ H ≤ M}

@[expose] def H2Fam (M Q : Subgroup G) : Set (Subgroup G) :=
  {H | H ≠ ⊤ ∧ H ∈ hSet Q M}

@[expose] def IsPComponentIn (p : ℕ) (L H : Subgroup G) : Prop :=
  L ≤ H ∧ CFSG.IsPComponent p (L.subgroupOf H)

@[expose] def pLayerIn (p : ℕ) (H : Subgroup G) : Subgroup G :=
  (CFSG.pLayer H p).map H.subtype

open Classical in
@[expose] noncomputable def kSub (p : ℕ) (M H : Subgroup G) : Subgroup G :=
  if pLayerIn p H ≤ M then sSup {Y : Subgroup G | Y ≤ H ∧ Nat.card Y = p}
  else sSup {Y : Subgroup G | IsPComponentIn p Y H ∧ ¬ Y ≤ M}

@[expose] noncomputable def kStar (p : ℕ) (M H : Subgroup G) :
    Subgroup (H ⧸ primeComplementCore (G := H) p) :=
  ((kSub p M H).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p))

@[expose] noncomputable def xSub (p : ℕ) (M H : Subgroup G) : Subgroup G :=
  CFSG.AGLEmbedding.d1PlusCore p H (kStar p M H)

@[expose] def muSet (M : Subgroup G) : Set ℕ :=
  {p | p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card M ∧ ∃ Q ∈ QSet M p, (HFam M Q).Nonempty}

@[expose] def IsStdE (p k : ℕ) (M Q E : Subgroup G) : Prop :=
  (k = 2 ∨ k = 3) ∧ E ≤ Q ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k ∧
    rankThreeGamma (k - 1) p E ≤ M

@[expose] def invTwoSubgroups (X Q : Subgroup G) : Set (Subgroup G) :=
  {R | R ≤ X ∧ IsPGroup 2 R ∧ Q ≤ normalizer (R : Set G)}

@[expose] def CondA (p : ℕ) (M Q H : Subgroup G) : Prop :=
  CFSG.ABGLocalTools.IsSylowOf p (Q ⊓ kSub p M H) (kSub p M H) ∨
    (HasPrimeConstraint (G := H) p ∧ 2 < CFSG.Open.pRank p Q ∧ HypA G ∧
      CFSG.ABGLocalTools.IsSylowOf p (Q ⊓ ⁅kSub p M H, kSub p M H⁆) ⁅kSub p M H, kSub p M H⁆)

@[expose] def H4Fam (p : ℕ) (M Q : Subgroup G) : Set (Subgroup G) :=
  {H | H ∈ H2Fam M Q ∧ CondA p M Q H ∧ pCoreOf 2 H = pCoreOf 2 (H ⊓ M)}

@[expose] def H2StarFam (M Q : Subgroup G) : Set (Subgroup G) :=
  {H | H ∈ H2Fam M Q ∧ ∀ H' ∈ H2Fam M Q, H ≤ H' → H' = H}

@[expose] def H4StarFam (p : ℕ) (M Q : Subgroup G) : Set (Subgroup G) :=
  H2StarFam M Q ∩ H4Fam p M Q

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
