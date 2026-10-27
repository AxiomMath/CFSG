module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs7
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal

structure S6Ctx (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  kProper : CFSG.Open.IsKProper G
  charTwo : IsCharTwoType G
  rank_ge : 4 ≤ GLATwoLocalRank p G
  weakCore : ∀ q ∈ GLABeta (GLATwoLocalRank p G + 1) G, GLAWeakCoreLocal G q
  stage3 : Stage3 G p
  stage4Order : Stage4Order G p
  stage4 : Stage4 G p
  stage5 : Stage5 G p

variable {G : Type} [Group G] [Finite G]

theorem S6Ctx.of_ctx {m : ℕ} (hctx : ThmACtx G m) {p : ℕ} (hp : p ∈ Mu G m) (h3 : Stage3 G p)
    (h4o : Stage4Order G p) (h4 : Stage4 G p) (h5 : Stage5 G p) : S6Ctx G p where
  prime := hp.1.1
  odd := hp.1.2.1
  simple := hctx.1.simple
  nonabelian := hctx.1.nonabelian
  kProper := hctx.1.kProper
  charTwo := hctx.1.charTwo
  rank_ge := hp.2.1 ▸ hctx.1.four_le
  weakCore := by
    rw [hp.2.1]
    exact hctx.1.weakCore_above
  stage3 := h3
  stage4Order := h4o
  stage4 := h4
  stage5 := h5

@[expose] def InT (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) : Prop :=
  GLAIsBmax p B ∧ x ∈ B ∧ x ≠ 1 ∧ GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L ∧
    B ≤ Subgroup.normalizer (L : Set G) ∧ CentModEqZpowers p B L x

@[expose] def InTq (q p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) : Prop :=
  InT p B x L ∧ IsChevSimple q (PSimple p L)

@[expose] def InD (p : ℕ) (B : Subgroup G) (_x : G) (L D J : Subgroup G) : Prop :=
  (D ≤ B ∧ p ^ 2 ≤ Nat.card D ∧ p ^ 2 * Nat.card D ≤ Nat.card B) ∧
  (GLAPComponent p (L ⊓ Subgroup.centralizer (D : Set G)) J ∧ B ≤ Subgroup.normalizer (J : Set G) ∧
    ∀ b ∈ B, CentMod p J b ↔ b ∈ D) ∧
  (Nat.card D = p ^ 2 → ∃ E : Subgroup G, E ≤ B ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧ D ≤ E ∧
    GLAPLayer p (J ⊓ Subgroup.centralizer (E : Set G)) ≠ ⊥)

@[expose] def CoversMod (p : ℕ) (N J : Subgroup G) : Prop :=
  (N ⊓ J) ⊔ GLAPPrimeCoreOf p J = J

@[expose] def InD0 (p : ℕ) (B : Subgroup G) (x : G) (L D J : Subgroup G) : Prop :=
  InD p B x L D J ∧ ∃ N : Subgroup G, IsTwoLocal N ∧ D ≤ N ∧ CoversMod p N J

@[expose] def pSimpleIsLie (p : ℕ) (L : Subgroup G) (d : TauCeti.LieTypeIndex) : Prop :=
  catalogIs (PSimple p L) (onLie fun d' => d' = d)

@[expose] def IsDirectZpowersInf (B : Subgroup G) (x : G) (L : Subgroup G) : Prop :=
  B = Subgroup.zpowers x ⊔ (B ⊓ L) ∧ Subgroup.zpowers x ⊓ (B ⊓ L) = ⊥

@[expose] def IsU3Case (p q : ℕ) (L : Subgroup G) : Prop :=
  ∃ Q : TauCeti.PrimePower, Q.p = q ∧ p ∣ Q.card + 1 ∧ pSimpleIsLie p L (.twistedA 2 Q)

@[expose] def Lemma64Cases (p q : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) : Prop :=
  (Nat.card B = p ^ 4 ∧ ∃ Q : TauCeti.PrimePower, Q.p = q ∧
    ((pSimpleIsLie p L (.A 2 Q) ∧ p ∣ Q.card - 1) ∨
      (pSimpleIsLie p L (.twistedA 2 Q) ∧ p ∣ Q.card + 1))) ∨
  (Nat.card B = p ^ 4 ∧ IsDirectZpowersInf B x L ∧ Subgroup.center (PQuot p L) = ⊥ ∧
    ∃ Q : TauCeti.PrimePower, Q.p = q ∧
      ((pSimpleIsLie p L (.A 3 Q) ∧ p ∣ Q.card - 1) ∨
        (pSimpleIsLie p L (.twistedA 3 Q) ∧ p ∣ Q.card + 1))) ∨
  (Nat.card B = p ^ 4 ∧ IsDirectZpowersInf B x L ∧ Subgroup.center (PQuot p L) = ⊥ ∧
    ∃ Q : TauCeti.PrimePower, Q.p = q ∧
      (pSimpleIsLie p L (.B 3 Q) ∨ pSimpleIsLie p L (.twistedD 4 Q)) ∧ p ∣ Q.card ^ 2 - 1) ∨
  ((Nat.card B = p ^ 5 ∨ Nat.card B = p ^ 6) ∧ Nat.card (B ⊓ L : Subgroup G) = p ^ 4 ∧
    Subgroup.center (PQuot p L) = ⊥ ∧
    ∃ Q : TauCeti.PrimePower, Q.p = q ∧ pSimpleIsLie p L (.D 4 Q) ∧ p ∣ Q.card ^ 2 - 1)

@[expose] def Prop61At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ (B : Subgroup G) (x : G) (L : Subgroup G), IsSStarMax p B x L → ¬ IsChevSimple p (PSimple p L)

@[expose] def Lemma62At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p → ∀ (B : Subgroup G) (x : G) (L : Subgroup G),
    InTq q p B x L → ∀ D J : Subgroup G, ¬ InD0 p B x L D J

@[expose] def Lemma63At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p → ∀ (B : Subgroup G) (x : G) (L : Subgroup G),
    InTq q p B x L → GLATwoLocalRank p G < GLATwoLocalRank q G →
    IsU3Case p q L ∨ ∀ D J : Subgroup G, ¬ InD p B x L D J

@[expose] def Lemma64At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p → ∀ (B : Subgroup G) (x : G) (L : Subgroup G),
    InTq q p B x L → Lemma64Cases p q B x L

@[expose] def Prop65At (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p → ∀ (B : Subgroup G) (x : G) (L : Subgroup G),
    IsSStarMax p B x L → ¬ IsChevSimple q (PSimple p L)

theorem IsSStarMax.bmax {p : ℕ} {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : IsSStarMax p B x L) : GLAIsBmax p B := h.1.1.1.1

theorem IsSStarMax.essential {p : ℕ} {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : IsSStarMax p B x L) : IsEssential p B x := h.1.1.1.2.1

theorem IsSStarMax.component {p : ℕ} {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : IsSStarMax p B x L) : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L :=
  h.1.1.1.2.2

theorem IsSStarMax.normalizes {p : ℕ} {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : IsSStarMax p B x L) : B ≤ Subgroup.normalizer (L : Set G) := h.1.2.2

theorem IsSStarMax.cycMod {p : ℕ} {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : IsSStarMax p B x L) : CycModSylow p L := h.2

theorem IsSStarMax.level {p : ℕ} {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : IsSStarMax p B x L) : tripleLevel p B L = dLevel G p := h.1.1.2

theorem IsSStarMax.inT {p : ℕ} (hc : S6Ctx G p) {B : Subgroup G} {x : G} {L : Subgroup G}
    (h : IsSStarMax p B x L) : InT p B x L :=
  ⟨IsSStarMax.bmax h, (IsSStarMax.essential h).1, (IsSStarMax.essential h).2.1,
    IsSStarMax.component h, IsSStarMax.normalizes h, hc.stage5.2.1 B x L h.1⟩

end CFSG.LocalAnalysis.GLTheoremA
