module

public import CFSG.LocalAnalysis.GLTheoremA.S6.Setup
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsGamma
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

@[expose] def Stage11At (G : Type) [Group G] [Finite G] (m p : ℕ) : Prop :=
  ∀ (B : Subgroup G) (x : G) (L : Subgroup G), GLAIsBmax p B → x ∈ B → x ≠ 1 →
    GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L →
    B ≤ Subgroup.normalizer (L : Set G) → CentModEqZpowers p B L x → CFSG.Open.IsQuasisimple ↥L →
    InnerDiagMarking B L →
    evenRank ↥L ≤ m ∧
      GLAMarking L (fun lab _ _ I _ θ => GLAHalfSplit16 p lab (Subgroup.center ↥L = ⊥) ∧
        B ≤ Subgroup.normalizer (L : Set G) ∧
        ∀ b ∈ B, ∃ φ ∈ I, GLAInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)

theorem stage11At_of_stage11 {G : Type} [Group G] [Finite G] {m p : ℕ} (h : Stage11 G m) (hp : p ∈ Mu G m) :
    Stage11At G m p :=
  fun B x L hB hx hx1 hc hn hcent hqs hid => h p hp B x L hB hx hx1 hc hn hcent hqs hid

structure S12Ctx (G : Type) [Group G] [Finite G] (m p : ℕ) : Prop where
  ctx : S10Ctx G p
  weakCore : ∀ q ∈ GLABeta (GLATwoLocalRank p G + 1) G, GLAWeakCoreLocal G q
  rank : GLATwoLocalRank p G = m
  stage11 : Stage11At G m p

theorem S12Ctx.of_ctx {G : Type} [Group G] [Finite G] {m : ℕ} (hctx : ThmACtx G m) (hsf : StageFacts G m)
    (h11 : Stage11 G m) {p : ℕ} (hp : p ∈ Mu G m) : S12Ctx G m p where
  ctx := S10Ctx.of_ctx hctx hsf hp
  weakCore := by
    rw [hp.2.1]
    exact hctx.1.weakCore_above
  rank := hp.2.1
  stage11 := stage11At_of_stage11 h11 hp

theorem S12Ctx.toS6 {G : Type} [Group G] [Finite G] {m p : ℕ} (hc : S12Ctx G m p) : S6Ctx G p where
  prime := hc.ctx.ctx.prime
  odd := hc.ctx.ctx.odd
  simple := hc.ctx.ctx.simple
  nonabelian := hc.ctx.ctx.nonabelian
  kProper := hc.ctx.ctx.kProper
  charTwo := hc.ctx.ctx.charTwo
  rank_ge := hc.ctx.ctx.rank_ge
  weakCore := hc.weakCore
  stage3 := hc.ctx.stage3
  stage4Order := hc.ctx.stage4o
  stage4 := hc.ctx.stage4
  stage5 := hc.ctx.stage5

theorem S12Ctx.card_B {G : Type} [Group G] [Finite G] {m p : ℕ} (hc : S12Ctx G m p) {B : Subgroup G}
    (hB : GLAIsBmax p B) : Nat.card B = p ^ m := by
  rw [hB.2.1, hc.rank]

structure Triple12 (G : Type) [Group G] [Finite G] (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) : Prop where
  star : IsSStarMax p B x L
  split : SplitInnerDiagMarking16 p B L

theorem innerDiagMarking_of_split16 {G : Type} [Group G] [Finite G] {p : ℕ} {B L : Subgroup G}
    (h : SplitInnerDiagMarking16 p B L) : InnerDiagMarking B L :=
  CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.2) h

namespace Triple12

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} {x : G} {L : Subgroup G}

theorem bmax (h : Triple12 G p B x L) : GLAIsBmax p B := IsSStarMax.bmax h.star

theorem mem (h : Triple12 G p B x L) : x ∈ B := (IsSStarMax.essential h.star).1

theorem ne_one (h : Triple12 G p B x L) : x ≠ 1 := (IsSStarMax.essential h.star).2.1

theorem comp (h : Triple12 G p B x L) : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L :=
  IsSStarMax.component h.star

theorem norm (h : Triple12 G p B x L) : B ≤ Subgroup.normalizer (L : Set G) := IsSStarMax.normalizes h.star

theorem cycMod (h : Triple12 G p B x L) : CycModSylow p L := IsSStarMax.cycMod h.star

theorem idiag (h : Triple12 G p B x L) : InnerDiagMarking B L := innerDiagMarking_of_split16 h.split

theorem cent {m : ℕ} (hc : S12Ctx G m p) (h : Triple12 G p B x L) : CentModEqZpowers p B L x :=
  hc.ctx.stage5.2.1 B x L h.star.1

theorem qs {m : ℕ} (hc : S12Ctx G m p) (h : Triple12 G p B x L) : CFSG.Open.IsQuasisimple ↥L :=
  (hc.ctx.stage9.1 B x L h.star).1

theorem chev2 {m : ℕ} (hc : S12Ctx G m p) (h : Triple12 G p B x L) : IsChevSimple 2 (PSimple p L) :=
  hc.ctx.stage8.1 B x L h.star

theorem layer {m : ℕ} (hc : S12Ctx G m p) (h : Triple12 G p B x L) :
    GLAPLayer p (Subgroup.centralizer ({x} : Set G)) = L :=
  sstarMax_layer_eq hc.toS6 h.star

end Triple12

variable {G : Type} [Group G] [Finite G]

@[expose] def U42Type (p : ℕ) (K : Subgroup G) : Prop := catalogIs (PSimple p K) S9.isU4two

@[expose] def A6Type (p : ℕ) (K : Subgroup G) : Prop := catalogIs (PSimple p K) S10.isA6

@[expose] def SmallType (p : ℕ) (K : Subgroup G) : Prop := U42Type p K ∨ A6Type p K

@[expose] def IsE3 (p : ℕ) (B E : Subgroup G) : Prop :=
  E ≤ B ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3

@[expose] def IsE2 (p : ℕ) (B D : Subgroup G) : Prop :=
  D ≤ B ∧ IsElemAbelian p D ∧ Nat.card D = p ^ 2

@[expose] def Concl121 (G : Type) [Group G] [Finite G] (p : ℕ) (B L D K : Subgroup G) : Prop :=
  (U42Type p K ∧ p = 3 ∧ dLevel G p = 2 ∧ (∀ b ∈ B, InducesInnerMod p L b) ∧
      catalogIs (PSimple p L) (fun i => S9.isD4two i ∨ S9.isU5two i ∨ S9.isU6two i)) ∨
    (¬ SmallType p K ∧ dLevel G p = 5 ∧
      ∃ E : Subgroup G, IsE3 p B E ∧ D ≤ E ∧ GLAPLayer p (L ⊓ cs E) ≠ ⊥ ∧ GLAPLayer p (K ⊓ cs E) ≠ ⊥)


abbrev Ky (p : ℕ) (K : Subgroup G) (y : G) : Subgroup G := closureIn K (GLAPLayer p (cx y))

structure Nbr12 (p : ℕ) (B : Subgroup G) (x : G) (L D K : Subgroup G) (y : G) (J : Subgroup G) : Prop where
  shat : GLASHat p B y J
  std : GLAStdSub p B x L D K
  nb : GLANeighbor p x y J D K

theorem isNeighborOf_iff {p : ℕ} {B : Subgroup G} {x : G} {L : Subgroup G} {y : G} {J : Subgroup G} :
    GLAIsNeighborOf p B x L y J ↔ ∃ D K : Subgroup G, Nbr12 p B x L D K y J :=
  ⟨fun ⟨hs, D, K, hstd, hnb⟩ => ⟨D, K, ⟨hs, hstd, hnb⟩⟩, fun ⟨D, K, h⟩ => ⟨h.shat, D, K, h.std, h.nb⟩⟩

@[expose] def NoNbr12 (p : ℕ) (B : Subgroup G) (x : G) (L D K : Subgroup G) : Prop :=
  ∀ (y : G) (J : Subgroup G), ¬ (GLASHat p B y J ∧ GLANeighbor p x y J D K)

end CFSG.LocalAnalysis.GLTheoremA
