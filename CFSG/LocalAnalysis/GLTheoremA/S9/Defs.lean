module

public import CFSG.LocalAnalysis.GLTheoremA.S3.Basic
public import CFSG.LocalAnalysis.GLTheoremA.P55.Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

structure S9Ctx (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  ctx : S3Ctx G p
  weakCore : ∀ q ∈ GLABeta (GLATwoLocalRank p G + 1) G, GLAWeakCoreLocal G q
  stage3 : Stage3 G p
  stage4o : Stage4Order G p
  stage4 : Stage4 G p
  stage5 : Stage5 G p
  stage6 : Stage6 G p
  stage7 : Stage7 G p
  stage8 : Stage8 G p

theorem S9Ctx.of_ctx {G : Type} [Group G] [Finite G] {m : ℕ} (hctx : ThmACtx G m) {p : ℕ}
    (hp : p ∈ Mu G m) (h3 : Stage3 G p) (h4o : Stage4Order G p) (h4 : Stage4 G p)
    (h5 : Stage5 G p) (h6 : Stage6 G p) (h7 : Stage7 G p) (h8 : Stage8 G p) : S9Ctx G p where
  ctx := S3Ctx.of_ctx hctx hp
  weakCore := by
    rw [hp.2.1]
    exact hctx.1.weakCore_above
  stage3 := h3
  stage4o := h4o
  stage4 := h4
  stage5 := h5
  stage6 := h6
  stage7 := h7
  stage8 := h8

variable {G : Type} [Group G] [Finite G]

structure H92 (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) : Prop where
  bmax : GLAIsBmax p B
  mem : x ∈ B
  ne_one : x ≠ 1
  comp : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L
  norm : B ≤ Subgroup.normalizer (L : Set G)
  cent : CentModEqZpowers p B L x
  chev2 : IsChevSimple 2 (PSimple p L)
  alt : IsS0 p B x L ∨ IsGB p B L ∨ (¬ IsSC p B ∧ IsEssential p B x)

structure Setup92 (p q : ℕ) (L Q₁ : Subgroup G) : Prop where
  prime : q.Prime
  ne_two : q ≠ 2
  ne_p : q ≠ p
  le_core : Q₁ ≤ pCoreOf q L
  exp : ∀ g ∈ Q₁, g ^ q = 1
  class_two : ∀ a ∈ Q₁, ∀ b ∈ Q₁, ∀ c ∈ Q₁, ⁅a, b⁆ * c = c * ⁅a, b⁆
  char : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (Q₁ : Set G)
  cent : L ⊓ Subgroup.centralizer (Q₁ : Set G) ≤ oPPrimeP p L
  ne_bot : Q₁ ≠ ⊥

theorem H92.of_sstarMax {p : ℕ} (h5 : Stage5 G p) (h8 : Stage8 G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} (h : IsSStarMax p B x L) : H92 p B x L where
  bmax := h.1.1.1.1
  mem := h.1.1.1.2.1.1
  ne_one := h.1.1.1.2.1.2.1
  comp := h.1.1.1.2.2
  norm := h.1.2.2
  cent := h5.2.1 B x L h.1
  chev2 := h8.1 B x L h
  alt := Or.inl h.1.1

namespace S9

abbrev cx (x : G) : Subgroup G := Subgroup.centralizer ({x} : Set G)

@[expose] def Covers (p : ℕ) (N J : Subgroup G) : Prop :=
  (N ⊓ J) ⊔ GLAPPrimeCoreOf p J = J

@[expose] def isD4two : TauCeti.CFSGIndex → Prop :=
  onLie fun | .D 4 q => q.card = 2 | _ => False

@[expose] def isU4two : TauCeti.CFSGIndex → Prop :=
  onLie fun | .twistedA 3 q => q.card = 2 | _ => False

@[expose] def isU5two : TauCeti.CFSGIndex → Prop :=
  onLie fun | .twistedA 4 q => q.card = 2 | _ => False

@[expose] def isU6two : TauCeti.CFSGIndex → Prop :=
  onLie fun | .twistedA 5 q => q.card = 2 | _ => False

@[expose] def isSp6two : TauCeti.CFSGIndex → Prop :=
  onLie fun | .B 3 q => q.card = 2 | _ => False

@[expose] def isTD4two : TauCeti.CFSGIndex → Prop :=
  onLie fun | .trialityD4 q => q.card = 2 | _ => False

@[expose] def isU3eight : TauCeti.CFSGIndex → Prop :=
  onLie fun | .twistedA 2 q => q.card = 8 | _ => False

@[expose] def isF4two : TauCeti.CFSGIndex → Prop :=
  onLie fun | .F4 q => q.card = 2 | _ => False

@[expose] def isTE6two : TauCeti.CFSGIndex → Prop :=
  onLie fun | .twistedE6 q => q.card = 2 | _ => False

@[expose] def isL3four : TauCeti.CFSGIndex → Prop :=
  onLie fun | .A 2 q => q.card = 4 | _ => False

@[expose] def isL2odd : TauCeti.CFSGIndex → Prop
  | .alternating n _ => n = 5 ∨ n = 6
  | .lie i =>
    match i.1 with
    | .A 1 q => Odd q.card ∧ 3 < q.card
    | _ => False
  | _ => False

@[expose] def isL2prime : TauCeti.CFSGIndex → Prop
  | .alternating n _ => n = 5
  | .lie i =>
    match i.1 with
    | .A 1 q => q.card.Prime ∧ 7 ≤ q.card
    | _ => False
  | _ => False

@[expose] def isList94 (i : TauCeti.CFSGIndex) : Prop :=
  isSp6two i ∨ isU4two i ∨ isD4two i ∨ isU5two i

@[expose] def isList67 (i : TauCeti.CFSGIndex) : Prop :=
  isSp6two i ∨ isD4two i ∨ isF4two i ∨ isU4two i ∨ isU6two i ∨ isTE6two i

@[expose] def isList107 (i : TauCeti.CFSGIndex) : Prop :=
  isSp6two i ∨ isU4two i ∨ isU5two i ∨ isU3eight i ∨ isD4two i ∨ isTD4two i

@[expose] def isSp4eight : TauCeti.CFSGIndex → Prop :=
  onLie fun | .B 2 q => q.card = 8 | _ => False

@[expose] def isG2eight : TauCeti.CFSGIndex → Prop :=
  onLie fun | .G2 q => q.card = 8 | _ => False

@[expose] def isU4eight : TauCeti.CFSGIndex → Prop :=
  onLie fun | .twistedA 3 q => q.card = 8 | _ => False

@[expose] def isReeF48 : TauCeti.CFSGIndex → Prop :=
  onLie fun | .reeF4 m => m = 1 | _ => False

@[expose] def isReeF432 : TauCeti.CFSGIndex → Prop :=
  onLie fun | .reeF4 m => m = 2 | _ => False

@[expose] def isL3char2 : TauCeti.CFSGIndex → Prop :=
  onLie fun | .A 2 q => q.p = 2 ∧ q.card % 3 = 1 | _ => False

@[expose] def isU3char2 : TauCeti.CFSGIndex → Prop :=
  onLie fun | .twistedA 2 q => q.p = 2 ∧ q.card % 3 = 2 | _ => False

@[expose] def isList269 (i : TauCeti.CFSGIndex) : Prop :=
  isSp6two i ∨ isU4two i ∨ isD4two i ∨ isTD4two i ∨ isU3eight i ∨ isU5two i

@[expose] def isList93 (p : ℕ) (i : TauCeti.CFSGIndex) : Prop :=
  (p = 5 ∧ isReeF432 i) ∨
    (p = 3 ∧ (isD4two i ∨ isSp4eight i ∨ isG2eight i ∨ isU4eight i ∨ isU6two i ∨ isTD4two i ∨
      isReeF48 i ∨ isL3char2 i ∨ isU3char2 i))

@[expose] def InvolvedSL2 (q : ℕ) (S : Type) [Group S] : Prop :=
  ∃ (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod q))) (φ : H →* S),
    Function.Surjective φ

end S9

end CFSG.LocalAnalysis.GLTheoremA
