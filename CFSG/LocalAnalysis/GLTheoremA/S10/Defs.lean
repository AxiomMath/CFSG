module

public import CFSG.LocalAnalysis.GLTheoremA.S3.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

structure S10Ctx (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  ctx : S3Ctx G p
  stage3 : Stage3 G p
  stage4o : Stage4Order G p
  stage4 : Stage4 G p
  stage5 : Stage5 G p
  stage6 : Stage6 G p
  stage7 : Stage7 G p
  stage8 : Stage8 G p
  stage9 : Stage9 G p
  marking : ∀ (B : Subgroup G) (x : G) (L : Subgroup G), IsSStarMax p B x L →
    GLAMarking L (fun _ _ _ _ _ _ => True)

theorem S10Ctx.of_ctx {G : Type} [Group G] [Finite G] {m : ℕ} (hctx : ThmACtx G m)
    (hsf : StageFacts G m) {p : ℕ} (hp : p ∈ Mu G m) : S10Ctx G p := by
  obtain ⟨h3, h4o, h4, h5, h6, h7, h8, h9, hm⟩ := hsf p hp
  exact ⟨S3Ctx.of_ctx hctx hp, h3, h4o, h4, h5, h6, h7, h8, h9, hm⟩

@[expose] def Ys09Label (lab : GLALabel) : Prop :=
  (lab.tag = .twA ∧ (lab.rank = 4 ∨ lab.rank = 5) ∧ lab.n = 1) ∨
    ((lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 4 ∧ lab.n = 1) ∨
    (lab.tag = .D ∧ lab.rank = 4 ∧ lab.n = 1)

@[expose] def Alt1 (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∃ (B : Subgroup G) (x : G) (L : Subgroup G), IsSStarMax p B x L ∧ InnerDiagMarking B L

@[expose] def Alt2 (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p = 3 ∧ ∃ (B : Subgroup G) (x : G) (L : Subgroup G),
    GLASStar 3 B x L ∧ GLAStandardType 3 B x L ∧ GLAMarking L (fun lab _ _ _ _ _ => Ys09Label lab)

@[expose] def Concl101 (G : Type) [Group G] [Finite G] (p : ℕ) : Prop := Alt1 G p ∨ Alt2 G p

theorem concl101_iff (G : Type) [Group G] [Finite G] (p : ℕ) :
    Concl101 G p ↔ ((∃ (B : Subgroup G) (x : G) (L : Subgroup G), IsSStarMax p B x L ∧
        InnerDiagMarking B L) ∨
      (p = 3 ∧ ∃ (B : Subgroup G) (x : G) (L : Subgroup G),
        GLASStar 3 B x L ∧ GLAStandardType 3 B x L ∧
          GLAMarking L (fun lab _ _ _ _ _ =>
            (lab.tag = .twA ∧ (lab.rank = 4 ∨ lab.rank = 5) ∧ lab.n = 1) ∨
              ((lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 4 ∧ lab.n = 1) ∨
              (lab.tag = .D ∧ lab.rank = 4 ∧ lab.n = 1)))) :=
  Iff.rfl

namespace S10

noncomputable section

variable {G : Type} [Group G] [Finite G]

abbrev cx (x : G) : Subgroup G := Subgroup.centralizer ({x} : Set G)

abbrev cs (A : Subgroup G) : Subgroup G := Subgroup.centralizer (A : Set G)

@[expose] def twoPart (n : ℕ) : ℕ := 2 ^ n.factorization 2

abbrev Dgrp (b x : G) : Subgroup G := Subgroup.closure {b, x}

abbrev Ipart (p : ℕ) (L : Subgroup G) (b : G) : Subgroup G := GLAPLayer p (L ⊓ cx b)

abbrev Jpart (p : ℕ) (I : Subgroup G) (a : G) : Subgroup G := closureIn I (GLAPLayer p (cx a))

theorem catalogIs_imp {S : Type} [Group S] {Q Q' : TauCeti.CFSGIndex → Prop} (hQ : ∀ i, Q i → Q' i)
    (h : catalogIs S Q) : catalogIs S Q' := by
  obtain ⟨i, hi, f⟩ := h
  exact ⟨i, hQ i hi, f⟩

@[expose] def indRel (p : ℕ) (L : Subgroup G) (g : G) : PQuot p L → PQuot p L → Prop :=
  fun q q' => ∃ l l' : ↥L, (QuotientGroup.mk l : PQuot p L) = q ∧ (QuotientGroup.mk l' : PQuot p L) = q' ∧
    (l' : G) = g⁻¹ * l * g

@[expose] def card2 (p : ℕ) (L : Subgroup G) : ℕ := twoPart (Nat.card (PQuot p L))

@[expose] def centCard2 (p : ℕ) (L : Subgroup G) (g : G) : ℕ :=
  twoPart (Nat.card {q : PQuot p L // indRel p L g q q})

@[expose] def InnDiagOn (p : ℕ) (A L : Subgroup G) : Prop :=
  A ≤ Subgroup.normalizer (L : Set G) ∧
    GLAMarking (PQuot p L) fun _ _ _ I _ θ => ∀ a ∈ A, ∃ φ ∈ I, GLAInduces θ (indRel p L a) φ

@[expose] def FieldOn (p : ℕ) (g : G) (L : Subgroup G) : Prop :=
  g ∈ Subgroup.normalizer (L : Set G) ∧
    GLAMarking (PQuot p L) fun lab _ _ I F θ => GLAPrimeField p lab I F (GLAInduces θ (indRel p L g))

@[expose] def IsTD4 (p : ℕ) (L : Subgroup G) : Prop :=
  catalogIs (PSimple p L) (onLie fun | .trialityD4 _ => True | _ => False)

@[expose] def NonInner (p : ℕ) (g : G) (L : Subgroup G) : Prop :=
  g ∈ Subgroup.normalizer (L : Set G) ∧ ¬ InducesInnerMod p L g

@[expose] def NonInnDiag (p : ℕ) (g : G) (L : Subgroup G) : Prop :=
  g ∈ Subgroup.normalizer (L : Set G) ∧ ¬ InnDiagOn p (Subgroup.zpowers g) L

@[expose] def indRelS (p : ℕ) (L : Subgroup G) (g : G) : PSimple p L → PSimple p L → Prop :=
  fun s s' => ∃ q q' : PQuot p L, indRel p L g q q' ∧
    (QuotientGroup.mk q : PSimple p L) = s ∧ (QuotientGroup.mk q' : PSimple p L) = s'

@[expose] def IsoPresAct (p : ℕ) (y : G) (J K : Subgroup G) (e : PSimple p J ≃* PSimple p K) : Prop :=
  ∀ s s' : PSimple p J, indRelS p J y s s' → indRelS p K y (e s) (e s')

@[expose] def R2Prop (p : ℕ) (g : G) (L : Subgroup G) : Prop :=
  FieldOn p g L ∨ (p = 3 ∧ IsTD4 3 L ∧ NonInner 3 g L)

@[expose] def isG2Quot : TauCeti.CFSGIndex → Prop :=
  fun i => onLie (fun | .G2 _ => True | _ => False) i ∨
    onLie (fun | .twistedA 2 q => q.card = 3 | _ => False) i

@[expose] def IsG2Quot (p : ℕ) (I : Subgroup G) : Prop := catalogIs (PQuot p I) isG2Quot

@[expose] def IsS2 (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) : Prop :=
  IsSTriple p B x L ∧ IsChevSimple 2 (PSimple p L)

@[expose] def R2TD4 (p : ℕ) (B L : Subgroup G) : Prop :=
  p = 3 ∧ IsTD4 3 L ∧ ∃ b ∈ B, b ≠ 1 ∧ NonInner 3 b L

open Classical in
@[expose] noncomputable def r2 (p : ℕ) (B L : Subgroup G) : ℕ :=
  if R2TD4 p B L then Nat.sqrt (card2 3 L)
  else if h : ∃ b ∈ B, FieldOn p b L then centCard2 p L h.choose
  else card2 p L

end

end S10

end CFSG.LocalAnalysis.GLTheoremA
