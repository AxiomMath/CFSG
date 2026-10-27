module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdInputs

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.QuasithinUnique.Ch1

section Setting

variable {G : Type} [Group G]

structure IdentSetting (X K : Subgroup G) (t : G) : Prop where
  quasi : CFSG.IsQuasisimple ↥X
  tN : t ∈ Subgroup.normalizer (X : Set G)
  sq : t * t = 1
  comm : ⁅X, Subgroup.zpowers t⁆ = X
  comp : IsComponentIn K (X ⊓ Subgroup.centralizer ({t} : Set G))
  ktype : IsKType K

@[expose] def IdentConcl (X K : Subgroup G) (t : G) : Prop :=
  IsPGroup 2 (Subgroup.center ↥X) ∧
    K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
      (X ⊓ Subgroup.centralizer ({t} : Set G)) ∧
    ¬ IsL2pBig K ∧ (IsL32 K → PatA X K t ∨ PatB X K t) ∧
    (IsA6 K → PatSp4 X K ∨ PatL5 X K ∨ PatHS X K t ∨ PatA8 X K t)

end Setting

@[expose] def TabIdentFor (P : ∀ {G : Type} [Group G], Subgroup G → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K : Subgroup G) (t : G), IdentSetting X K t → P X →
    IdentConcl X K t

namespace Ident

section Families

variable {G : Type} [Group G]

@[expose] def FamL2Even (X : Subgroup G) : Prop :=
  IsSimpleGroup ↥X ∧ ∃ f : ℕ, 2 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥X .PSL 2 2 f

@[expose] def FamL3Two (X : Subgroup G) : Prop :=
  IsSimpleGroup ↥X ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥X .PSL 3 2 1

@[expose] def FamL3Four (X : Subgroup G) : Prop :=
  IsSimpleGroup ↥X ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥X .PSL 3 2 2

@[expose] def FamL3Even (X : Subgroup G) : Prop :=
  IsSimpleGroup ↥X ∧ ∃ f : ℕ, 3 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥X .PSL 3 2 f

@[expose] def FamU3Four (X : Subgroup G) : Prop :=
  IsSimpleGroup ↥X ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥X .PSU 3 2 2

@[expose] def FamU3Even (X : Subgroup G) : Prop :=
  IsSimpleGroup ↥X ∧ ∃ f : ℕ, 3 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥X .PSU 3 2 f

@[expose] def FamSp4Four (X : Subgroup G) : Prop :=
  IsSimpleGroup ↥X ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥X .PSp 2 2 2

@[expose] def FamSp4Even (X : Subgroup G) : Prop :=
  IsSimpleGroup ↥X ∧ ∃ f : ℕ, 3 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥X .PSp 2 2 f

@[expose] def FamG2Even (X : Subgroup G) : Prop :=
  IsSimpleGroup ↥X ∧ ∃ f : ℕ, 2 ≤ f ∧ ChevalleyExceptionalModel ↥X .G2 2 f

@[expose] def FamTrialityEven (X : Subgroup G) : Prop :=
  IsSimpleGroup ↥X ∧ ∃ f : ℕ, 1 ≤ f ∧ ChevalleyExceptionalModel ↥X .trialityD4 2 f

@[expose] def FamTwistedF4 (X : Subgroup G) : Prop :=
  IsSimpleGroup ↥X ∧ ∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ ReeTitsModel ↥X .twistedF4 2 f

@[expose] def FamSuzuki (X : Subgroup G) : Prop :=
  IsSimpleGroup ↥X ∧ ∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ SuzukiModel ↥X 2 f

@[expose] def FamTits (X : Subgroup G) : Prop :=
  IsSimpleGroup ↥X ∧ ReeTitsModel ↥X .Tits 2 1

@[expose] def FamL4Two (X : Subgroup G) : Prop :=
  IsSimpleGroup ↥X ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥X .PSL 4 2 1

@[expose] def FamL5Two (X : Subgroup G) : Prop :=
  IsSimpleGroup ↥X ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥X .PSL 5 2 1

@[expose] def FamA6Simple (X : Subgroup G) : Prop :=
  IsSimpleGroup ↥X ∧ Nonempty (↥X ≃* alternatingGroup (Fin 6))

@[expose] def FamU33 (X : Subgroup G) : Prop :=
  IsSimpleGroup ↥X ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥X .PSU 3 3 1

@[expose] def FamCoverL34 (X : Subgroup G) : Prop :=
  Subgroup.center ↥X ≠ ⊥ ∧ Subgroup.center ↥X = CFSG.pCore 2 ↥X ∧
    CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥X ⧸ CFSG.pCore 2 ↥X) .PSL 3 2 2

@[expose] def FamCoverG24 (X : Subgroup G) : Prop :=
  Subgroup.center ↥X ≠ ⊥ ∧ Subgroup.center ↥X = CFSG.pCore 2 ↥X ∧
    ChevalleyExceptionalModel (↥X ⧸ CFSG.pCore 2 ↥X) .G2 2 2

@[expose] def FamAlt6 (X : Subgroup G) : Prop :=
  Nonempty ((↥X ⧸ Subgroup.center ↥X) ≃* alternatingGroup (Fin 6)) ∧
    (Nat.card (Subgroup.center ↥X) = 1 ∨ Nat.card (Subgroup.center ↥X) = 3)

@[expose] def FamAlt7 (X : Subgroup G) : Prop :=
  Nonempty ((↥X ⧸ Subgroup.center ↥X) ≃* alternatingGroup (Fin 7)) ∧
    (Nat.card (Subgroup.center ↥X) = 1 ∨ Nat.card (Subgroup.center ↥X) = 3)

@[expose] def FamL33 (X : Subgroup G) : Prop :=
  CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥X .PSL 3 3 1

@[expose] def FamL2Odd (X : Subgroup G) : Prop :=
  ∃ p : ℕ, IsFermatOrMersennePrime p ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥X .PSL 2 p 1

end Families

@[expose] def FamSporadic (s : TauCeti.SporadicName) {G : Type} [Group G] (X : Subgroup G) : Prop :=
  Nonempty ((↥X ⧸ CFSG.pCore 2 ↥X) ≃* NativeSporadic.Carrier s)

end Ident

open Ident

structure IdentFamilies : Prop where
  l2Even : TabIdentFor @FamL2Even
  l3Two : TabIdentFor @FamL3Two
  l3Four : TabIdentFor @FamL3Four
  l3Even : TabIdentFor @FamL3Even
  u3Four : TabIdentFor @FamU3Four
  u3Even : TabIdentFor @FamU3Even
  sp4Four : TabIdentFor @FamSp4Four
  sp4Even : TabIdentFor @FamSp4Even
  g2Even : TabIdentFor @FamG2Even
  trialityEven : TabIdentFor @FamTrialityEven
  twistedF4 : TabIdentFor @FamTwistedF4
  suzuki : TabIdentFor @FamSuzuki
  tits : TabIdentFor @FamTits
  l4Two : TabIdentFor @FamL4Two
  l5Two : TabIdentFor @FamL5Two
  a6Simple : TabIdentFor @FamA6Simple
  u33 : TabIdentFor @FamU33
  coverL34 : TabIdentFor @FamCoverL34
  coverG24 : TabIdentFor @FamCoverG24
  alt6 : TabIdentFor @FamAlt6
  alt7 : TabIdentFor @FamAlt7
  l33 : TabIdentFor @FamL33
  l2Odd : TabIdentFor @FamL2Odd
  m11 : TabIdentFor (@FamSporadic .M11)
  m12 : TabIdentFor (@FamSporadic .M12)
  m22 : TabIdentFor (@FamSporadic .M22)
  m23 : TabIdentFor (@FamSporadic .M23)
  m24 : TabIdentFor (@FamSporadic .M24)
  j2 : TabIdentFor (@FamSporadic .J2)
  j4 : TabIdentFor (@FamSporadic .J4)
  hs : TabIdentFor (@FamSporadic .HS)
  he : TabIdentFor (@FamSporadic .He)
  ru : TabIdentFor (@FamSporadic .Ru)

theorem tabIdent_of_families (h : IdentFamilies) : TabIdent := by
  intro G _ _ X K t hq hz hN hsq hcomm hcomp hk
  have hs : IdentSetting X K t := ⟨hq, hN, hsq, hcomm, hcomp, hk⟩
  obtain ⟨z, hz⟩ := hz
  rcases hz with ⟨hsimple, hlie, -⟩ | ⟨hZ, hZ2, hL34, -⟩ | ⟨φ, σ, hZc, -⟩ | ⟨φ, σ, hZc, -⟩ |
    ⟨hE, -⟩ | ⟨⟨s, hname, hiso⟩, -⟩
  ·
    rcases hlie with ((⟨f, ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ |
        ⟨hodd, hf, hm⟩ | ⟨hodd, hf, hm⟩⟩ | htits) | ⟨n, hn, hm⟩) | hA6 | hU33
    · exact h.l2Even G X K t hs ⟨hsimple, f, hf, hm⟩
    · rcases lt_trichotomy f 2 with hf2 | rfl | hf2
      · obtain rfl : f = 1 := by omega
        exact h.l3Two G X K t hs ⟨hsimple, hm⟩
      · exact h.l3Four G X K t hs ⟨hsimple, hm⟩
      · exact h.l3Even G X K t hs ⟨hsimple, f, hf2, hm⟩
    · rcases Nat.eq_or_lt_of_le hf with rfl | hf3
      · exact h.u3Four G X K t hs ⟨hsimple, hm⟩
      · exact h.u3Even G X K t hs ⟨hsimple, f, hf3, hm⟩
    · rcases Nat.eq_or_lt_of_le hf with rfl | hf3
      · exact h.sp4Four G X K t hs ⟨hsimple, hm⟩
      · exact h.sp4Even G X K t hs ⟨hsimple, f, hf3, hm⟩
    · exact h.g2Even G X K t hs ⟨hsimple, f, hf, hm⟩
    · exact h.trialityEven G X K t hs ⟨hsimple, f, hf, hm⟩
    · exact h.twistedF4 G X K t hs ⟨hsimple, f, hodd, hf, hm⟩
    · exact h.suzuki G X K t hs ⟨hsimple, f, hodd, hf, hm⟩
    · exact h.tits G X K t hs ⟨hsimple, htits⟩
    · rcases hn with rfl | rfl
      · exact h.l4Two G X K t hs ⟨hsimple, hm⟩
      · exact h.l5Two G X K t hs ⟨hsimple, hm⟩
    · exact h.a6Simple G X K t hs ⟨hsimple, hA6⟩
    · exact h.u33 G X K t hs ⟨hsimple, hU33⟩
  ·
    rcases hL34 with hm | hm
    · exact h.coverL34 G X K t hs ⟨hZ, hZ2, hm⟩
    · exact h.coverG24 G X K t hs ⟨hZ, hZ2, hm⟩
  · exact h.alt6 G X K t hs ⟨⟨φ⟩, hZc⟩
  · exact h.alt7 G X K t hs ⟨⟨φ⟩, hZc⟩
  ·
    rcases hE with hm | ⟨p, hp, hm⟩
    · exact h.l33 G X K t hs hm
    · exact h.l2Odd G X K t hs ⟨p, hp, hm⟩
  ·
    rcases hname with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h.m11 G X K t hs hiso
    · exact h.m12 G X K t hs hiso
    · exact h.m22 G X K t hs hiso
    · exact h.m23 G X K t hs hiso
    · exact h.m24 G X K t hs hiso
    · exact h.j2 G X K t hs hiso
    · exact h.j4 G X K t hs hiso
    · exact h.hs G X K t hs hiso
    · exact h.he G X K t hs hiso
    · exact h.ru G X K t hs hiso

end CFSG.QuasithinUnique.Id2519
