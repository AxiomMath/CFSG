module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamDefs

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Blueprint

@[expose] def FamAlt (S : Type) [Group S] : Prop :=
  ∃ n : ℕ, 5 ≤ n ∧ n ≤ 8 ∧ Nonempty (S ≃* alternatingGroup (Fin n))

@[expose] def FamOddL2 (S : Type) [Group S] : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ∃ f : ℕ, (f = 1 ∨ f = 2) ∧ StatedClassicalModel S .PSL 2 p f

@[expose] def FamOddL3 (S : Type) [Group S] : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ StatedClassicalModel S .PSL 3 p 1

@[expose] def FamOddU3 (S : Type) [Group S] : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ StatedClassicalModel S .PSU 3 p 1

@[expose] def FamEvenL2 (S : Type) [Group S] : Prop :=
  ∃ f : ℕ, 2 ≤ f ∧ StatedClassicalModel S .PSL 2 2 f

@[expose] def FamEvenL3 (S : Type) [Group S] : Prop :=
  ∃ f : ℕ, 1 ≤ f ∧ StatedClassicalModel S .PSL 3 2 f

@[expose] def FamEvenL3Large (S : Type) [Group S] : Prop :=
  ∃ f : ℕ, 3 ≤ f ∧ StatedClassicalModel S .PSL 3 2 f

@[expose] def FamEvenU3 (S : Type) [Group S] : Prop :=
  ∃ f : ℕ, 2 ≤ f ∧ StatedClassicalModel S .PSU 3 2 f

@[expose] def FamEvenSp4 (S : Type) [Group S] : Prop :=
  ∃ f : ℕ, 2 ≤ f ∧ StatedClassicalModel S .PSp 2 2 f

@[expose] def FamG2 (S : Type) [Group S] : Prop :=
  ∃ f : ℕ, 2 ≤ f ∧ ChevalleyExceptionalModel S .G2 2 f

@[expose] def FamD4 (S : Type) [Group S] : Prop :=
  ∃ f : ℕ, 1 ≤ f ∧ ChevalleyExceptionalModel S .trialityD4 2 f

@[expose] def FamF4 (S : Type) [Group S] : Prop :=
  ∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ ReeTitsModel S .twistedF4 2 f

@[expose] def FamSz (S : Type) [Group S] : Prop :=
  ∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ SuzukiModel S 2 f

@[expose] def FamTits (S : Type) [Group S] : Prop :=
  ReeTitsModel S .Tits 2 1

@[expose] def FamL4 (S : Type) [Group S] : Prop :=
  StatedClassicalModel S .PSL 4 2 1

@[expose] def FamL5 (S : Type) [Group S] : Prop :=
  StatedClassicalModel S .PSL 5 2 1

@[expose] def FamSporadic (s : TauCeti.SporadicName) (S : Type) [Group S] : Prop :=
  Nonempty (S ≃* NativeSporadic.Carrier s)

@[expose] def ExamExcludes (Fam : ∀ (S : Type) [Group S], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K B B' P R : Subgroup G) (m : ℕ),
    ExamConfig K B B' P R m → ¬ Fam (↥K ⧸ Subgroup.center ↥K)

@[expose] def ExamSp4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K B B' P R : Subgroup G) (m : ℕ),
    ExamConfig K B B' P R m → FamEvenSp4 (↥K ⧸ Subgroup.center ↥K) →
      ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ m ∧
        Nonempty (↥K ≃* StatedProj (StatedSp 2 F))

structure ExamKFamilies : Prop where
  alt : ExamExcludes FamAlt
  oddL2 : ExamExcludes FamOddL2
  oddL3 : ExamExcludes FamOddL3
  oddU3 : ExamExcludes FamOddU3
  evenL2 : ExamExcludes FamEvenL2
  evenL3 : ExamExcludes FamEvenL3
  evenU3 : ExamExcludes FamEvenU3
  sp4 : ExamSp4
  g2 : ExamExcludes FamG2
  d4 : ExamExcludes FamD4
  f4 : ExamExcludes FamF4
  sz : ExamExcludes FamSz
  tits : ExamExcludes FamTits
  l4 : ExamExcludes FamL4
  l5 : ExamExcludes FamL5
  sporadic : ∀ s : TauCeti.SporadicName,
    (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J2 ∨ s = .J4 ∨
      s = .HS ∨ s = .He ∨ s = .Ru) → ExamExcludes (FamSporadic s)

theorem examK_of_families (h : ExamKFamilies) : Lemma2_4_23_five_examK := by
  intro G _ _ K B B' P R m hcfg
  rcases hcfg.list with hA | ⟨p, hp, hp2, hL2 | hL3 | hU3⟩ |
      ⟨⟨f, hL2 | hL3 | hU3 | hSp | hG2 | hD4 | hF4 | hSz⟩ | hTits⟩ |
      ⟨n, hn, hn45⟩ | ⟨s, hs, hS⟩
  · exact absurd hA (h.alt G K B B' P R m hcfg)
  · exact absurd ⟨p, hp, hp2, hL2⟩ (h.oddL2 G K B B' P R m hcfg)
  · exact absurd ⟨p, hp, hp2, hL3⟩ (h.oddL3 G K B B' P R m hcfg)
  · exact absurd ⟨p, hp, hp2, hU3⟩ (h.oddU3 G K B B' P R m hcfg)
  · exact absurd ⟨f, hL2⟩ (h.evenL2 G K B B' P R m hcfg)
  · exact absurd ⟨f, hL3⟩ (h.evenL3 G K B B' P R m hcfg)
  · exact absurd ⟨f, hU3⟩ (h.evenU3 G K B B' P R m hcfg)
  · exact h.sp4 G K B B' P R m hcfg ⟨f, hSp⟩
  · exact absurd ⟨f, hG2⟩ (h.g2 G K B B' P R m hcfg)
  · exact absurd ⟨f, hD4⟩ (h.d4 G K B B' P R m hcfg)
  · exact absurd ⟨f, hF4⟩ (h.f4 G K B B' P R m hcfg)
  · exact absurd ⟨f, hSz⟩ (h.sz G K B B' P R m hcfg)
  · exact absurd hTits (h.tits G K B B' P R m hcfg)
  · rcases hn with rfl | rfl
    · exact absurd hn45 (h.l4 G K B B' P R m hcfg)
    · exact absurd hn45 (h.l5 G K B B' P R m hcfg)
  · exact absurd hS (h.sporadic s hs G K B B' P R m hcfg)

end CFSG.QuasithinUnique.Lin2
