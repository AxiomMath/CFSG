module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBasic
public import CFSG.Quasithin.Background.A3Structure36AQuasi
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Alt
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L

open CFSG.Open CFSG.SectionRank CFSG.Assembly.LowTwoRank
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

@[expose] def FamAlt6 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsAlt 6 X → A312For X

@[expose] def FamAlt7 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsAlt 7 X → A312For X

@[expose] def FamL2p : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), CFSG.IsQuasisimple X → p.Prime → p ≠ 2 →
    IsPSL 2 p 1 X → A312For X

@[expose] def FamL2psq : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), CFSG.IsQuasisimple X → p.Prime → p ≠ 2 →
    IsPSL 2 p 2 X → A312For X

@[expose] def FamL3odd : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), CFSG.IsQuasisimple X → p.Prime → p ≠ 2 →
    IsPSL 3 p 1 X → A312For X

@[expose] def FamU3odd : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), CFSG.IsQuasisimple X → p.Prime → p ≠ 2 →
    IsPSU 3 p 1 X → A312For X

@[expose] def FamL2even : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (f : ℕ), CFSG.IsQuasisimple X → 2 ≤ f →
    IsPSL 2 2 f X → A312For X

@[expose] def FamL3even : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (f : ℕ), CFSG.IsQuasisimple X → 1 ≤ f →
    IsPSL 3 2 f X → A312For X

@[expose] def FamU3even : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (f : ℕ), CFSG.IsQuasisimple X → 2 ≤ f →
    IsPSU 3 2 f X → A312For X

@[expose] def FamSp4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (f : ℕ), CFSG.IsQuasisimple X → 2 ≤ f →
    IsPSp4 2 f X → A312For X

@[expose] def FamG2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (f : ℕ), CFSG.IsQuasisimple X → 2 ≤ f →
    IsG2 2 f X → A312For X

@[expose] def FamD4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (f : ℕ), CFSG.IsQuasisimple X → 1 ≤ f →
    Is3D4 2 f X → A312For X

@[expose] def FamF4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (f : ℕ), CFSG.IsQuasisimple X → Odd f → 3 ≤ f →
    Is2F4 f X → A312For X

@[expose] def FamSz : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (f : ℕ), CFSG.IsQuasisimple X → Odd f → 3 ≤ f →
    IsSz f X → A312For X

@[expose] def FamTits : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsTits X → A312For X

@[expose] def FamL4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsPSL 4 2 1 X → A312For X

@[expose] def FamL5 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsPSL 5 2 1 X → A312For X

@[expose] def FamM11 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSporadic .M11 X →
    A312For X

@[expose] def FamM12 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSporadic .M12 X →
    A312For X

@[expose] def FamM22 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSporadic .M22 X →
    A312For X

@[expose] def FamM23 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSporadic .M23 X →
    A312For X

@[expose] def FamM24 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSporadic .M24 X →
    A312For X

@[expose] def FamJ1 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSporadic .J1 X → A312For X

@[expose] def FamJ2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSporadic .J2 X → A312For X

@[expose] def FamJ4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSporadic .J4 X → A312For X

@[expose] def FamHs : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSporadic .HS X → A312For X

@[expose] def FamHe : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSporadic .He X → A312For X

@[expose] def FamRu : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSporadic .Ru X → A312For X

@[expose] def FamSl3even : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (s : Bool) (e : ℕ), CFSG.IsQuasisimple X → 1 ≤ e →
    Int.ModEq 3 ((2 ^ e : ℕ) : ℤ) (if s then 1 else -1) → IsSLEps3 s (2 ^ e) X → A312For X

@[expose] def FamSl3odd : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (s : Bool) (p : ℕ), CFSG.IsQuasisimple X →
    p.Prime → p ≠ 2 → IsSLEps3 s p X → A312For X

@[expose] def FamHat6 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X →
    IsHat X (alternatingGroup (Fin 6)) → A312For X

@[expose] def FamHat7 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X →
    IsHat X (alternatingGroup (Fin 7)) → A312For X

@[expose] def FamHatM22 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X →
    IsHat X (CFSG.Blueprint.NativeSporadic.Carrier .M22) → A312For X

structure A312Families : Prop where
  alt6 : FamAlt6
  alt7 : FamAlt7
  l2p : FamL2p
  l2psq : FamL2psq
  l3odd : FamL3odd
  u3odd : FamU3odd
  l2even : FamL2even
  l3even : FamL3even
  u3even : FamU3even
  sp4 : FamSp4
  g2 : FamG2
  d4 : FamD4
  f4 : FamF4
  sz : FamSz
  tits : FamTits
  l4 : FamL4
  l5 : FamL5
  m11 : FamM11
  m12 : FamM12
  m22 : FamM22
  m23 : FamM23
  m24 : FamM24
  j1 : FamJ1
  j2 : FamJ2
  j4 : FamJ4
  hs : FamHs
  he : FamHe
  ru : FamRu
  sl3even : FamSl3even
  sl3odd : FamSl3odd
  hat6 : FamHat6
  hat7 : FamHat7
  hatM22 : FamHatM22

theorem a312For_of_sqtkSimpleList
    (hF : A312Families) {X : Type} [Group X] [Finite X]
    (hq : CFSG.IsQuasisimple X) (h : CFSG.Milestones.SQTKSimpleList X) : A312For X := by
  rcases h with ⟨n, h5, h8, ⟨e⟩⟩ | ⟨p, hp, hp2, ⟨f, hf, hm⟩ | hm | hm⟩ |
      (⟨f, ⟨h2, hm⟩ | ⟨h1, hm⟩ | ⟨h2, hm⟩ | ⟨h2, hm⟩ | ⟨h2, hm⟩ | ⟨h1, hm⟩ | ⟨ho, h3, hm⟩ |
        ⟨ho, h3, hm⟩⟩ | hT) | ⟨n, hn, hm⟩ | ⟨s, hs, ⟨e⟩⟩
  · obtain rfl | rfl | rfl | rfl : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
    · exact hF.l2even X 2 hq le_rfl
        (CFSG.QuasithinUnique.Ch1.statedClassicalModel_psl_two_four_of_alternating_five X ⟨e⟩)
    · exact hF.alt6 X hq ⟨e⟩
    · exact hF.alt7 X hq ⟨e⟩
    · exact hF.l4 X hq
        (CFSG.QuasithinUnique.Ch1.statedClassicalModel_psl_four_two_of_alternating_eight X ⟨e⟩)
  · rcases hf with rfl | rfl
    · exact hF.l2p X p hq hp hp2 hm
    · exact hF.l2psq X p hq hp hp2 hm
  · exact hF.l3odd X p hq hp hp2 hm
  · exact hF.u3odd X p hq hp hp2 hm
  · exact hF.l2even X f hq h2 hm
  · exact hF.l3even X f hq h1 hm
  · exact hF.u3even X f hq h2 hm
  · exact hF.sp4 X f hq h2 hm
  · exact hF.g2 X f hq h2 hm
  · exact hF.d4 X f hq h1 hm
  · exact hF.f4 X f hq ho h3 hm
  · exact hF.sz X f hq ho h3 hm
  · exact hF.tits X hq hT
  · obtain rfl | rfl := hn
    · exact hF.l4 X hq hm
    · exact hF.l5 X hq hm
  · rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hF.m11 X hq ⟨e⟩
    · exact hF.m12 X hq ⟨e⟩
    · exact hF.m22 X hq ⟨e⟩
    · exact hF.m23 X hq ⟨e⟩
    · exact hF.m24 X hq ⟨e⟩
    · exact hF.j1 X hq ⟨e⟩
    · exact hF.j2 X hq ⟨e⟩
    · exact hF.j4 X hq ⟨e⟩
    · exact hF.hs X hq ⟨e⟩
    · exact hF.he X hq ⟨e⟩
    · exact hF.ru X hq ⟨e⟩

theorem a312For_of_coverList (hF : A312Families) {X : Type} [Group X] [Finite X]
    (hq : CFSG.IsQuasisimple X) (h : A36Case2List X) : A312For X := by
  rcases h with ⟨s, p, e, hp, he, ⟨rfl, hmod⟩ | ⟨hp2, rfl⟩, hX⟩ | h6 | h7 | h22
  · exact hF.sl3even X s e hq he hmod hX
  · rw [pow_one] at hX
    exact hF.sl3odd X s p hq hp hp2 hX
  · exact hF.hat6 X hq h6
  · exact hF.hat7 X hq h7
  · exact hF.hatM22 X hq h22

theorem a312ListFactsCat_of_families
    (hT : ThreeCoverFactCat) (hF : A312Families) :
    A312ListFactsCat := by
  intro X _ _ hq hS hO T hTs B hB hBtop
  have key : A312For X := by
    have hodd : Odd (Nat.card (Subgroup.center X)) := A36A.odd_card_center hO
    have hstep : CatalogStepConclusion X := catalogStepHyp X hq hS hodd
    have hnonab : ∃ a b : X ⧸ Subgroup.center X, a * b ≠ b * a := hq.2.2
    have hlist : CFSG.Milestones.SQTKSimpleList (X ⧸ Subgroup.center X) :=
      CFSG.Milestones.cl_lit_sqtk_simple_list _ hnonab (hstep.2 _ le_rfl)
        (catalog_center_quotient hq hS.2)
    rcases hstep.1 with h1 | h3
    · have hZbot : Subgroup.center X = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
      exact a312For_of_sqtkSimpleList hF hq
        (CFSG.QuasithinUnique.Ch1.sqtkSimpleList_of_mulEquiv
          (CFSG.QuasithinUnique.Ch1.mulEquivQuotientOfCenterEqBot hZbot) hlist)
    · exact a312For_of_coverList hF hq (hT X hq h3 hlist)
  exact key T hTs B hB hBtop

end CFSG.QuasithinUnique.Vol2Native.A312L
