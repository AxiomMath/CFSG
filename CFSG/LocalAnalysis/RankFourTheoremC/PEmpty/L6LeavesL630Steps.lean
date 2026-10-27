module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (smallRankF smallRankR smallRankIsQ8D8 Lemma630Iii)

variable {G : Type} [Group G] [Finite G]

structure L630Setting (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G)
    (x z : G) (T : Subgroup G) (f : ℕ) : Prop where
  situation : Situation G p P M
  point : Point P M x
  central : Central P z
  prop614 : Prop614At M x z
  sylowTwo : CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankSylowTwo P M T
  cover : CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankCover p M x
  lemma628 : CFSG.LocalAnalysis.RankThreeTheoremC.Lemma628Concl p M x z T
  prime : f.Prime
  ne_two : f ≠ 2
  core_ne_bot : pCoreOf f (CFSG.LocalAnalysis.RankThreeTheoremC.smallRankD p x) ≠ ⊥
  lemma629 : CFSG.LocalAnalysis.RankThreeTheoremC.Lemma629Concl p M x z T f

@[expose] def KFactAutQ8D8Five : Prop :=
  ∀ (R : Type) [Group R] [Finite R], smallRankIsQ8D8 (⊤ : Subgroup R) →
    ∀ P : Subgroup (MulAut R), IsPGroup 5 P → Nat.card P ≤ 5

@[expose] def L613f3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G),
    Situation G p P M → Point P M x → Central P z →
    ¬ CFSG.ABGLocalTools.IsPConstrained p ↥M →
    ∀ (H K : Subgroup G), H ≤ M ⊓ centralizer ({x} : Set G) → S622IsSimpleSection H K →
      p ∣ K.relIndex H → 3 ∣ K.relIndex H → CFSG.Open.GLBStronglyEmbedded 3 M

@[expose] def StepFiveFPF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G)
    (T : Subgroup G) (f : ℕ), L630Setting G p P M x z T f →
    ∀ g ∈ normalizer ((smallRankF p f x : Subgroup G) : Set G),
      g ^ p ∈ centralizer ((smallRankF p f x : Subgroup G) : Set G) →
      g ∉ centralizer ((smallRankF p f x : Subgroup G) : Set G) →
      ∀ a ∈ smallRankF p f x, a ≠ 1 → g * a * g⁻¹ ≠ a

@[expose] def StepNineFPF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G)
    (T : Subgroup G) (f : ℕ), L630Setting G p P M x z T f →
    ∀ g ∈ normalizer ((smallRankF p f x : Subgroup G) : Set G),
      g ^ 3 ∈ centralizer ((smallRankF p f x : Subgroup G) : Set G) →
      g ∉ centralizer ((smallRankF p f x : Subgroup G) : Set G) →
      ∀ a ∈ smallRankF p f x, a ≠ 1 → g * a * g⁻¹ ≠ a

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630
