module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264sTD42
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264sU38

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open TauCeti

@[expose] def TD42SevenRank : Prop :=
  ∀ (S : Type) [Group S] [Finite S], catalogIs S fTD42 → ∀ E T : Subgroup S,
    IsElemAbelian 7 E → IsPGroup 2 T → T ≠ ⊥ → E ≤ Subgroup.normalizer (T : Set S) → Nat.card E ≤ 7

structure I264bResidual2 : Prop where
  td42_3 : KDescFam 3 fTD42
  td42_7 : TD42SevenRank
  u38_3 : KDescFam 3 fU38
  linear : ∀ p, KDescFam p fLinear
  unitary : ∀ p, KDescFam p fUnitary
  symplectic : ∀ p, KDescFam p fSymplectic
  omegaPlus : ∀ p, KDescFam p fOmegaPlus
  omegaMinus : ∀ p, KDescFam p fOmegaMinus
  e6 : ∀ p, KDescFam p fE6
  e7 : ∀ p, KDescFam p fE7
  e8 : ∀ p, KDescFam p fE8
  f4 : ∀ p, KDescFam p fF4
  g2 : ∀ p, KDescFam p fG2
  twE6 : ∀ p, KDescFam p fTwE6
  triD4 : ∀ p, KDescFam p fTriD4
  suzuki : ∀ p, KDescFam p fSuzuki
  reeTits : ∀ p, KDescFam p fReeTits

section I264bRes2


theorem i264bResidual_of_2 (h : I264bResidual2) : I264bResidual where
  td42 p := by
    by_cases h3 : p = 3
    · subst h3; exact h.td42_3
    · exact kDescFam_td42_of_ne_three h.td42_7 p h3
  u38 p := by
    by_cases h3 : p = 3
    · subst h3; exact h.u38_3
    · exact kDescFam_u38_of_ne_three p h3
  linear := h.linear
  unitary := h.unitary
  symplectic := h.symplectic
  omegaPlus := h.omegaPlus
  omegaMinus := h.omegaMinus
  e6 := h.e6
  e7 := h.e7
  e8 := h.e8
  f4 := h.f4
  g2 := h.g2
  twE6 := h.twE6
  triD4 := h.triD4
  suzuki := h.suzuki
  reeTits := h.reeTits

end I264bRes2

end CFSG.LocalAnalysis.GLTheoremA
