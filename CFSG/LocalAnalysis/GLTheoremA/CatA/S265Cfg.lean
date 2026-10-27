module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

structure UCfg (p : ℕ) {Ω : Type} [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x b : Ω) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  kgroup : CFSG.Open.IsKGroup Ω
  comp : GLAPComponent p (⊤ : Subgroup Ω) S
  normal : S.Normal
  chev : IsChevSimple 2 (PSimple p S)
  gen : S ⊔ B ⊔ T = ⊤
  elem : IsElemAbelian p B
  two : IsPGroup 2 T
  bnorm : B ≤ Subgroup.normalizer (T : Set Ω)
  ne : (⁅T, B⁆ : Subgroup Ω) ≠ ⊥
  rank : p ^ GLATwoLocalRank p Ω ≤ Nat.card B
  big : p ^ 4 ≤ Nat.card B
  cyc : CycModSylow p S
  xB : x ∈ B
  x1 : x ≠ 1
  xcen : ∀ g : Ω, g * x = x * g
  centB : ∀ c ∈ B, CentMod p S c ↔ c ∈ Subgroup.zpowers x
  hb : b ∈ B
  hbx : b ∉ Subgroup.zpowers x
  prop : R2Prop p b S
  g2 : p = 3 → IsTD4 3 S → centCard2 3 S b = Nat.sqrt (card2 3 S)
  ipart : Ipart p S b ≠ ⊥
  noninn : ¬ InnDiagOn p B S
  gstar : ∃ E : Subgroup Ω, E ≤ B ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
    GLAPLayer p (S ⊓ cs E) ≠ ⊥

@[expose] def FactU : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x b : Ω), UCfg p S B T x b →
    (∃ E : Subgroup Ω, E ≤ B ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧ Dgrp b x ≤ E ∧
        GLAPLayer p (S ⊓ cs E) ≠ ⊥) ∨
      (p = 3 ∧ catalogIs (PSimple 3 S) S9.isU4eight ∧ FieldOn 3 b S)

structure SCfg (p : ℕ) {Ω : Type} [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  kgroup : CFSG.Open.IsKGroup Ω
  comp : GLAPComponent p (⊤ : Subgroup Ω) S
  normal : S.Normal
  quasi : CFSG.Open.IsQuasisimple ↥S
  chev : IsChevSimple 2 (PSimple p S)
  gen : S ⊔ B ⊔ T = ⊤
  elem : IsElemAbelian p B
  two : IsPGroup 2 T
  bnorm : B ≤ Subgroup.normalizer (T : Set Ω)
  ne : (⁅T, B⁆ : Subgroup Ω) ≠ ⊥
  rank : p ^ GLATwoLocalRank p Ω ≤ Nat.card B
  big : p ^ 4 ≤ Nat.card B
  cyc : CycModSylow p S
  xB : x ∈ B
  x1 : x ≠ 1
  xcen : ∀ g : Ω, g * x = x * g
  centB : ∀ c ∈ B, CentMod p S c ↔ c ∈ Subgroup.zpowers x
  inn : InnDiagOn p B S
  std : GLAStdSubPre p B x S D K

@[expose] def FactS : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω), SCfg p S B T x D K →
    (∃ E : Subgroup Ω, IsE3 p B E ∧ D ≤ E ∧ GLAPLayer p (S ⊓ cs E) ≠ ⊥) ∨ (p = 3 ∧ SmallType 3 K)

end CFSG.LocalAnalysis.GLTheoremA.S265

end
