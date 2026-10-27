module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Step
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265QCfg

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

@[expose] def QFactUNL : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x b : Ω), QUCfg p S B T x b →
    (∀ e ∈ B, e ∉ Dgrp b x → GLAPLayer p (Ipart p S b ⊓ cx e) = ⊥) →
    (∃ E : Subgroup Ω, E ≤ B ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧ Dgrp b x ≤ E ∧
        GLAPLayer p (S ⊓ cs E) ≠ ⊥) ∨
      (p = 3 ∧ catalogIs (PSimple 3 S) S9.isU4eight ∧ FieldOn 3 b S)

@[expose] def QFactSNL : Prop :=
  ∀ (p : ℕ) (Ω : Type) [Group Ω] [Finite Ω] (S B T : Subgroup Ω) (x : Ω) (D K : Subgroup Ω), QSCfg p S B T x D K →
    (∀ e ∈ B, e ∉ D → GLAPLayer p (K ⊓ cx e) = ⊥) →
    (∃ E : Subgroup Ω, IsE3 p B E ∧ D ≤ E ∧ GLAPLayer p (S ⊓ cs E) ≠ ⊥) ∨ (p = 3 ∧ SmallType 3 K)

theorem qFactU_of_NL (h : QFactUNL) : QFactU := by
  intro p Ω _ _ S B T x b cfg
  by_cases hlay : ∃ e ∈ B, e ∉ Dgrp b x ∧ GLAPLayer p (Ipart p S b ⊓ cx e) ≠ ⊥
  · obtain ⟨e, heB, heD, hne⟩ := hlay
    exact Or.inl (stepB_used cfg.prime cfg.elem cfg.xB cfg.x1
      (fun s _ => Subgroup.mem_centralizer_singleton_iff.2 (cfg.xcen s)) cfg.hb cfg.hbx heB heD hne)
  · push Not at hlay
    exact h p Ω S B T x b cfg hlay

theorem qFactS_of_NL (h : QFactSNL) : QFactS := by
  intro p Ω _ _ S B T x D K cfg
  by_cases hlay : ∃ e ∈ B, e ∉ D ∧ GLAPLayer p (K ⊓ cx e) ≠ ⊥
  · obtain ⟨e, heB, heD, hne⟩ := hlay
    exact Or.inl (stepB_std cfg.prime cfg.elem cfg.std heB heD hne)
  · push Not at hlay
    exact h p Ω S B T x D K cfg hlay

end CFSG.LocalAnalysis.GLTheoremA.S265

end
