module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GSpMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GExcD
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GExcG2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GExcTD4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GExcSz
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GExcTwF4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GExcE6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156

open CFSG.Assembly CFSG.StandardType

@[expose] def RestLabel₅ (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .E6 ∧ p = 3 ∧ Even lab.n) ∨ (lab.tag = .triD4 ∧ p = 3) ∨ lab.tag = .twE6

@[expose] def T156Rest₅ : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → RestLabel₅ p lab →
    MI.CAll lab (GeomBody p lab)

section Core


theorem t156Rest₄_of_rest₅ (h : T156Rest₅) : T156Rest₄ := by
  intro p hp hp2 lab hlab hr
  by_cases h5 : RestLabel₅ p lab
  · exact h p hp hp2 lab hlab h5
  obtain ⟨t, l, n⟩ := lab
  unfold RestLabel₄ at hr
  unfold RestLabel₅ at h5
  dsimp only at hr h5
  rcases hr with ⟨rfl, hl4, -⟩ | rfl | rfl | rfl | rfl | ⟨rfl, -⟩ | rfl
  · exact cAll_geomBody_D_all hp hp2 hl4 hlab.1
  · obtain ⟨hl, hn⟩ := hlab.2
    subst hl
    exact cAll_geomBody_g2 hp hp2 hn
  · have hl : l = 0 := hlab.2
    subst hl
    exact cAll_geomBody_td4 hp hp2 (fun h3 => h5 (Or.inr (Or.inl ⟨rfl, h3⟩))) hlab.1
  · obtain ⟨hl, hodd, h3⟩ := hlab.2
    subst hl
    exact cAll_geomBody_sz hp hp2 h3 hodd
  · obtain ⟨hl, hodd, h3⟩ := hlab.2
    subst hl
    exact cAll_geomBody_twF4 hp hp2 h3 hodd
  · have hl : l = 0 := hlab.2
    subst hl
    rcases Nat.even_or_odd n with hev | hodd
    · exact cAll_geomBody_e6_even hp hp2 (fun h3 => h5 (Or.inl ⟨rfl, h3, hev⟩)) hlab.1 hev
    · exact cAll_geomBody_e6_odd hp hp2 hodd
  · exact absurd (Or.inr (Or.inr rfl)) h5

theorem t156FactOmega_of_rest₅ (h : T156Rest₅) (p : ℕ) : T156FactOmega p :=
  t156FactOmega_of_rest₄ (t156Rest₄_of_rest₅ h) p

end Core

end CFSG.LocalAnalysis.GLTheoremA.T156

end
