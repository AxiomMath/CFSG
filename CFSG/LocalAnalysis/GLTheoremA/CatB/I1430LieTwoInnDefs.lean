module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.LocalAnalysis.GLTheoremA.H1431c (CompOfType)

@[expose] def I1430LieTwoInnNo (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, P d.1 → d.1.characteristic = 2 →
      KD264Lie.fieldSize d.1 = 2 →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ α : MulAut S, α ∈ innAutDerived S → α ^ 3 = 1 → α ≠ 1 → ¬ CompOfType S α isA6

@[expose] def I1430InnNoA : Prop :=
  I1430LieTwoInnNo fun d => ∃ n q, d = .A n q

@[expose] def I1430InnNoTwistedA : Prop :=
  I1430LieTwoInnNo fun d => ∃ n q, d = .twistedA n q

@[expose] def I1430InnNoD : Prop :=
  I1430LieTwoInnNo fun d => ∃ n q, d = .D n q

@[expose] def I1430InnNoTwistedD : Prop :=
  I1430LieTwoInnNo fun d => ∃ n q, d = .twistedD n q

@[expose] def I1430InnNoE : Prop :=
  I1430LieTwoInnNo fun d => ∃ q, d = .E6 q ∨ d = .E7 q ∨ d = .E8 q

@[expose] def I1430InnNoTwistedE6 : Prop :=
  I1430LieTwoInnNo fun d => ∃ q, d = .twistedE6 q

@[expose] def I1430InnNoF4 : Prop :=
  I1430LieTwoInnNo fun d => ∃ q, d = .F4 q

@[expose] def I1430InnOther (d : TauCeti.LieTypeIndex) : Prop :=
  (∃ n q, d = .C n q) ∨ (∃ q, d = .G2 q) ∨ (∃ q, d = .trialityD4 q) ∨ (∃ m, d = .suzuki m) ∨
    (∃ m, d = .reeG2 m) ∨ (∃ m, d = .reeF4 m) ∨ d = .tits

@[expose] def I1430InnNoOther : Prop :=
  I1430LieTwoInnNo I1430InnOther

theorem i1430LieTwoInnNo_notB (hA : I1430InnNoA) (htA : I1430InnNoTwistedA) (hD : I1430InnNoD)
    (htD : I1430InnNoTwistedD) (hE : I1430InnNoE) (htE6 : I1430InnNoTwistedE6)
    (hF4 : I1430InnNoF4) (hO : I1430InnNoOther) :
    I1430LieTwoInnNo fun d => ¬ ∃ n q, d = .B n q := by
  intro S _ _ hS hnc d hP hc hf hSd α hα h3 h1
  obtain ⟨d, hv⟩ := d
  cases d with
  | A n q => exact hA S hS hnc ⟨_, hv⟩ ⟨n, q, rfl⟩ hc hf hSd α hα h3 h1
  | twistedA n q => exact htA S hS hnc ⟨_, hv⟩ ⟨n, q, rfl⟩ hc hf hSd α hα h3 h1
  | B n q => exact absurd ⟨n, q, rfl⟩ hP
  | C n q => exact hO S hS hnc ⟨_, hv⟩ (Or.inl ⟨n, q, rfl⟩) hc hf hSd α hα h3 h1
  | D n q => exact hD S hS hnc ⟨_, hv⟩ ⟨n, q, rfl⟩ hc hf hSd α hα h3 h1
  | twistedD n q => exact htD S hS hnc ⟨_, hv⟩ ⟨n, q, rfl⟩ hc hf hSd α hα h3 h1
  | E6 q => exact hE S hS hnc ⟨_, hv⟩ ⟨q, Or.inl rfl⟩ hc hf hSd α hα h3 h1
  | E7 q => exact hE S hS hnc ⟨_, hv⟩ ⟨q, Or.inr (Or.inl rfl)⟩ hc hf hSd α hα h3 h1
  | E8 q => exact hE S hS hnc ⟨_, hv⟩ ⟨q, Or.inr (Or.inr rfl)⟩ hc hf hSd α hα h3 h1
  | F4 q => exact hF4 S hS hnc ⟨_, hv⟩ ⟨q, rfl⟩ hc hf hSd α hα h3 h1
  | G2 q => exact hO S hS hnc ⟨_, hv⟩ (Or.inr (Or.inl ⟨q, rfl⟩)) hc hf hSd α hα h3 h1
  | twistedE6 q => exact htE6 S hS hnc ⟨_, hv⟩ ⟨q, rfl⟩ hc hf hSd α hα h3 h1
  | trialityD4 q =>
    exact hO S hS hnc ⟨_, hv⟩ (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩))) hc hf hSd α hα h3 h1
  | suzuki m =>
    exact hO S hS hnc ⟨_, hv⟩ (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rfl⟩)))) hc hf hSd α hα h3 h1
  | reeG2 m =>
    exact hO S hS hnc ⟨_, hv⟩ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rfl⟩))))) hc hf hSd α hα
      h3 h1
  | reeF4 m =>
    exact hO S hS hnc ⟨_, hv⟩ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rfl⟩))))))
      hc hf hSd α hα h3 h1
  | tits =>
    exact hO S hS hnc ⟨_, hv⟩ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))) hc hf hSd
      α hα h3 h1

end CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed

end
