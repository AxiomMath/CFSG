module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.Actor
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG.Quasithin CFSG.SectionRank CFSG.Blueprint CFSG.Assembly.LowTwoRank

structure FFHyp (V : Type) [CommGroup V] [Finite V] (H T M E : Subgroup (MulAut V)) : Prop where
  elementary : ∀ v : V, v * v = 1
  o2_trivial : ∀ N : Subgroup (MulAut V), N ≤ H → (N.subgroupOf H).Normal → IsPGroup 2 N → N = ⊥
  sylow : IsSylowTwoOf T H
  not_normal : ¬ (T.subgroupOf H).Normal
  max : T ≤ M ∧ M < H ∧ ∀ X : Subgroup (MulAut V), T ≤ X → X < H → X ≤ M
  offender : E ≤ H ∧ E ≠ ⊥ ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ 2 = 1) ∧
    Nat.card V ≤ Nat.card E * Nat.card (fixV E)

theorem _root_.CFSG.QuasithinUnique.Setup.FFActor.toFFHyp {V : Type} [CommGroup V] [Finite V]
    {H T M E : Subgroup (MulAut V)} (h : FFActor V H T M E) : FFHyp V H T M E :=
  ⟨h.elementary, h.o2_trivial, h.sylow, h.not_normal, h.max, h.offender⟩

theorem FFHyp.toFFActor {V : Type} [CommGroup V] [Finite V] {H T M E : Subgroup (MulAut V)}
    (h : FFHyp V H T M E) (hsqt : CFSG.IsStronglyQuasithin H) : FFActor V H T M E :=
  ⟨h.elementary, h.o2_trivial, h.sylow, h.not_normal, h.max, hsqt, h.offender⟩

section Offenders

variable {V : Type} [CommGroup V]

@[expose] def IsBestOffender (H A : Subgroup (MulAut V)) : Prop :=
  A ≤ H ∧ A ≠ ⊥ ∧ IsElemAbelian2 A ∧ Nat.card V ≤ Nat.card A * Nat.card (fixV A) ∧
    ∀ B : Subgroup (MulAut V), B ≤ A → B ≠ ⊥ → B ≠ A →
      Nat.card B * Nat.card (fixV B) < Nat.card A * Nat.card (fixV A)

@[expose] def bestJ (H : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  ⨆ (A : Subgroup (MulAut V)) (_ : IsBestOffender H A), A

end Offenders

section Ambient

variable {G : Type} [Group G]

@[expose] def centerIn (K : Subgroup G) : Subgroup G :=
  K ⊓ Subgroup.centralizer (K : Set G)

@[expose] def radIn (H : Subgroup G) : Subgroup G :=
  (CFSG.solvableRadical ↥H).map H.subtype

@[expose] def fittingIn (H : Subgroup G) : Subgroup G :=
  (CFSG.fittingSubgroup ↥H).map H.subtype

@[expose] def layerIn (H : Subgroup G) : Subgroup G :=
  (CFSG.layer ↥H).map H.subtype

@[expose] def genFittingIn (H : Subgroup G) : Subgroup G :=
  (CFSG.generalizedFitting ↥H).map H.subtype

@[expose] def coreIn (H M : Subgroup G) : Subgroup G :=
  (M.subgroupOf H).normalCore.map H.subtype

abbrev IsComp (L H : Subgroup G) : Prop := CFSG.Open.IsComponentOf L H

abbrev CQ (L : Subgroup G) : Type := ↥L ⧸ Subgroup.center ↥L

end Ambient


theorem isQuasisimple_of_isComp {G : Type} [Group G] {L H : Subgroup G} (hL : IsComp L H) :
    CFSG.IsQuasisimple ↥L :=
  (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥L).1 hL.2.2

@[expose] def NoEvenSL2Component {G : Type} [Group G] (H : Subgroup G) : Prop :=
  ∀ D : Subgroup G, IsComp D H → ∀ (F : Type) [Field F] [Finite F] (a : ℕ), 2 ≤ a →
    Nat.card F = 2 ^ a → ¬ Nonempty (CQ D ≃* Matrix.SpecialLinearGroup (Fin 2) F)

@[expose] def ResidualFamily (S : Type) [Group S] : Prop :=
  Nonempty (S ≃* alternatingGroup (Fin 6)) ∨
  StatedClassicalModel S .PSU 3 3 1 ∨
  (∃ f : ℕ, 2 ≤ f ∧ (StatedClassicalModel S .PSL 3 2 f ∨ StatedClassicalModel S .PSU 3 2 f ∨
    StatedClassicalModel S .PSp 2 2 f)) ∨
  (∃ f : ℕ, 2 ≤ f ∧ ChevalleyExceptionalModel S .G2 2 f) ∨
  (∃ f : ℕ, 1 ≤ f ∧ ChevalleyExceptionalModel S .trialityD4 2 f) ∨
  (∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ ReeTitsModel S .twistedF4 2 f) ∨
  ReeTitsModel S .Tits 2 1

@[expose] def SmallOddTuple (t : StatedLieTag) (n p f : ℕ) : Prop :=
  (t = .PSL ∧ n = 2 ∧ p = 5 ∧ f = 1) ∨ (t = .PSL ∧ n = 2 ∧ p = 3 ∧ f = 2) ∨
    (t = .PSU ∧ n = 3 ∧ p = 3 ∧ f = 1)

end CFSG.QuasithinUnique.Setup.Family
