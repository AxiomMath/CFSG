module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWHyp
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinBridge
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscData
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSep
public import CFSG.ClassicalInvolution.Q3.TL4InductDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc

namespace ThmE

section Defs


structure EIH (r n : ℕ) : Prop where
  cit : CIT3Below n
  tbelow : TightBelowR r n
  twin : Thm1RTwinBelowR r n
  t4 : Thm4RTwinBelow r n

theorem EIH.mono {r m n : ℕ} (h : m ≤ n) (H : EIH r n) : EIH r m :=
  ⟨cit3Below_mono h H.cit, TL4.Induct.tightBelowR_mono h H.tbelow, H.twin.mono h, H.t4.mono h⟩

structure EStand (r : ℕ) {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G)
    (S : Sylow 2 G) (R W : Subgroup G) : Prop where
  hyp : HypOmegaGen Ω
  cls : Q3CL.ClassicalClause Ω
  quat : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧
    Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2)))
  two : ∀ L ∈ Ω, IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L)
  ih : EIH r (Nat.card G)
  mem : K ∈ Ω
  aEmpty : AEmpty Ω K
  twin : ∃ K' ∈ twinSet Ω K, K' ≠ K ∧ ∃ R' ∈ RSet Ω, R' ≤ K' ∧ R' ≤ (S : Subgroup G)
  hR : R ∈ RSet Ω ∧ R ≤ K ∧ R ≤ (S : Subgroup G)
  hW : W ∈ WSet Ω ∧ W ≤ (S : Subgroup G) ∧ ∀ s ∈ (S : Subgroup G), conjSub s W = W

@[expose] def ThmEBelow (r n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G < n →
    ∀ (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G) (R W H : Subgroup G),
      EStand r Ω K S R W → TwinThmEW.EHypAll Ω K (S : Subgroup G) W H → H = ⊤

@[expose] def ThmEAll (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), EStand r Ω K S R W → TwinThmEW.EHypAll Ω K (S : Subgroup G) W H → H = ⊤

structure MinCex (r : ℕ) {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G)
    (S : Sylow 2 G) (R W H : Subgroup G) : Prop where
  stand : EStand r Ω K S R W
  hyp : TwinThmEW.EHypAll Ω K (S : Subgroup G) W H
  proper : H ≠ ⊤
  minimal : ThmEBelow r (Nat.card G)

@[expose] def MinCexFalse (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex r Ω K S R W H → False

theorem thmEAll_of_minCexFalse {r : ℕ} (h : MinCexFalse r) : ThmEAll r := by
  have key : ∀ n, ThmEBelow r n := by
    intro n
    induction n with
    | zero =>
      intro G _ _ hG
      exact absurd hG (by omega)
    | succ n ih =>
      intro G _ _ hG Ω K S R W H hst hH
      by_cases hn : Nat.card G < n
      · exact ih G hn Ω K S R W H hst hH
      · have hGn : Nat.card G = n := by omega
        by_contra hne
        exact h G Ω K S R W H ⟨hst, hH, hne, hGn ▸ ih⟩
  intro G _ _ Ω K S R W H hst hH
  exact key (Nat.card G + 1) G (Nat.lt_succ_self _) Ω K S R W H hst hH

end Defs

end ThmE

end CFSG.CGT.PushingUpLit.SolKNA.R4
