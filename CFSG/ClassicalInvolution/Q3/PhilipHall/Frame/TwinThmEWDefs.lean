module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWHyp

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section Defs

@[expose] def ThmEBelowQ8 (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nat.card G < n →
    ∀ (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G) (R W H : Subgroup G),
      EStandQ8 Ω K S R W → EHypAll Ω K (S : Subgroup G) W H → H = ⊤

@[expose] def ThmEQ8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), EStandQ8 Ω K S R W → EHypAll Ω K (S : Subgroup G) W H → H = ⊤

structure MinCexQ8 {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G)
    (S : Sylow 2 G) (R W H : Subgroup G) : Prop where
  stand : EStandQ8 Ω K S R W
  hyp : EHypAll Ω K (S : Subgroup G) W H
  proper : H ≠ ⊤
  minimal : ThmEBelowQ8 (Nat.card G)

@[expose] def MinCexFalseQ8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCexQ8 Ω K S R W H → False

theorem thmEQ8_of_minCexFalse (h : MinCexFalseQ8) : ThmEQ8 := by
  have key : ∀ n, ThmEBelowQ8 n := by
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

@[expose] def E18_1Q8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCexQ8 Ω K S R W H →
      (∀ g : G, conjSub g K ∈ dstarComp Ω K → g ∈ H) ∧ ∃ J ∈ Ω, J ∉ dstarComp Ω K

@[expose] def E18_3Q8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCexQ8 Ω K S R W H → ∀ J ∈ Ω, ∃ g : G, conjSub g K = J

@[expose] def E18_4CQ8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCexQ8 Ω K S R W H →
      ∀ K' ∈ twinSet Ω K, K' ≠ K → ∀ R' ∈ RSet Ω, R' ≤ K' → IsPGroup 2 ↥(R ⊔ R') →
        ∀ w : G, w ≠ 1 → w * w = 1 → R ⊔ R' ≤ Subgroup.centralizer ({w} : Set G) →
          Subgroup.centralizer ({w} : Set G) ≠ ⊤ → Subgroup.centralizer ({w} : Set G) ≤ H

@[expose] def E18_6Q8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCexQ8 Ω K S R W H →
      classicalInvolutionOddCore G = ⊥ ∧
        ∃ F : Subgroup G, F.Normal ∧ IsSimpleGroup ↥F ∧ (∃ x ∈ F, ∃ y ∈ F, x * y ≠ y * x) ∧
          Subgroup.centralizer (F : Set G) = ⊥

@[expose] def E18_7Q8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCexQ8 Ω K S R W H →
      ∀ a : G, a ≠ 1 → a * a = 1 → Subgroup.centralizer ({a} : Set G) ≤ H →
        ∀ g : G, g * a * g⁻¹ ∈ H → ∃ h ∈ H, h * a * h⁻¹ = g * a * g⁻¹

@[expose] def E18_8zQ8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCexQ8 Ω K S R W H →
      ∀ z : G, IsUniqueInvolution K z → FixesUniqueCoset z H

@[expose] def E18_9Q8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCexQ8 Ω K S R W H →
      ∀ z : G, IsUniqueInvolution K z → ∀ h : G, h⁻¹ * z * h ∈ (S : Subgroup G) →
        h⁻¹ * z * h ≠ z → z * (h⁻¹ * z * h) = (h⁻¹ * z * h) * z →
          FixesUniqueCoset (z * (h⁻¹ * z * h)) H

end Defs

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
