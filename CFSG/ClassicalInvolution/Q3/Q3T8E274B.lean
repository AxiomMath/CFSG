module

public import CFSG.ClassicalInvolution.Q3.Q3T8E274A
import CFSG.ClassicalInvolution.Q3.Q3CLFrame274
import CFSG.StronglyEmbedded.UniqueCosetFixedEng

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

abbrev _root_.CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T8.IsFrameInv :=
  @CFSG.ClassicalInvolution.Asc77.T8.IsFrameInv

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
    CFSG.GH74.Uniqueness CFSG.StronglyEmbedded.UniqueCoset CFSG.ClassicalInvolution.Asc77.AscP1Nine3
namespace T8
open CFSG.ClassicalInvolution.Asc77.T8
section Min
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem le_centralizer_mul {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8 Ω K J S R T W z t) :
    R ≤ Subgroup.centralizer ({z * t} : Set G) :=
  Q3CL.Frame.T8.le_centralizer_mul hs.toFrame

theorem exists_sylow_centralizer {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G}
    {z t : G} (hs : Std8 Ω K J S R T W z t) :
    ∃ S' : Sylow 2 G, R ≤ (S' : Subgroup G) ∧
      IsSylow2In ((S' : Subgroup G) ⊓ Subgroup.centralizer ({z * t} : Set G))
        (Subgroup.centralizer ({z * t} : Set G)) :=
  Q3CL.Frame.T8.exists_sylow_centralizer hs.toFrame

theorem sylow_le_H274_of_ge {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8 Ω K J S R T W z t) {S' : Sylow 2 G} (hRS' : R ≤ (S' : Subgroup G)) :
    (S' : Subgroup G) ≤ H274 Ω K z :=
  Q3CL.Frame.T8.sylow_le_H274_of_ge hs.toFrame hRS'

theorem not_commute_of_not_mem_H274 {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G}
    {z t : G} (hs : Std8 Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K) {g w : G}
    (hg : g ∉ H274 Ω K z) (hw : IsConj z w) (hwH : w ∈ H274 Ω K z) :
    g⁻¹ * (z * t) * g * w ≠ w * (g⁻¹ * (z * t) * g) :=
  Q3CL.Frame.T8.not_commute_of_not_mem_H274 hs.toFrame hcomp hg hw hwH

theorem frame_facts {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8 Ω K J S R T W z t) {S' : Sylow 2 G}
    (hS'H : (S' : Subgroup G) ≤ H274 Ω K z) {X M : Subgroup G} {x : G} (hXS : X ≤ (S' : Subgroup G))
    (hM : M ∈ Ω) (hXM : IsSylow2In X M) (hXΩ : X ∈ RSet Ω) (hx : IsUniqueInvolution M x) :
    x ∈ X ∧ x ∈ H274 Ω K z ∧ IsConj z x ∧ (∀ y ∈ X, x * y = y * x) :=
  Q3CL.Frame.T8.frame_facts hs.toFrame hS'H hXS hM hXM hXΩ hx

theorem conjSub_ne_of_not_mem_H274 {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G}
    {z t : G} (hs : Std8 Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K)
    {S' : Sylow 2 G} (hS'H : (S' : Subgroup G) ≤ H274 Ω K z) {g : G} (hg : g ∉ H274 Ω K z)
    {X M : Subgroup G} {x : G} (hXS : X ≤ (S' : Subgroup G)) (hM : M ∈ Ω)
    (hXM : IsSylow2In X M) (hXΩ : X ∈ RSet Ω) (hx : IsUniqueInvolution M x) :
    conjSub (g⁻¹ * (z * t) * g) X ≠ X :=
  Q3CL.Frame.T8.conjSub_ne_of_not_mem_H274 hs.toFrame hcomp hS'H hg hXS hM hXM hXΩ hx

theorem exists_normalized_conj {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G}
    {z t : G} (hs : Std8 Ω K J S R T W z t) {S' : Sylow 2 G}
    (hS'a : IsSylow2In ((S' : Subgroup G) ⊓ Subgroup.centralizer ({z * t} : Set G))
      (Subgroup.centralizer ({z * t} : Set G)))
    (hS'H : (S' : Subgroup G) ≤ H274 Ω K z) {g : G} (hg : g ∉ H274 Ω K z)
    (hgH : g⁻¹ * (z * t) * g ∈ H274 Ω K z) :
    ∃ g' : G, g' ∉ H274 Ω K z ∧ g'⁻¹ * (z * t) * g' ∈ (S' : Subgroup G) ∧
      ∀ s ∈ (S' : Subgroup G), (g'⁻¹ * (z * t) * g') * s = s * (g'⁻¹ * (z * t) * g') →
        g' * s * g'⁻¹ ∈ (S' : Subgroup G) :=
  Q3CL.Frame.T8.exists_normalized_conj hs.toFrame hS'a hS'H hg hgH

theorem eight_le_card_RSet {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8 Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K) {S' : Sylow 2 G}
    (hRS' : R ≤ (S' : Subgroup G)) (hS'H : (S' : Subgroup G) ≤ H274 Ω K z) {g : G}
    (hg : g ∉ H274 Ω K z) (hdS : g⁻¹ * (z * t) * g ∈ (S' : Subgroup G))
    (hCS : ∀ s ∈ (S' : Subgroup G), (g⁻¹ * (z * t) * g) * s = s * (g⁻¹ * (z * t) * g) →
      g * s * g⁻¹ ∈ (S' : Subgroup G)) :
    8 ≤ Nat.card {X : Subgroup G // X ∈ RSet Ω ∧ X ≤ (S' : Subgroup G)} :=
  Q3CL.Frame.T8.eight_le_card_RSet hs.toFrame hcomp hRS' hS'H hg hdS hCS

theorem IsFrameInv.mem (hΩ : HypOmegaMod Ω) {X : Subgroup G} {x : G}
    (hX : X ∈ RSet Ω) (h : IsFrameInv Ω X x) : x ∈ X :=
  Q3CL.Frame.T8.IsFrameInv.mem hΩ hX h

theorem IsFrameInv.ne {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8 Ω K J S R T W z t) {X Y : Subgroup G} {x y : G} (hx : IsFrameInv Ω X x)
    (hy : IsFrameInv Ω Y y) (hXY : X ≠ Y) (hc : Commutes X Y) : x ≠ y :=
  Q3CL.Frame.T8.IsFrameInv.ne hs.toFrame hx hy hXY hc

theorem exists_four_group {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8 Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K) {S' : Sylow 2 G}
    (hRS' : R ≤ (S' : Subgroup G)) (hS'H : (S' : Subgroup G) ≤ H274 Ω K z) {g : G}
    (hg : g ∉ H274 Ω K z) (hdS : g⁻¹ * (z * t) * g ∈ (S' : Subgroup G))
    (hcount : 8 ≤ Nat.card {X : Subgroup G // X ∈ RSet Ω ∧ X ≤ (S' : Subgroup G)}) :
    ∃ u v : G, u ∈ (S' : Subgroup G) ∧ v ∈ (S' : Subgroup G) ∧ u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v ∧
      u * u = 1 ∧ v * v = 1 ∧ u * v = v * u ∧
      (g⁻¹ * (z * t) * g) * u = u * (g⁻¹ * (z * t) * g) ∧
      (g⁻¹ * (z * t) * g) * v = v * (g⁻¹ * (z * t) * g) ∧
      (∀ Y ∈ RSet Ω, Y ≤ (S' : Subgroup G) → ∀ y ∈ Y, u * y = y * u) ∧
      (∀ Y ∈ RSet Ω, Y ≤ (S' : Subgroup G) → ∀ y ∈ Y, v * y = y * v) :=
  Q3CL.Frame.T8.exists_four_group hs.toFrame hcomp hRS' hS'H hg hdS hcount

theorem mem_H274_of_min {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hs : Std8 Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K)
    (hmin : ∀ S₂ : Sylow 2 G, R ≤ (S₂ : Subgroup G) →
      8 ≤ Nat.card {X : Subgroup G // X ∈ RSet Ω ∧ X ≤ (S₂ : Subgroup G)} →
        ∀ x : G, x ∈ (S₂ : Subgroup G) → x * x = 1 → x ≠ 1 →
          (∀ Y ∈ RSet Ω, Y ≤ (S₂ : Subgroup G) → ∀ y ∈ Y, x * y = y * x) →
            Subgroup.centralizer ({x} : Set G) ≤ H274 Ω K z)
    {g : G} (hgH : g⁻¹ * (z * t) * g ∈ H274 Ω K z) : g ∈ H274 Ω K z :=
  Q3CL.Frame.T8.mem_H274_of_min hs.toFrame hcomp hmin hgH
end Min
end T8

@[expose] def C27_4M : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
      ¬ DConnected Ω → ∀ S₂ : Sylow 2 G, R ≤ (S₂ : Subgroup G) →
        8 ≤ Nat.card {X : Subgroup G // X ∈ RSet Ω ∧ X ≤ (S₂ : Subgroup G)} →
          ∀ x : G, x ∈ (S₂ : Subgroup G) → x * x = 1 → x ≠ 1 →
            (∀ Y ∈ RSet Ω, Y ≤ (S₂ : Subgroup G) → ∀ y ∈ Y, x * y = y * x) →
              Subgroup.centralizer ({x} : Set G) ≤ T8.H274 Ω K z

theorem c27_4a_of_min (h2 : C27_2) (hmin : C27_4M) : C27_4a := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc
  have hcomp : dComp Ω K = dstarComp Ω K := h2 G Ω K J S R T W z t hs hdisc
  have hmin' := hmin G Ω K J S R T W z t hs hdisc
  have hzt : z * t ∈ T8.H274 Ω K z :=
    T8.centralizer_mul_le_H274 hs.hJ hs.ht (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  refine CFSG.StronglyEmbedded.UniqueCoset.existsUnique_fixed_of_mem hzt (fun g hg => ?_)
  exact T8.mem_H274_of_min hs hcomp hmin' hg
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
section Main
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}
end Main

@[expose] def C27_8E4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
      ¬ DConnected Ω → MuIsoE4 Ω W → Subgroup.centralizer ({z * t} : Set G) ≤ sigmaNorm Ω K

@[expose] def C27_8nE4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 Ω K J S R T W z t →
      ¬ DConnected Ω → ¬ MuIsoE4 Ω W → Subgroup.centralizer ({z * t} : Set G) ≤ sigmaNorm Ω K

theorem c27_8_of_split (h1 : C27_8E4) (h2 : C27_8nE4) : C27_8 := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc
  by_cases hE4 : MuIsoE4 Ω W
  · exact h1 G Ω K J S R T W z t hs hdisc hE4
  · exact h2 G Ω K J S R T W z t hs hdisc hE4
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

theorem c27_2_of_c26_2_c26_13 (h2 : C26_2) (h13 : C26_13) : C27_2 := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc
  by_contra hne
  have hP : PartIHyp Ω := ⟨hs.stand.hyp, hs.stand.cls, hs.stand.aEmpty⟩
  have hW : W ∈ WSet Ω := hs.hW.1
  have hnc : ¬ DbarConnected Ω W := thompsonGraphAll G Ω hP hs.stand.mem hne hW
  rcases l7_10_proved G Ω hP W hW hnc with h3 | h4 | h5
  · exact T8.not_muIsoS3_of_std8 hs h3
  · exact h2 G Ω K J S R T W z t hs hdisc h4
  · exact h13 G Ω K J S R T W z t hs hdisc h5

theorem thm8A_of_c26_2_c26_13 (h2 : C26_2) (h13 : C26_13) (h274a : C27_4a)
    (h278 : C27_8) : Thm8A :=
  thm8A_of_steps c27_nbr_proved c27_setup_proved
    (c27_4_of_steps (c27_2_of_c26_2_c26_13 h2 h13) h274a) h278
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
