module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrL18Def
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrJSec
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrJAct
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrImg
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YAFacts

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem frame_A_le_S {Γ : Type} [Group Γ] (fr : SFrame Γ) : fr.A ≤ fr.S := by
  rw [SFrame.A, SFrame.S, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

private theorem frame_E_le_A {Γ : Type} [Group Γ] (fr : SFrame Γ) : fr.E ≤ fr.A := by
  rw [SFrame.E, SFrame.A, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact Subgroup.mul_mem fr.A (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  · exact Subgroup.mul_mem fr.A
      (Subgroup.mul_mem fr.A (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))) (Subgroup.subset_closure (by simp))
  · exact Subgroup.pow_mem fr.A (Subgroup.subset_closure (by simp)) 2

private theorem frame_F_le_A {Γ : Type} [Group Γ] (fr : SFrame Γ) : fr.F ≤ fr.A := by
  rw [SFrame.F, SFrame.A, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact Subgroup.mul_mem fr.A (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  · exact Subgroup.mul_mem fr.A (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  · exact Subgroup.pow_mem fr.A (Subgroup.subset_closure (by simp)) 2

private theorem frame_Z_le_E {Γ : Type} [Group Γ] (fr : SFrame Γ) : fr.Z ≤ fr.E := by
  rw [SFrame.Z, SFrame.E, Subgroup.zpowers_le]
  exact Subgroup.subset_closure (by simp)

private theorem frame_Z_le_F {Γ : Type} [Group Γ] (fr : SFrame Γ) : fr.Z ≤ fr.F := by
  rw [SFrame.Z, SFrame.F, Subgroup.zpowers_le]
  exact Subgroup.subset_closure (by simp)

private theorem frame_A_le_normalizer {Γ : Type} [Group Γ] [Finite Γ] (fr : Frame Γ)
    (h14 : fr.Fact14) {X : Subgroup Γ} (hXA : X ≤ fr.A) (hZX : fr.Z ≤ X) :
    fr.A ≤ Subgroup.normalizer (X : Set Γ) := by
  have hAf := A_facts fr h14
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hcomm : ⁅a, x⁆ ∈ fr.Z := hAf.2.1 a ha x (hXA hx)
    have heq : a * x * a⁻¹ = ⁅a, x⁆ * x := by
      rw [commutatorElement_def]; group
    rw [heq]
    exact Subgroup.mul_mem X (hZX hcomm) hx
  · intro hx
    have hcomm : ⁅a⁻¹, a * x * a⁻¹⁆ ∈ fr.Z :=
      hAf.2.1 a⁻¹ (inv_mem ha) (a * x * a⁻¹) (hXA hx)
    have heq : a⁻¹ * (a * x * a⁻¹) * a = ⁅a⁻¹, a * x * a⁻¹⁆ * (a * x * a⁻¹) := by
      rw [commutatorElement_def]; group
    have hxeq : x = a⁻¹ * (a * x * a⁻¹) * a := by group
    rw [hxeq, heq]
    exact Subgroup.mul_mem X (hZX hcomm) hx

theorem lf18_4e_of (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) : LF18_4e s := by
  haveI := isPerfect_of_hrSetting hS
  obtain ⟨-, -, -, h14, -, -, -, h18, -, -⟩ := s.facts
  obtain ⟨h18_1, -, -, h18E, -⟩ := h18
  obtain ⟨-, -, hSecE, -, hRegE⟩ := h18E
  have hA_norm_E : s.fr'.A ≤ Subgroup.normalizer (s.fr'.E : Set (MulAut (L ⧸ center L))) :=
    frame_A_le_normalizer s.fr' h14 (frame_E_le_A s.fr'.toSFrame) (frame_Z_le_E s.fr'.toSFrame)
  have hS_le_L' : s.fr'.S ≤ innerAut (L ⧸ center L) := by
    calc s.fr'.S = normIn (innerAut (L ⧸ center L)) s.fr'.S := h18_1.2.symm
      _ ≤ innerAut (L ⧸ center L) := inf_le_left
  have hA_le_L' : s.fr'.A ≤ innerAut (L ⧸ center L) := (frame_A_le_S s.fr'.toSFrame).trans hS_le_L'
  have hA_in_normE : s.fr'.A ≤ normIn (innerAut (L ⧸ center L)) s.fr'.E :=
    le_inf hA_le_L' hA_norm_E
  intro k hk hk3 hkz
  have hkL : k ∈ L := hk.1
  let α : MulAut (L ⧸ center L) := MulAut.conj (QuotientGroup.mk (⟨k, hkL⟩ : ↥L))
  have hα : ActsAs L k α := actsAs_of_mem L hkL
  have hA2 : IsPGroup 2 ↥s.fr.A := s3_isPGroup_of_le s (s3_A_le_S s)
  have hE2 : IsPGroup 2 ↥s.fr.E :=
    s3_isPGroup_of_le s ((s3_E_le_A s).trans (s3_A_le_S s))
  have hAL : s.fr.A ≤ L := (s3_A_le_S s).trans (s3_S_le_L s)
  have hEL : s.fr.E ≤ L := (s3_E_le_A s).trans hAL
  have hA'2 : IsPGroup 2 ↥s.fr'.A := by
    have h := isPGroup_jSub (L := L) (V := s.fr.A) hA2
    rwa [s3_jSub_A s] at h
  have hα3 : IsPGroup 3 ↥(zpowers α) := isPGroup_zpowers_of_actsAs hα hk3
  have hα1 : α ≠ 1 := ne_one_of_actsAs_of_not_mem_zL hkL hα hkz
  have hnormE : jSub L (normIn L s.fr.E) = normIn (innerAut (L ⧸ center L)) s.fr'.E := by
    rw [jSub_normIn hZ hEL hE2, jSub_self L, s3_jSub_E hS hZ s]
  have hαN : α ∈ normIn (innerAut (L ⧸ center L)) s.fr'.E := by
    rw [← hnormE]
    exact (mem_jSub L).mpr ⟨k, hk, hα⟩
  have hSyl : IsSylowIn 3 (normIn (innerAut (L ⧸ center L)) s.fr'.E) (zpowers α) :=
    isSylowIn_zpowers_of_secProp_perm3 hSecE hA_in_normE hA'2 hαN hα3 hα1
  obtain ⟨hregEZ, hregAE⟩ := hRegE (zpowers α) hSyl
  refine ⟨?_, ?_⟩
  · have hreg : Sec1.ActsRegularly (zpowers α) (jSub L s.fr.E) (jSub L s.fr.Z) := by
      rw [s3_jSub_E hS hZ s, s3_jSub_Z s]
      exact hregEZ
    exact actsTransitively_of_jSub hZ hkL hα hEL hE2 (s3_Z_le_E s) hreg
  · have hreg : Sec1.ActsRegularly (zpowers α) (jSub L s.fr.A) (jSub L s.fr.E) := by
      rw [s3_jSub_A s, s3_jSub_E hS hZ s]
      exact hregAE
    exact actsTransitively_of_jSub hZ hkL hα hAL hA2 (s3_E_le_A s) hreg

theorem lf18_5f_of (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) : LF18_5f s := by
  haveI := isPerfect_of_hrSetting hS
  obtain ⟨-, -, -, h14, -, -, -, h18, -, -⟩ := s.facts
  obtain ⟨h18_1, -, -, -, h18F⟩ := h18
  obtain ⟨-, -, -, hSecAF, hRegAF⟩ := h18F
  have hA_norm_F : s.fr'.A ≤ Subgroup.normalizer (s.fr'.F : Set (MulAut (L ⧸ center L))) :=
    frame_A_le_normalizer s.fr' h14 (frame_F_le_A s.fr'.toSFrame) (frame_Z_le_F s.fr'.toSFrame)
  have hS_le_L' : s.fr'.S ≤ innerAut (L ⧸ center L) := by
    calc s.fr'.S = normIn (innerAut (L ⧸ center L)) s.fr'.S := h18_1.2.symm
      _ ≤ innerAut (L ⧸ center L) := inf_le_left
  have hA_le_L' : s.fr'.A ≤ innerAut (L ⧸ center L) := (frame_A_le_S s.fr'.toSFrame).trans hS_le_L'
  have hA_in_normA : s.fr'.A ≤ normIn (innerAut (L ⧸ center L)) s.fr'.A :=
    le_inf hA_le_L' Subgroup.le_normalizer
  have hA_in_normF : s.fr'.A ≤ normIn (innerAut (L ⧸ center L)) s.fr'.F :=
    le_inf hA_le_L' hA_norm_F
  have hA_in_normAF : s.fr'.A ≤
      normIn (innerAut (L ⧸ center L)) s.fr'.A ⊓
        normIn (innerAut (L ⧸ center L)) s.fr'.F :=
    le_inf hA_in_normA hA_in_normF
  intro k hk hk3 hkz
  have hkA : k ∈ normIn L s.fr.A := hk.1
  have hkF : k ∈ normIn L s.fr.F := hk.2
  have hkL : k ∈ L := hkA.1
  let α : MulAut (L ⧸ center L) := MulAut.conj (QuotientGroup.mk (⟨k, hkL⟩ : ↥L))
  have hα : ActsAs L k α := actsAs_of_mem L hkL
  have hAL : s.fr.A ≤ L := (s3_A_le_S s).trans (s3_S_le_L s)
  have hFL : s.fr.F ≤ L := (s3_F_le_A s).trans hAL
  have hA2 : IsPGroup 2 ↥s.fr.A := s3_isPGroup_of_le s (s3_A_le_S s)
  have hF2 : IsPGroup 2 ↥s.fr.F :=
    s3_isPGroup_of_le s ((s3_F_le_A s).trans (s3_A_le_S s))
  have hA'2 : IsPGroup 2 ↥s.fr'.A := by
    have h := isPGroup_jSub (L := L) (V := s.fr.A) hA2
    rwa [s3_jSub_A s] at h
  have hα3 : IsPGroup 3 ↥(zpowers α) := isPGroup_zpowers_of_actsAs hα hk3
  have hα1 : α ≠ 1 := ne_one_of_actsAs_of_not_mem_zL hkL hα hkz
  have hnormAF : jSub L (normIn L s.fr.A ⊓ normIn L s.fr.F) =
      normIn (innerAut (L ⧸ center L)) s.fr'.A ⊓
        normIn (innerAut (L ⧸ center L)) s.fr'.F := by
    rw [jSub_inf (L := L) (V := normIn L s.fr.A) (W := normIn L s.fr.F) inf_le_left
        inf_le_left (zL_le_normIn (L := L) hAL),
      jSub_normIn hZ hAL hA2, jSub_normIn hZ hFL hF2, jSub_self L,
      s3_jSub_A s, s3_jSub_F hS hZ s]
  have hαN : α ∈ normIn (innerAut (L ⧸ center L)) s.fr'.A ⊓
      normIn (innerAut (L ⧸ center L)) s.fr'.F := by
    rw [← hnormAF]
    exact (mem_jSub L).mpr ⟨k, hk, hα⟩
  have hSyl : IsSylowIn 3 (normIn (innerAut (L ⧸ center L)) s.fr'.A ⊓
      normIn (innerAut (L ⧸ center L)) s.fr'.F) (zpowers α) :=
    isSylowIn_zpowers_of_secProp_perm3 hSecAF hA_in_normAF hA'2 hαN hα3 hα1
  obtain ⟨hregFZ, hregAF⟩ := hRegAF (zpowers α) hSyl
  refine ⟨?_, ?_⟩
  · have hreg : Sec1.ActsRegularly (zpowers α) (jSub L s.fr.F) (jSub L s.fr.Z) := by
      rw [s3_jSub_F hS hZ s, s3_jSub_Z s]
      exact hregFZ
    exact actsTransitively_of_jSub hZ hkL hα hFL hF2 (s3_Z_le_F s) hreg
  · have hreg : Sec1.ActsRegularly (zpowers α) (jSub L s.fr.A) (jSub L s.fr.F) := by
      rw [s3_jSub_A s, s3_jSub_F hS hZ s]
      exact hregAF
    exact actsTransitively_of_jSub hZ hkL hα hAL hA2 (s3_F_le_A s) hreg

end CFSG.OddStandard.HigherRank.YamadaG23
