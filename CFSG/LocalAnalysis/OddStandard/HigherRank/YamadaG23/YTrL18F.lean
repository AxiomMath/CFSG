module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrL18Def
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrJSec
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrJAct
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrImg
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YAFacts
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YAutFrame

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private def IsGL3 (Y : Type) [Group Y] : Prop :=
  Nonempty (Y ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))

private def IsPerm3 (Y : Type) [Group Y] : Prop :=
  Nonempty (Y ≃* Equiv.Perm (Fin 3))

private lemma sframe_A_le_S {Γ : Type} [Group Γ] (fr : SFrame Γ) : fr.A ≤ fr.S := by
  rw [SFrame.A, SFrame.S, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

private lemma sframe_F_le_A {Γ : Type} [Group Γ] (fr : SFrame Γ) : fr.F ≤ fr.A := by
  rw [SFrame.F, SFrame.A, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact Subgroup.mul_mem fr.A (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  · exact Subgroup.mul_mem fr.A (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  · exact Subgroup.pow_mem fr.A (Subgroup.subset_closure (by simp)) 2

private lemma sframe_Z_le_F {Γ : Type} [Group Γ] (fr : SFrame Γ) : fr.Z ≤ fr.F := by
  rw [SFrame.Z, SFrame.F, Subgroup.zpowers_le]
  exact Subgroup.subset_closure (by simp)

private theorem s3_A_le_normIn_F (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) : s.fr.A ≤ normIn L s.fr.F := by
  haveI := isPerfect_of_hrSetting (L := L) hS
  have hAL : s.fr.A ≤ L := (s3_A_le_S s).trans (s3_S_le_L s)
  have hAS : s.fr.A ≤ s.fr.S := s3_A_le_S s
  have hFS : s.fr.F ≤ s.fr.S := (s3_F_le_A s).trans hAS
  have hFL : s.fr.F ≤ L := hFS.trans (s3_S_le_L s)
  have hF2 : IsPGroup 2 ↥s.fr.F := s3_isPGroup_of_le s hFS
  have hA'F : s.fr'.A ≤ normIn (innerAut (L ⧸ center L)) s.fr'.F := by
    have hFS' : s.fr'.F ≤ s.fr'.A := sframe_F_le_A s.fr'.toSFrame
    have hZF' : s.fr'.Z ≤ s.fr'.F := sframe_Z_le_F s.fr'.toSFrame
    have hAf := A_facts s.fr' s.facts.2.2.2.1
    intro a ha
    refine ⟨frame_S_le_inner s.fr' s.facts.1 (sframe_A_le_S s.fr'.toSFrame ha), ?_⟩
    change a ∈ Subgroup.normalizer (s.fr'.F : Set (MulAut (L ⧸ center L)))
    rw [Subgroup.mem_normalizer_iff]
    intro f
    constructor
    · intro hf
      have hcomm : ⁅a, f⁆ ∈ s.fr'.Z := hAf.2.1 a ha f (hFS' hf)
      have hmem : ⁅a, f⁆ ∈ s.fr'.F := hZF' hcomm
      have heq : a * f * a⁻¹ = ⁅a, f⁆ * f := by
        rw [commutatorElement_def]; group
      rw [heq]; exact Subgroup.mul_mem s.fr'.F hmem hf
    · intro hf
      have hmid : a * f * a⁻¹ ∈ s.fr'.F := hf
      have hcomm : ⁅a⁻¹, a * f * a⁻¹⁆ ∈ s.fr'.Z :=
        hAf.2.1 a⁻¹ (inv_mem ha) (a * f * a⁻¹) (hFS' hmid)
      have hmem : ⁅a⁻¹, a * f * a⁻¹⁆ ∈ s.fr'.F := hZF' hcomm
      have heq : a⁻¹ * (a * f * a⁻¹) * a =
          ⁅a⁻¹, a * f * a⁻¹⁆ * (a * f * a⁻¹) := by
        rw [commutatorElement_def]; group
      have hfeq : f = a⁻¹ * (a * f * a⁻¹) * a := by group
      rw [hfeq, heq]; exact Subgroup.mul_mem s.fr'.F hmem hmid
  have hzW : zL L ≤ normIn L s.fr.F := zL_le_normIn hFL
  refine (jSub_le_iff (L := L) (V := s.fr.A) (W := normIn L s.fr.F) hAL
    (inf_le_left : normIn L s.fr.F ≤ L) hzW).mp ?_
  rw [s3_jSub_A s, jSub_normIn (L := L) hZ hFL hF2, jSub_self L,
    s3_jSub_F (L := L) hS hZ s]
  exact hA'F

theorem lf18_5a_of (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) : LF18_5a s := by
  haveI := isPerfect_of_hrSetting (L := L) hS
  have h5 := s.facts.2.2.2.2.2.2.2.1.2.2.2.2
  obtain ⟨h5a, -, -, -, -⟩ := h5
  have hFS : s.fr.F ≤ s.fr.S := (s3_F_le_A s).trans (s3_A_le_S s)
  have hFL : s.fr.F ≤ L := hFS.trans (s3_S_le_L s)
  have hF2 : IsPGroup 2 ↥s.fr.F := s3_isPGroup_of_le s hFS
  have hV : centIn L s.fr.F ≤ L := by
    change L ⊓ centralizer (s.fr.F : Set G) ≤ L
    exact inf_le_left
  have hW : zL L ⊔ s.fr.F ≤ L := sup_le zL_le hFL
  have hzV : zL L ≤ centIn L s.fr.F := zL_le_centIn hFL
  have hzW : zL L ≤ zL L ⊔ s.fr.F := le_sup_left
  refine jSub_inj (L := L) (V := centIn L s.fr.F) (W := zL L ⊔ s.fr.F) hV hW hzV hzW ?_
  have hjC : jSub L (centIn L s.fr.F) = centIn (innerAut (L ⧸ center L)) s.fr'.F := by
    rw [jSub_centIn (L := L) hZ hFL hF2, jSub_self L, s3_jSub_F (L := L) hS hZ s]
  have hjW : jSub L (zL L ⊔ s.fr.F) = s.fr'.F := by
    rw [jSub_sup_zL (L := L) hFL, s3_jSub_F (L := L) hS hZ s]
  rw [hjC, hjW]
  exact h5a

theorem lf18_5b_of (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) : LF18_5b s := by
  haveI := isPerfect_of_hrSetting (L := L) hS
  have h5 := s.facts.2.2.2.2.2.2.2.1.2.2.2.2
  obtain ⟨-, h5b, -, -, -⟩ := h5
  have hFS : s.fr.F ≤ s.fr.S := (s3_F_le_A s).trans (s3_A_le_S s)
  have hFL : s.fr.F ≤ L := hFS.trans (s3_S_le_L s)
  have hF2 : IsPGroup 2 ↥s.fr.F := s3_isPGroup_of_le s hFS
  have hV : normIn L s.fr.F ≤ normalizer (L : Set G) :=
    (inf_le_left : normIn L s.fr.F ≤ L).trans Subgroup.le_normalizer
  have hNV : zL L ⊔ s.fr.F ≤ normIn L s.fr.F :=
    sup_le (zL_le_normIn hFL) (le_inf hFL Subgroup.le_normalizer)
  have hK : ∀ x ∈ normIn L s.fr.F, x ∈ centralizer (L : Set G) → x ∈ zL L ⊔ s.fr.F := by
    intro x hx hxc
    have hxL : x ∈ L := (inf_le_left : normIn L s.fr.F ≤ L) hx
    exact Subgroup.mem_sup_left ((mem_zL_iff (L := L)).mpr ⟨hxL, hxc⟩)
  refine (secProp_jSub (L := L) (V := normIn L s.fr.F) (N := zL L ⊔ s.fr.F) hV hNV hK
    IsGL3 (fun Y Y' _ _ e => ⟨fun ⟨f⟩ => ⟨e.symm.trans f⟩,
      fun ⟨f⟩ => ⟨e.trans f⟩⟩)).mpr ?_
  have hjN : jSub L (normIn L s.fr.F) = normIn (innerAut (L ⧸ center L)) s.fr'.F := by
    rw [jSub_normIn (L := L) hZ hFL hF2, jSub_self L, s3_jSub_F (L := L) hS hZ s]
  have hjW : jSub L (zL L ⊔ s.fr.F) = s.fr'.F := by
    rw [jSub_sup_zL (L := L) hFL, s3_jSub_F (L := L) hS hZ s]
  rw [hjN, hjW]
  exact h5b

theorem lf18_5c_of (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) : LF18_5c s := by
  haveI := isPerfect_of_hrSetting (L := L) hS
  have h5 := s.facts.2.2.2.2.2.2.2.1.2.2.2.2
  obtain ⟨-, -, h5c, -, -⟩ := h5
  have hFS : s.fr.F ≤ s.fr.S := (s3_F_le_A s).trans (s3_A_le_S s)
  have hFL : s.fr.F ≤ L := hFS.trans (s3_S_le_L s)
  have hF2 : IsPGroup 2 ↥s.fr.F := s3_isPGroup_of_le s hFS
  intro hsplit
  have hFN : s.fr.F ≤ normIn L s.fr.F := le_inf hFL Subgroup.le_normalizer
  have h : SplitsOver (jSub L (normIn L s.fr.F)) (jSub L s.fr.F) :=
    splitsOver_jSub (L := L) hZ inf_le_left hFN hF2 hsplit
  have hjN : jSub L (normIn L s.fr.F) = normIn (innerAut (L ⧸ center L)) s.fr'.F := by
    rw [jSub_normIn (L := L) hZ hFL hF2, jSub_self L, s3_jSub_F (L := L) hS hZ s]
  have hjF : jSub L s.fr.F = s.fr'.F := s3_jSub_F (L := L) hS hZ s
  rw [hjN, hjF] at h
  exact h5c h

theorem lf18_5e_of (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) : LF18_5e s := by
  haveI := isPerfect_of_hrSetting (L := L) hS
  have h5 := s.facts.2.2.2.2.2.2.2.1.2.2.2.2
  obtain ⟨-, -, -, h5d, -⟩ := h5
  have hAS : s.fr.A ≤ s.fr.S := s3_A_le_S s
  have hAL : s.fr.A ≤ L := hAS.trans (s3_S_le_L s)
  have hFS : s.fr.F ≤ s.fr.S := (s3_F_le_A s).trans hAS
  have hFL : s.fr.F ≤ L := hFS.trans (s3_S_le_L s)
  have hA2 : IsPGroup 2 ↥s.fr.A := s3_isPGroup_of_le s hAS
  have hF2 : IsPGroup 2 ↥s.fr.F := s3_isPGroup_of_le s hFS
  have hAF : s.fr.A ≤ normIn L s.fr.F := s3_A_le_normIn_F hS hZ s
  have hV : normIn L s.fr.A ⊓ normIn L s.fr.F ≤ normalizer (L : Set G) :=
    ((inf_le_left : normIn L s.fr.A ⊓ normIn L s.fr.F ≤ normIn L s.fr.A).trans
      (inf_le_left : normIn L s.fr.A ≤ L)).trans Subgroup.le_normalizer
  have hNV : zL L ⊔ s.fr.A ≤ normIn L s.fr.A ⊓ normIn L s.fr.F :=
    le_inf (sup_le (zL_le_normIn hAL) (le_inf hAL Subgroup.le_normalizer))
      (sup_le (zL_le_normIn hFL) hAF)
  have hK : ∀ x ∈ normIn L s.fr.A ⊓ normIn L s.fr.F, x ∈ centralizer (L : Set G) →
      x ∈ zL L ⊔ s.fr.A := by
    intro x hx hxc
    have hxL : x ∈ L :=
      ((inf_le_left : normIn L s.fr.A ⊓ normIn L s.fr.F ≤ normIn L s.fr.A).trans
        (inf_le_left : normIn L s.fr.A ≤ L)) hx
    exact Subgroup.mem_sup_left ((mem_zL_iff (L := L)).mpr ⟨hxL, hxc⟩)
  refine (secProp_jSub (L := L) (V := normIn L s.fr.A ⊓ normIn L s.fr.F)
    (N := zL L ⊔ s.fr.A) hV hNV hK IsPerm3
    (fun Y Y' _ _ e => ⟨fun ⟨f⟩ => ⟨e.symm.trans f⟩,
      fun ⟨f⟩ => ⟨e.trans f⟩⟩)).mpr ?_
  have hjA : jSub L (normIn L s.fr.A) = normIn (innerAut (L ⧸ center L)) s.fr'.A := by
    rw [jSub_normIn (L := L) hZ hAL hA2, jSub_self L, s3_jSub_A s]
  have hjF : jSub L (normIn L s.fr.F) = normIn (innerAut (L ⧸ center L)) s.fr'.F := by
    rw [jSub_normIn (L := L) hZ hFL hF2, jSub_self L, s3_jSub_F (L := L) hS hZ s]
  have hjN : jSub L (zL L ⊔ s.fr.A) = s.fr'.A := by
    rw [jSub_sup_zL (L := L) hAL, s3_jSub_A s]
  rw [jSub_inf (L := L) (V := normIn L s.fr.A) (W := normIn L s.fr.F) inf_le_left
      (inf_le_left : normIn L s.fr.F ≤ L) (zL_le_normIn hAL), hjA, hjF, hjN]
  exact h5d

end CFSG.OddStandard.HigherRank.YamadaG23
