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

private lemma sframe_E_le_A {Γ : Type} [Group Γ] (fr : SFrame Γ) : fr.E ≤ fr.A := by
  rw [SFrame.E, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact Subgroup.mul_mem fr.A (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  · exact Subgroup.mul_mem fr.A
      (Subgroup.mul_mem fr.A (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp)))
      (Subgroup.subset_closure (by simp))
  · exact Subgroup.pow_mem fr.A (Subgroup.subset_closure (by simp)) 2

private lemma sframe_Z_le_E {Γ : Type} [Group Γ] (fr : SFrame Γ) : fr.Z ≤ fr.E := by
  rw [SFrame.Z, SFrame.E, Subgroup.zpowers_le]
  exact Subgroup.subset_closure (by simp)

private theorem E_le_S (s : Setting3 G L) : s.fr.E ≤ s.fr.S :=
  (s3_E_le_A s).trans (s3_A_le_S s)

private theorem E_le_L (s : Setting3 G L) : s.fr.E ≤ L :=
  (E_le_S s).trans (s3_S_le_L s)

private theorem A_le_L (s : Setting3 G L) : s.fr.A ≤ L :=
  (s3_A_le_S s).trans (s3_S_le_L s)

private theorem Z_le_L (s : Setting3 G L) : s.fr.Z ≤ L :=
  ((s3_Z_le_A s).trans (s3_A_le_S s)).trans (s3_S_le_L s)

private theorem isPGroup_E (s : Setting3 G L) : IsPGroup 2 ↥s.fr.E :=
  s3_isPGroup_of_le s (E_le_S s)

private theorem isPGroup_A (s : Setting3 G L) : IsPGroup 2 ↥s.fr.A :=
  s3_isPGroup_of_le s (s3_A_le_S s)

private theorem isPGroup_Z (s : Setting3 G L) : IsPGroup 2 ↥s.fr.Z :=
  s3_isPGroup_of_le s ((s3_Z_le_A s).trans (s3_A_le_S s))

private theorem s3_A_le_normIn_E (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) : s.fr.A ≤ normIn L s.fr.E := by
  haveI := isPerfect_of_hrSetting (L := L) hS
  have hAL : s.fr.A ≤ L := A_le_L s
  have hEL : s.fr.E ≤ L := E_le_L s
  have hE2 : IsPGroup 2 ↥s.fr.E := isPGroup_E s
  have hA'E : s.fr'.A ≤ normIn (innerAut (L ⧸ center L)) s.fr'.E := by
    have hEA' : s.fr'.E ≤ s.fr'.A := sframe_E_le_A s.fr'.toSFrame
    have hZE' : s.fr'.Z ≤ s.fr'.E := sframe_Z_le_E s.fr'.toSFrame
    have hAf := A_facts s.fr' s.facts.2.2.2.1
    have hAinner : s.fr'.A ≤ innerAut (L ⧸ center L) := by
      rw [← s3_jSub_A s, ← jSub_self L]
      exact jSub_mono L (A_le_L s)
    intro a ha
    refine ⟨hAinner ha, ?_⟩
    change a ∈ Subgroup.normalizer (s.fr'.E : Set (MulAut (L ⧸ center L)))
    rw [Subgroup.mem_normalizer_iff]
    intro e
    constructor
    · intro he
      have hcomm : ⁅a, e⁆ ∈ s.fr'.Z := hAf.2.1 a ha e (hEA' he)
      have hmem : ⁅a, e⁆ ∈ s.fr'.E := hZE' hcomm
      have heq : a * e * a⁻¹ = ⁅a, e⁆ * e := by rw [commutatorElement_def]; group
      rw [heq]; exact Subgroup.mul_mem s.fr'.E hmem he
    · intro he
      have hmid : a * e * a⁻¹ ∈ s.fr'.E := he
      have hcomm : ⁅a⁻¹, a * e * a⁻¹⁆ ∈ s.fr'.Z :=
        hAf.2.1 a⁻¹ (inv_mem ha) (a * e * a⁻¹) (hEA' hmid)
      have hmem : ⁅a⁻¹, a * e * a⁻¹⁆ ∈ s.fr'.E := hZE' hcomm
      have heq : a⁻¹ * (a * e * a⁻¹) * a = ⁅a⁻¹, a * e * a⁻¹⁆ * (a * e * a⁻¹) := by
        rw [commutatorElement_def]; group
      have heeq : e = a⁻¹ * (a * e * a⁻¹) * a := by group
      rw [heeq, heq]; exact Subgroup.mul_mem s.fr'.E hmem hmid
  refine (jSub_le_iff (L := L) (V := s.fr.A) (W := normIn L s.fr.E) hAL
    (inf_le_left : normIn L s.fr.E ≤ L) (zL_le_normIn hEL)).mp ?_
  rw [s3_jSub_A s, jSub_normIn (L := L) hZ hEL hE2, jSub_self L,
    s3_jSub_E (L := L) hS hZ s]
  exact hA'E

theorem lf18_4a_of (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) : LF18_4a s := by
  haveI := isPerfect_of_hrSetting (L := L) hS
  obtain ⟨-, -, -, -, -, -, -, h18, -, -⟩ := s.facts
  have h4a : centIn (innerAut (L ⧸ center L)) s.fr'.E = s.fr'.E := h18.2.2.2.1.1
  have hEL : s.fr.E ≤ L := E_le_L s
  have hE2 : IsPGroup 2 ↥s.fr.E := isPGroup_E s
  have hV : centIn L s.fr.E ≤ L := inf_le_left
  have hW : zL L ⊔ s.fr.E ≤ L := sup_le zL_le hEL
  have hzV : zL L ≤ centIn L s.fr.E := zL_le_centIn hEL
  have hzW : zL L ≤ zL L ⊔ s.fr.E := le_sup_left
  refine jSub_inj (L := L) (V := centIn L s.fr.E) (W := zL L ⊔ s.fr.E) hV hW hzV hzW ?_
  rw [jSub_centIn (L := L) hZ hEL hE2, jSub_self L, s3_jSub_E (L := L) hS hZ s,
    jSub_sup_zL (L := L) hEL, s3_jSub_E (L := L) hS hZ s]
  exact h4a

theorem lf18_4b_of (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) : LF18_4b s := by
  haveI := isPerfect_of_hrSetting (L := L) hS
  obtain ⟨-, -, -, -, -, -, -, h18, -, -⟩ := s.facts
  have h4b : normIn (innerAut (L ⧸ center L)) s.fr'.E ≤
      normIn (innerAut (L ⧸ center L)) s.fr'.A := h18.2.2.2.1.2.1
  have hEL : s.fr.E ≤ L := E_le_L s
  have hAL : s.fr.A ≤ L := A_le_L s
  have hE2 : IsPGroup 2 ↥s.fr.E := isPGroup_E s
  have hA2 : IsPGroup 2 ↥s.fr.A := isPGroup_A s
  refine (jSub_le_iff (L := L) (V := normIn L s.fr.E) (W := normIn L s.fr.A)
    (inf_le_left : normIn L s.fr.E ≤ L) (inf_le_left : normIn L s.fr.A ≤ L)
    (zL_le_normIn hAL)).mp ?_
  rw [jSub_normIn (L := L) hZ hEL hE2, jSub_normIn (L := L) hZ hAL hA2, jSub_self L,
    s3_jSub_E (L := L) hS hZ s, s3_jSub_A s]
  exact h4b

theorem lf18_4c_of (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) : LF18_4c s := by
  haveI := isPerfect_of_hrSetting (L := L) hS
  obtain ⟨-, -, -, -, -, -, -, h18, -, -⟩ := s.facts
  have h4c : SecProp (normIn (innerAut (L ⧸ center L)) s.fr'.E) s.fr'.A
      (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))) := h18.2.2.2.1.2.2.1
  have hEL : s.fr.E ≤ L := E_le_L s
  have hAL : s.fr.A ≤ L := A_le_L s
  have hE2 : IsPGroup 2 ↥s.fr.E := isPGroup_E s
  have hA_le : s.fr.A ≤ normIn L s.fr.E := s3_A_le_normIn_E hS hZ s
  have hV : normIn L s.fr.E ≤ normalizer (L : Set G) :=
    (inf_le_left : normIn L s.fr.E ≤ L).trans Subgroup.le_normalizer
  have hNV : zL L ⊔ s.fr.A ≤ normIn L s.fr.E :=
    sup_le (zL_le_normIn hEL) hA_le
  have hK : ∀ x ∈ normIn L s.fr.E, x ∈ centralizer (L : Set G) → x ∈ zL L ⊔ s.fr.A := by
    intro x hx hxc
    refine Subgroup.mem_sup_left ((mem_zL_iff (L := L)).mpr ⟨?_, hxc⟩)
    exact (inf_le_left : normIn L s.fr.E ≤ L) hx
  refine (secProp_jSub (L := L) hV hNV hK (fun Y _ => Nonempty (Y ≃* Equiv.Perm (Fin 3)))
    (fun Y Y' _ _ e => ⟨fun ⟨f⟩ => ⟨e.symm.trans f⟩, fun ⟨f⟩ => ⟨e.trans f⟩⟩)).mpr ?_
  rw [jSub_normIn (L := L) hZ hEL hE2, jSub_self L, s3_jSub_E (L := L) hS hZ s,
    jSub_sup_zL (L := L) hAL, s3_jSub_A s]
  exact h4c

theorem lf18_4d_of (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) : LF18_4d s := by
  haveI := isPerfect_of_hrSetting (L := L) hS
  obtain ⟨-, -, -, -, -, -, -, h18, -, -⟩ := s.facts
  have h4d : ∀ u ∈ s.fr'.E, u ∉ s.fr'.Z → ∀ v ∈ s.fr'.E, v ∉ s.fr'.Z →
      ∃ k ∈ normIn (innerAut (L ⧸ center L)) s.fr'.E, k * u * k⁻¹ = v :=
    h18.2.2.2.1.2.2.2.1
  have hEL : s.fr.E ≤ L := E_le_L s
  have hE2 : IsPGroup 2 ↥s.fr.E := isPGroup_E s
  intro u huE huZ v hvE hvZ
  have huS : u ∈ s.fr.S := E_le_S s huE
  have hvS : v ∈ s.fr.S := E_le_S s hvE
  have huL : u ∈ L := s3_S_le_L s huS
  have hvL : v ∈ L := s3_S_le_L s hvS
  let α : MulAut (L ⧸ center L) :=
    MulAut.conj (QuotientGroup.mk (⟨u, huL⟩ : ↥L) : L ⧸ center L)
  let β : MulAut (L ⧸ center L) :=
    MulAut.conj (QuotientGroup.mk (⟨v, hvL⟩ : ↥L) : L ⧸ center L)
  have hα : ActsAs L u α := actsAs_of_mem L huL
  have hβ : ActsAs L v β := actsAs_of_mem L hvL
  have hαE : α ∈ s.fr'.E := by
    rw [← s3_jSub_E (L := L) hS hZ s]
    exact (mem_jSub L).mpr ⟨u, huE, hα⟩
  have hβE : β ∈ s.fr'.E := by
    rw [← s3_jSub_E (L := L) hS hZ s]
    exact (mem_jSub L).mpr ⟨v, hvE, hβ⟩
  have hαZ : α ∉ s.fr'.Z := by
    rw [← s3_jSub_Z s]
    intro hmem
    exact huZ ((mem_jSub_iff_mem (L := L) hZ (Z_le_L s) (isPGroup_Z s) huL
      (s3_isPGroup_zpowers s huS) hα).mp hmem)
  have hβZ : β ∉ s.fr'.Z := by
    rw [← s3_jSub_Z s]
    intro hmem
    exact hvZ ((mem_jSub_iff_mem (L := L) hZ (Z_le_L s) (isPGroup_Z s) hvL
      (s3_isPGroup_zpowers s hvS) hβ).mp hmem)
  obtain ⟨κ, hκN, hκeq⟩ := h4d α hαE hαZ β hβE hβZ
  have hκ : κ ∈ jSub L (normIn L s.fr.E) := by
    rw [jSub_normIn (L := L) hZ hEL hE2, jSub_self L, s3_jSub_E (L := L) hS hZ s]
    exact hκN
  exact exists_conj_of_jSub (L := L) hZ hEL hE2 huE hvE hα hβ hκ hκeq

end CFSG.OddStandard.HigherRank.YamadaG23
