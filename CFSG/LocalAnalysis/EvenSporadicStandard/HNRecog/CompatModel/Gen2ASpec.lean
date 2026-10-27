module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.CheckSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Elems
public import Certificates.Certificate441873

public section

namespace CFSG.EvenSporadicStandard.HNRecog.CompatModel

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.EvenSporadicStandard.HNRecog

@[expose] noncomputable def modelC1 : ↥P1408 := ⟨elemW gen2aC1, elemW_mem _⟩

@[expose] noncomputable def modelC2 : ↥P1408 := ⟨elemW gen2aC2, elemW_mem _⟩

@[expose] noncomputable def modelG : ↥P1408 := ⟨elemW gen2aG, elemW_mem _⟩

section Cert


private theorem gen2aOK_parts : gen2aBasicOK = true ∧ gen2aGenOK = true := by
  have h : gen2aOK = true := Certificates.certificate441873
  simpa only [gen2aOK, Bool.and_eq_true] using h

theorem gen2a_basic :
    orderOf modelC1 = 2 ∧ orderOf modelC2 = 2 ∧ modelC1 * pB = pB * modelC1 ∧
      modelC2 * pB = pB * modelC2 ∧ modelC1 ≠ pA ∧ modelC1 ≠ pB ∧ modelC1 ≠ pA * pB ∧
      modelC2 ≠ pA ∧ modelC2 ≠ pB ∧ modelC2 ≠ pA * pB ∧ modelG * modelC1 = modelC1 * modelG ∧
      modelG * modelC2 = modelC2 * modelG ∧ modelG * pB ≠ pB * modelG := by
  have h := gen2aOK_parts.1
  simp only [gen2aBasicOK, Bool.and_eq_true, Bool.not_eq_true', and_assoc] at h
  obtain ⟨hgens, hwA, hwB, hw1, hw2, hwg, hi1, hi2, hb1, hb2, hna1, hnb1, hnab1, hna2, hnb2,
    hnab2, hg1, hg2, hgb⟩ := h
  have rA : Rep 1408 (tabW wordA) elemA := rep_elemW_of_gensOK hgens hwA
  have rB : Rep 1408 (tabW wordB) elemB := rep_elemW_of_gensOK hgens hwB
  have r1 : Rep 1408 (tabW gen2aC1) (elemW gen2aC1) := rep_elemW_of_gensOK hgens hw1
  have r2 : Rep 1408 (tabW gen2aC2) (elemW gen2aC2) := rep_elemW_of_gensOK hgens hw2
  have rg : Rep 1408 (tabW gen2aG) (elemW gen2aG) := rep_elemW_of_gensOK hgens hwg
  have rAB : Rep 1408 (compT 1408 (tabW wordA) (tabW wordB)) (elemA * elemB) := Rep.compT rA rB
  have ne : ∀ {T U : Table} {s t : Equiv.Perm (Fin 1408)}, Rep 1408 T s → Rep 1408 U t →
      tblEq 1408 T U = false → s ≠ t := fun hT hU hf e => by
    rw [(tblEq_iff_eq hT hU).2 e] at hf
    exact Bool.noConfusion hf
  refine ⟨(Subgroup.orderOf_coe modelC1).symm.trans
      (orderOf_eq_two_of_involOK (by norm_num) r1 hi1),
    (Subgroup.orderOf_coe modelC2).symm.trans (orderOf_eq_two_of_involOK (by norm_num) r2 hi2),
    Subtype.ext ((commTT_iff r1 rB).1 hb1), Subtype.ext ((commTT_iff r2 rB).1 hb2),
    fun e => ne r1 rA hna1 (congrArg Subtype.val e),
    fun e => ne r1 rB hnb1 (congrArg Subtype.val e),
    fun e => ne r1 rAB hnab1 (congrArg Subtype.val e),
    fun e => ne r2 rA hna2 (congrArg Subtype.val e),
    fun e => ne r2 rB hnb2 (congrArg Subtype.val e),
    fun e => ne r2 rAB hnab2 (congrArg Subtype.val e),
    Subtype.ext ((commTT_iff rg r1).1 hg1), Subtype.ext ((commTT_iff rg r2).1 hg2),
    fun e => ?_⟩
  rw [(commTT_iff rg rB).2 (congrArg Subtype.val e)] at hgb
  exact Bool.noConfusion hgb

theorem gen2a_closure :
    closure ((centralizer ({modelC1} : Set ↥P1408) : Set ↥P1408) ∪
      (centralizer ({modelC2} : Set ↥P1408) : Set ↥P1408)) = ⊤ := by
  have h := gen2aOK_parts.2
  simp only [gen2aGenOK, Bool.and_eq_true, and_assoc] at h
  obtain ⟨hgens, hw1, hw2, hwu, hcomm, hinv, hperm, hprod⟩ := h
  have r1 : Rep 1408 (tabW gen2aC1) (elemW gen2aC1) := rep_elemW_of_gensOK hgens hw1
  have r2 : Rep 1408 (tabW gen2aC2) (elemW gen2aC2) := rep_elemW_of_gensOK hgens hw2
  set K : Subgroup ↥P1408 := closure ((centralizer ({modelC1} : Set ↥P1408) : Set ↥P1408) ∪
    (centralizer ({modelC2} : Set ↥P1408) : Set ↥P1408)) with hK
  have hrU : ∀ w ∈ gen2aU, Rep 1408 (tabW w) (elemW w) := fun w hw =>
    rep_elemW_of_gensOK hgens (List.all_eq_true.1 hwu w hw)
  have hU : ∀ w ∈ gen2aU, elemW w ∈ K.map P1408.subtype := by
    intro w hw
    have hc := List.all_eq_true.1 hcomm (tabW w) (List.mem_map.2 ⟨w, hw, rfl⟩)
    rw [Bool.or_eq_true] at hc
    refine Subgroup.mem_map.2 ⟨⟨elemW w, elemW_mem w⟩, ?_, rfl⟩
    rcases hc with hc | hc
    · refine Subgroup.subset_closure (Or.inl ?_)
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext ((commTT_iff (hrU w hw) r1).1 hc)
    · refine Subgroup.subset_closure (Or.inr ?_)
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext ((commTT_iff (hrU w hw) r2).1 hc)
  have hgT : gen2aTabs.length = 8 := by decide
  have hperm' : ∀ x ∈ gen2aTabs, permOK 1408 x = true := List.all_eq_true.1 hperm
  have hle : genOf 1408 gen2aTabs ≤ K.map P1408.subtype := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ gen2aTabs := by simpa using hx
    have hxp := hperm' x hx'
    rcases List.mem_append.1 hx' with hx1 | hx2
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx1
      rw [rep_unique (rep_tp hxp) (hrU w hw)]
      exact hU w hw
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hx2
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hu
      have hri : Rep 1408 (invT 1408 (tabW w)) (elemW w)⁻¹ :=
        Rep.inv_of_invOK (hrU w hw) (List.all_eq_true.1 hinv (tabW w) (List.mem_map.2 ⟨w, hw, rfl⟩))
      rw [rep_unique (rep_tp hxp) hri]
      exact (K.map P1408.subtype).inv_mem (hU w hw)
  have hgen : ∀ j : Fin 7, h1408GenPerm j ∈ K.map P1408.subtype := by
    intro j
    obtain ⟨p, hp, hpj⟩ : ∃ p ∈ gen2aProd, p.1 = j.val := by revert j; decide
    have hpp := List.all_eq_true.1 hprod p hp
    rw [Bool.and_eq_true, List.all_eq_true] at hpp
    obtain ⟨hl, he⟩ := hpp
    have hlet : ∀ l ∈ p.2, 1 ≤ l ∧ l ≤ gen2aTabs.length := fun l hl' => by
      rw [hgT]
      exact of_decide_eq_true (hl l hl')
    obtain ⟨x, hx, hrx⟩ := rep_wordTbl (n := 1408) (by norm_num) hperm' p.2 hlet
    rw [hpj] at he
    rw [← (tblEq_iff_eq hrx (rep_h1408Gen j)).1 he]
    exact hle hx
  have hP : P1408 ≤ K.map P1408.subtype := by
    show closure (Set.range h1408GenPerm) ≤ _
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, rfl⟩
    exact hgen j
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (hP x.2)
  rwa [show y = x from Subtype.ext hyx] at hy

theorem gen2a_model :
    ∃ c₁ c₂ g : ↥P1408, orderOf c₁ = 2 ∧ orderOf c₂ = 2 ∧ c₁ * pB = pB * c₁ ∧ c₂ * pB = pB * c₂ ∧
      c₁ ≠ pA ∧ c₁ ≠ pB ∧ c₁ ≠ pA * pB ∧ c₂ ≠ pA ∧ c₂ ≠ pB ∧ c₂ ≠ pA * pB ∧
      g * c₁ = c₁ * g ∧ g * c₂ = c₂ * g ∧ g * pB ≠ pB * g ∧
      closure ((centralizer ({c₁} : Set ↥P1408) : Set ↥P1408) ∪
        (centralizer ({c₂} : Set ↥P1408) : Set ↥P1408)) = ⊤ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := gen2a_basic
  exact ⟨modelC1, modelC2, modelG, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    gen2a_closure⟩

end Cert

end CFSG.EvenSporadicStandard.HNRecog.CompatModel
