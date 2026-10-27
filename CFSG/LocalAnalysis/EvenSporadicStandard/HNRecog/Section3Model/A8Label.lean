module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.A8Abstract
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.A8LabelCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.RowModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.SubModelClass
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.InvClasses
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeGlue
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableIP
public import Certificates.Certificate441705
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.DerivedOf
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open Subgroup CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.SmallOddCore.Native

open scoped commutatorElement

local notation "𝒞" => CFSG.Sporadic.SmallOddCore.conjClass

section Cert

set_option linter.unusedSectionVars false


private theorem a8_parts :
    gensOK = true ∧ wordOK a8WX = true ∧ wordOK a8WY = true ∧ wordOK a8W0 = true ∧
      commutatorEqOK (tabW a8WX) (tabW a8WY) (tabW a8W0) = true ∧
      conjEqOK a8WZ (tabW wordZ) (tabW a8W0) = true ∧
      orbRowOK a8Cap classb.centGens a8W0 80640 a8Row = true := by
  have h : a8LabelOK = true := Certificates.certificate441705
  simp only [a8LabelOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hg, hx⟩, hy⟩, h0⟩, hcomm⟩, hconj⟩, hrow⟩ := h
  exact ⟨hg, hx, hy, h0, hcomm, hconj, hrow⟩

private theorem a8_classb_spec (hP : Nat.card ↥P1408 = 177408000) :
    closure (elemW '' {w | w ∈ classb.centGens}) =
        P1408 ⊓ centralizer ({elemW wordB} : Set (Equiv.Perm (Fin 1408))) ∧
      Nat.card ↥(P1408 ⊓ centralizer ({elemW wordB} : Set (Equiv.Perm (Fin 1408)))) = 80640 := by
  obtain ⟨-, -, hb, -⟩ := invClasses_classSpec hP
  exact ⟨hb.cent_eq, hb.cent_card⟩

private theorem wordP_specWord_mem_Gx (hP : Nat.card ↥P1408 = 177408000)
    (s : List (ℕ × ℕ)) : wordP (specWord classb.centGens s) ∈ Gx pB := by
  have h : elemW (specWord classb.centGens s) ∈
      P1408 ⊓ centralizer ({elemW wordB} : Set (Equiv.Perm (Fin 1408))) := by
    rw [← (a8_classb_spec hP).1]
    exact elemW_specWord_mem classb.centGens s
  have h2 := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp h).2
  rw [mem_Gx]
  exact Subtype.ext h2.symm

private theorem wordP_a8W0_mem_derivedOf (hP : Nat.card ↥P1408 = 177408000) :
    wordP a8W0 ∈ derivedOf (Gx pB) := by
  obtain ⟨hg, hx, hy, h0, hcomm, -, -⟩ := a8_parts
  have hc := commutatorEqOK_spec (rep_elemW_of_gensOK hg hx) (rep_elemW_of_gensOK hg hy)
    (rep_elemW_of_gensOK hg h0) hcomm
  have hxG : wordP a8WX ∈ Gx pB := wordP_specWord_mem_Gx hP a8SX
  have hyG : wordP a8WY ∈ Gx pB := wordP_specWord_mem_Gx hP a8SY
  have hu : wordP a8W0 = wordP a8WX * wordP a8WY * (wordP a8WX)⁻¹ * (wordP a8WY)⁻¹ :=
    Subtype.ext hc.symm
  have hmem : wordP a8W0 ∈ Gx pB := by
    rw [hu]
    exact mul_mem (mul_mem (mul_mem hxG hyG) (inv_mem hxG)) (inv_mem hyG)
  refine mem_derivedOf_iff.mpr ⟨hmem, ?_⟩
  have hcomm' : (⟨wordP a8W0, hmem⟩ : ↥(Gx pB)) =
      ⁅(⟨wordP a8WX, hxG⟩ : ↥(Gx pB)), (⟨wordP a8WY, hyG⟩ : ↥(Gx pB))⁆ :=
    Subtype.ext (by rw [commutatorElement_def]; exact hu)
  rw [hcomm', _root_.commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

private theorem ncard_conjClass_a8W0_le (hP : Nat.card ↥P1408 = 177408000) :
    (𝒞 (P1408 ⊓ centralizer ({elemW wordB} : Set (Equiv.Perm (Fin 1408)))) (elemW a8W0)).ncard ≤
      105 := by
  obtain ⟨-, -, -, -, -, -, hrow⟩ := a8_parts
  have hK := a8_classb_spec hP
  have h := (orbRowOK_spec_closure hrow (by rw [hK.1]; exact hK.2)).2.1
  rw [hK.1] at h
  have hrep : a8Row.repElem a8W0 = elemW a8W0 := by
    simp [OrbRow.repElem, a8Row, elemW_nil]
  rw [hrep] at h
  exact h.le

theorem model_A8Label (hP : Nat.card ↥P1408 = 177408000) (u : ↥(derivedOf (Gx pB)))
    (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (hc : Nat.card ↥(Subgroup.centralizer ({u} : Set ↥(derivedOf (Gx pB)))) = 192) :
    IsConj pZ (u : ↥P1408) := by
  obtain ⟨φ⟩ := nonempty_mulEquiv_A8_derivedOf (cent_b_P hP)
  obtain ⟨hgens, -, -, -, -, hconj, -⟩ := a8_parts
  let u₀ : ↥(derivedOf (Gx pB)) := ⟨wordP a8W0, wordP_a8W0_mem_derivedOf hP⟩
  have hZ0 : IsConj pZ (u₀ : ↥P1408) :=
    isConj_of_conjEqOK hgens rep_elemZ (rep_elemW_of_gensOK hgens (a8_parts.2.2.2.1)) hconj
  have hpZ : orderOf pZ = 2 := (Subgroup.orderOf_coe pZ).symm.trans twoHSBasic_spec.2.1
  have hpZ2 : pZ * pZ = 1 := mul_self_eq_one_of_orderOf_eq_two hpZ
  have hpZ1 : pZ ≠ 1 := ne_one_of_orderOf_eq_two hpZ
  obtain ⟨c, hcz⟩ := isConj_iff.mp hZ0
  have hu₀2 : u₀ * u₀ = 1 := by
    refine Subtype.ext ?_
    change (u₀ : ↥P1408) * (u₀ : ↥P1408) = 1
    rw [← hcz]
    calc c * pZ * c⁻¹ * (c * pZ * c⁻¹) = c * (pZ * pZ) * c⁻¹ := by group
      _ = 1 := by rw [hpZ2]; group
  have hu₀1 : u₀ ≠ 1 := by
    intro h1
    apply hpZ1
    have h2 : (u₀ : ↥P1408) = 1 := congrArg Subtype.val h1
    rw [← hcz] at h2
    calc pZ = c⁻¹ * (c * pZ * c⁻¹) * c := by group
      _ = 1 := by rw [h2]; group
  have hmem : ∀ g : ↥(derivedOf (Gx pB)),
      ((g : ↥P1408) : Equiv.Perm (Fin 1408)) ∈
        P1408 ⊓ centralizer ({elemW wordB} : Set (Equiv.Perm (Fin 1408))) := by
    intro g
    refine Subgroup.mem_inf.mpr ⟨(g : ↥P1408).2, ?_⟩
    have h1 : (g : ↥P1408) ∈ Gx pB := derivedOf_le (Gx pB) g.2
    rw [mem_Gx] at h1
    exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val h1).symm
  have hmain := isConj_of_card_centralizer_192 φ
    (F := fun g : ↥(derivedOf (Gx pB)) => ((g : ↥P1408) : Equiv.Perm (Fin 1408)))
    (Subtype.val_injective.comp Subtype.val_injective)
    (T := 𝒞 (P1408 ⊓ centralizer ({elemW wordB} : Set (Equiv.Perm (Fin 1408)))) (elemW a8W0))
    (Set.toFinite _) (ncard_conjClass_a8W0_le hP) hu₀2 hu₀1
    (fun g => ⟨(g : ↥P1408), hmem g, rfl⟩) hu2 hu1 hc
  obtain ⟨d, hd⟩ := isConj_iff.mp hmain
  refine hZ0.trans (isConj_iff.mpr ⟨(d : ↥P1408), ?_⟩)
  exact congrArg Subtype.val hd

end Cert

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
