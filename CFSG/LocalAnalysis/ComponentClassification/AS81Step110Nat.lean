module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

section NatMod

variable {H : Type} [Group H] {Q : Subgroup H} {h : H}

theorem commute_of_mem_rightConjugate (hQ : IsElemAbelian 2 Q) {a b : H}
    (ha : a ∈ rightConjugate Q h) (hb : b ∈ rightConjugate Q h) : a * b = b * a := by
  rw [mem_rightConjugate_iff] at ha hb
  have := congrArg Subtype.val (hQ.1.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
  simp only [Subgroup.coe_mul] at this
  have h2 : h * (a * b) * h⁻¹ = h * (b * a) * h⁻¹ := by
    calc h * (a * b) * h⁻¹ = (h * a * h⁻¹) * (h * b * h⁻¹) := by group
      _ = (h * b * h⁻¹) * (h * a * h⁻¹) := this
      _ = h * (b * a) * h⁻¹ := by group
  simpa using h2

theorem mul_self_eq_one_of_elem (hQ : IsElemAbelian 2 Q) {a : H} (ha : a ∈ Q) : a * a = 1 := by
  rw [← sq]
  exact hQ.2 a ha

theorem mul_self_eq_one_of_mem_rightConjugate (hQ : IsElemAbelian 2 Q) {a : H}
    (ha : a ∈ rightConjugate Q h) : a * a = 1 := by
  rw [mem_rightConjugate_iff] at ha
  have h1 := mul_self_eq_one_of_elem hQ ha
  have h2 : h * (a * a) * h⁻¹ = 1 := by
    calc h * (a * a) * h⁻¹ = (h * a * h⁻¹) * (h * a * h⁻¹) := by group
      _ = 1 := h1
  calc a * a = h⁻¹ * (h * (a * a) * h⁻¹) * h := by group
    _ = 1 := by rw [h2]; group

end NatMod

end CFSG.ComponentClassification.AS81
