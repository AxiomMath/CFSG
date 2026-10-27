module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropTenAbelian

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Subgroup

namespace JankoTen.Hyp

variable {G : Type} [Group G] [Finite G] {z : G} {fr : JankoFrame G z}

theorem M_pow_three
    (h : Hyp fr) {a : G} (ha : a ∈ fr.M) : a ^ 3 = 1 := by
  have hle : fr.M ≤ powSubgroup fr.M (M_comm h) 3 :=
    calc fr.M = fr.P₁ ⊔ fr.At ⊔ fr.Atz := M_eq h
      _ ≤ powSubgroup fr.M (M_comm h) 3 :=
        sup_le (sup_le (fun _ hx => ⟨P₁_le_M fr hx, pow_three_of_mem_P₁ fr hx⟩)
          (fun _ hx => ⟨At_le_M fr hx, pow_three_of_mem_At h hx⟩))
          (fun _ hx => ⟨hx.1, pow_three_of_mem_Atz h hx⟩)
  exact (hle ha).2

theorem centralizer_M_eq (h : Hyp fr) :
    centralizer (fr.M : Set G) ⊓ centralizer (fr.P₁ : Set G) = fr.M :=
  le_antisymm (centralizer_M_le h)
    (le_inf (fun a ha => mem_centralizer_iff.mpr fun b hb => M_comm h b hb a ha) (M_le_C₁ fr))

end JankoTen.Hyp

theorem jankoStep10 : JankoStep10 := by
  intro G _ _ z fr hset hfrs p7 h9
  have h : JankoTen.Hyp fr := ⟨hset, hfrs, p7, h9⟩
  exact
    { P₁_le_M := JankoTen.Hyp.P₁_le_M fr
      centralizer_P₁ := JankoTen.Hyp.centralizer_P₁_eq h
      M_inf_F := JankoTen.Hyp.M_inf_F h
      M_inf_centralizer_z := JankoTen.Hyp.M_inf_H h
      card_M := JankoTen.Hyp.card_M h
      M_comm := JankoTen.Hyp.M_comm h
      M_pow_three := fun _ ha => JankoTen.Hyp.M_pow_three h ha
      centralizer_M := JankoTen.Hyp.centralizer_M_eq h
      card_At := JankoTen.Hyp.card_At h
      card_Atz := JankoTen.Hyp.card_Atz h
      At_inf_centralizer_z := JankoTen.Hyp.At_inf_H h
      M_eq := JankoTen.Hyp.M_eq h
      not_At_le := JankoTen.Hyp.not_At_le h
      isConj_of_mem_At := fun _ hx hx1 => JankoTen.Hyp.isConj_of_mem_At h hx hx1
      isConj_of_mem_Atz := fun _ hx hx1 => JankoTen.Hyp.isConj_of_mem_Atz h hx hx1
      false_of_sylow := fun N₀ y hy hZ Q hQA hQ3 X₀ hX₀ hP hQ ht hc =>
        JankoTen.Hyp.false_of_sylow h N₀ y hy hZ Q hQA hQ3 X₀ hX₀ hP hQ ht hc }

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
