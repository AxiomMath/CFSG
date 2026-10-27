module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Basic
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Core
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

theorem lemma52_aux (hII : II4_4_4_center) (h52a : IVK_1_2j_52) (h52b : IVK_1_9_52)
    (hC : Cfg5 G z S K₁ K₂) {a : G} (ha : Elt5 G z S K₁ K₂ a) {A B : Subgroup G}
    (hAB : A = K₁ ∧ B = K₂ ∨ A = K₂ ∧ B = K₁) : Qof S B = Pof S A := by
  by_contra hne
  have hM := m4_of_std hII hC.std
  have hP := h52a G z S K₁ K₂ a hC ha A B hAB hne
  have hcyc := h52b G z S K₁ K₂ a hC ha A B hAB hne hP
  have hBc : B = K₁ ∨ B = K₂ := by
    rcases hAB with ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inr h
    · exact Or.inl h
  have hmQ : pRank 2 ↥(Qof S B) = 1 := by
    rcases hAB with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact hC.m₂
    · exact hC.m₁
  have haB : a ∉ Qof S B := fun hmem =>
    ha.ne (by
      rw [eq_z_of_mem_Qof hM hBc hmQ hC.std.orderOf_z hmem ha.inv]
      exact mem_zpowers z)
  have hX : IsPGroup 2 ↥(Qof S B ⊔ zpowers a) :=
    hM.S_pgroup.to_le (sup_le inf_le_left (zpowers_le.2 ha.mem))
  exact core52 hX (Pof_le_Qof hM hAB) le_sup_left (mem_sup_right (mem_zpowers a))
    (mul_self_eq_one_of_orderOf_eq_two ha.inv) haB hne hcyc

theorem lemma_5_2 (hII : II4_4_4_center) (h52a : IVK_1_2j_52) (h52b : IVK_1_9_52) :
    Lemma5_2 := by
  intro G _ _ z S K₁ K₂ a x hctr
  exact ⟨lemma52_aux hII h52a h52b hctr.cfg hctr.elt (Or.inr ⟨rfl, rfl⟩),
    lemma52_aux hII h52a h52b hctr.cfg hctr.elt (Or.inl ⟨rfl, rfl⟩)⟩

theorem lemma_5_3 (h32 : IVK_3_2_lifted) (h52 : Lemma5_2) : Lemma5_3 := by
  intro G _ _ z S K₁ K₂ a x hctr
  exact h32 G z S K₁ K₂ a x hctr (h52 G z S K₁ K₂ a x hctr)

end CFSG.GH74.GLS.Stage1.Thm3.Sec5
