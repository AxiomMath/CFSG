module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23ME16
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2M23MStr

public section

namespace CFSG.Quasithin.H13

open Equiv CFSG.M23Norm3 CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94
open scoped Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem eq_or_eq_of_isElemAbelian_of_le_inf_L_F4
    (h526 : Stmt5_2_6_F4) (h527 : Stmt5_2_7_F4) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz_F4)
    (hU4 : Stmt5_2_8_U4_F4) (hsp : Stmt5_2_8_special_F4) (hQ : Stmt5_2_8_Q_F4)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) {E : Subgroup G} (hE : E ≤ T ⊓ L)
    (hE2 : ∀ g ∈ E, g * g = 1) (hEc : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g)
    (hE16 : Nat.card E = 16) : E = pCoreOf 2 M2 ∨ E = pCoreOf 2 L := by
  obtain ⟨-, ⟨hG1, hG2, hG12, hSL, -, -⟩, -⟩ := h527 G T M L V H B D L₂ n hyp
  have hTL : T ⊓ L ≤ (L ⊔ (sec52S M H ⊓ L) ⊔ (B ⊓ oTwoUpper H)) ⊓
      (D ⊔ (sec52S M H ⊓ L) ⊔ oTwoUpper H) := by
    rw [hG1, hG2, hG12, ← hSL]
    exact le_sup_left.trans le_sup_left
  obtain ⟨W1, W2, hW⟩ : ∃ W1 W2 : Subgroup G, ∀ E' : Subgroup G, E' ≤ T ⊓ L →
      (∀ g ∈ E', g * g = 1) → (∀ g ∈ E', ∀ h ∈ E', g * h = h * g) → Nat.card E' = 16 →
        E' = W1 ∨ E' = W2 := by
    rcases isParabolicIsoData_of_isAmalgamOfGroup hM23.1 with ⟨φ₁, -, -, hiff⟩ |
        ⟨φ₁, -, -, hiff⟩
    · exact ⟨_, _, fun E' hE' h2 hc h16 =>
        eq_image_of_isElemAbelian φ₁ hiff (hE'.trans hTL) h2 hc h16⟩
    · exact ⟨_, _, fun E' hE' h2 hc h16 =>
        eq_image_of_isElemAbelian φ₁ hiff (hE'.trans (hTL.trans (le_of_eq (inf_comm _ _)))) h2 hc
          h16⟩
  obtain ⟨-, hUle, hVle, -⟩ := inf_L_facts_of_setting_F4 h526 h527 h1284 hSz hU4 hsp hQ hyp hM23 hS
  obtain ⟨hbl, -, h16, hUQ, -⟩ := setting_L_facts_F4 h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  obtain ⟨hab, hU16, -⟩ := hQ G T M L V H B D L₂ n M2 hyp hM23 hS.K_lt hS.maximal hS.excA7
  have hU := hW (pCoreOf 2 M2) hUle
    (fun g hg => by rw [← sq]; exact hab.2 g hg)
    (fun g hg h hh => congrArg Subtype.val (hab.1.1.comm ⟨g, hg⟩ ⟨h, hh⟩)) hU16
  have hVsq := hbl.1.2.2.1
  rw [hUQ] at hVsq
  have hV := hW (pCoreOf 2 L) hVle
    (fun g hg => by rw [← sq]; exact hVsq.2 g hg)
    (fun g hg h hh => (Subgroup.mem_centralizer_iff.mp (hVsq.1 hh).2) g hg) h16
  have hne := pCoreOf_M2_ne_pCoreOf_L hyp hS h16
  rcases hW E hE hE2 hEc hE16 with rfl | rfl <;> rcases hU with hU | hU <;>
    rcases hV with hV | hV
  all_goals first
    | exact Or.inl hU.symm
    | exact Or.inr hV.symm
    | exact absurd (hU.trans hV.symm) hne

end CFSG.Quasithin.H13
