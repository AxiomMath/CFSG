module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinAltPerm

public section

namespace CFSG.ComponentClassification.HarrisLit.L35

open Equiv Equiv.Perm Subgroup CFSG.ComponentClassification.GSThmB.Catalog82A10
open CFSG.ComponentClassification.HarrisLit.Hin

variable {α : Type*} {σ : Perm α} (hσ : σ * σ = 1)

include hσ in
theorem fixes_support_of_comm [DecidableEq α] [Fintype α] {L : Subgroup (Perm α)}
    (hLperf : ⁅L, L⁆ = L) (hLC : ∀ g ∈ L, g * σ = σ * g)
    (hcomm : ∀ g ∈ L, ∀ x ∈ pairSub hσ, x ∈ alternatingGroup α → g * x = x * g) :
    ∀ g ∈ L, ∀ a ∈ σ.support, g a = a := by
  classical
  have hpres : ∀ g ∈ L, ∀ x, g x ∈ σ.support ↔ x ∈ σ.support := fun g hg x =>
    GSThmB.Catalog82A10.mem_support_iff_of_commute (hLC g hg) x
  by_cases hS : σ.support.card ≤ 4
  · exact perfect_fix_small L hLperf σ.support hS hpres
  push Not at hS
  have hsw : ∀ a ∈ σ.support, ∀ b ∈ σ.support, b ≠ a → b ≠ σ a → ∀ g ∈ L,
      g a = a ∨ g a = σ a ∨ g a = b ∨ g a = σ b := by
    intro a ha b hb hba hbσa g hg
    have hσa : σ a ≠ a := Perm.mem_support.mp ha
    have hσb : σ b ≠ b := Perm.mem_support.mp hb
    set e := swap a (σ a) * swap b (σ b) with he
    have heB : e ∈ pairSub hσ := swap_mul_swap_mem_pairSub hσ hba hbσa
    have heA : e ∈ alternatingGroup α := by
      rw [mem_alternatingGroup, he, Perm.sign_mul, Perm.sign_swap hσa.symm,
        Perm.sign_swap hσb.symm]
      decide
    have hab' : a ≠ b := hba.symm
    have haσb : a ≠ σ b := fun h => hbσa (by rw [h, apply_apply_of_mul_self hσ])
    have hea : e a = σ a := by
      rw [he, Perm.mul_apply, swap_apply_of_ne_of_ne hab' haσb, swap_apply_left]
    have hge := hcomm g hg e heB heA
    have h1 : e (g a) = g (σ a) := by
      rw [← hea]
      change (e * g) a = (g * e) a
      rw [hge]
    refine mem_of_swap_mul_swap_ne fun h => ?_
    rw [h1] at h
    exact hσa (g.injective h)
  have hkey : ∀ a ∈ σ.support, ∀ g ∈ L, g a = a ∨ g a = σ a := by
    intro a ha g hg
    have hcard1 : σ.support.card - 4 ≤
        ((((σ.support.erase a).erase (σ a)).erase a).erase (σ a)).card := by
      have := Finset.pred_card_le_card_erase (s := σ.support) (a := a)
      have := Finset.pred_card_le_card_erase (s := σ.support.erase a) (a := σ a)
      have := Finset.pred_card_le_card_erase (s := (σ.support.erase a).erase (σ a)) (a := a)
      have := Finset.pred_card_le_card_erase
        (s := ((σ.support.erase a).erase (σ a)).erase a) (a := σ a)
      omega
    obtain ⟨b, hb⟩ : (((((σ.support.erase a).erase (σ a)).erase a).erase (σ a))).Nonempty :=
      Finset.card_pos.mp (by omega)
    simp only [Finset.mem_erase] at hb
    obtain ⟨-, -, hbσa, hba, hbs⟩ := hb
    have hcard2 : σ.support.card - 4 ≤
        ((((σ.support.erase a).erase (σ a)).erase b).erase (σ b)).card := by
      have := Finset.pred_card_le_card_erase (s := σ.support) (a := a)
      have := Finset.pred_card_le_card_erase (s := σ.support.erase a) (a := σ a)
      have := Finset.pred_card_le_card_erase (s := (σ.support.erase a).erase (σ a)) (a := b)
      have := Finset.pred_card_le_card_erase
        (s := ((σ.support.erase a).erase (σ a)).erase b) (a := σ b)
      omega
    obtain ⟨c, hc⟩ : ((((σ.support.erase a).erase (σ a)).erase b).erase (σ b)).Nonempty :=
      Finset.card_pos.mp (by omega)
    simp only [Finset.mem_erase] at hc
    obtain ⟨hcσb, hcb, hcσa, hca, hcs⟩ := hc
    have h1 := hsw a ha b hbs hba hbσa g hg
    have h2 := hsw a ha c hcs hca hcσa g hg
    have hσcb : σ c ≠ b := fun h => hcσb (by rw [← h, apply_apply_of_mul_self hσ])
    have hσcσb : σ c ≠ σ b := fun h => hcb (σ.injective h)
    have hσba : σ b ≠ a := fun h => hbσa (by rw [← h, apply_apply_of_mul_self hσ])
    have hσbσa : σ b ≠ σ a := fun h => hba (σ.injective h)
    rcases h1 with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      rcases h2 with h' | h' | h' | h' <;> rw [h] at h'
      · exact hba h'
      · exact hbσa h'
      · exact hcb h'.symm
      · exact hσcb h'.symm
    · exfalso
      rcases h2 with h' | h' | h' | h' <;> rw [h] at h'
      · exact hσba h'
      · exact hσbσa h'
      · exact hcσb h'.symm
      · exact hσcσb h'.symm
  intro g hg a ha
  have hP : ({a, σ a} : Finset α).card ≤ 4 :=
    (Finset.card_insert_le _ _).trans (by simp)
  exact perfect_fix_small L hLperf {a, σ a} hP (pair_pres hσ hLC (hkey a ha)) g hg a
    (Finset.mem_insert_self _ _)

include hσ in
theorem le_altOn_of_comm [DecidableEq α] [Fintype α] {L : Subgroup (Perm α)}
    (hLperf : ⁅L, L⁆ = L) (hLC : ∀ g ∈ L, g * σ = σ * g)
    (hcomm : ∀ g ∈ L, ∀ x ∈ pairSub hσ, x ∈ alternatingGroup α → g * x = x * g) :
    L ≤ altOn σ.supportᶜ := by
  have hfix := fixes_support_of_comm hσ hLperf hLC hcomm
  intro g hg
  refine mem_altOn.mpr ⟨perfect_le_alternating L hLperf hg, fun x hx => ?_⟩
  rw [Finset.mem_compl]
  intro hxs
  exact (Perm.mem_support.mp hx) (hfix g hg x hxs)

end CFSG.ComponentClassification.HarrisLit.L35
