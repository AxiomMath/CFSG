module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82A10Perm

public section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open Equiv Equiv.Perm Subgroup CFSG.ComponentClassification.GSThmB.Catalog82A10

variable {α : Type*} {σ : Perm α}

theorem apply_apply_of_mul_self (hσ : σ * σ = 1) (a : α) : σ (σ a) = a := by
  have := congrArg (fun g : Perm α => g a) hσ
  simpa [Perm.mul_apply] using this

@[expose] def pairSub (hσ : σ * σ = 1) : Subgroup (Perm α) where
  carrier := {x | ∀ a, x a = a ∨ x a = σ a}
  mul_mem' := by
    intro x y hx hy a
    rcases hy a with h | h
    · simp only [Perm.mul_apply, h]
      exact hx a
    · simp only [Perm.mul_apply, h]
      rcases hx (σ a) with h' | h'
      · exact Or.inr h'
      · left
        rw [h', apply_apply_of_mul_self hσ]
  one_mem' := fun _ => Or.inl rfl
  inv_mem' := by
    intro x hx a
    have hxb : x (x⁻¹ a) = a := Equiv.apply_symm_apply x a
    rcases hx (x⁻¹ a) with h | h
    · exact Or.inl (h.symm.trans hxb)
    · right
      conv_rhs => rw [← hxb, h, apply_apply_of_mul_self hσ]

variable (hσ : σ * σ = 1)

theorem mem_pairSub {x : Perm α} : x ∈ pairSub hσ ↔ ∀ a, x a = a ∨ x a = σ a := Iff.rfl

include hσ in
theorem apply_sigma_of_mem_pairSub {x : Perm α} (hx : x ∈ pairSub hσ) (a : α) :
    x (σ a) = σ (x a) := by
  rcases hx a with h | h <;> rcases hx (σ a) with h' | h'
  · rw [h, h']
  · rw [apply_apply_of_mul_self hσ] at h'
    have hσa : σ a = a := x.injective (h'.trans h.symm)
    rw [h, hσa]
    exact h
  · have hσa : σ a = a := x.injective (h'.trans h.symm)
    rw [h', h, apply_apply_of_mul_self hσ]
    exact hσa
  · rw [h, h']

theorem pairSub_le_centralizer : pairSub hσ ≤ centralizer ({σ} : Set (Perm α)) := by
  intro x hx
  rw [mem_centralizer_singleton_iff]
  ext a
  exact apply_sigma_of_mem_pairSub hσ hx a

theorem pairSub_comm {x y : Perm α} (hx : x ∈ pairSub hσ) (hy : y ∈ pairSub hσ) :
    x * y = y * x := by
  ext a
  simp only [Perm.mul_apply]
  rcases hy a with h | h <;> rcases hx a with h' | h'
  · rw [h, h', h]
  · rw [h, h', apply_sigma_of_mem_pairSub hσ hy, h]
  · rw [h, h', apply_sigma_of_mem_pairSub hσ hx, h', h]
  · rw [h, h', apply_sigma_of_mem_pairSub hσ hx, apply_sigma_of_mem_pairSub hσ hy, h, h']

theorem pairSub_sq {x : Perm α} (hx : x ∈ pairSub hσ) : x * x = 1 := by
  ext a
  simp only [Perm.mul_apply, Perm.one_apply]
  rcases hx a with h | h
  · rw [h, h]
  · rw [h, apply_sigma_of_mem_pairSub hσ hx, h, apply_apply_of_mul_self hσ]

theorem conj_mem_pairSub {c x : Perm α} (hc : c * σ = σ * c) (hx : x ∈ pairSub hσ) :
    c * x * c⁻¹ ∈ pairSub hσ := by
  intro a
  simp only [Perm.mul_apply]
  have hcσ : ∀ b, c (σ b) = σ (c b) := fun b => by
    change (c * σ) b = (σ * c) b
    rw [hc]
  rcases hx (c⁻¹ a) with h | h
  · left
    rw [h]
    exact Equiv.apply_symm_apply c a
  · right
    rw [h, hcσ]
    exact congrArg σ (Equiv.apply_symm_apply c a)

theorem swap_mul_swap_mem_pairSub [DecidableEq α] {a b : α} (hb : b ≠ a) (hb' : b ≠ σ a) :
    swap a (σ a) * swap b (σ b) ∈ pairSub hσ := by
  have hσb : σ b ≠ a := fun h => hb' (by rw [← h, apply_apply_of_mul_self hσ])
  have hσb' : σ b ≠ σ a := fun h => hb (σ.injective h)
  intro x
  simp only [Perm.mul_apply]
  by_cases hx1 : x = b
  · subst hx1
    rw [swap_apply_left, swap_apply_of_ne_of_ne hσb hσb']
    exact Or.inr rfl
  by_cases hx2 : x = σ b
  · subst hx2
    rw [swap_apply_right, swap_apply_of_ne_of_ne hb hb']
    exact Or.inr (apply_apply_of_mul_self hσ b).symm
  rw [swap_apply_of_ne_of_ne hx1 hx2]
  by_cases hx3 : x = a
  · subst hx3
    rw [swap_apply_left]
    exact Or.inr rfl
  by_cases hx4 : x = σ a
  · subst hx4
    rw [swap_apply_right]
    exact Or.inr (apply_apply_of_mul_self hσ a).symm
  rw [swap_apply_of_ne_of_ne hx3 hx4]
  exact Or.inl rfl

theorem mem_of_swap_mul_swap_ne [DecidableEq α] {a b x : α}
    (hx : (swap a (σ a) * swap b (σ b)) x ≠ x) : x = a ∨ x = σ a ∨ x = b ∨ x = σ b := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  apply hx
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne h3 h4, swap_apply_of_ne_of_ne h1 h2]

include hσ in
theorem pair_pres [DecidableEq α] {L : Subgroup (Perm α)} (hLC : ∀ g ∈ L, g * σ = σ * g) {a : α}
    (hkey : ∀ g ∈ L, g a = a ∨ g a = σ a) :
    ∀ g ∈ L, ∀ x, g x ∈ ({a, σ a} : Finset α) ↔ x ∈ ({a, σ a} : Finset α) := by
  have hσg : ∀ g ∈ L, ∀ y, g (σ y) = σ (g y) := fun g hg y => by
    change (g * σ) y = (σ * g) y
    rw [hLC g hg]
  have himp : ∀ g ∈ L, ∀ x, x ∈ ({a, σ a} : Finset α) → g x ∈ ({a, σ a} : Finset α) := by
    intro g hg x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx with rfl | rfl
    · exact hkey g hg
    · rw [hσg g hg]
      rcases hkey g hg with h | h
      · right
        rw [h]
      · left
        rw [h, apply_apply_of_mul_self hσ]
  intro g hg x
  refine ⟨fun h => ?_, himp g hg x⟩
  have := himp g⁻¹ (L.inv_mem hg) (g x) h
  rwa [show g⁻¹ (g x) = x from Equiv.symm_apply_apply g x] at this

theorem fixes_support_of_normal [DecidableEq α] [Fintype α] {L : Subgroup (Perm α)}
    (hLperf : ⁅L, L⁆ = L)
    (hLs : IsSimpleGroup L) (hLnab : ∃ a b : L, a * b ≠ b * a)
    (hLC : ∀ g ∈ L, g * σ = σ * g)
    (hLn : ∀ x ∈ pairSub hσ, x ∈ alternatingGroup α → ∀ g ∈ L, x * g * x⁻¹ ∈ L) :
    ∀ g ∈ L, ∀ a ∈ σ.support, g a = a := by
  classical
  have hpres : ∀ g ∈ L, ∀ x, g x ∈ σ.support ↔ x ∈ σ.support := fun g hg x =>
    GSThmB.Catalog82A10.mem_support_iff_of_commute (hLC g hg) x
  by_cases hS : σ.support.card ≤ 4
  · exact perfect_fix_small L hLperf σ.support hS hpres
  push Not at hS
  have hLB : ∀ y ∈ L, y ∈ pairSub hσ → y = 1 := by
    have hn : ((pairSub hσ).subgroupOf L).Normal := by
      refine ⟨fun y hy l => ?_⟩
      rw [mem_subgroupOf] at hy ⊢
      exact conj_mem_pairSub hσ (hLC l l.2) hy
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((pairSub hσ).subgroupOf L) with hb | ht
    · intro y hyL hyB
      have : (⟨y, hyL⟩ : L) ∈ (pairSub hσ).subgroupOf L := hyB
      rw [hb, mem_bot] at this
      exact congrArg Subtype.val this
    · exfalso
      obtain ⟨a, b, hab⟩ := hLnab
      apply hab
      have hle : L ≤ pairSub hσ := subgroupOf_eq_top.mp ht
      exact Subtype.ext (pairSub_comm hσ (hle a.2) (hle b.2))
  have hcomm : ∀ g ∈ L, ∀ x ∈ pairSub hσ, x ∈ alternatingGroup α → g * x = x * g := by
    intro g hg x hx hxA
    have h1 : g * x * g⁻¹ * x⁻¹ ∈ L := by
      have h2 : g * (x * g⁻¹ * x⁻¹) ∈ L := L.mul_mem hg (hLn x hx hxA g⁻¹ (L.inv_mem hg))
      simpa [mul_assoc] using h2
    have h3 : g * x * g⁻¹ * x⁻¹ ∈ pairSub hσ :=
      (pairSub hσ).mul_mem (conj_mem_pairSub hσ (hLC g hg) hx) ((pairSub hσ).inv_mem hx)
    have h4 := hLB _ h1 h3
    calc g * x = g * x * g⁻¹ * x⁻¹ * (x * g) := by group
      _ = x * g := by rw [h4, one_mul]
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

theorem le_altOn_of_normal [DecidableEq α] [Fintype α] {L : Subgroup (Perm α)}
    (hLperf : ⁅L, L⁆ = L)
    (hLs : IsSimpleGroup L) (hLnab : ∃ a b : L, a * b ≠ b * a)
    (hLC : ∀ g ∈ L, g * σ = σ * g)
    (hLn : ∀ x ∈ pairSub hσ, x ∈ alternatingGroup α → ∀ g ∈ L, x * g * x⁻¹ ∈ L) :
    L ≤ altOn σ.supportᶜ := by
  have hfix := fixes_support_of_normal hσ hLperf hLs hLnab hLC hLn
  intro g hg
  refine mem_altOn.mpr ⟨perfect_le_alternating L hLperf hg, fun x hx => ?_⟩
  rw [Finset.mem_compl]
  intro hxs
  exact (Perm.mem_support.mp hx) (hfix g hg x hxs)

end CFSG.ComponentClassification.HarrisLit.Hin
