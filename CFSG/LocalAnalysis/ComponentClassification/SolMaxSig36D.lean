module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36C

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {α : Type*} [DecidableEq α]

theorem swap_mul_swap_mul_self {a b c d : α} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) : swap a b * swap c d * (swap a b * swap c d) = 1 := by
  calc swap a b * swap c d * (swap a b * swap c d) =
      swap a b * (swap c d * swap a b) * swap c d := by group
    _ = swap a b * (swap a b * swap c d) * swap c d := by
        rw [swap_mul_swap_comm_of_ne hac had hbc hbd]
    _ = 1 := by rw [← mul_assoc, swap_mul_self, one_mul, swap_mul_self]

variable [Fintype α]

theorem card_support_swap_mul_swap {a b c d : α} (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) : (swap a b * swap c d).support.card = 4 := by
  have hdisj' : Disjoint (swap a b).support (swap c d).support := by
    rw [Perm.support_swap hab, Perm.support_swap hcd]
    simp [Finset.disjoint_left, hac, had, hbc, hbd]
  have hdisj : (swap a b).Disjoint (swap c d) := Perm.disjoint_iff_disjoint_support.mpr hdisj'
  rw [hdisj.support_mul, Finset.card_union_of_disjoint hdisj', Perm.support_swap hab,
    Perm.support_swap hcd, Finset.card_pair hab, Finset.card_pair hcd]

theorem four_dvd_card_support_of_mem_alternating {σ : Perm α} (hσ : σ * σ = 1)
    (hA : σ ∈ alternatingGroup α) : 4 ∣ σ.support.card := by
  by_cases h1 : σ = 1
  · rw [h1, Perm.support_one, Finset.card_empty]
    exact dvd_zero 4
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσ) h1
  obtain ⟨k, hk⟩ := Perm.cycleType_prime_order (σ := σ) (by rw [hord]; exact Nat.prime_two)
  rw [hord] at hk
  have hsum := Perm.sum_cycleType σ
  rw [hk, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hsign := Perm.sign_of_cycleType σ
  rw [hk, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul,
    Perm.mem_alternatingGroup.mp hA] at hsign
  have heven : Even ((k + 1) * 2 + (k + 1)) := by
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    rw [hodd.neg_one_pow] at hsign
    exact absurd hsign (by decide)
  obtain ⟨j, hj⟩ := heven
  rw [← hsum]
  omega

theorem exists_four_mem_oddCentGen {σ : Perm α} (hσ : σ * σ = 1)
    (hcard : 9 ≤ Fintype.card α) :
    ∃ δ ∈ oddCentGen σ, δ * δ = 1 ∧ δ.support.card = 4 := by
  classical
  have hσσ : ∀ v, σ (σ v) = v := fun v => by rw [← Perm.mul_apply, hσ, Perm.one_apply]
  by_cases h6 : 6 ≤ σ.support.card
  ·
    obtain ⟨a₁, ha₁⟩ := Finset.card_pos.mp (by omega : 0 < σ.support.card)
    have h₁ : σ a₁ ≠ a₁ := Perm.mem_support.mp ha₁
    obtain ⟨a₂, ha₂, ha₂n⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := {a₁, σ a₁}) (t := σ.support) (lt_of_le_of_lt Finset.card_le_two (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha₂n
    have h₂ : σ a₂ ≠ a₂ := Perm.mem_support.mp ha₂
    obtain ⟨a₃, ha₃, ha₃n⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := {a₁, σ a₁, a₂, σ a₂}) (t := σ.support) (lt_of_le_of_lt Finset.card_le_four (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha₃n
    have h₃ : σ a₃ ≠ a₃ := Perm.mem_support.mp ha₃
    have hmem := pair_mem_oddCentGen hσ h₁ h₂ h₃ ha₂n.1 ha₂n.2 ha₃n.1 ha₃n.2.1 ha₃n.2.2.1
      ha₃n.2.2.2
    have hac : a₂ ≠ a₃ := Ne.symm ha₃n.2.2.1
    have hbc : σ a₂ ≠ a₃ := Ne.symm ha₃n.2.2.2
    have had : a₂ ≠ σ a₃ := fun h => ha₃n.2.2.2 (by rw [h, hσσ])
    have hbd : σ a₂ ≠ σ a₃ := fun h => hac (σ.injective h)
    exact ⟨_, hmem, swap_mul_swap_mul_self hac had hbc hbd,
      card_support_swap_mul_swap (Ne.symm h₂) (Ne.symm h₃) hac had hbc hbd⟩
  ·
    push Not at h6
    have hF : 4 ≤ (σ.supportᶜ).card := by
      rw [Finset.card_compl]
      omega
    have hfix : ∀ x ∈ σ.supportᶜ, σ x = x := fun x hx => by
      rw [Finset.mem_compl, Perm.mem_support, not_not] at hx
      exact hx
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < (σ.supportᶜ).card)
    obtain ⟨b, hb, hbn⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := {a}) (t := σ.supportᶜ) (by rw [Finset.card_singleton]; omega)
    obtain ⟨c, hc, hcn⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := {a, b}) (t := σ.supportᶜ) (lt_of_le_of_lt Finset.card_le_two (by omega))
    obtain ⟨d, hd, hdn⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := {a, b, c}) (t := σ.supportᶜ) (lt_of_le_of_lt Finset.card_le_three (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hbn hcn hdn
    have hab : a ≠ b := Ne.symm hbn
    have hac : a ≠ c := Ne.symm hcn.1
    have hbc : b ≠ c := Ne.symm hcn.2
    have had : a ≠ d := Ne.symm hdn.1
    have hbd : b ≠ d := Ne.symm hdn.2.1
    have hcd : c ≠ d := Ne.symm hdn.2.2
    exact ⟨_, fix_pair_mem_oddCentGen (hfix a ha) (hfix b hb) (hfix c hc) (hfix d hd) hab hac had
      hbc hbd hcd, swap_mul_swap_mul_self hac had hbc hbd,
      card_support_swap_mul_swap hab hcd hac had hbc hbd⟩

theorem card_support_mul_pair {σ ν : Perm α} (hν : ν * ν = 1)
    (hνσ : ∀ x, ν x ≠ x → ν x = σ x) {a b : α} (ha : ν a ≠ a) (hb : ν b ≠ b) (hba : b ≠ a)
    (hbσa : b ≠ σ a) :
    (ν * (swap a (σ a) * swap b (σ b))) * (ν * (swap a (σ a) * swap b (σ b))) = 1 ∧
      (∀ x, (ν * (swap a (σ a) * swap b (σ b))) x ≠ x →
        (ν * (swap a (σ a) * swap b (σ b))) x = σ x) ∧
      (ν * (swap a (σ a) * swap b (σ b))).support.card + 4 = ν.support.card := by
  have hνν : ∀ v, ν (ν v) = v := fun v => by rw [← Perm.mul_apply, hν, Perm.one_apply]
  have hνa : ν a = σ a := hνσ a ha
  have hνb : ν b = σ b := hνσ b hb
  rw [← hνa, ← hνb]
  rw [← hνa] at hbσa
  have h1 : a ≠ ν a := Ne.symm ha
  have h2 : b ≠ ν b := Ne.symm hb
  have hσab : ν b ≠ a := fun h => hbσa (by rw [← h, hνν])
  have hσaσb : ν b ≠ ν a := fun h => hba (ν.injective h)
  set δ := swap a (ν a) * swap b (ν b) with hδ
  have hδν : δ * ν = ν * δ := by
    have h3 := swap_mul_comm_of_involution hν a
    have h4 := swap_mul_comm_of_involution hν b
    rw [hδ, mul_assoc, h4, ← mul_assoc, h3, mul_assoc]
  have hδδ : δ * δ = 1 :=
    swap_mul_swap_mul_self (Ne.symm hba) (Ne.symm hσab) (Ne.symm hbσa) (Ne.symm hσaσb)
  have hva : (ν * δ) a = a := by
    rw [Perm.mul_apply, hδ, Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hba) (Ne.symm hσab),
      swap_apply_left, hνν]
  have hvσa : (ν * δ) (ν a) = ν a := by
    rw [Perm.mul_apply, hδ, Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hbσa)
      (Ne.symm hσaσb), swap_apply_right]
  have hvb : (ν * δ) b = b := by
    rw [Perm.mul_apply, hδ, Perm.mul_apply, swap_apply_left,
      swap_apply_of_ne_of_ne hσab hσaσb, hνν]
  have hvσb : (ν * δ) (ν b) = ν b := by
    rw [Perm.mul_apply, hδ, Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne hba hbσa]
  have hvx : ∀ x, x ≠ a → x ≠ ν a → x ≠ b → x ≠ ν b → (ν * δ) x = ν x := by
    intro x hxa hxσa hxb hxσb
    rw [Perm.mul_apply, hδ, Perm.mul_apply, swap_apply_of_ne_of_ne hxb hxσb,
      swap_apply_of_ne_of_ne hxa hxσa]
  refine ⟨?_, ?_, ?_⟩
  · calc ν * δ * (ν * δ) = ν * (δ * ν) * δ := by group
      _ = ν * (ν * δ) * δ := by rw [hδν]
      _ = 1 := by rw [← mul_assoc ν ν δ, hν, one_mul, hδδ]
  · intro x hx
    by_cases hxa : x = a
    · exact absurd (by rw [hxa]; exact hva) hx
    by_cases hxσa : x = ν a
    · exact absurd (by rw [hxσa]; exact hvσa) hx
    by_cases hxb : x = b
    · exact absurd (by rw [hxb]; exact hvb) hx
    by_cases hxσb : x = ν b
    · exact absurd (by rw [hxσb]; exact hvσb) hx
    rw [hvx x hxa hxσa hxb hxσb] at hx ⊢
    exact hνσ x hx
  · have hsupp : (ν * δ).support = ν.support \ {a, ν a, b, ν b} := by
      ext x
      simp only [Perm.mem_support, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hx
        by_cases hxa : x = a
        · exact absurd (by rw [hxa]; exact hva) hx
        by_cases hxσa : x = ν a
        · exact absurd (by rw [hxσa]; exact hvσa) hx
        by_cases hxb : x = b
        · exact absurd (by rw [hxb]; exact hvb) hx
        by_cases hxσb : x = ν b
        · exact absurd (by rw [hxσb]; exact hvσb) hx
        rw [hvx x hxa hxσa hxb hxσb] at hx
        exact ⟨hx, by tauto⟩
      · rintro ⟨hx, hxn⟩
        push Not at hxn
        rw [hvx x hxn.1 hxn.2.1 hxn.2.2.1 hxn.2.2.2]
        exact hx
    have hsub : ({a, ν a, b, ν b} : Finset α) ⊆ ν.support := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Perm.mem_support]
      rcases hx with rfl | rfl | rfl | rfl
      · exact ha
      · rw [hνν]; exact h1
      · exact hb
      · rw [hνν]; exact h2
    have hcard4 : ({a, ν a, b, ν b} : Finset α).card = 4 := by
      have n1 : a ∉ ({ν a, b, ν b} : Finset α) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨h1, Ne.symm hba, Ne.symm hσab⟩
      have n2 : ν a ∉ ({b, ν b} : Finset α) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => hbσa h.symm, Ne.symm hσaσb⟩
      rw [Finset.card_insert_of_notMem n1, Finset.card_insert_of_notMem n2, Finset.card_pair h2]
    rw [hsupp, Finset.card_sdiff_of_subset hsub, hcard4]
    have := Finset.card_le_card hsub
    omega

theorem mem_oddCentGen_self {σ : Perm α} (hσ : σ * σ = 1) (hσA : σ ∈ alternatingGroup α)
    (h8 : 8 ≤ σ.support.card) : σ ∈ oddCentGen σ := by
  classical
  have hσσ : ∀ v, σ (σ v) = v := fun v => by rw [← Perm.mul_apply, hσ, Perm.one_apply]
  have key : ∀ k : ℕ, ∀ ν : Perm α, ν * ν = 1 → (∀ x, ν x ≠ x → ν x = σ x) →
      ν.support.card = 4 * k → ν ∈ oddCentGen σ := by
    intro k
    induction k with
    | zero =>
      intro ν _ _ hc
      rw [mul_zero, Finset.card_eq_zero, Perm.support_eq_empty_iff] at hc
      rw [hc]
      exact one_mem _
    | succ k ih =>
      intro ν hν hνσ hc
      obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < ν.support.card)
      have ha' : ν a ≠ a := Perm.mem_support.mp ha
      have hνa : ν a = σ a := hνσ a ha'
      obtain ⟨b, hb, hbn⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (s := {a, σ a}) (t := ν.support) (lt_of_le_of_lt Finset.card_le_two (by omega))
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hbn
      have hb' : ν b ≠ b := Perm.mem_support.mp hb
      have hνb : ν b = σ b := hνσ b hb'
      have hσa : σ a ≠ a := hνa ▸ ha'
      have hσb : σ b ≠ b := hνb ▸ hb'
      obtain ⟨c, hc', hcn⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (s := {a, σ a, b, σ b}) (t := σ.support) (lt_of_le_of_lt Finset.card_le_four (by omega))
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcn
      have hσc : σ c ≠ c := Perm.mem_support.mp hc'
      have hac : a ≠ c := Ne.symm hcn.1
      have haσc : a ≠ σ c := fun h => hcn.2.1 (by rw [h, hσσ])
      have hbc : b ≠ c := Ne.symm hcn.2.2.1
      have hbσc : b ≠ σ c := fun h => hcn.2.2.2 (by rw [h, hσσ])
      have hδ := pair_mem_oddCentGen hσ hσc hσa hσb hac haσc hbc hbσc hbn.1 hbn.2
      obtain ⟨h1, h2, h3⟩ := card_support_mul_pair hν hνσ ha' hb' hbn.1 hbn.2
      have hν' := ih _ h1 h2 (by omega)
      have hδδ : swap a (σ a) * swap b (σ b) * (swap a (σ a) * swap b (σ b)) = 1 := by
        have had : a ≠ σ b := fun h => hbn.2 (by rw [h, hσσ])
        have hbd : σ a ≠ σ b := fun h => hbn.1 (σ.injective h).symm
        exact swap_mul_swap_mul_self (Ne.symm hbn.1) had (Ne.symm hbn.2) hbd
      have hνeq : ν = ν * (swap a (σ a) * swap b (σ b)) * (swap a (σ a) * swap b (σ b)) := by
        rw [mul_assoc, hδδ, mul_one]
      rw [hνeq]
      exact mul_mem hν' hδ
  obtain ⟨k, hk⟩ := four_dvd_card_support_of_mem_alternating hσ hσA
  exact key k σ hσ (fun _ _ => rfl) hk

end CFSG.ComponentClassification.SolMax
