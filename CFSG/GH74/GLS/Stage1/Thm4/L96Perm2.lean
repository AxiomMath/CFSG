module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.GH74.GLS.Stage1.Thm4.L96

open Equiv Equiv.Perm

theorem ne_of_nodup_six {α : Type*} [DecidableEq α] {a b c d e f : α}
    (h : [a, b, c, d, e, f].Nodup) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ a ≠ f ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ b ≠ f ∧ c ≠ d ∧ c ≠ e ∧
      c ≠ f ∧ d ≠ e ∧ d ≠ f ∧ e ≠ f := by
  simp [List.nodup_cons] at h
  grind

theorem orderOf_mul_threeCycles {α : Type*} [DecidableEq α] [Fintype α] {u w : Perm α}
    (hu : u.IsThreeCycle) (hw : w.IsThreeCycle) (hd : Disjoint u w) : orderOf (u * w) = 3 := by
  rw [hd.orderOf, hu.orderOf, hw.orderOf]
  rfl

theorem exists_order_three_commuting_aux {α : Type*} [DecidableEq α] [Fintype α]
    {a b c d e f : α} (h : [a, b, c, d, e, f].Nodup) :
    ∃ γ₁ γ₂ : Perm α, orderOf γ₁ = 3 ∧ orderOf γ₂ = 3 ∧
      Commute γ₁ (swap a b * swap c d * swap e f) ∧ Commute γ₂ (swap a b * swap c d * swap e f) ∧
      (γ₁ * γ₂).cycleType = {2, 2} := by
  obtain ⟨hab, hac, had, hae, haf, hbc, hbd, hbe, hbf, hcd, hce, hcf, hde, hdf, hef⟩ :=
    ne_of_nodup_six h
  refine ⟨swap a e * swap a c * (swap b f * swap b d), swap a c * swap a f * (swap b d * swap b e),
    ?_, ?_, ?_, ?_, ?_⟩
  · refine orderOf_mul_threeCycles (isThreeCycle_swap_mul_swap_same hae hac hce.symm)
      (isThreeCycle_swap_mul_swap_same hbf hbd hdf.symm) fun x => ?_
    simp only [Perm.mul_apply, swap_apply_def]
    grind
  · refine orderOf_mul_threeCycles (isThreeCycle_swap_mul_swap_same hac haf hcf)
      (isThreeCycle_swap_mul_swap_same hbd hbe hde) fun x => ?_
    simp only [Perm.mul_apply, swap_apply_def]
    grind
  · refine Equiv.ext fun x => ?_
    simp only [Perm.mul_apply, swap_apply_def]
    grind
  · refine Equiv.ext fun x => ?_
    simp only [Perm.mul_apply, swap_apply_def]
    grind
  · have hprod : swap a e * swap a c * (swap b f * swap b d) *
        (swap a c * swap a f * (swap b d * swap b e)) = swap e f * swap a b := by
      refine Equiv.ext fun x => ?_
      simp only [Perm.mul_apply, swap_apply_def]
      grind
    rw [hprod]
    exact cycleType_swap_mul_swap_of_nodup (by simp [List.nodup_cons]; grind)

theorem cycleType_swap_mul_swap_mul_swap {α : Type*} [DecidableEq α] [Fintype α]
    {a b c d e f : α} (h : [a, b, c, d, e, f].Nodup) :
    (swap a b * swap c d * swap e f).cycleType = {2, 2, 2} := by
  obtain ⟨hab, hac, had, hae, haf, hbc, hbd, hbe, hbf, hcd, hce, hcf, hde, hdf, hef⟩ :=
    ne_of_nodup_six h
  rw [Disjoint.cycleType_mul, cycleType_swap_mul_swap_of_nodup (by simp [List.nodup_cons]; grind),
    isSwap_iff_cycleType.mp (swap_isSwap_iff.mpr hef)]
  · rfl
  · exact (disjoint_swap_swap (by simp [List.nodup_cons]; grind)).mul_left
      (disjoint_swap_swap (by simp [List.nodup_cons]; grind))

theorem exists_swaps_of_cycleType {n : ℕ} {σ : Perm (Fin n)} (hσ : σ.cycleType = {2, 2, 2}) :
    ∃ p : Fin 6 → Fin n, Function.Injective p ∧
      σ = swap (p 0) (p 1) * swap (p 2) (p 3) * swap (p 4) (p 5) := by
  have hn : 6 ≤ n := by
    have := Perm.sum_cycleType_le σ
    rw [hσ, Fintype.card_fin] at this
    simpa using this
  have hinj : Function.Injective (Fin.castLE hn) := Fin.castLE_injective hn
  have hc := cycleType_swap_mul_swap_mul_swap (a := Fin.castLE hn (0 : Fin 6))
    (b := Fin.castLE hn 1) (c := Fin.castLE hn 2) (d := Fin.castLE hn 3) (e := Fin.castLE hn 4)
    (f := Fin.castLE hn 5)
    (List.Nodup.map hinj (by decide : [(0 : Fin 6), 1, 2, 3, 4, 5].Nodup))
  obtain ⟨c, hc'⟩ := isConj_iff.mp (Perm.isConj_of_cycleType_eq (hc.trans hσ.symm))
  refine ⟨fun k => c (Fin.castLE hn k), c.injective.comp hinj, ?_⟩
  rw [← hc', swap_apply_apply, swap_apply_apply, swap_apply_apply]
  group

theorem exists_two_order_three_commuting {n : ℕ} {σ : Perm (Fin n)}
    (hσ : σ.cycleType = {2, 2, 2}) :
    ∃ γ₁ γ₂ : Perm (Fin n), orderOf γ₁ = 3 ∧ orderOf γ₂ = 3 ∧ Commute γ₁ σ ∧ Commute γ₂ σ ∧
      (γ₁ * γ₂).cycleType = {2, 2} := by
  obtain ⟨p, hp, rfl⟩ := exists_swaps_of_cycleType hσ
  exact exists_order_three_commuting_aux (a := p 0) (b := p 1) (c := p 2) (d := p 3) (e := p 4)
    (f := p 5) (List.Nodup.map hp (by decide : [(0 : Fin 6), 1, 2, 3, 4, 5].Nodup))

theorem apply_apply_of_cycleType_two_four {n : ℕ} {α : Perm (Fin n)}
    (hα : α.cycleType = {2, 2, 2, 2}) (x : Fin n) : α (α x) = x := by
  have h : orderOf α = 2 := by
    rw [← Perm.lcm_cycleType, hα]
    decide
  have h2 : α ^ 2 = 1 := by
    rw [← h]
    exact pow_orderOf_eq_one α
  simpa [pow_two] using DFunLike.congr_fun h2 x

theorem card_support_of_cycleType_two_four {n : ℕ} {α : Perm (Fin n)}
    (hα : α.cycleType = {2, 2, 2, 2}) : α.support.card = 8 := by
  rw [← Perm.sum_cycleType, hα]
  decide

theorem ne_self_of_cycleType_two_four {α : Perm (Fin 8)} (hα : α.cycleType = {2, 2, 2, 2})
    (x : Fin 8) : α x ≠ x := by
  have h8 : α.support = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [card_support_of_cycleType_two_four hα, Fintype.card_fin])
  have hx : x ∈ α.support := by rw [h8]; exact Finset.mem_univ x
  exact Perm.mem_support.mp hx

theorem fixed_unique_of_cycleType_two_four {α : Perm (Fin 9)} (hα : α.cycleType = {2, 2, 2, 2})
    {x y : Fin 9} (hx : α x = x) (hy : α y = y) : x = y := by
  have hc : (α.supportᶜ).card = 1 := by
    rw [Finset.card_compl, card_support_of_cycleType_two_four hα, Fintype.card_fin]
  have hx' : x ∈ α.supportᶜ := by simpa [Perm.mem_support] using hx
  have hy' : y ∈ α.supportᶜ := by simpa [Perm.mem_support] using hy
  exact Finset.card_le_one.mp hc.le x hx' y hy'

theorem exists_fixedPoint_enum {n m : ℕ} (hm : m + 6 = n) {σ : Perm (Fin n)}
    (hσ : σ.cycleType = {2, 2, 2}) :
    ∃ i : Fin m → Fin n, Function.Injective i ∧ (∀ k, σ (i k) = i k) ∧
      ∀ x, σ x = x → ∃ k, i k = x := by
  have hsupp : σ.support.card = 6 := by
    rw [← Perm.sum_cycleType, hσ]
    decide
  have hs : (σ.supportᶜ).card = m := by
    rw [Finset.card_compl, hsupp, Fintype.card_fin]
    omega
  refine ⟨fun k => (σ.supportᶜ).orderEmbOfFin hs k, (σ.supportᶜ).orderEmbOfFin hs |>.injective,
    fun k => ?_, fun x hx => ?_⟩
  · have h' : (σ.supportᶜ).orderEmbOfFin hs k ∉ σ.support :=
      Finset.mem_compl.mp (Finset.orderEmbOfFin_mem (σ.supportᶜ) hs k)
    by_contra h
    exact h' (Perm.mem_support.mpr h)
  · have hx' : x ∈ σ.supportᶜ := by
      rw [Finset.mem_compl, Perm.mem_support, not_not]
      exact hx
    have hr : x ∈ Set.range ((σ.supportᶜ).orderEmbOfFin hs) := by
      rw [Finset.range_orderEmbOfFin]
      exact hx'
    obtain ⟨k, hk⟩ := hr
    exact ⟨k, hk⟩

theorem exists_restrict_fixedPoint_enum {n m : ℕ} {i : Fin m → Fin n} {σ g : Perm (Fin n)}
    (hi : ∀ k, σ (i k) = i k) (hr : ∀ x, σ x = x → ∃ k, i k = x) (hg : Commute g σ) :
    ∃ g' : Fin m → Fin m, ∀ k, g (i k) = i (g' k) := by
  have h : ∀ k, ∃ l, g (i k) = i l := fun k => by
    obtain ⟨l, hl⟩ := hr (g (i k)) (by
      have := DFunLike.congr_fun hg.eq (i k)
      simp only [Perm.mul_apply, hi] at this
      exact this.symm)
    exact ⟨l, hl.symm⟩
  exact ⟨fun k => (h k).choose, fun k => (h k).choose_spec⟩

theorem finTwo_core : ∀ f g : Fin 2 → Fin 2, (∀ k, f k ≠ k) → (∀ k, g k ≠ k) →
    (∀ k, f (g k) ≠ k) → False := by
  decide

theorem finThree_core : ∀ f g : Fin 3 → Fin 3, (∀ k, f (f k) = k) → (∀ k, g (g k) = k) →
    (∀ k l, f k = k → f l = l → k = l) → (∀ k l, g k = k → g l = l → k = l) →
    (∀ k, f (g (f (g k))) = k) → (∀ k l, f (g k) = k → f (g l) = l → k = l) → False := by
  decide

theorem no_two_four_of_commuting {n : ℕ} (hn : n = 8 ∨ n = 9) {σ α β : Perm (Fin n)}
    (hσ : σ.cycleType = {2, 2, 2}) (hα : α.cycleType = {2, 2, 2, 2})
    (hβ : β.cycleType = {2, 2, 2, 2}) (hαβ : (α * β).cycleType = {2, 2, 2, 2})
    (h₁ : Commute α σ) (h₂ : Commute β σ) : False := by
  rcases hn with rfl | rfl
  · obtain ⟨i, hinj, hi, hr⟩ := exists_fixedPoint_enum (m := 2) rfl hσ
    obtain ⟨f, hf⟩ := exists_restrict_fixedPoint_enum hi hr h₁
    obtain ⟨g, hg⟩ := exists_restrict_fixedPoint_enum hi hr h₂
    refine finTwo_core f g (fun k hk => ?_) (fun k hk => ?_) (fun k hk => ?_)
    · exact ne_self_of_cycleType_two_four hα (i k) (by rw [hf, hk])
    · exact ne_self_of_cycleType_two_four hβ (i k) (by rw [hg, hk])
    · exact ne_self_of_cycleType_two_four hαβ (i k) (by rw [Perm.mul_apply, hg, hf, hk])
  · obtain ⟨i, hinj, hi, hr⟩ := exists_fixedPoint_enum (m := 3) rfl hσ
    obtain ⟨f, hf⟩ := exists_restrict_fixedPoint_enum hi hr h₁
    obtain ⟨g, hg⟩ := exists_restrict_fixedPoint_enum hi hr h₂
    refine finThree_core f g (fun k => ?_) (fun k => ?_) (fun k l hk hl => ?_)
      (fun k l hk hl => ?_) (fun k => ?_) (fun k l hk hl => ?_)
    · apply hinj
      rw [← hf, ← hf, apply_apply_of_cycleType_two_four hα]
    · apply hinj
      rw [← hg, ← hg, apply_apply_of_cycleType_two_four hβ]
    · exact hinj (fixed_unique_of_cycleType_two_four hα (by rw [hf, hk]) (by rw [hf, hl]))
    · exact hinj (fixed_unique_of_cycleType_two_four hβ (by rw [hg, hk]) (by rw [hg, hl]))
    · apply hinj
      have := apply_apply_of_cycleType_two_four hαβ (i k)
      simp only [Perm.mul_apply] at this
      rw [← hf, ← hg, ← hf, ← hg]
      exact this
    · exact hinj (fixed_unique_of_cycleType_two_four hαβ
        (by rw [Perm.mul_apply, hg, hf, hk]) (by rw [Perm.mul_apply, hg, hf, hl]))

end CFSG.GH74.GLS.Stage1.Thm4.L96
