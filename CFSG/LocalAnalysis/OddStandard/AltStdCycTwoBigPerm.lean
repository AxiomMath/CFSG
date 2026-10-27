module

public import CFSG.LocalAnalysis.OddStandard.AltStdBalPermCenter

public section

namespace CFSG.OddStandard.AltStdCycTwo

open Equiv Equiv.Perm AltStdBal

section Helpers

variable {α : Type*} [DecidableEq α]

private theorem false_of_sq_eq_one_mem {V : Subgroup (Perm α)} (hV : Odd (Nat.card V))
    {g : Perm α} (hg : g ∈ V) (h1 : g ≠ 1) (h2 : g ^ 2 = 1) : False := by
  have hd := V.orderOf_dvd_natCard hg
  rw [orderOf_eq_prime h2 h1] at hd
  obtain ⟨m, hm⟩ := hV
  omega

private theorem false_of_swap_mul_swap_mem {V : Subgroup (Perm α)} (hV : Odd (Nat.card V))
    {p q r s : α} (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s)
    (h : swap p q * swap r s ∈ V) : False := by
  refine false_of_sq_eq_one_mem hV h (fun h1 => hpq ?_) ?_
  · have h2 := Equiv.congr_fun h1 p
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hpr hps, swap_apply_left, Perm.one_apply] at h2
    exact h2.symm
  · ext y
    simp only [pow_two, Perm.mul_apply, swap_apply_def, Perm.one_apply]
    grind

private theorem comm_swap_mul_swap (c : Perm α) (a b d e : α) :
    c * (swap a b * swap d e) * c⁻¹ * (swap a b * swap d e)⁻¹ =
      swap (c a) (c b) * swap (c d) (c e) * (swap d e * swap a b) := by
  rw [swap_apply_apply, swap_apply_apply, mul_inv_rev, swap_inv, swap_inv]
  simp only [mul_assoc, inv_mul_cancel_left]

private theorem swap_mul_swap_sq {a b d : α} (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    (swap a d * swap d b) ^ 2 = swap a b * swap b d := by
  ext y
  simp only [pow_two, Perm.mul_apply, swap_apply_def]
  grind

private theorem three_cycle_mul_three_cycle {u u' w₁ w₂ : α} (h1 : u ≠ u') (h2 : u ≠ w₁)
    (h3 : u ≠ w₂) (h4 : u' ≠ w₁) (h5 : u' ≠ w₂) (h6 : w₁ ≠ w₂) :
    swap u' w₁ * swap u w₁ * (swap u' w₂ * swap u w₂) = swap u w₁ * swap u' w₂ := by
  ext y
  simp only [Perm.mul_apply, swap_apply_def]
  grind

private theorem swap_mul_swap_comm {σ : Perm α} {a b d e : α}
    (h1 : σ * swap a b = swap a b * σ) (h2 : σ * swap d e = swap d e * σ) :
    swap a b * swap d e * σ = σ * (swap a b * swap d e) := by
  rw [mul_assoc, ← h2, ← mul_assoc, ← h1, mul_assoc]

private theorem swap_orbit {σ : Perm α} (hσσ : ∀ y, σ (σ y) = y) (a y : α) :
    swap a (σ a) y = y ∨ swap a (σ a) y = σ y := by
  rw [swap_apply_def]
  split_ifs with h1 h2
  · exact Or.inr (by rw [h1])
  · exact Or.inr (by rw [h2, hσσ])
  · exact Or.inl rfl

private theorem orbit_mul {σ f g : Perm α} (hσσ : ∀ y, σ (σ y) = y)
    (hf : ∀ y, f y = y ∨ f y = σ y) (hg : ∀ y, g y = y ∨ g y = σ y) (y : α) :
    (f * g) y = y ∨ (f * g) y = σ y := by
  rw [Perm.mul_apply]
  rcases hg y with h | h <;> rcases hf (g y) with h' | h' <;> rw [h', h]
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · exact Or.inl (hσσ y)

private theorem orbit_sq {σ g : Perm α} (hσσ : ∀ y, σ (σ y) = y)
    (hg : ∀ y, g y = y ∨ g y = σ y) : g ^ 2 = 1 := by
  ext y
  rw [pow_two, Perm.mul_apply, Perm.one_apply]
  rcases hg y with h | h
  · rw [h, h]
  · rcases hg (σ y) with h' | h'
    · rw [h, h']
      exact (g.injective (h.trans h'.symm)).symm
    · rw [h, h', hσσ]

variable [Fintype α]

private theorem exists_not_mem_list (l : List α) (h : l.length < Fintype.card α) :
    ∃ y, y ∉ l := by
  by_contra hne
  push Not at hne
  have h1 : (Finset.univ : Finset α).card ≤ l.toFinset.card :=
    Finset.card_le_card (by intro y _; exact List.mem_toFinset.mpr (hne y))
  rw [Finset.card_univ] at h1
  have h2 := List.toFinset_card_le l
  omega

private theorem comm_three_cycle_mem {σ c : Perm α} {V : Subgroup (Perm α)}
    (hsq : ∀ D ∈ alternatingGroup α, D * σ = σ * D → c * D ^ 2 * c⁻¹ * (D ^ 2)⁻¹ ∈ V)
    {a b d : α} (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) (ha : σ a = a) (hb : σ b = b)
    (hd : σ d = d) : swap (c a) (c b) * swap (c b) (c d) * (swap b d * swap a b) ∈ V := by
  have hDA : swap a d * swap d b ∈ alternatingGroup α := by
    rw [mem_alternatingGroup, Perm.sign_mul, sign_swap had, sign_swap hbd.symm]
    decide
  have h := hsq _ hDA (swap_mul_swap_comm (permC_swap_comm (Or.inl ⟨ha, hd⟩))
    (permC_swap_comm (Or.inl ⟨hd, hb⟩)))
  rwa [swap_mul_swap_sq hab had hbd, comm_swap_mul_swap] at h

private theorem false_of_moved_outside (hα : 8 ≤ Fintype.card α) {c σ : Perm α}
    (hσσ : ∀ y, σ (σ y) = y) (hcc : ∀ y, c (c y) = σ y) (hcσ : ∀ y, c (σ y) = σ (c y))
    {V : Subgroup (Perm α)} (hV : Odd (Nat.card V))
    (hsq : ∀ D ∈ alternatingGroup α, D * σ = σ * D → c * D ^ 2 * c⁻¹ * (D ^ 2)⁻¹ ∈ V)
    {x r : α} (hx : σ x ≠ x) (hr : σ r ≠ r) (hrx : r ≠ x) (hrcx : r ≠ c x) (hrσx : r ≠ σ x)
    (hrσcx : r ≠ σ (c x)) : False := by
  have hcx : c x ≠ x := fun h => hx (by rw [← hcc x, h, h])
  have hcxσ : c x ≠ σ x := fun h => hx (by rw [← hcc x, h, hcσ, h, hσσ])
  have hxσr : x ≠ σ r := fun h => hrσx (by rw [h, hσσ])
  have hσxσr : σ x ≠ σ r := fun h => hrx (σ.injective h).symm
  obtain ⟨D, hD1, hDσ, hD2⟩ := permC_exists_sq_dswap hα hσσ (p := x) (q := σ x) (r := r)
    (s := σ r) rfl rfl hx.symm hrx.symm hxσr hrσx.symm hσxσr hr.symm
  have h := hsq D (mem_alternatingGroup.mpr hD1) hDσ
  rw [hD2, comm_swap_mul_swap, hcσ x, hcσ r] at h
  have h3 : σ x ≠ c r := fun h => hrcx (c.injective (by rw [hcc x]; exact h.symm))
  have h4 : σ x ≠ σ (c r) := fun h =>
    hrσcx (c.injective (by rw [hcσ, hcc, hσσ]; exact (σ.injective h).symm))
  have h5 : σ x ≠ σ (c x) := fun h => hcx (σ.injective h).symm
  refine false_of_sq_eq_one_mem hV h (fun h1 => hx ?_) (orbit_sq hσσ (orbit_mul hσσ
    (orbit_mul hσσ (swap_orbit hσσ _) (swap_orbit hσσ _))
    (orbit_mul hσσ (swap_orbit hσσ _) (swap_orbit hσσ _))))
  have h2 := Equiv.congr_fun h1 x
  simp only [Perm.mul_apply, Perm.one_apply, swap_apply_left] at h2
  rwa [swap_apply_of_ne_of_ne hrσx.symm hσxσr, swap_apply_of_ne_of_ne h3 h4,
    swap_apply_of_ne_of_ne hcxσ.symm h5] at h2

private theorem false_of_fixed_outside (hα : 9 ≤ Fintype.card α) {c σ : Perm α}
    (hσσ : ∀ y, σ (σ y) = y) (hcc : ∀ y, c (c y) = σ y) (hcσ : ∀ y, c (σ y) = σ (c y))
    {V : Subgroup (Perm α)} (hV : Odd (Nat.card V))
    (hsq : ∀ D ∈ alternatingGroup α, D * σ = σ * D → c * D ^ 2 * c⁻¹ * (D ^ 2)⁻¹ ∈ V)
    (hcomm : (∀ D ∈ alternatingGroup α, D * σ = σ * D → c * D * c⁻¹ * D⁻¹ ∈ V) ∨ sign c = 1)
    {x : α} (hx : σ x ≠ x)
    (hfix : ∀ y, y ≠ x → y ≠ c x → y ≠ σ x → y ≠ σ (c x) → σ y = y) : False := by
  have hcx : c x ≠ x := fun h => hx (by rw [← hcc x, h, h])
  have hcxσ : c x ≠ σ x := fun h => hx (by rw [← hcc x, h, hcσ, h, hσσ])
  have hcxσcx : c x ≠ σ (c x) := fun h => hx (c.injective (by rw [hcσ]; exact h.symm))
  have hσcxx : σ (c x) ≠ x := fun h => hcxσ (by rw [← hσσ (c x), h])
  have hσcxσx : σ (c x) ≠ σ x := fun h => hcx (σ.injective h)
  by_cases hu : ∃ u, σ u = u ∧ c u ≠ u
  · obtain ⟨u, hσu, hcu⟩ := hu
    by_cases hw : ∃ w, σ w = w ∧ w ≠ u ∧ w ≠ c u ∧ c w ≠ w
    ·
      obtain ⟨w, hσw, hwu, hwcu, hcw⟩ := hw
      have h := comm_three_cycle_mem hsq (a := u) (b := c w) (d := w)
        (fun h => hwcu (by rw [h, hcc, hσw])) hwu.symm hcw hσu (by rw [← hcσ, hσw]) hσw
      rw [hcc w, hσw, swap_comm (c w) w, mul_assoc, swap_mul_self_mul] at h
      exact false_of_swap_mul_swap_mem hV hwcu.symm hcu (fun h => hwu (c.injective h).symm) hwu
        hcw.symm h
    ·
      push Not at hw
      obtain ⟨w₁, hw₁⟩ := exists_not_mem_list [x, c x, σ x, σ (c x), u, c u]
        (by simp only [List.length_cons, List.length_nil]; omega)
      obtain ⟨w₂, hw₂⟩ := exists_not_mem_list [x, c x, σ x, σ (c x), u, c u, w₁]
        (by simp only [List.length_cons, List.length_nil]; omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hw₁ hw₂
      obtain ⟨h1x, h1cx, h1σx, h1σcx, h1u, h1cu⟩ := hw₁
      obtain ⟨h2x, h2cx, h2σx, h2σcx, h2u, h2cu, h21⟩ := hw₂
      have hσ1 := hfix w₁ h1x h1cx h1σx h1σcx
      have hσ2 := hfix w₂ h2x h2cx h2σx h2σcx
      have hc1 := hw w₁ hσ1 h1u h1cu
      have hc2 := hw w₂ hσ2 h2u h2cu
      have g1 := comm_three_cycle_mem hsq (a := u) (b := w₁) (d := w₂) (Ne.symm h1u)
        (Ne.symm h2u) (Ne.symm h21) hσu hσ1 hσ2
      have g2 := comm_three_cycle_mem hsq (a := u) (b := w₂) (d := w₁) (Ne.symm h2u)
        (Ne.symm h1u) h21 hσu hσ2 hσ1
      rw [hc1, hc2, mul_assoc, swap_mul_self_mul] at g1 g2
      have h := V.mul_mem g1 g2
      rw [three_cycle_mul_three_cycle (Ne.symm hcu) (Ne.symm h1u) (Ne.symm h2u) (Ne.symm h1cu)
        (Ne.symm h2cu) (Ne.symm h21)] at h
      exact false_of_swap_mul_swap_mem hV (Ne.symm h1u) (Ne.symm hcu) (Ne.symm h2u) h1cu
        (Ne.symm h21) h
  · push Not at hu
    rcases hcomm with h1 | hs
    ·
      obtain ⟨t, ht⟩ := exists_not_mem_list [x, c x, σ x, σ (c x)]
        (by simp only [List.length_cons, List.length_nil]; omega)
      obtain ⟨v, hv⟩ := exists_not_mem_list [x, c x, σ x, σ (c x), t]
        (by simp only [List.length_cons, List.length_nil]; omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ht hv
      obtain ⟨htx, htcx, htσx, htσcx⟩ := ht
      obtain ⟨hvx, hvcx, hvσx, hvσcx, hvt⟩ := hv
      have hσt := hfix t htx htcx htσx htσcx
      have hσv := hfix v hvx hvcx hvσx hvσcx
      have hDA : swap x (σ x) * swap t v ∈ alternatingGroup α := by
        rw [mem_alternatingGroup, Perm.sign_mul, sign_swap hx.symm, sign_swap (Ne.symm hvt)]
        decide
      have h := h1 _ hDA (swap_mul_swap_comm
        (permC_swap_comm (S := σ) (a := x) (b := σ x) (Or.inr ⟨rfl, hσσ x⟩))
        (permC_swap_comm (Or.inl ⟨hσt, hσv⟩)))
      rw [comm_swap_mul_swap, hu t hσt, hu v hσv, hcσ x, mul_assoc, swap_mul_self_mul] at h
      exact false_of_swap_mul_swap_mem hV hcxσcx hcx hcxσ hσcxx hσcxσx h
    ·
      obtain ⟨γ, hγ0, hγ1, hγ2, hγ3, hγo, hγsign⟩ := permC_exists_cyc4 (a := x) (b := c x)
        (c := σ x) (d := σ (c x)) hcx.symm hx.symm hσcxx.symm hcxσ hcxσcx (Ne.symm hσcxσx)
      have hcγ : c = γ := by
        ext y
        by_cases hy : y = x ∨ y = c x ∨ y = σ x ∨ y = σ (c x)
        · rcases hy with rfl | rfl | rfl | rfl
          · rw [hγ0]
          · rw [hcc, hγ1]
          · rw [hcσ, hγ2]
          · rw [hcσ, hcc, hσσ, hγ3]
        · push Not at hy
          rw [hu y (hfix y hy.1 hy.2.1 hy.2.2.1 hy.2.2.2), hγo y hy.1 hy.2.1 hy.2.2.1 hy.2.2.2]
      rw [hcγ, hγsign] at hs
      exact absurd hs (by decide)

end Helpers

theorem no_sq_root_mod_odd' {α : Type*} [Fintype α] [DecidableEq α] (hα : 9 ≤ Fintype.card α)
    {c σ : Equiv.Perm α} (hc : c ^ 2 = σ) (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1)
    (V : Subgroup (Equiv.Perm α)) (hV : Odd (Nat.card V))
    (hcomm : (∀ D ∈ alternatingGroup α, D * σ = σ * D → c * D * c⁻¹ * D⁻¹ ∈ V) ∨
      (Equiv.Perm.sign c = 1 ∧ ∀ D ∈ alternatingGroup α, D * σ = σ * D →
        c * D ^ 2 * c⁻¹ * (D ^ 2)⁻¹ ∈ V)) : False := by
  have hσσ : ∀ y, σ (σ y) = y := fun y => by
    rw [← Perm.mul_apply, ← pow_two, hσ2, Perm.one_apply]
  have hcc : ∀ y, c (c y) = σ y := fun y => by rw [← Perm.mul_apply, ← pow_two, hc]
  have hcσ : ∀ y, c (σ y) = σ (c y) := fun y => by rw [← hcc y, ← hcc (c y)]
  have hsq : ∀ D ∈ alternatingGroup α, D * σ = σ * D → c * D ^ 2 * c⁻¹ * (D ^ 2)⁻¹ ∈ V := by
    intro D hD hDσ
    rcases hcomm with h | h
    · exact h _ (pow_mem hD 2) ((show Commute D σ from hDσ).pow_left 2).eq
    · exact h.2 D hD hDσ
  obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
    by_contra h
    push Not at h
    exact hσ1 (Equiv.ext fun y => by rw [h y, Perm.one_apply])
  by_cases hA : ∃ r, σ r ≠ r ∧ r ≠ x ∧ r ≠ c x ∧ r ≠ σ x ∧ r ≠ σ (c x)
  · obtain ⟨r, hr, h1, h2, h3, h4⟩ := hA
    exact false_of_moved_outside (by omega) hσσ hcc hcσ hV hsq hx hr h1 h2 h3 h4
  · push Not at hA
    exact false_of_fixed_outside hα hσσ hcc hcσ hV hsq (hcomm.imp id And.left) hx
      fun y h1 h2 h3 h4 => by
        by_contra h
        exact h4 (hA y h h1 h2 h3)

end CFSG.OddStandard.AltStdCycTwo
