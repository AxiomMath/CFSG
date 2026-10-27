module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33K

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

theorem card_support_eq_four_of_mem_alternatingGroup_seven {φ : Perm (Fin 7)}
    (hφA : φ ∈ alternatingGroup (Fin 7)) (hφ2 : φ * φ = 1) (hφ1 : φ ≠ 1) :
    φ.support.card = 4 := by
  classical
  have hcyc : ∀ k ∈ φ.cycleType, k = 2 := by
    intro k hk
    have h1 := Perm.two_le_of_mem_cycleType hk
    have h2 := Perm.dvd_of_mem_cycleType hk
    have h3 : orderOf φ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hφ2)
    have h4 := Nat.le_of_dvd (by norm_num) (h2.trans h3)
    omega
  have hrep : φ.cycleType = Multiset.replicate (Multiset.card φ.cycleType) 2 :=
    Multiset.eq_replicate_card.mpr hcyc
  have hsum : φ.support.card = 2 * Multiset.card φ.cycleType := by
    rw [← Perm.sum_cycleType]
    conv_lhs => rw [hrep]
    rw [Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hsign := Perm.sign_of_cycleType φ
  rw [Perm.mem_alternatingGroup.mp hφA, Perm.sum_cycleType, hsum] at hsign
  have hle : φ.support.card ≤ 7 := by simpa using φ.support.card_le_univ
  have h4 := four_le_card_support_of_mem_alternatingGroup hφA hφ2 hφ1
  set c := Multiset.card φ.cycleType with hc
  have hc3 : c = 2 ∨ c = 3 := by omega
  rcases hc3 with h | h
  · omega
  · exfalso
    rw [h] at hsign
    have h9 := congrArg Units.val hsign
    norm_num at h9

theorem exists_sqrt_of_card_support_four {α : Type*} [Fintype α] [DecidableEq α]
    {φ : Perm α} (hφ2 : φ * φ = 1) (h4 : φ.support.card = 4) :
    ∃ σ : Perm α, σ * σ = φ ∧ Perm.sign σ = -1 ∧ ∀ x, σ x ≠ x → φ x ≠ x := by
  classical
  have hφφ : ∀ x, φ (φ x) = x := fun x => by rw [← Perm.mul_apply, hφ2, Perm.one_apply]
  obtain ⟨p, hp⟩ : φ.support.Nonempty := by rw [← Finset.card_pos, h4]; norm_num
  have hpp : φ p ≠ p := Perm.mem_support.mp hp
  have hp's : φ p ∈ φ.support := Perm.mem_support.mpr (by rw [hφφ]; exact hpp.symm)
  have hcard : 0 < ((φ.support.erase p).erase (φ p)).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hpp, hp's⟩),
      Finset.card_erase_of_mem hp, h4]
    norm_num
  obtain ⟨r, hr⟩ := Finset.card_pos.mp hcard
  simp only [Finset.mem_erase] at hr
  obtain ⟨hrp', hrp, hrs⟩ := hr
  have hrr : φ r ≠ r := Perm.mem_support.mp hrs
  have hr'p : φ r ≠ p := fun h => hrp' (by rw [← h, hφφ])
  have hr'p' : φ r ≠ φ p := fun h => hrp (φ.injective h)
  have hsub : ({p, φ p, r, φ r} : Finset α) ⊆ φ.support := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hp
    · exact hp's
    · exact hrs
    · exact Perm.mem_support.mpr (by rw [hφφ]; exact hrr.symm)
  have hcard4 : ({p, φ p, r, φ r} : Finset α).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_pair_eq_two_iff.mpr (Ne.symm hrr)]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hrp', Ne.symm hr'p'⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hpp.symm, Ne.symm hrp, Ne.symm hr'p⟩
  have hsupp : φ.support = {p, φ p, r, φ r} :=
    (Finset.eq_of_subset_of_card_le hsub (by rw [h4, hcard4])).symm
  have hfix : ∀ x, x ≠ p → x ≠ φ p → x ≠ r → x ≠ φ r → φ x = x := by
    intro x h1 h2 h3 h4
    by_contra hx
    have hx' : x ∈ φ.support := Perm.mem_support.mpr hx
    rw [hsupp] at hx'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
    rcases hx' with h | h | h | h
    · exact h1 h
    · exact h2 h
    · exact h3 h
    · exact h4 h
  set σ := swap p r * swap r (φ p) * swap (φ p) (φ r) with hσdef
  have hσp : σ p = r := by
    rw [hσdef, Perm.mul_apply, Perm.mul_apply, swap_apply_of_ne_of_ne hpp.symm hr'p.symm,
      swap_apply_of_ne_of_ne hrp.symm hpp.symm, swap_apply_left]
  have hσr : σ r = φ p := by
    rw [hσdef, Perm.mul_apply, Perm.mul_apply, swap_apply_of_ne_of_ne hrp' hrr.symm,
      swap_apply_left, swap_apply_of_ne_of_ne hpp hrp'.symm]
  have hσp' : σ (φ p) = φ r := by
    rw [hσdef, Perm.mul_apply, Perm.mul_apply, swap_apply_left,
      swap_apply_of_ne_of_ne hrr hr'p', swap_apply_of_ne_of_ne hr'p hrr]
  have hσr' : σ (φ r) = p := by
    rw [hσdef, Perm.mul_apply, Perm.mul_apply, swap_apply_right, swap_apply_right,
      swap_apply_right]
  have hσx : ∀ x, x ≠ p → x ≠ φ p → x ≠ r → x ≠ φ r → σ x = x := by
    intro x h1 h2 h3 h4
    rw [hσdef, Perm.mul_apply, Perm.mul_apply, swap_apply_of_ne_of_ne h2 h4,
      swap_apply_of_ne_of_ne h3 h2, swap_apply_of_ne_of_ne h1 h3]
  refine ⟨σ, ?_, ?_, ?_⟩
  · ext x
    rw [Perm.mul_apply]
    by_cases hxp : x = p
    · rw [hxp, hσp, hσr]
    by_cases hxp' : x = φ p
    · rw [hxp', hσp', hσr', hφφ]
    by_cases hxr : x = r
    · rw [hxr, hσr, hσp']
    by_cases hxr' : x = φ r
    · rw [hxr', hσr', hσp, hφφ]
    rw [hσx x hxp hxp' hxr hxr', hσx x hxp hxp' hxr hxr', hfix x hxp hxp' hxr hxr']
  · rw [hσdef, Perm.sign_mul, Perm.sign_mul, Perm.sign_swap hrp.symm, Perm.sign_swap hrp',
      Perm.sign_swap hr'p'.symm]
    decide
  · intro x hx hφx
    apply hx
    have hxs : x ∉ φ.support := Perm.notMem_support.mpr hφx
    rw [hsupp] at hxs
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hxs
    obtain ⟨h1, h2, h3, h4⟩ := hxs
    exact hσx x h1 h2 h3 h4

theorem commute_of_odd_of_commute_seven {φ : Perm (Fin 7)} (hφA : φ ∈ alternatingGroup (Fin 7))
    (hφ2 : φ * φ = 1) (hφ1 : φ ≠ 1) {P : Subgroup (Perm (Fin 7))} (hodd : Odd (Nat.card P))
    (hc : ∀ g ∈ P, g * φ = φ * g) {a b : Perm (Fin 7)} (ha : a ∈ P) (hb : b ∈ P) :
    a * b = b * a := by
  classical
  have h4 := card_support_eq_four_of_mem_alternatingGroup_seven hφA hφ2 hφ1
  have hfix : ∀ g ∈ P, ∀ x ∈ φ.support, g x = x := by
    intro g hg x hx
    have hog : Odd (orderOf g) := hodd.of_dvd_nat (by
      rw [← Subgroup.orderOf_mk g hg]
      exact orderOf_dvd_natCard _)
    exact apply_eq_of_odd_commute hφ2 h4.le (hc g hg) hog hx
  set p : Fin 7 → Prop := fun x => x ∉ φ.support with hpdef
  have hP : P ≤ (Perm.ofSubtype : Perm (Subtype p) →* Perm (Fin 7)).range := by
    intro g hg
    have h₁ : ∀ x, p (g x) ↔ p x := by
      intro x
      simp only [hpdef]
      constructor
      · intro h hx
        exact h (by rw [hfix g hg x hx]; exact hx)
      · intro h hgx
        apply h
        have h5 := hfix g hg (g x) hgx
        rw [g.injective h5] at hgx
        exact hgx
    have h₂ : ∀ x, g x ≠ x → p x := fun x hx hxs => hx (hfix g hg x hxs)
    exact ⟨_, Perm.ofSubtype_subtypePerm h₁ h₂⟩
  have hc3 : Nat.card (Subtype p) = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have h6 : (Finset.univ.filter p) = φ.supportᶜ := by
      ext x
      simp [hpdef]
    rw [h6, Finset.card_compl, Fintype.card_fin, h4]
  have hcard : Nat.card (Perm.ofSubtype : Perm (Subtype p) →* Perm (Fin 7)).range = 6 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective Perm.ofSubtype_injective).toEquiv,
      Nat.card_perm, hc3]
    rfl
  have hdvd : Nat.card P ∣ 6 := hcard ▸ card_dvd_of_le hP
  have h13 : Nat.card P = 1 ∨ Nat.card P = 3 := by
    have h7 : Nat.card P ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    obtain ⟨k, hk⟩ := hodd
    rcases (show Nat.card P = 1 ∨ Nat.card P = 3 ∨ Nat.card P = 5 by omega) with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · rw [h] at hdvd
      norm_num at hdvd
  rcases h13 with h | h
  · have hPb : P = ⊥ := Subgroup.eq_bot_of_card_eq P h
    rw [hPb, mem_bot] at ha hb
    rw [ha, hb]
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcyc : IsCyclic P := isCyclic_of_prime_card h
    exact congrArg Subtype.val
      ((IsCyclic.isMulCommutative (α := P)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem exists_sq_eq_not_commute {φ a : Perm (Fin 7)} (hφA : φ ∈ alternatingGroup (Fin 7))
    (hφ2 : φ * φ = 1) (hφ1 : φ ≠ 1) (ha1 : a ≠ 1) (hodd : Odd (orderOf a))
    (hac : a * φ = φ * a) :
    ∃ g ∈ alternatingGroup (Fin 7), g * g = φ ∧ g * a ≠ a * g := by
  classical
  have h4 := card_support_eq_four_of_mem_alternatingGroup_seven hφA hφ2 hφ1
  have hfix : ∀ x ∈ φ.support, a x = x := fun x hx =>
    apply_eq_of_odd_commute hφ2 h4.le hac hodd hx
  obtain ⟨σ, hσσ, hσs, hσsupp⟩ := exists_sqrt_of_card_support_four hφ2 h4
  obtain ⟨q, hq⟩ : ∃ q, a q ≠ q := by
    by_contra h
    push Not at h
    exact ha1 (Equiv.ext h)
  have hqF : q ∉ φ.support := fun hqs => hq (hfix q hqs)
  have haqF : a q ∉ φ.support := fun h => hq (a.injective (hfix (a q) h))
  have hσq : σ q = q := by
    by_contra h
    exact hqF (Perm.mem_support.mpr (hσsupp q h))
  have hσaq : σ (a q) = a q := by
    by_contra h
    exact haqF (Perm.mem_support.mpr (hσsupp _ h))
  have hστ : σ * swap q (a q) = swap q (a q) * σ := by
    have hd : Perm.Disjoint σ (swap q (a q)) := by
      intro x
      by_cases hx : x = q ∨ x = a q
      · left
        rcases hx with rfl | rfl
        · exact hσq
        · exact hσaq
      · right
        push Not at hx
        exact swap_apply_of_ne_of_ne hx.1 hx.2
    exact hd.commute.eq
  refine ⟨σ * swap q (a q), ?_, ?_, ?_⟩
  · rw [Perm.mem_alternatingGroup, Perm.sign_mul, hσs, Perm.sign_swap (Ne.symm hq)]
    decide
  · calc σ * swap q (a q) * (σ * swap q (a q)) = σ * σ * (swap q (a q) * swap q (a q)) := by
          rw [mul_assoc, ← mul_assoc (swap q (a q)) σ, ← hστ]
          group
      _ = φ := by rw [hσσ, swap_mul_self, mul_one]
  · intro hc
    have h1 := congrArg (fun f => f q) hc
    simp only [Perm.mul_apply, swap_apply_left, swap_apply_right] at h1
    rw [hσq, hσaq] at h1
    obtain ⟨k, hk⟩ := hodd
    have h2 : ∀ j : ℕ, (a ^ (2 * j)) q = q := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [show 2 * (j + 1) = 2 + 2 * j by ring, pow_add, Perm.mul_apply, ih, sq,
          Perm.mul_apply]
        exact h1.symm
    have h3 : a ^ (2 * (k + 1)) = a := by
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, ← hk, pow_orderOf_eq_one,
        one_mul]
    exact hq (by rw [← h3]; exact h2 (k + 1))

end CFSG.ComponentClassification.SolMax
