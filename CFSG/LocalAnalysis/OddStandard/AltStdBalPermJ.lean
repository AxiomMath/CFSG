module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.OddStandard.AltStdBal

open Subgroup Equiv

section Swaps

variable {α : Type*} [DecidableEq α]

theorem permJ_commute_swap_of_swapped {Y : Perm α} {p q : α} (hp : Y p = q) (hq : Y q = p) :
    Commute Y (swap p q) := by
  show Y * swap p q = swap p q * Y
  rw [mul_swap_eq_swap_mul, hp, hq, swap_comm]

theorem permJ_commute_swap_of_fixed {Y : Perm α} {p q : α} (hp : Y p = p) (hq : Y q = q) :
    Commute Y (swap p q) := by
  show Y * swap p q = swap p q * Y
  rw [mul_swap_eq_swap_mul, hp, hq]

theorem permJ_swap_mul_swap_comm {p q r s : α} (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r)
    (hqs : q ≠ s) : swap p q * swap r s = swap r s * swap p q := by
  ext x
  simp only [Equiv.Perm.mul_apply, swap_apply_def]
  grind

theorem permJ_commute_swap_mul_swap {Y : Perm α} {a b c d : α}
    (hdisj : swap a b * swap c d = swap c d * swap a b) (ha : Y a = c) (hb : Y b = d)
    (hc : Y c = a) (hd : Y d = b) : Commute Y (swap a b * swap c d) := by
  show Y * (swap a b * swap c d) = swap a b * swap c d * Y
  calc Y * (swap a b * swap c d) = Y * swap a b * swap c d := (mul_assoc _ _ _).symm
    _ = swap c d * Y * swap c d := by rw [mul_swap_eq_swap_mul Y a b, ha, hb]
    _ = swap c d * (Y * swap c d) := mul_assoc _ _ _
    _ = swap c d * (swap a b * Y) := by rw [mul_swap_eq_swap_mul Y c d, hc, hd]
    _ = swap c d * swap a b * Y := (mul_assoc _ _ _).symm
    _ = swap a b * swap c d * Y := by rw [hdisj]

theorem permJ_commutator_eq {p q r s t v : α} (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) (htp : t ≠ p) (htq : t ≠ q) (htr : t ≠ r)
    (hts : t ≠ s) (hvp : v ≠ p) (hvq : v ≠ q) (hvr : v ≠ r) (hvs : v ≠ s) :
    (swap p q * swap t v) * (swap p r * swap q s) * (swap p q * swap t v)⁻¹ *
      (swap p r * swap q s)⁻¹ = swap p q * swap r s := by
  ext x
  simp only [mul_inv_rev, swap_inv, Equiv.Perm.mul_apply, swap_apply_def]
  grind

end Swaps

section Reduction

variable {α : Type*} [Fintype α] [DecidableEq α]

def permJ_subgroup (y : alternatingGroup α) : Subgroup (Perm α) :=
  (⁅centralizer ({y} : Set (alternatingGroup α)),
    centralizer ({y} : Set (alternatingGroup α))⁆).map (alternatingGroup α).subtype

theorem permJ_commutator_mem {y : alternatingGroup α} {a b : Perm α}
    (ha : a ∈ alternatingGroup α) (hb : b ∈ alternatingGroup α)
    (hay : Commute (y : Perm α) a) (hby : Commute (y : Perm α) b) :
    a * b * a⁻¹ * b⁻¹ ∈ permJ_subgroup y := by
  have hA : (⟨a, ha⟩ : alternatingGroup α) ∈ centralizer ({y} : Set (alternatingGroup α)) :=
    mem_centralizer_singleton_iff.2 (Subtype.ext hay.symm.eq)
  have hB : (⟨b, hb⟩ : alternatingGroup α) ∈ centralizer ({y} : Set (alternatingGroup α)) :=
    mem_centralizer_singleton_iff.2 (Subtype.ext hby.symm.eq)
  exact Subgroup.mem_map.2 ⟨_, commutator_mem_commutator hA hB, rfl⟩

theorem permJ_swap_mul_swap_mem {p q r s : α} (hpq : p ≠ q) (hrs : r ≠ s) :
    swap p q * swap r s ∈ alternatingGroup α := by
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hpq,
    Equiv.Perm.sign_swap hrs]
  decide

theorem permJ_exists_pair (hα : 8 ≤ Fintype.card α) {Y : Perm α} (hY : ∀ x, Y (Y x) = x)
    {p q r s : α} (hp : Y p = q) (hq : Y q = p) (hr : Y r = s) (hs : Y s = r) :
    ∃ t v : α, t ≠ v ∧ t ≠ p ∧ t ≠ q ∧ t ≠ r ∧ t ≠ s ∧ v ≠ p ∧ v ≠ q ∧ v ≠ r ∧ v ≠ s ∧
      ((Y t = v ∧ Y v = t) ∨ (Y t = t ∧ Y v = v)) := by
  by_cases h : ∃ t, t ≠ p ∧ t ≠ q ∧ t ≠ r ∧ t ≠ s ∧ Y t ≠ t
  · obtain ⟨t, htp, htq, htr, hts, htY⟩ := h
    have hYY := hY t
    refine ⟨t, Y t, fun h => htY h.symm, htp, htq, htr, hts, ?_, ?_, ?_, ?_,
      Or.inl ⟨rfl, hYY⟩⟩
    · intro h
      rw [h, hp] at hYY
      exact htq hYY.symm
    · intro h
      rw [h, hq] at hYY
      exact htp hYY.symm
    · intro h
      rw [h, hr] at hYY
      exact hts hYY.symm
    · intro h
      rw [h, hs] at hYY
      exact htr hYY.symm
  · push Not at h
    have h4 : ([p, q, r, s].toFinset).card < (Finset.univ : Finset α).card := by
      have := List.toFinset_card_le [p, q, r, s]
      have hl : ([p, q, r, s] : List α).length = 4 := rfl
      rw [Finset.card_univ]
      omega
    obtain ⟨t, -, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card h4
    have h5 : ([p, q, r, s, t].toFinset).card < (Finset.univ : Finset α).card := by
      have := List.toFinset_card_le [p, q, r, s, t]
      have hl : ([p, q, r, s, t] : List α).length = 5 := rfl
      rw [Finset.card_univ]
      omega
    obtain ⟨v, -, hv⟩ := Finset.exists_mem_notMem_of_card_lt_card h5
    simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false, not_or] at ht hv
    obtain ⟨htp, htq, htr, hts⟩ := ht
    obtain ⟨hvp, hvq, hvr, hvs, hvt⟩ := hv
    exact ⟨t, v, fun h => hvt h.symm, htp, htq, htr, hts, hvp, hvq, hvr, hvs,
      Or.inr ⟨h t htp htq htr hts, h v hvp hvq hvr hvs⟩⟩

theorem permJ_swap_swap_mem (hα : 8 ≤ Fintype.card α) {y : alternatingGroup α}
    (hY : ∀ x, (y : Perm α) ((y : Perm α) x) = x) {p q r s : α}
    (hp : (y : Perm α) p = q) (hq : (y : Perm α) q = p) (hr : (y : Perm α) r = s)
    (hs : (y : Perm α) s = r) (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r)
    (hqs : q ≠ s) (hrs : r ≠ s) : swap p q * swap r s ∈ permJ_subgroup y := by
  obtain ⟨t, v, htv, htp, htq, htr, hts, hvp, hvq, hvr, hvs, htv'⟩ :=
    permJ_exists_pair hα hY hp hq hr hs
  have hcomm_tv : Commute (y : Perm α) (swap t v) :=
    htv'.elim (fun h => permJ_commute_swap_of_swapped h.1 h.2)
      (fun h => permJ_commute_swap_of_fixed h.1 h.2)
  have ha : Commute (y : Perm α) (swap p q * swap t v) :=
    (permJ_commute_swap_of_swapped hp hq).mul_right hcomm_tv
  have hb : Commute (y : Perm α) (swap p r * swap q s) :=
    permJ_commute_swap_mul_swap (permJ_swap_mul_swap_comm hpq hps hqr.symm hrs) hp hr hq hs
  have key := permJ_commutator_mem (y := y) (permJ_swap_mul_swap_mem hpq htv)
    (permJ_swap_mul_swap_mem hpr hqs) ha hb
  rwa [permJ_commutator_eq hpq hpr hps hqr hqs hrs htp htq htr hts hvp hvq hvr hvs] at key

theorem permJ_exists_two_pairs {u : Perm α} (huu : ∀ x, u (u x) = x)
    (hus : u ∈ alternatingGroup α) (hu1 : u ≠ 1) :
    ∃ p r : α, u p ≠ p ∧ u r ≠ r ∧ r ≠ p ∧ r ≠ u p := by
  obtain ⟨p, hp⟩ : ∃ p, u p ≠ p := by
    by_contra hcon
    push Not at hcon
    exact hu1 (Equiv.ext hcon)
  by_cases hr : ∃ r, u r ≠ r ∧ r ≠ p ∧ r ≠ u p
  · obtain ⟨r, hr1, hr2, hr3⟩ := hr
    exact ⟨p, r, hp, hr1, hr2, hr3⟩
  · exfalso
    push Not at hr
    have hu : u = swap p (u p) := by
      ext x
      by_cases hxp : x = p
      · rw [hxp, swap_apply_left]
      · by_cases hxq : x = u p
        · rw [hxq, swap_apply_right, huu]
        · rw [swap_apply_of_ne_of_ne hxp hxq]
          by_contra hne
          exact hxq (hr x hne hxp)
    rw [Equiv.Perm.mem_alternatingGroup, hu, Equiv.Perm.sign_swap (Ne.symm hp)] at hus
    exact absurd hus (by decide)

theorem permJ_step (hα : 8 ≤ Fintype.card α) {y : alternatingGroup α}
    (hY : ∀ x, (y : Perm α) ((y : Perm α) x) = x) {n : ℕ}
    (ih : ∀ m < n, ∀ u : Perm α, u.support.card = m → (∀ x, u (u x) = x) →
      u ∈ alternatingGroup α → (∀ x, u x ≠ x → u x = (y : Perm α) x) → u ∈ permJ_subgroup y)
    {u : Perm α} (hn : u.support.card = n) (huu : ∀ x, u (u x) = x)
    (hus : u ∈ alternatingGroup α) (hdom : ∀ x, u x ≠ x → u x = (y : Perm α) x) {p r : α}
    (hp : u p ≠ p) (hr : u r ≠ r) (hrp : r ≠ p) (hrq : r ≠ u p) : u ∈ permJ_subgroup y := by
  obtain ⟨q, hq⟩ : ∃ q, u p = q := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, u r = s := ⟨_, rfl⟩
  rw [hq] at hrq
  have huq : u q = p := by rw [← hq]; exact huu p
  have hus' : u s = r := by rw [← hs]; exact huu r
  have hpq : p ≠ q := fun h => hp (hq.trans h.symm)
  have hrs : r ≠ s := fun h => hr (hs.trans h.symm)
  have hsp : s ≠ p := by
    intro h
    apply hrq
    have := huu r
    rw [hs, h, hq] at this
    exact this.symm
  have hsq : s ≠ q := by
    intro h
    apply hrp
    have := huu r
    rw [hs, h, huq] at this
    exact this.symm
  have hYp : (y : Perm α) p = q := by rw [← hdom p hp]; exact hq
  have hYq : (y : Perm α) q = p := by rw [← hYp]; exact hY p
  have hYr : (y : Perm α) r = s := by rw [← hdom r hr]; exact hs
  have hYs : (y : Perm α) s = r := by rw [← hYr]; exact hY r
  have hmem := permJ_swap_swap_mem hα hY hYp hYq hYr hYs hpq hrp.symm hsp.symm hrq.symm
    hsq.symm hrs
  obtain ⟨u', hu'⟩ : ∃ u' : Perm α, u' = swap p q * swap r s * u := ⟨_, rfl⟩
  have hu'x : ∀ x, u' x = swap p q (swap r s (u x)) := fun x => by subst hu'; rfl
  have hux : ∀ x, x ≠ p → x ≠ q → x ≠ r → x ≠ s →
      u x ≠ p ∧ u x ≠ q ∧ u x ≠ r ∧ u x ≠ s := by
    intro x hxp hxq hxr hxs
    have h := huu x
    refine ⟨fun hh => hxq ?_, fun hh => hxp ?_, fun hh => hxs ?_, fun hh => hxr ?_⟩
    · rw [hh, hq] at h
      exact h.symm
    · rw [hh, huq] at h
      exact h.symm
    · rw [hh, hs] at h
      exact h.symm
    · rw [hh, hus'] at h
      exact h.symm
  have hfp : u' p = p := by
    rw [hu'x, hq, swap_apply_of_ne_of_ne hrq.symm hsq.symm, swap_apply_right]
  have hfq : u' q = q := by
    rw [hu'x, huq, swap_apply_of_ne_of_ne hrp.symm hsp.symm, swap_apply_left]
  have hfr : u' r = r := by
    rw [hu'x, hs, swap_apply_right, swap_apply_of_ne_of_ne hrp hrq]
  have hfs : u' s = s := by
    rw [hu'x, hus', swap_apply_left, swap_apply_of_ne_of_ne hsp hsq]
  have hout : ∀ x, x ≠ p → x ≠ q → x ≠ r → x ≠ s → u' x = u x := by
    intro x hxp hxq hxr hxs
    obtain ⟨h1, h2, h3, h4⟩ := hux x hxp hxq hxr hxs
    rw [hu'x, swap_apply_of_ne_of_ne h3 h4, swap_apply_of_ne_of_ne h1 h2]
  have hfix : ∀ x, (x = p ∨ x = q ∨ x = r ∨ x = s) → u' x = x := by
    rintro x (h | h | h | h)
    · rw [h]
      exact hfp
    · rw [h]
      exact hfq
    · rw [h]
      exact hfr
    · rw [h]
      exact hfs
  have hinv : ∀ x, u' (u' x) = x := by
    intro x
    by_cases h : x = p ∨ x = q ∨ x = r ∨ x = s
    · rw [hfix x h, hfix x h]
    · simp only [not_or] at h
      obtain ⟨hxp, hxq, hxr, hxs⟩ := h
      obtain ⟨h1, h2, h3, h4⟩ := hux x hxp hxq hxr hxs
      rw [hout x hxp hxq hxr hxs, hout (u x) h1 h2 h3 h4, huu]
  have hsign : u' ∈ alternatingGroup α := by
    rw [hu']
    exact mul_mem (permJ_swap_mul_swap_mem hpq hrs) hus
  have hdom' : ∀ x, u' x ≠ x → u' x = (y : Perm α) x := by
    intro x hx
    by_cases h : x = p ∨ x = q ∨ x = r ∨ x = s
    · exact absurd (hfix x h) hx
    · simp only [not_or] at h
      obtain ⟨hxp, hxq, hxr, hxs⟩ := h
      rw [hout x hxp hxq hxr hxs] at hx ⊢
      exact hdom x hx
  have hsub : u'.support ⊆ u.support := by
    intro x hx
    rw [Equiv.Perm.mem_support] at hx ⊢
    by_cases h : x = p ∨ x = q ∨ x = r ∨ x = s
    · exact absurd (hfix x h) hx
    · simp only [not_or] at h
      obtain ⟨hxp, hxq, hxr, hxs⟩ := h
      rwa [hout x hxp hxq hxr hxs] at hx
  have hlt : u'.support.card < n := by
    rw [← hn]
    exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).2
      ⟨p, Equiv.Perm.mem_support.2 hp, fun h => (Equiv.Perm.mem_support.1 h) hfp⟩)
  have hmem' : u' ∈ permJ_subgroup y := ih _ hlt u' rfl hinv hsign hdom'
  have := mul_mem (inv_mem hmem) hmem'
  rwa [hu', inv_mul_cancel_left] at this

theorem permJ_dominated_mem (hα : 8 ≤ Fintype.card α) {y : alternatingGroup α}
    (hY : ∀ x, (y : Perm α) ((y : Perm α) x) = x) (n : ℕ) :
    ∀ u : Perm α, u.support.card = n → (∀ x, u (u x) = x) → u ∈ alternatingGroup α →
      (∀ x, u x ≠ x → u x = (y : Perm α) x) → u ∈ permJ_subgroup y := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u hn huu hus hdom
    by_cases hu1 : u = 1
    · rw [hu1]
      exact one_mem _
    · obtain ⟨p, r, hp, hr, hrp, hrq⟩ := permJ_exists_two_pairs huu hus hu1
      exact permJ_step hα hY ih hn huu hus hdom hp hr hrp hrq

end Reduction

theorem mem_commutator_centralizer_of_involution {α : Type*} [Fintype α] [DecidableEq α]
    (hα : 8 ≤ Fintype.card α) {y : alternatingGroup α} (hy : orderOf y = 2) :
    y ∈ ⁅centralizer ({y} : Set (alternatingGroup α)),
      centralizer ({y} : Set (alternatingGroup α))⁆ := by
  have hsq : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rw [hy, sq] at h
    exact h
  have hY : ∀ x, (y : Perm α) ((y : Perm α) x) = x := by
    intro x
    have h := congrArg (fun z : alternatingGroup α => (z : Perm α) x) hsq
    simpa using h
  have hmem := permJ_dominated_mem hα hY _ (y : Perm α) rfl hY y.2 (fun x _ => rfl)
  exact (Subgroup.mem_map_iff_mem (alternatingGroup α).subtype_injective).1 hmem

end CFSG.OddStandard.AltStdBal
