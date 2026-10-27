module

public import CFSG.CGT.PushingUpLit.BHS7.OmegaMaxSwapCore

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.Quasithin.A1b CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.BHS6

variable {n : ℕ}

theorem even_card_of_invariant {T' : Set (Equiv.Perm (Fin n))} (hs : ∀ t ∈ T', t.IsSwap)
    (hc : ∀ t ∈ T', ∀ t' ∈ T', t * t' = t' * t) {c : Fin n}
    (huniq : ∀ x, (∀ t ∈ T', t x = x) → x = c) {Ω : Finset (Fin n)}
    (hΩ : ∀ t ∈ T', ∀ x, t x ∈ Ω ↔ x ∈ Ω) (hcΩ : c ∉ Ω) : Even Ω.card := by
  classical
  have hfin : T'.Finite := Set.toFinite T'
  set Pr : Finset (Equiv.Perm (Fin n)) := hfin.toFinset.filter fun t => t.support ⊆ Ω with hPr
  have hΩeq : Ω = Pr.biUnion Equiv.Perm.support := by
    ext x
    simp only [Finset.mem_biUnion]
    constructor
    · intro hx
      have hxc : x ≠ c := fun h => hcΩ (h ▸ hx)
      have hmov : ∃ t ∈ T', t x ≠ x := by
        by_contra hall
        push Not at hall
        exact hxc (huniq x hall)
      obtain ⟨t, ht, htx⟩ := hmov
      refine ⟨t, ?_, Equiv.Perm.mem_support.2 htx⟩
      rw [hPr, Finset.mem_filter]
      refine ⟨hfin.mem_toFinset.2 ht, fun y hy => ?_⟩
      have e1 : t = Equiv.swap x (t x) := eq_swap_of_isSwap_apply_ne (hs t ht) htx
      have hsupp : t.support = {x, t x} := by
        have := Equiv.Perm.support_swap htx.symm
        rw [← e1] at this
        exact this
      rw [hsupp] at hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact hx
      · exact (hΩ t ht x).2 hx
    · rintro ⟨t, ht, hx⟩
      exact (Finset.mem_filter.1 ht).2 hx
  have hd : (↑Pr : Set (Equiv.Perm (Fin n))).PairwiseDisjoint Equiv.Perm.support := by
    intro t ht t' ht' hne
    have ht1 := hfin.mem_toFinset.1 (Finset.mem_filter.1 ht).1
    have ht2 := hfin.mem_toFinset.1 (Finset.mem_filter.1 ht').1
    exact disjoint_support_of_commute (hs t ht1) (hs t' ht2) (hc t ht1 t' ht2) hne
  have hcard : Ω.card = Pr.card * 2 := by
    conv_lhs => rw [hΩeq]
    rw [Finset.card_biUnion hd]
    have h2 : ∑ t ∈ Pr, t.support.card = ∑ t ∈ Pr, 2 :=
      Finset.sum_congr rfl fun t ht => Equiv.Perm.card_support_eq_two.2
        (hs t (hfin.mem_toFinset.1 (Finset.mem_filter.1 ht).1))
    rw [h2, Finset.sum_const, smul_eq_mul]
  exact ⟨Pr.card, by omega⟩

@[expose] def pairExchange (x a y b : Fin n) : Equiv.Perm (Fin n) :=
  Equiv.swap x a * Equiv.swap y b

section Exchange

variable {x a y b : Fin n}

theorem pairExchange_apply_a (hay : a ≠ y) (hab : a ≠ b) : pairExchange x a y b a = x := by
  simp [pairExchange, Equiv.swap_apply_of_ne_of_ne hay hab]

theorem pairExchange_apply_b (hyx : y ≠ x) (hya : y ≠ a) : pairExchange x a y b b = y := by
  simp [pairExchange, Equiv.swap_apply_of_ne_of_ne hyx hya]

theorem pairExchange_apply_x (hxy : x ≠ y) (hxb : x ≠ b) : pairExchange x a y b x = a := by
  simp [pairExchange, Equiv.swap_apply_of_ne_of_ne hxy hxb]

theorem pairExchange_apply_y (hbx : b ≠ x) (hba : b ≠ a) : pairExchange x a y b y = b := by
  simp [pairExchange, Equiv.swap_apply_of_ne_of_ne hbx hba]

theorem pairExchange_apply_of_ne {z : Fin n} (hzx : z ≠ x) (hza : z ≠ a) (hzy : z ≠ y)
    (hzb : z ≠ b) : pairExchange x a y b z = z := by
  simp [pairExchange, Equiv.swap_apply_of_ne_of_ne hzy hzb, Equiv.swap_apply_of_ne_of_ne hzx hza]

theorem sign_pairExchange (hxa : x ≠ a) (hyb : y ≠ b) :
    Equiv.Perm.sign (pairExchange x a y b) = 1 := by
  rw [pairExchange, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hxa, Equiv.Perm.sign_swap hyb]
  decide

end Exchange

section Pairs

variable {T' : Set (Equiv.Perm (Fin n))} (hs : ∀ t ∈ T', t.IsSwap)
  (hc : ∀ t ∈ T', ∀ t' ∈ T', t * t' = t' * t)
include hs hc

theorem pair_ne_of_ne {t₁ t₂ : Equiv.Perm (Fin n)} (h₁ : t₁ ∈ T') (h₂ : t₂ ∈ T') {a x : Fin n}
    (ha : t₁ a ≠ a) (hx : t₂ x ≠ x) (hxa : x ≠ a) (hxb : x ≠ t₁ a) :
    t₁ ≠ t₂ ∧ a ≠ t₂ x ∧ t₁ a ≠ t₂ x := by
  have e1 : t₁ = Equiv.swap a (t₁ a) := eq_swap_of_isSwap_apply_ne (hs t₁ h₁) ha
  have hne : t₁ ≠ t₂ := by
    intro h
    subst h
    exact hx (by rw [e1]; exact Equiv.swap_apply_of_ne_of_ne hxa hxb)
  have h12 : ∀ u, t₁ u ≠ u → t₂ u = u := fun u hu =>
    apply_eq_of_commute_swap (hs t₁ h₁) (hs t₂ h₂) (hc t₁ h₁ t₂ h₂) hne hu
  have hb1 : t₁ (t₁ a) ≠ t₁ a := by
    rw [isSwap_apply_apply (hs t₁ h₁) a]
    exact ha.symm
  refine ⟨hne, ?_, ?_⟩
  · intro h
    have h1 : t₂ a = a := h12 a ha
    rw [h, isSwap_apply_apply (hs t₂ h₂) x] at h1
    exact hxa (h1.trans h.symm)
  · intro h
    have h1 : t₂ (t₁ a) = t₁ a := h12 (t₁ a) hb1
    rw [h, isSwap_apply_apply (hs t₂ h₂) x] at h1
    exact hxb (h1.trans h.symm)

omit hc in
theorem pairExchange_apply_of_fixed {t₁ t₂ : Equiv.Perm (Fin n)} (h₁ : t₁ ∈ T') (h₂ : t₂ ∈ T')
    {a x c : Fin n} (ha : t₁ a ≠ a) (hx : t₂ x ≠ x) (hcfix : ∀ t ∈ T', t c = c) :
    pairExchange x a (t₂ x) (t₁ a) c = c := by
  have hc1 := hcfix t₁ h₁
  have hc2 := hcfix t₂ h₂
  have hb1 : t₁ (t₁ a) ≠ t₁ a := by
    rw [isSwap_apply_apply (hs t₁ h₁) a]
    exact ha.symm
  have hy2 : t₂ (t₂ x) ≠ t₂ x := by
    rw [isSwap_apply_apply (hs t₂ h₂) x]
    exact hx.symm
  refine pairExchange_apply_of_ne ?_ ?_ ?_ ?_
  · rintro rfl
    exact hx hc2
  · rintro rfl
    exact ha hc1
  · rintro rfl
    exact hy2 hc2
  · rintro rfl
    exact hb1 hc1

theorem pairExchange_mem_normalizer {t₁ t₂ : Equiv.Perm (Fin n)} (h₁ : t₁ ∈ T') (h₂ : t₂ ∈ T')
    {a x : Fin n} (ha : t₁ a ≠ a) (hx : t₂ x ≠ x) (hxa : x ≠ a) (hxb : x ≠ t₁ a) :
    pairExchange x a (t₂ x) (t₁ a) ∈
      Subgroup.normalizer (Subgroup.closure T' : Set (Equiv.Perm (Fin n))) := by
  classical
  have e1 : t₁ = Equiv.swap a (t₁ a) := eq_swap_of_isSwap_apply_ne (hs t₁ h₁) ha
  have e2 : t₂ = Equiv.swap x (t₂ x) := eq_swap_of_isSwap_apply_ne (hs t₂ h₂) hx
  have hne : t₁ ≠ t₂ := by
    intro h
    subst h
    exact hx (by rw [e1]; exact Equiv.swap_apply_of_ne_of_ne hxa hxb)
  have h12 : ∀ u, t₁ u ≠ u → t₂ u = u := fun u hu =>
    apply_eq_of_commute_swap (hs t₁ h₁) (hs t₂ h₂) (hc t₁ h₁ t₂ h₂) hne hu
  have h21 : ∀ u, t₂ u ≠ u → t₁ u = u := fun u hu =>
    apply_eq_of_commute_swap (hs t₂ h₂) (hs t₁ h₁) (hc t₂ h₂ t₁ h₁) hne.symm hu
  have hb1 : t₁ (t₁ a) ≠ t₁ a := by
    rw [isSwap_apply_apply (hs t₁ h₁) a]
    exact ha.symm
  have hy2 : t₂ (t₂ x) ≠ t₂ x := by
    rw [isSwap_apply_apply (hs t₂ h₂) x]
    exact hx.symm
  have hay : a ≠ t₂ x := by
    intro h
    have h1 : t₂ a = a := h12 a ha
    rw [h, isSwap_apply_apply (hs t₂ h₂) x] at h1
    exact hxa (h1.trans h.symm)
  have hby : t₁ a ≠ t₂ x := by
    intro h
    have h1 : t₂ (t₁ a) = t₁ a := h12 (t₁ a) hb1
    rw [h, isSwap_apply_apply (hs t₂ h₂) x] at h1
    exact hxb (h1.trans h.symm)
  have hxy : x ≠ t₂ x := hx.symm
  have hab : a ≠ t₁ a := ha.symm
  set σ : Equiv.Perm (Fin n) := pairExchange x a (t₂ x) (t₁ a) with hσ
  have σa : σ a = x := pairExchange_apply_a hay hab
  have σb : σ (t₁ a) = t₂ x := pairExchange_apply_b hxy.symm hay.symm
  have σx : σ x = a := pairExchange_apply_x hxy hxb
  have σy : σ (t₂ x) = t₁ a := pairExchange_apply_y hxb.symm ha
  have hfix : ∀ t'' ∈ T', t'' ≠ t₁ → t'' ≠ t₂ →
      t'' a = a ∧ t'' (t₁ a) = t₁ a ∧ t'' x = x ∧ t'' (t₂ x) = t₂ x := by
    intro t'' ht'' hn1 hn2
    have f1 : ∀ u, t₁ u ≠ u → t'' u = u := fun u hu =>
      apply_eq_of_commute_swap (hs t₁ h₁) (hs t'' ht'') (hc t₁ h₁ t'' ht'') hn1.symm hu
    have f2 : ∀ u, t₂ u ≠ u → t'' u = u := fun u hu =>
      apply_eq_of_commute_swap (hs t₂ h₂) (hs t'' ht'') (hc t₂ h₂ t'' ht'') hn2.symm hu
    exact ⟨f1 _ ha, f1 _ hb1, f2 _ hx, f2 _ hy2⟩
  have c1 : σ * t₁ * σ⁻¹ = t₂ := by
    have h := congrArg (fun p : Equiv.Perm (Fin n) => σ * p * σ⁻¹) e1
    rw [h, ← Equiv.swap_apply_apply, σa, σb, ← e2]
  have c2 : σ * t₂ * σ⁻¹ = t₁ := by
    have h := congrArg (fun p : Equiv.Perm (Fin n) => σ * p * σ⁻¹) e2
    rw [h, ← Equiv.swap_apply_apply, σx, σy, ← e1]
  have hconj : ∀ t'' ∈ T', σ * t'' * σ⁻¹ ∈ T' := by
    intro t'' ht''
    by_cases h1 : t'' = t₁
    · rw [h1, c1]
      exact h₂
    by_cases h2 : t'' = t₂
    · rw [h2, c2]
      exact h₁
    obtain ⟨fa, fb, fx, fy⟩ := hfix t'' ht'' h1 h2
    obtain ⟨u, v, huv, rfl⟩ := hs t'' ht''
    have hnot : ∀ z, Equiv.swap u v z = z → z ≠ u ∧ z ≠ v := by
      intro z hz
      refine ⟨fun h => huv ?_, fun h => huv ?_⟩
      · rw [h, Equiv.swap_apply_left] at hz
        exact hz.symm
      · rw [h, Equiv.swap_apply_right] at hz
        exact hz
    obtain ⟨na1, na2⟩ := hnot a fa
    obtain ⟨nb1, nb2⟩ := hnot (t₁ a) fb
    obtain ⟨nx1, nx2⟩ := hnot x fx
    obtain ⟨ny1, ny2⟩ := hnot (t₂ x) fy
    have hσu : σ u = u := pairExchange_apply_of_ne (Ne.symm nx1) (Ne.symm na1) (Ne.symm ny1)
      (Ne.symm nb1)
    have hσv : σ v = v := pairExchange_apply_of_ne (Ne.symm nx2) (Ne.symm na2) (Ne.symm ny2)
      (Ne.symm nb2)
    rw [← Equiv.swap_apply_apply, hσu, hσv]
    exact ht''
  have hle : A1b.conjSub σ (Subgroup.closure T') ≤ Subgroup.closure T' := by
    unfold A1b.conjSub
    rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    intro t ht
    have := hconj t ht
    show σ * t * σ⁻¹ ∈ Subgroup.closure T'
    exact Subgroup.subset_closure this
  have heq : A1b.conjSub σ (Subgroup.closure T') = Subgroup.closure T' :=
    Subgroup.eq_of_le_of_card_ge hle (OMS.card_conjSub_eq σ _).ge
  exact mem_normalizer_of_conjSub_eq heq

end Pairs

end CFSG.CGT.PushingUpLit.BHS7
