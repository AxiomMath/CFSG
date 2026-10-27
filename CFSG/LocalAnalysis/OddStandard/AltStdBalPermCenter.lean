module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.OddStandard.AltStdBal

open Subgroup Equiv Equiv.Perm

section PermHelpers

variable {α : Type*} [DecidableEq α]

theorem permC_swap_comm {S : Perm α} {a b : α} (h : (S a = a ∧ S b = b) ∨ (S a = b ∧ S b = a)) :
    S * swap a b = swap a b * S := by
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [mul_swap_eq_swap_mul, ha, hb]
  · rw [mul_swap_eq_swap_mul, ha, hb, swap_comm]

theorem permC_exists_cyc4 [Fintype α] {a b c d : α} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ∃ g : Perm α, g a = b ∧ g b = c ∧ g c = d ∧ g d = a ∧
      (∀ y, y ≠ a → y ≠ b → y ≠ c → y ≠ d → g y = y) ∧ sign g = -1 := by
  refine ⟨swap a b * swap b c * swap c d, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Perm.mul_apply, swap_apply_def]; grind
  · simp only [Perm.mul_apply, swap_apply_def]; grind
  · simp only [Perm.mul_apply, swap_apply_def]; grind
  · simp only [Perm.mul_apply, swap_apply_def]; grind
  · intro y h1 h2 h3 h4
    simp only [Perm.mul_apply, swap_apply_def]; grind
  · simp [sign_mul, *]

end PermHelpers

theorem permC_moved_of_comm {α : Type*} {C E : Perm α} (h : C * E = E * C) {u : α}
    (hu : E u ≠ u) : E (C u) ≠ C u := by
  intro h'
  apply hu
  apply C.injective
  have h2 : C (E u) = E (C u) := by simpa using congrArg (fun f => f u) h
  rw [h2, h']

theorem permC_mem_four_of_comm {α : Type*} [DecidableEq α] {C : Perm α} {p q r s : α}
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (h : C * (swap p q * swap r s) = (swap p q * swap r s) * C) {u : α}
    (hu : u = p ∨ u = q ∨ u = r ∨ u = s) : C u = p ∨ C u = q ∨ C u = r ∨ C u = s := by
  have h1 : (swap p q * swap r s) u ≠ u := by
    simp only [Perm.mul_apply, swap_apply_def]; grind
  have h2 := permC_moved_of_comm h h1
  simp only [Perm.mul_apply, swap_apply_def] at h2
  grind

theorem permC_exists_free_pair {α : Type*} [Fintype α] [DecidableEq α]
    (hα : 8 ≤ Fintype.card α) {S : Perm α} (hSS : ∀ x, S (S x) = x) {p q r s : α}
    (hp : S p = q) (hr : S r = s) :
    ∃ t v : α, t ≠ v ∧ t ≠ p ∧ t ≠ q ∧ t ≠ r ∧ t ≠ s ∧ v ≠ p ∧ v ≠ q ∧ v ≠ r ∧ v ≠ s ∧
      ((S t = t ∧ S v = v) ∨ (S t = v ∧ S v = t)) := by
  have hq : S q = p := by rw [← hp, hSS]
  have hs : S s = r := by rw [← hr, hSS]
  by_cases hex : ∃ t, t ≠ p ∧ t ≠ q ∧ t ≠ r ∧ t ≠ s ∧ S t ≠ t
  · obtain ⟨t, h1, h2, h3, h4, h5⟩ := hex
    refine ⟨t, S t, fun h => h5 h.symm, h1, h2, h3, h4, ?_, ?_, ?_, ?_, Or.inr ⟨rfl, hSS t⟩⟩
    · intro h; apply h2; rw [← hSS t, h, hp]
    · intro h; apply h1; rw [← hSS t, h, hq]
    · intro h; apply h4; rw [← hSS t, h, hr]
    · intro h; apply h3; rw [← hSS t, h, hs]
  · push Not at hex
    obtain ⟨t, -, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {p, q, r, s})
      (t := Finset.univ) (by
        have := Finset.card_le_four (a := p) (b := q) (c := r) (d := s)
        rw [Finset.card_univ]; omega)
    obtain ⟨v, -, hv⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {p, q, r, s, t})
      (t := Finset.univ) (by
        have := Finset.card_le_five (a := p) (b := q) (c := r) (d := s) (e := t)
        rw [Finset.card_univ]; omega)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht hv
    exact ⟨t, v, fun h => hv.2.2.2.2 h.symm, ht.1, ht.2.1, ht.2.2.1, ht.2.2.2, hv.1, hv.2.1,
      hv.2.2.1, hv.2.2.2.1, Or.inl ⟨hex t ht.1 ht.2.1 ht.2.2.1 ht.2.2.2,
        hex v hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.1⟩⟩

theorem permC_exists_sq_dswap {α : Type*} [Fintype α] [DecidableEq α]
    (hα : 8 ≤ Fintype.card α) {S : Perm α} (hSS : ∀ x, S (S x) = x) {p q r s : α}
    (hp : S p = q) (hr : S r = s) (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r)
    (hqs : q ≠ s) (hrs : r ≠ s) :
    ∃ D : Perm α, sign D = 1 ∧ D * S = S * D ∧ D ^ 2 = swap p q * swap r s := by
  have hq : S q = p := by rw [← hp, hSS]
  have hs : S s = r := by rw [← hr, hSS]
  obtain ⟨t, v, htv, htp, htq, htr, hts, hvp, hvq, hvr, hvs, htS⟩ :=
    permC_exists_free_pair hα hSS hp hr
  obtain ⟨γ, hγp, hγr, hγq, hγs, hγo, hγsign⟩ :=
    permC_exists_cyc4 (a := p) (b := r) (c := q) (d := s) hpr hpq hps hqr.symm hrs hqs
  have hγS : γ * S = S * γ := by
    ext y
    simp only [Perm.mul_apply]
    by_cases hy : y = p ∨ y = q ∨ y = r ∨ y = s
    · rcases hy with rfl | rfl | rfl | rfl <;> simp [*]
    · push Not at hy
      have h1 : S y ≠ p := fun h => hy.2.1 (by rw [← hSS y, h, hp])
      have h2 : S y ≠ q := fun h => hy.1 (by rw [← hSS y, h, hq])
      have h3 : S y ≠ r := fun h => hy.2.2.2 (by rw [← hSS y, h, hr])
      have h4 : S y ≠ s := fun h => hy.2.2.1 (by rw [← hSS y, h, hs])
      rw [hγo (S y) h1 h3 h2 h4, hγo y hy.1 hy.2.2.1 hy.2.1 hy.2.2.2]
  have hcomm : γ * swap t v = swap t v * γ := by
    have hinj : ∀ a b, γ a = γ b → a = b := fun a b h => γ.injective h
    have hγt : γ t = t := hγo t htp htr htq hts
    have hγv : γ v = v := hγo v hvp hvr hvq hvs
    ext y
    simp only [Perm.mul_apply, swap_apply_def]
    grind
  have hγ2 : γ ^ 2 = swap p q * swap r s := by
    ext y
    simp only [pow_two, Perm.mul_apply, swap_apply_def]
    grind
  refine ⟨γ * swap t v, ?_, ?_, ?_⟩
  · rw [sign_mul, hγsign, sign_swap htv]
    decide
  · rw [mul_assoc, ← permC_swap_comm htS, ← mul_assoc, hγS, mul_assoc]
  · rw [(show Commute γ (swap t v) from hcomm).mul_pow, hγ2, pow_two (swap t v), swap_mul_self,
      mul_one]

theorem permC_mem_four_orbits {α : Type*} [Fintype α] [DecidableEq α]
    (hα : 8 ≤ Fintype.card α) {S C : Perm α} (hSS : ∀ x, S (S x) = x)
    (H : ∀ D : Perm α, sign D = 1 → D * S = S * D → C * D ^ 2 = D ^ 2 * C) {p r : α}
    (hp : S p ≠ p) (hr : S r ≠ r) (hrp : r ≠ p) (hrq : r ≠ S p) :
    C p = p ∨ C p = S p ∨ C p = r ∨ C p = S r := by
  have hpr : p ≠ S r := fun h => hrq (by rw [h, hSS])
  have hqs : S p ≠ S r := fun h => hrp (by simpa using (S.injective h).symm)
  obtain ⟨D, hD1, hDS, hD2⟩ := permC_exists_sq_dswap hα hSS (p := p) (q := S p) (r := r)
    (s := S r) rfl rfl hp.symm hrp.symm hpr hrq.symm hqs hr.symm
  have h := H D hD1 hDS
  rw [hD2] at h
  exact permC_mem_four_of_comm hp.symm hrp.symm hpr hrq.symm hqs hr.symm h (Or.inl rfl)

theorem permC_mem_three {α : Type*} [Fintype α] [DecidableEq α] {S C : Perm α}
    (H : ∀ D : Perm α, sign D = 1 → D * S = S * D → C * D ^ 2 = D ^ 2 * C) {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (ha : S a = a) (hb : S b = b) (hc : S c = c)
    {u : α} (hu : u = a ∨ u = b ∨ u = c) : C u = a ∨ C u = b ∨ C u = c := by
  have hsign : sign (swap a b * swap a c) = 1 := by
    rw [sign_mul, sign_swap hab, sign_swap hac]
    decide
  have hcomm : (swap a b * swap a c) * S = S * (swap a b * swap a c) := by
    rw [mul_assoc, ← permC_swap_comm (Or.inl ⟨ha, hc⟩), ← mul_assoc,
      ← permC_swap_comm (Or.inl ⟨ha, hb⟩), mul_assoc]
  have h := H _ hsign hcomm
  have h1 : ((swap a b * swap a c) ^ 2) u ≠ u := by
    simp only [pow_two, Perm.mul_apply, swap_apply_def]; grind
  have h2 := permC_moved_of_comm h h1
  simp only [pow_two, Perm.mul_apply, swap_apply_def] at h2
  grind

theorem permC_fix_of_card_fixed {α : Type*} [Fintype α] [DecidableEq α] {S C : Perm α}
    (H : ∀ D : Perm α, sign D = 1 → D * S = S * D → C * D ^ 2 = D ^ 2 * C)
    (hF : 4 ≤ (Finset.univ.filter (fun z => S z = z)).card) {y : α} (hy : S y = y) :
    C y = y := by
  have hy' : y ∈ Finset.univ.filter (fun z => S z = z) := by simp [hy]
  have h3 : 2 < ((Finset.univ.filter (fun z => S z = z)).erase y).card := by
    rw [Finset.card_erase_of_mem hy']; omega
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp h3
  simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb hc
  have h1 := permC_mem_three H (a := y) (b := a) (c := b) ha.1.symm hb.1.symm hab hy ha.2 hb.2
    (u := y) (Or.inl rfl)
  have h2 := permC_mem_three H (a := y) (b := a) (c := c) ha.1.symm hc.1.symm hac hy ha.2 hc.2
    (u := y) (Or.inl rfl)
  have h3 := permC_mem_three H (a := y) (b := b) (c := c) hb.1.symm hc.1.symm hbc hy hb.2 hc.2
    (u := y) (Or.inl rfl)
  grind

theorem permC_apply_apply {α : Type*} [Fintype α] [DecidableEq α]
    (hα : 8 ≤ Fintype.card α) {S C : Perm α} (hSS : ∀ x, S (S x) = x)
    (hCS : ∀ x, C (S x) = S (C x)) (hC4 : ∀ x, C (C (C (C x))) = x) (hCs : sign C = 1)
    (H : ∀ D : Perm α, sign D = 1 → D * S = S * D → C * D ^ 2 = D ^ 2 * C) (x : α) :
    C (C x) = x := by
  by_contra hne
  have hinj : ∀ a b, C a = C b → a = b := fun a b h => C.injective h
  obtain ⟨x1, h01⟩ : ∃ y, C x = y := ⟨_, rfl⟩
  obtain ⟨x2, h12⟩ : ∃ y, C x1 = y := ⟨_, rfl⟩
  obtain ⟨x3, h23⟩ : ∃ y, C x2 = y := ⟨_, rfl⟩
  have h30 : C x3 = x := by rw [← h23, ← h12, ← h01]; exact hC4 x
  have hne2 : x2 ≠ x := by rw [← h12, ← h01]; exact hne
  have d01 : x ≠ x1 := by grind
  have d02 : x ≠ x2 := fun h => hne2 h.symm
  have d03 : x ≠ x3 := by grind
  have d12 : x1 ≠ x2 := by grind
  have d13 : x1 ≠ x3 := by grind
  have d23 : x2 ≠ x3 := by grind
  have hcard4 : ({x, x1, x2, x3} : Finset α).card = 4 :=
    Finset.card_eq_four.mpr ⟨x, x1, x2, x3, d01, d02, d03, d12, d13, d23, rfl⟩
  have hSF : ∀ y, S y = y → S (C y) = C y := fun y hy => by rw [← hCS, hy]
  have hSM : ∀ y, ¬ S y = y → ¬ S (C y) = C y :=
    fun y hy h => hy (hinj _ _ (by rw [hCS]; exact h))
  by_cases hxF : S x = x
  · have hx1 : S x1 = x1 := by rw [← h01]; exact hSF x hxF
    have hx2 : S x2 = x2 := by rw [← h12]; exact hSF x1 hx1
    have hx3 : S x3 = x3 := by rw [← h23]; exact hSF x2 hx2
    have hF : 4 ≤ (Finset.univ.filter (fun z => S z = z)).card := by
      rw [← hcard4]
      refine Finset.card_le_card ?_
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hz with rfl | rfl | rfl | rfl <;> assumption
    exact d01 (by rw [← h01, permC_fix_of_card_fixed H hF hxF])
  · have hx1 : ¬ S x1 = x1 := by rw [← h01]; exact hSM x hxF
    have hx2 : ¬ S x2 = x2 := by rw [← h12]; exact hSM x1 hx1
    have hx3 : ¬ S x3 = x3 := by rw [← h23]; exact hSM x2 hx2
    by_cases hM : 5 ≤ (Finset.univ.filter (fun z => ¬ S z = z)).card
    · obtain ⟨r, hrM, hr⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {x, S x})
        (t := Finset.univ.filter (fun z => ¬ S z = z))
        (by have := Finset.card_le_two (a := x) (b := S x); omega)
      obtain ⟨r', hrM', hr'⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {x, S x, r, S r})
        (t := Finset.univ.filter (fun z => ¬ S z = z))
        (by have := Finset.card_le_four (a := x) (b := S x) (c := r) (d := S r); omega)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hrM hrM'
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr hr'
      have e1 := permC_mem_four_orbits hα hSS H hxF hrM hr.1 hr.2
      have e2 := permC_mem_four_orbits hα hSS H hxF hrM' hr'.1 hr'.2.1
      have a1 := hSS x
      have a2 := hSS r
      have a3 := hSS r'
      have hSinj : ∀ a b, S a = S b → a = b := fun a b h => S.injective h
      have hfin : C x = x ∨ C x = S x := by grind
      apply hne
      rcases hfin with h | h
      · rw [h, h]
      · rw [h, hCS, h, hSS]
    · have hsub : ({x, x1, x2, x3} : Finset α) ⊆ Finset.univ.filter (fun z => ¬ S z = z) := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hz with rfl | rfl | rfl | rfl <;> assumption
      have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
      have hMmem : ∀ z, ¬ S z = z → z = x ∨ z = x1 ∨ z = x2 ∨ z = x3 := by
        intro z hz
        have hz' : z ∈ Finset.univ.filter (fun z => ¬ S z = z) := by simp [hz]
        rw [← heq] at hz'
        simpa using hz'
      have hF4 : 4 ≤ (Finset.univ.filter (fun z => S z = z)).card := by
        have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset α))
          (fun z => S z = z)
        rw [Finset.card_univ] at this
        omega
      obtain ⟨g, hg0, hg1, hg2, hg3, hgo, hgsign⟩ := permC_exists_cyc4 d01 d02 d03 d12 d13 d23
      have hCg : C = g := by
        ext y
        by_cases hy : y = x ∨ y = x1 ∨ y = x2 ∨ y = x3
        · rcases hy with rfl | rfl | rfl | rfl
          · rw [h01, hg0]
          · rw [h12, hg1]
          · rw [h23, hg2]
          · rw [h30, hg3]
        · push Not at hy
          have hSy : S y = y := by
            by_contra h
            grind
          rw [permC_fix_of_card_fixed H hF4 hSy, hgo y hy.1 hy.2.1 hy.2.2.1 hy.2.2.2]
      rw [hCg, hgsign] at hCs
      exact absurd hCs (by decide)

theorem sq_eq_one_of_commute_sq_centralizer {α : Type*} [Fintype α] [DecidableEq α]
    (hα : 8 ≤ Fintype.card α) {σ : alternatingGroup α} (hσ : orderOf σ = 2)
    {c : alternatingGroup α} (hcσ : c ∈ centralizer ({σ} : Set (alternatingGroup α)))
    (hcsq : ∀ d ∈ centralizer ({σ} : Set (alternatingGroup α)), c * d ^ 2 = d ^ 2 * c)
    (hc4 : c ^ 4 = 1) : c ^ 2 = 1 := by
  have hσ2 : σ ^ 2 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hSS : ∀ x, (σ : Perm α) ((σ : Perm α) x) = x := by
    intro x
    have h := congrArg (fun f : alternatingGroup α => (f : Perm α) x) hσ2
    simpa [pow_two] using h
  have hCS : ∀ x, (c : Perm α) ((σ : Perm α) x) = (σ : Perm α) ((c : Perm α) x) := by
    intro x
    have h := congrArg (fun f : alternatingGroup α => (f : Perm α) x)
      (Subgroup.mem_centralizer_singleton_iff.mp hcσ)
    simpa using h
  have hC4 : ∀ x, (c : Perm α) ((c : Perm α) ((c : Perm α) ((c : Perm α) x))) = x := by
    intro x
    have h := congrArg (fun f : alternatingGroup α => (f : Perm α) x) hc4
    simpa [pow_succ] using h
  have hcs : sign (c : Perm α) = 1 := mem_alternatingGroup.mp c.2
  have H : ∀ D : Perm α, sign D = 1 → D * (σ : Perm α) = (σ : Perm α) * D →
      (c : Perm α) * D ^ 2 = D ^ 2 * (c : Perm α) := by
    intro D hD hDS
    have hmem : D ∈ alternatingGroup α := mem_alternatingGroup.mpr hD
    have hd : (⟨D, hmem⟩ : alternatingGroup α) ∈ centralizer ({σ} : Set (alternatingGroup α)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext hDS
    have h := congrArg (fun f : alternatingGroup α => (f : Perm α)) (hcsq _ hd)
    simpa using h
  have key := permC_apply_apply hα hSS hCS hC4 hcs H
  apply Subtype.ext
  ext x
  simpa [pow_two] using key x

end CFSG.OddStandard.AltStdBal
