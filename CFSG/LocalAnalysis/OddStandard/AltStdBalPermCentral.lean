module

public import CFSG.LocalAnalysis.OddStandard.AltStdBalPermCenter

public section

namespace CFSG.OddStandard.AltStdBal

open Subgroup Equiv Equiv.Perm

theorem permC2_apply_apply {α : Type*} [Fintype α] [DecidableEq α]
    (hα : 8 ≤ Fintype.card α) {S C : Perm α} (hSS : ∀ x, S (S x) = x)
    (hCS : ∀ x, C (S x) = S (C x)) (hC4 : ∀ x, C (C (C (C x))) = x)
    (H' : ∀ D : Perm α, sign D = 1 → D * S = S * D → C * D = D * C) (x : α) :
    C (C x) = x := by
  have H : ∀ D : Perm α, sign D = 1 → D * S = S * D → C * D ^ 2 = D ^ 2 * C :=
    fun D hD hDS => (show Commute C D from H' D hD hDS).pow_right 2
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
      have hSx : S x = x2 := by
        rcases hMmem (S x) (by rw [hSS]; exact fun h => hxF h.symm) with h | h | h | h
        · exact absurd h hxF
        · exfalso
          have h2 := hCS x
          rw [h, h01, h12, ← h, hSS] at h2
          exact d02 h2.symm
        · exact h
        · exfalso
          have h1 : S x1 = x := by rw [← h01, ← hCS, h, h30]
          exact d13 (by rw [← h, ← h1, hSS])
      have hSx2 : S x2 = x := by rw [← hSx, hSS]
      obtain ⟨t, ht, v, hv, htv⟩ := Finset.one_lt_card.mp
        (show 1 < (Finset.univ.filter (fun z => S z = z)).card by omega)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht hv
      have hsign : sign (swap x x2 * swap t v) = 1 := by
        rw [sign_mul, sign_swap d02, sign_swap htv]
        decide
      have hcomm : (swap x x2 * swap t v) * S = S * (swap x x2 * swap t v) := by
        rw [mul_assoc, ← permC_swap_comm (Or.inl ⟨ht, hv⟩), ← mul_assoc,
          ← permC_swap_comm (Or.inr ⟨hSx, hSx2⟩), mul_assoc]
      have hC' := H' _ hsign hcomm
      have e := permC_mem_four_of_comm d02 (fun h => hxF (by rw [h]; exact ht))
        (fun h => hxF (by rw [h]; exact hv)) (fun h => hx2 (by rw [h]; exact ht))
        (fun h => hx2 (by rw [h]; exact hv)) htv hC' (u := x) (Or.inl rfl)
      rw [h01] at e
      rcases e with h | h | h | h
      · exact d01 h.symm
      · exact d12 h
      · exact hx1 (by rw [h]; exact ht)
      · exact hx1 (by rw [h]; exact hv)

theorem sq_eq_one_of_commute_centralizer {α : Type*} [Fintype α] [DecidableEq α]
    (hα : 8 ≤ Fintype.card α) {σ : alternatingGroup α} (hσ : orderOf σ = 2) {c : Perm α}
    (hc : ∀ d ∈ centralizer ({σ} : Set (alternatingGroup α)),
      c * (d : Perm α) = (d : Perm α) * c)
    (hc4 : c ^ 4 = 1) : c ^ 2 = 1 := by
  have hσ2 : σ ^ 2 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hSS : ∀ x, (σ : Perm α) ((σ : Perm α) x) = x := by
    intro x
    have h := congrArg (fun f : alternatingGroup α => (f : Perm α) x) hσ2
    simpa [pow_two] using h
  have hCS : ∀ x, c ((σ : Perm α) x) = (σ : Perm α) (c x) := by
    intro x
    have h := congrArg (fun f : Perm α => f x)
      (hc σ (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
    simpa using h
  have hC4 : ∀ x, c (c (c (c x))) = x := by
    intro x
    have h := congrArg (fun f : Perm α => f x) hc4
    simpa [pow_succ] using h
  have H' : ∀ D : Perm α, sign D = 1 → D * (σ : Perm α) = (σ : Perm α) * D →
      c * D = D * c := by
    intro D hD hDS
    have hmem : D ∈ alternatingGroup α := mem_alternatingGroup.mpr hD
    have hd : (⟨D, hmem⟩ : alternatingGroup α) ∈ centralizer ({σ} : Set (alternatingGroup α)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext hDS
    exact hc _ hd
  have key := permC2_apply_apply hα hSS hCS hC4 H'
  ext x
  simpa [pow_two] using key x

end CFSG.OddStandard.AltStdBal
