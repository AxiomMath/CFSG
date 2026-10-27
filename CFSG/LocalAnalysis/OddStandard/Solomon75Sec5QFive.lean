module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5DefsModel

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS


theorem perm_apply_apply_of_mul_self_eq_one {n : ℕ} {σ : Perm (Fin n)} (hσ : σ * σ = 1)
    (x : Fin n) : σ (σ x) = x := by
  simpa using Perm.ext_iff.1 hσ x

theorem commute_swap_pair_of_involution {n : ℕ} {σ : Perm (Fin n)} (hσ : σ * σ = 1) (b b' : Fin n) :
    Commute (swap b (σ b)) (swap b' (σ b')) := by
  have hσσ := perm_apply_apply_of_mul_self_eq_one hσ
  by_cases h1 : b' = b
  · subst h1
    exact Commute.refl _
  by_cases h2 : b' = σ b
  · subst h2
    rw [hσσ, swap_comm]
  · refine Equiv.Perm.Disjoint.commute ?_
    rw [Equiv.Perm.disjoint_iff_eq_or_eq]
    intro x
    by_cases hx : x = b ∨ x = σ b
    · right
      refine swap_apply_of_ne_of_ne ?_ ?_
      · rintro rfl
        rcases hx with rfl | rfl
        · exact h1 rfl
        · exact h2 rfl
      · intro hxσ
        rcases hx with rfl | rfl
        · exact h2 (by rw [← hσσ b', ← hxσ])
        · exact h1 (by simpa using congrArg σ hxσ.symm)
    · left
      rw [not_or] at hx
      exact swap_apply_of_ne_of_ne hx.1 hx.2

theorem conj_swap_pair_of_commute {n : ℕ} {σ g : Perm (Fin n)} (hg : g * σ = σ * g) (b : Fin n) :
    g * swap b (σ b) * g⁻¹ = swap (g b) (σ (g b)) := by
  have h : g (σ b) = σ (g b) := by simpa using Perm.ext_iff.1 hg b
  rw [← h, swap_apply_apply]

theorem support_swap_pair_subset {n : ℕ} (σ : Perm (Fin n)) (b : Fin n) :
    (swap b (σ b)).support ⊆ {b, σ b} := by
  intro x hx
  by_contra h
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
  exact (Equiv.Perm.mem_support.1 hx) (swap_apply_of_ne_of_ne h.1 h.2)

theorem commute_doublePairSwap_of_hinv {n k : ℕ} {σ : Perm (Fin n)} (hσ : σ * σ = 1)
    (hk : σ.support.card = 2 * k) (hk6 : 6 ≤ k)
    {R : Subgroup (Perm (Fin n))} (hRc : ∀ r ∈ R, r * σ = σ * r)
    (hRn : ∀ a c : Fin n, σ a ≠ a → σ c ≠ c → c ≠ a → c ≠ σ a → ∀ r ∈ R,
      (swap a (σ a) * swap c (σ c)) * r * (swap a (σ a) * swap c (σ c))⁻¹ ∈ R)
    (hinv : ∀ r ∈ R, r * r = 1 → r ≠ 1 → fixCount r ≤ 3)
    {a c : Fin n} (ha : σ a ≠ a) (hc : σ c ≠ c) (hca : c ≠ a) (hcσ : c ≠ σ a)
    {r : Perm (Fin n)} (hr : r ∈ R) :
    r * (swap a (σ a) * swap c (σ c)) = (swap a (σ a) * swap c (σ c)) * r := by
  have hrσ := hRc r hr
  have he : swap a (σ a) * swap c (σ c) * r * (swap a (σ a) * swap c (σ c))⁻¹ * r⁻¹ ∈ R :=
    mul_mem (hRn a c ha hc hca hcσ r hr) (inv_mem hr)
  have hform : swap a (σ a) * swap c (σ c) * r * (swap a (σ a) * swap c (σ c))⁻¹ * r⁻¹ =
      (swap a (σ a) * swap c (σ c)) * (swap (r c) (σ (r c)) * swap (r a) (σ (r a))) := by
    rw [mul_inv_rev, swap_inv, swap_inv, ← conj_swap_pair_of_commute hrσ a,
      ← conj_swap_pair_of_commute hrσ c]
    group
  have hcomm : Commute (swap a (σ a) * swap c (σ c))
      (swap (r c) (σ (r c)) * swap (r a) (σ (r a))) := by
    refine Commute.mul_left (Commute.mul_right ?_ ?_) (Commute.mul_right ?_ ?_) <;>
      exact commute_swap_pair_of_involution hσ _ _
  have hsq : (swap a (σ a) * swap c (σ c)) * (swap (r c) (σ (r c)) * swap (r a) (σ (r a))) *
      ((swap a (σ a) * swap c (σ c)) * (swap (r c) (σ (r c)) * swap (r a) (σ (r a)))) = 1 := by
    rw [← sq, hcomm.mul_pow, (commute_swap_pair_of_involution hσ a c).mul_pow,
      (commute_swap_pair_of_involution hσ (r c) (r a)).mul_pow]
    simp [sq]
  have hsupp : (swap a (σ a) * swap c (σ c) *
      (swap (r c) (σ (r c)) * swap (r a) (σ (r a)))).support.card ≤ 8 := by
    have hsub : (swap a (σ a) * swap c (σ c) *
        (swap (r c) (σ (r c)) * swap (r a) (σ (r a)))).support ⊆
        ({a, σ a} ∪ {c, σ c}) ∪ ({r c, σ (r c)} ∪ {r a, σ (r a)}) := by
      refine (Equiv.Perm.support_mul_le _ _).trans (Finset.union_subset_union ?_ ?_)
      · exact (Equiv.Perm.support_mul_le _ _).trans (Finset.union_subset_union
          (support_swap_pair_subset σ a) (support_swap_pair_subset σ c))
      · exact (Equiv.Perm.support_mul_le _ _).trans (Finset.union_subset_union
          (support_swap_pair_subset σ _) (support_swap_pair_subset σ _))
    refine (Finset.card_le_card hsub).trans ?_
    have h1 := Finset.card_union_le ({a, σ a} : Finset (Fin n)) {c, σ c}
    have h2 := Finset.card_union_le ({r c, σ (r c)} : Finset (Fin n)) {r a, σ (r a)}
    have h3 := Finset.card_union_le (({a, σ a} : Finset (Fin n)) ∪ {c, σ c})
      ({r c, σ (r c)} ∪ {r a, σ (r a)})
    have h4 := Finset.card_le_two (a := a) (b := σ a)
    have h5 := Finset.card_le_two (a := c) (b := σ c)
    have h6 := Finset.card_le_two (a := r c) (b := σ (r c))
    have h7 := Finset.card_le_two (a := r a) (b := σ (r a))
    omega
  have hn : 2 * k ≤ n := by
    have := Finset.card_le_univ σ.support
    simpa [hk] using this
  have hfx := fixCount_add_support (swap a (σ a) * swap c (σ c) *
    (swap (r c) (σ (r c)) * swap (r a) (σ (r a))))
  have hE1 : swap a (σ a) * swap c (σ c) *
      (swap (r c) (σ (r c)) * swap (r a) (σ (r a))) = 1 := by
    by_contra hne
    have := hinv _ (hform ▸ he) hsq hne
    omega
  have h1 : swap a (σ a) * swap c (σ c) * r * (swap a (σ a) * swap c (σ c))⁻¹ * r⁻¹ = 1 := by
    rw [hform]
    exact hE1
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact h1.symm

theorem apply_mem_pair_of_hinv {n k : ℕ} {σ : Perm (Fin n)} (hσ : σ * σ = 1)
    (hk : σ.support.card = 2 * k) (hk6 : 6 ≤ k)
    {R : Subgroup (Perm (Fin n))} (hRc : ∀ r ∈ R, r * σ = σ * r)
    (hRn : ∀ a c : Fin n, σ a ≠ a → σ c ≠ c → c ≠ a → c ≠ σ a → ∀ r ∈ R,
      (swap a (σ a) * swap c (σ c)) * r * (swap a (σ a) * swap c (σ c))⁻¹ ∈ R)
    (hinv : ∀ r ∈ R, r * r = 1 → r ≠ 1 → fixCount r ≤ 3)
    {r : Perm (Fin n)} (hr : r ∈ R) {a : Fin n} (ha : σ a ≠ a) : r a = a ∨ r a = σ a := by
  have hσσ := perm_apply_apply_of_mul_self_eq_one hσ
  have hrσ : ∀ x, r (σ x) = σ (r x) := fun x => by simpa using Perm.ext_iff.1 (hRc r hr) x
  obtain ⟨c, hcmem, hcs⟩ : ∃ c, c ∈ σ.support ∧
      c ∉ ({a, σ a, r a, σ (r a)} : Finset (Fin n)) := by
    apply Finset.exists_mem_notMem_of_card_lt_card
    have h4 : ({a, σ a, r a, σ (r a)} : Finset (Fin n)).card ≤ 4 := Finset.card_le_four
    omega
  have hc : σ c ≠ c := Equiv.Perm.mem_support.1 hcmem
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcs
  obtain ⟨hca, hcσa, hcra, hcσra⟩ := hcs
  have hcomm := commute_doublePairSwap_of_hinv hσ hk hk6 hRc hRn hinv ha hc hca hcσa hr
  have h1 := Perm.ext_iff.1 hcomm a
  have hac : a ≠ c := fun h => hca h.symm
  have hacσ : a ≠ σ c := fun h => hcσa (by rw [h, hσσ])
  simp only [Perm.mul_apply] at h1
  rw [swap_apply_of_ne_of_ne hac hacσ, swap_apply_left, hrσ] at h1
  by_contra hne
  rw [not_or] at hne
  have hrac : r a ≠ c := fun h => hcra h.symm
  have hracσ : r a ≠ σ c := fun h => hcσra (by rw [h, hσσ])
  rw [swap_apply_of_ne_of_ne hrac hracσ, swap_apply_of_ne_of_ne hne.1 hne.2] at h1
  exact ha (r.injective (by rw [hrσ, h1]))

theorem eq_sigma_of_involution_of_hinv {n k : ℕ} {σ : Perm (Fin n)} (hσ : σ * σ = 1)
    (hk : σ.support.card = 2 * k) (hk6 : 6 ≤ k)
    {R : Subgroup (Perm (Fin n))} (hσR : σ ∈ R) (hRc : ∀ r ∈ R, r * σ = σ * r)
    (hRn : ∀ a c : Fin n, σ a ≠ a → σ c ≠ c → c ≠ a → c ≠ σ a → ∀ r ∈ R,
      (swap a (σ a) * swap c (σ c)) * r * (swap a (σ a) * swap c (σ c))⁻¹ ∈ R)
    (hinv : ∀ r ∈ R, r * r = 1 → r ≠ 1 → fixCount r ≤ 3)
    {ρ : Perm (Fin n)} (hρ : ρ ∈ R) (hρ2 : ρ * ρ = 1) (hρ1 : ρ ≠ 1) : ρ = σ := by
  have hσσ := perm_apply_apply_of_mul_self_eq_one hσ
  have hρσ : ∀ x, ρ (σ x) = σ (ρ x) := fun x => by simpa using Perm.ext_iff.1 (hRc ρ hρ) x
  have hτ : ρ * σ ∈ R := mul_mem hρ hσR
  have hτ2 : (ρ * σ) * (ρ * σ) = 1 := by
    calc ρ * σ * (ρ * σ) = ρ * (σ * ρ) * σ := by group
      _ = ρ * (ρ * σ) * σ := by rw [hRc ρ hρ]
      _ = (ρ * ρ) * (σ * σ) := by group
      _ = 1 := by rw [hρ2, hσ, one_mul]
  by_contra hne
  have hτ1 : ρ * σ ≠ 1 := fun h => hne (by
    rw [eq_inv_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_right hσ])
  have h1 := hinv ρ hρ hρ2 hρ1
  have h2 := hinv (ρ * σ) hτ hτ2 hτ1
  have hcover : σ.support ⊆ (Finset.univ.filter fun i => ρ i = i) ∪
      (Finset.univ.filter fun i => (ρ * σ) i = i) := by
    intro a ha
    have ha' : σ a ≠ a := Equiv.Perm.mem_support.1 ha
    rcases apply_mem_pair_of_hinv hσ hk hk6 hRc hRn hinv hρ ha' with h | h
    · exact Finset.mem_union_left _ (by simpa using h)
    · refine Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩)
      rw [Perm.mul_apply, hρσ, h, hσσ]
  have h3 := Finset.card_le_card hcover
  have h4 := Finset.card_union_le (Finset.univ.filter fun i => ρ i = i)
    (Finset.univ.filter fun i => (ρ * σ) i = i)
  unfold fixCount at h1 h2
  omega

theorem rbar_twoElts_of_ge_six {n k : ℕ} {σ : Perm (Fin n)} (hσ : σ * σ = 1)
    (hk : σ.support.card = 2 * k) (hk6 : 6 ≤ k)
    {R : Subgroup (Perm (Fin n))} (hσR : σ ∈ R) (hRc : ∀ r ∈ R, r * σ = σ * r)
    (hRn : ∀ a c : Fin n, σ a ≠ a → σ c ≠ c → c ≠ a → c ≠ σ a → ∀ r ∈ R,
      (swap a (σ a) * swap c (σ c)) * r * (swap a (σ a) * swap c (σ c))⁻¹ ∈ R)
    (hinv : ∀ r ∈ R, r * r = 1 → r ≠ 1 → fixCount r ≤ 3) :
    ∀ r ∈ R, (∃ j : ℕ, r ^ (2 ^ j) = 1) → r = 1 ∨ r = σ := by
  have hσσ := perm_apply_apply_of_mul_self_eq_one hσ
  have key : ∀ j : ℕ, ∀ r ∈ R, r ^ (2 ^ j) = 1 → r = 1 ∨ r = σ := by
    intro j
    induction j with
    | zero =>
      intro r _ h
      exact Or.inl (by simpa using h)
    | succ j ih =>
      intro r hr h
      have h' : (r ^ 2) ^ (2 ^ j) = 1 := by rw [← pow_mul, ← pow_succ']; exact h
      rcases ih (r ^ 2) (pow_mem hr 2) h' with h2 | h2
      · by_cases hr1 : r = 1
        · exact Or.inl hr1
        · exact Or.inr (eq_sigma_of_involution_of_hinv hσ hk hk6 hσR hRc hRn hinv hr
            (by rwa [← sq]) hr1)
      · exfalso
        have hpos : σ.support.Nonempty := by
          rw [← Finset.card_pos]
          omega
        obtain ⟨a, ha⟩ := hpos
        have ha' : σ a ≠ a := Equiv.Perm.mem_support.1 ha
        have hrσ : ∀ x, r (σ x) = σ (r x) := fun x => by
          simpa using Perm.ext_iff.1 (hRc r hr) x
        have hrr : r (r a) = a := by
          rcases apply_mem_pair_of_hinv hσ hk hk6 hRc hRn hinv hr ha' with h3 | h3
          · rw [h3, h3]
          · rw [h3, hrσ, h3, hσσ]
        apply ha'
        rw [← h2, sq, Perm.mul_apply, hrr]
  rintro r hr ⟨j, hj⟩
  exact key j r hr hj

end CFSG.OddStandard.Solomon75
