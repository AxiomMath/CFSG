module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.AltFib

open Equiv Equiv.Perm Subgroup

variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]

@[expose] def fib (f : α → ι) (i : ι) : Finset α := Finset.univ.filter fun x => f x = i

omit [DecidableEq α] [Fintype ι] in
theorem mem_fib {f : α → ι} {i : ι} {x : α} : x ∈ fib f i ↔ f x = i := by
  simp [fib]

theorem two_mul_card_dvd_fiber (f : α → ι) (h2 : ∃ i, 2 ≤ (fib f i).card)
    (P : Subgroup (Perm α)) (hPA : P ≤ alternatingGroup α)
    (hPf : ∀ g ∈ P, ∀ x, f (g x) = f x) :
    2 * Nat.card P ∣ ∏ i, (fib f i).card.factorial := by
  classical
  let β : ι → Type _ := fun i => {x // f x = i}
  let e : (Σ i, β i) ≃ α := Equiv.sigmaFiberEquiv f
  let Ψ : (∀ i, Perm (β i)) →* Perm α :=
    ((Equiv.permCongrHom e).toMonoidHom).comp (sigmaCongrRightHom β)
  have hΨ : Function.Injective Ψ :=
    (Equiv.permCongrHom e).injective.comp sigmaCongrRightHom_injective
  have hmem : ∀ g : Perm α, (∀ x, f (g x) = f x) → g ∈ Ψ.range := by
    intro g hg
    refine ⟨fun i => g.subtypePerm (fun x => by rw [hg x]), ?_⟩
    ext x
    simp [Ψ, e, Equiv.sigmaFiberEquiv, Equiv.permCongrHom, sigmaCongrRightHom, β]
  have hPrange : P ≤ Ψ.range := fun g hg => hmem g (hPf g hg)
  let σ : (∀ i, Perm (β i)) →* ℤˣ := Perm.sign.comp Ψ
  have hQ : Nat.card (∀ i, Perm (β i)) = ∏ i, (fib f i).card.factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_pi]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fintype.card_perm]
    congr 1
    rw [Fintype.card_subtype]
    rfl
  have hodd : ∃ x : (∀ i, Perm (β i)), σ x = -1 := by
    obtain ⟨i, hi⟩ := h2
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega : 1 < (fib f i).card)
    have hfa : f a = i := mem_fib.1 ha
    have hfb : f b = i := mem_fib.1 hb
    obtain ⟨x, hx⟩ := hmem (swap a b) (by
      intro y
      by_cases h1 : y = a
      · subst h1; rw [swap_apply_left, hfa, hfb]
      · by_cases h3 : y = b
        · subst h3; rw [swap_apply_right, hfa, hfb]
        · rw [swap_apply_of_ne_of_ne h1 h3])
    refine ⟨x, ?_⟩
    simp only [σ, MonoidHom.comp_apply]
    rw [hx, sign_swap hab]
  have hrange : σ.range = ⊤ := by
    rw [eq_top_iff]
    intro u _
    obtain ⟨x, hx⟩ := hodd
    rcases Int.units_eq_one_or u with h | h
    · rw [h]; exact one_mem _
    · rw [h, ← hx]; exact ⟨x, rfl⟩
  have hker : 2 * Nat.card σ.ker = ∏ i, (fib f i).card.factorial := by
    have h := Subgroup.card_ker_mul_card_range σ
    have hz : Nat.card ℤˣ = 2 := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_units_int
    rw [hrange, Subgroup.card_top, hz, hQ] at h
    omega
  have hP' : Nat.card (P.comap Ψ) = Nat.card P := by
    rw [← Subgroup.card_map_of_injective hΨ (K := P.comap Ψ), Subgroup.map_comap_eq,
      inf_eq_right.2 hPrange]
  have hle : P.comap Ψ ≤ σ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    exact Perm.mem_alternatingGroup.1 (hPA hx)
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [hP'] at hdvd
  rw [← hker]
  exact Nat.mul_dvd_mul_left 2 hdvd

theorem card_dvd_fix (B F : Set α) (hBF : Disjoint B F) (P : Subgroup (Perm α))
    (hPA : P ≤ alternatingGroup α) (hB : ∀ g ∈ P, ∀ b ∈ B, g b = b)
    (hF : ∀ g ∈ P, ∀ x, g x ∈ F ↔ x ∈ F)
    (h2 : 2 ≤ F.ncard ∨ 2 ≤ (B ∪ F)ᶜ.ncard) :
    2 * Nat.card P ∣ F.ncard.factorial * (B ∪ F)ᶜ.ncard.factorial := by
  classical
  let f : α → α ⊕ Bool := fun x =>
    if x ∈ B then Sum.inl x else if x ∈ F then Sum.inr true else Sum.inr false
  have hBpres : ∀ g ∈ P, ∀ x, g x ∈ B ↔ x ∈ B := by
    intro g hg x
    constructor
    · intro hx
      have h1 := hB g hg _ hx
      have : g x = g (g x) := h1.symm
      have := g.injective this
      rw [this]
      exact hx
    · intro hx
      rw [hB g hg x hx]
      exact hx
  have hPf : ∀ g ∈ P, ∀ x, f (g x) = f x := by
    intro g hg x
    by_cases hx : x ∈ B
    · simp [f, hB g hg x hx]
    · have hgx : g x ∉ B := fun h => hx ((hBpres g hg x).1 h)
      by_cases hxF : x ∈ F
      · simp [f, hx, hgx, hxF, (hF g hg x).2 hxF]
      · have : g x ∉ F := fun h => hxF ((hF g hg x).1 h)
        simp [f, hx, hgx, hxF, this]
  have hfibT : fib f (Sum.inr true) = F.toFinset := by
    ext x
    simp only [mem_fib, Set.mem_toFinset]
    by_cases hx : x ∈ B
    · have : x ∉ F := fun h => Set.disjoint_left.1 hBF hx h
      simp [f, hx, this]
    · by_cases hxF : x ∈ F <;> simp [f, hx, hxF]
  have hfibF : fib f (Sum.inr false) = ((B ∪ F)ᶜ : Set α).toFinset := by
    ext x
    simp only [mem_fib, Set.mem_toFinset, Set.mem_compl_iff, Set.mem_union]
    by_cases hx : x ∈ B
    · simp [f, hx]
    · by_cases hxF : x ∈ F <;> simp [f, hx, hxF]
  have hfibL : ∀ y, (fib f (Sum.inl y)).card.factorial = 1 := by
    intro y
    apply Nat.factorial_eq_one.2
    have hsub : fib f (Sum.inl y) ⊆ {y} := by
      intro x hx
      rw [mem_fib] at hx
      by_cases hxB : x ∈ B
      · simpa [f, hxB] using hx
      · by_cases hxF : x ∈ F <;> simp [f, hxB, hxF] at hx
    exact (Finset.card_le_card hsub).trans (by simp)
  have h2' : ∃ i, 2 ≤ (fib f i).card := by
    rcases h2 with h | h
    · refine ⟨Sum.inr true, ?_⟩
      rw [hfibT, ← Set.ncard_eq_toFinset_card']
      exact h
    · refine ⟨Sum.inr false, ?_⟩
      rw [hfibF, ← Set.ncard_eq_toFinset_card']
      exact h
  have key := two_mul_card_dvd_fiber f h2' P hPA hPf
  rw [Fintype.prod_sum_type, Fintype.prod_bool] at key
  simp only [hfibL, Finset.prod_const_one, one_mul] at key
  rw [hfibT, hfibF, ← Set.ncard_eq_toFinset_card', ← Set.ncard_eq_toFinset_card'] at key
  exact key

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.AltFib
