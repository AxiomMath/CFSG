module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.ClassicalInvolution.Asc77.Star3T

open Equiv

@[expose] def sw3 : Fin 3 → Perm (Fin 3) := ![swap 0 1, swap 0 2, swap 1 2]

theorem isSwap_iff_sw3 (σ : Perm (Fin 3)) : σ.IsSwap ↔ ∃ i, σ = sw3 i := by
  constructor
  · rintro ⟨x, y, hxy, rfl⟩
    have : ∀ x y : Fin 3, x ≠ y → ∃ i, swap x y = sw3 i := by decide
    exact this x y hxy
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact ⟨0, 1, by decide, rfl⟩
    · exact ⟨0, 2, by decide, rfl⟩
    · exact ⟨1, 2, by decide, rfl⟩

theorem sw3_injective : Function.Injective sw3 := by decide

theorem exists_swap_fixed_three (α : Perm (Fin 3) → Perm (Fin 3))
    (h2 : ∀ x, α (α x) = x) (hs : ∀ σ, σ.IsSwap → (α σ).IsSwap) :
    ∃ σ : Perm (Fin 3), σ.IsSwap ∧ α σ = σ := by
  have hex : ∀ i, ∃ j, α (sw3 i) = sw3 j := fun i =>
    (isSwap_iff_sw3 _).mp (hs _ ((isSwap_iff_sw3 _).mpr ⟨i, rfl⟩))
  choose π hπ using hex
  have hinv : Function.Involutive π := by
    intro i
    apply sw3_injective
    rw [← hπ, ← hπ, h2]
  have hfix : ∀ π : Perm (Fin 3), (∀ i, π (π i) = i) → ∃ i, π i = i := by decide
  obtain ⟨i, hi⟩ := hfix (hinv.toPerm π) hinv
  refine ⟨sw3 i, (isSwap_iff_sw3 _).mpr ⟨i, rfl⟩, ?_⟩
  rw [hπ i]
  exact congrArg sw3 hi

@[expose] def sw4 : Fin 6 → Perm (Fin 4) :=
  ![swap 0 1, swap 0 2, swap 0 3, swap 1 2, swap 1 3, swap 2 3]

theorem isSwap_iff_sw4 (σ : Perm (Fin 4)) : σ.IsSwap ↔ ∃ i, σ = sw4 i := by
  constructor
  · rintro ⟨x, y, hxy, rfl⟩
    have : ∀ x y : Fin 4, x ≠ y → ∃ i, swap x y = sw4 i := by decide
    exact this x y hxy
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact ⟨0, 1, by decide, rfl⟩
    · exact ⟨0, 2, by decide, rfl⟩
    · exact ⟨0, 3, by decide, rfl⟩
    · exact ⟨1, 2, by decide, rfl⟩
    · exact ⟨1, 3, by decide, rfl⟩
    · exact ⟨2, 3, by decide, rfl⟩

theorem sw4_injective : Function.Injective sw4 := by decide

@[expose] def cj4 : Fin 6 → Fin 6 → Fin 6 :=
  ![![0, 3, 4, 1, 2, 5], ![3, 1, 5, 0, 4, 2], ![4, 5, 2, 3, 0, 1], ![1, 0, 2, 3, 5, 4],
    ![2, 1, 0, 5, 4, 3], ![0, 2, 1, 4, 3, 5]]

theorem sw4_cj4 (i j : Fin 6) : sw4 (cj4 i j) = sw4 i * sw4 j * sw4 i := by
  have : ∀ i j : Fin 6, sw4 (cj4 i j) = sw4 i * sw4 j * sw4 i := by decide
  exact this i j

theorem exists_fixed_of_cj4 (π : Perm (Fin 6)) (hc : ∀ i j, π (cj4 i j) = cj4 (π i) (π j))
    (hπ : ∀ i, π (π i) = i) : ∃ i, π i = i := by
  have : ∀ π : Perm (Fin 6), (∀ i j, π (cj4 i j) = cj4 (π i) (π j)) → (∀ i, π (π i) = i) →
      ∃ i, π i = i := by decide +kernel
  exact this π hc hπ

theorem exists_swap_fixed_four (α : Perm (Fin 4) → Perm (Fin 4))
    (hmul : ∀ x y, α (x * y) = α x * α y) (h2 : ∀ x, α (α x) = x)
    (hs : ∀ σ, σ.IsSwap → (α σ).IsSwap) : ∃ σ : Perm (Fin 4), σ.IsSwap ∧ α σ = σ := by
  have hex : ∀ i, ∃ j, α (sw4 i) = sw4 j := fun i =>
    (isSwap_iff_sw4 _).mp (hs _ ((isSwap_iff_sw4 _).mpr ⟨i, rfl⟩))
  choose π hπ using hex
  have hinv : Function.Involutive π := by
    intro i
    apply sw4_injective
    rw [← hπ, ← hπ, h2]
  have hc : ∀ i j, π (cj4 i j) = cj4 (π i) (π j) := by
    intro i j
    apply sw4_injective
    rw [← hπ, sw4_cj4, sw4_cj4, hmul, hmul, hπ, hπ]
  obtain ⟨i, hi⟩ := exists_fixed_of_cj4 (hinv.toPerm π) hc hinv
  refine ⟨sw4 i, (isSwap_iff_sw4 _).mpr ⟨i, rfl⟩, ?_⟩
  rw [hπ i]
  exact congrArg sw4 hi

section Subgroup

variable {Q : Type*} [Group Q]

theorem exists_fixed_of_perm_three (α : Q ≃* Q) (h2 : ∀ x, α (α x) = x) {S : Set Q}
    (hS : ∀ x ∈ S, α x ∈ S) {H : Subgroup Q} (hH : ∀ x ∈ H, α x ∈ H)
    (ψ : ↥H ≃* Perm (Fin 3)) (hψ : ∀ (x : Q) (hx : x ∈ H), x ∈ S ↔ (ψ ⟨x, hx⟩).IsSwap) :
    ∃ x ∈ S, α x = x := by
  let β : Perm (Fin 3) → Perm (Fin 3) := fun σ => ψ ⟨α (ψ.symm σ : Q), hH _ (ψ.symm σ).2⟩
  have hmem : ∀ σ : Perm (Fin 3), σ.IsSwap → (ψ.symm σ : Q) ∈ S := fun σ hσ =>
    (hψ _ (ψ.symm σ).2).mpr (by simpa using hσ)
  have hβ2 : ∀ σ, β (β σ) = σ := fun σ => by
    simp only [β, MulEquiv.symm_apply_apply, h2, Subtype.coe_eta, MulEquiv.apply_symm_apply]
  have hβs : ∀ σ : Perm (Fin 3), σ.IsSwap → (β σ).IsSwap := fun σ hσ =>
    (hψ _ (hH _ (ψ.symm σ).2)).mp (hS _ (hmem σ hσ))
  obtain ⟨σ, hσ, hfix⟩ := exists_swap_fixed_three β hβ2 hβs
  refine ⟨(ψ.symm σ : Q), hmem σ hσ, ?_⟩
  have := congrArg ψ.symm hfix
  simp only [β, MulEquiv.symm_apply_apply] at this
  exact congrArg Subtype.val this

theorem exists_fixed_of_perm_four (α : Q ≃* Q) (h2 : ∀ x, α (α x) = x) {S : Set Q}
    (hS : ∀ x ∈ S, α x ∈ S) {H : Subgroup Q} (hH : ∀ x ∈ H, α x ∈ H)
    (ψ : ↥H ≃* Perm (Fin 4)) (hψ : ∀ (x : Q) (hx : x ∈ H), x ∈ S ↔ (ψ ⟨x, hx⟩).IsSwap) :
    ∃ x ∈ S, α x = x := by
  let β : Perm (Fin 4) → Perm (Fin 4) := fun σ => ψ ⟨α (ψ.symm σ : Q), hH _ (ψ.symm σ).2⟩
  have hmem : ∀ σ : Perm (Fin 4), σ.IsSwap → (ψ.symm σ : Q) ∈ S := fun σ hσ =>
    (hψ _ (ψ.symm σ).2).mpr (by simpa using hσ)
  have hβ2 : ∀ σ, β (β σ) = σ := fun σ => by
    simp only [β, MulEquiv.symm_apply_apply, h2, Subtype.coe_eta, MulEquiv.apply_symm_apply]
  have hβm : ∀ σ τ, β (σ * τ) = β σ * β τ := fun σ τ => by
    simp only [β, ← map_mul]
    congr 1
    apply Subtype.ext
    simp [map_mul]
  have hβs : ∀ σ : Perm (Fin 4), σ.IsSwap → (β σ).IsSwap := fun σ hσ =>
    (hψ _ (hH _ (ψ.symm σ).2)).mp (hS _ (hmem σ hσ))
  obtain ⟨σ, hσ, hfix⟩ := exists_swap_fixed_four β hβm hβ2 hβs
  refine ⟨(ψ.symm σ : Q), hmem σ hσ, ?_⟩
  have := congrArg ψ.symm hfix
  simp only [β, MulEquiv.symm_apply_apply] at this
  exact congrArg Subtype.val this

end Subgroup

end CFSG.ClassicalInvolution.Asc77.Star3T
