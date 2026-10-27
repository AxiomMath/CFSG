module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Tactic.NormNum.Ineq

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0

open Equiv Equiv.Perm

theorem perm_apply_inv_self {α : Type*} (σ : Perm α) (x : α) : σ (σ⁻¹ x) = x :=
  σ.apply_symm_apply x

variable {N : ℕ}

@[expose] def pairSwaps (ω : Perm (Fin N)) (Δ₀ : Finset (Fin N)) : Set (Perm (Fin N)) :=
  {τ | ∃ x, x ∉ Δ₀ ∧ τ = swap x (ω x)}

@[expose] def E0grp (P : Subgroup (Perm (Fin N))) (ω : Perm (Fin N)) (Δ₀ : Finset (Fin N)) :
    Subgroup (Perm (Fin N)) :=
  P ⊔ Subgroup.closure (pairSwaps ω Δ₀)

structure E0Shape (P : Subgroup (Perm (Fin N))) (ω : Perm (Fin N)) (Δ₀ : Finset (Fin N)) :
    Prop where
  card : Δ₀.card = 4
  Psq : ∀ p ∈ P, p * p = 1
  Pfix : ∀ p ∈ P, ∀ i, i ∉ Δ₀ → p i = i
  Pcard : Nat.card P = 4
  Ptrans : ∀ i ∈ Δ₀, ∀ j ∈ Δ₀, ∃ p ∈ P, p i = j
  ωω : ∀ x, ω (ω x) = x
  ωΔ : ∀ x ∈ Δ₀, ω x = x
  ωfree : ∀ x, x ∉ Δ₀ → ω x ≠ x

variable {P : Subgroup (Perm (Fin N))} {ω : Perm (Fin N)} {Δ₀ : Finset (Fin N)}

namespace E0Shape

theorem ω_not_mem (h : E0Shape P ω Δ₀) {x : Fin N} (hx : x ∉ Δ₀) : ω x ∉ Δ₀ := by
  intro hmem
  apply h.ωfree x hx
  have := h.ωΔ _ hmem
  rw [h.ωω] at this
  exact this.symm

theorem P_mem (h : E0Shape P ω Δ₀) {p : Perm (Fin N)} (hp : p ∈ P) {x : Fin N} (hx : x ∈ Δ₀) :
    p x ∈ Δ₀ := by
  by_contra hne
  have h1 := h.Pfix p hp (p x) hne
  have h2 : p x = x := p.injective h1
  exact hne (by rw [h2]; exact hx)

theorem reg (h : E0Shape P ω Δ₀) {p : Perm (Fin N)} (hp : p ∈ P) {x : Fin N} (hx : x ∈ Δ₀)
    (hpx : p x = x) : p = 1 := by
  classical
  have : Fintype P := Fintype.ofFinite P
  let g : P → Δ₀ := fun q => ⟨(q : Perm (Fin N)) x, h.P_mem q.2 hx⟩
  have hsurj : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨q, hq, hqy⟩ := h.Ptrans x hx y hy
    exact ⟨⟨q, hq⟩, Subtype.ext hqy⟩
  have hcard : Fintype.card P = Fintype.card Δ₀ := by
    rw [← Nat.card_eq_fintype_card, h.Pcard, Fintype.card_coe, h.card]
  have hbij := (Fintype.bijective_iff_surjective_and_card g).2 ⟨hsurj, hcard⟩
  have : g ⟨p, hp⟩ = g 1 := Subtype.ext (by simp [g, hpx])
  have := hbij.1 this
  exact congrArg Subtype.val this

@[expose] def Eprop (P : Subgroup (Perm (Fin N))) (ω : Perm (Fin N)) (Δ₀ : Finset (Fin N))
    (σ : Perm (Fin N)) : Prop :=
  (∃ p ∈ P, ∀ x ∈ Δ₀, σ x = p x) ∧ ∀ x, x ∉ Δ₀ → σ x = x ∨ σ x = ω x

theorem Eprop_mem_mono (h : E0Shape P ω Δ₀) {σ : Perm (Fin N)} (hσ : Eprop P ω Δ₀ σ)
    {x : Fin N} (hx : x ∈ Δ₀) : σ x ∈ Δ₀ := by
  obtain ⟨⟨p, hp, hpx⟩, -⟩ := hσ
  rw [hpx x hx]
  exact h.P_mem hp hx

theorem Eprop_not_mem (h : E0Shape P ω Δ₀) {σ : Perm (Fin N)} (hσ : Eprop P ω Δ₀ σ)
    {x : Fin N} (hx : x ∉ Δ₀) : σ x ∉ Δ₀ := by
  rcases hσ.2 x hx with h1 | h1
  · rw [h1]; exact hx
  · rw [h1]; exact h.ω_not_mem hx

theorem Eprop_mul (h : E0Shape P ω Δ₀) {σ τ : Perm (Fin N)} (hσ : Eprop P ω Δ₀ σ)
    (hτ : Eprop P ω Δ₀ τ) : Eprop P ω Δ₀ (σ * τ) := by
  refine ⟨?_, fun x hx => ?_⟩
  · obtain ⟨pσ, hpσ, hσx⟩ := hσ.1
    obtain ⟨pτ, hpτ, hτx⟩ := hτ.1
    refine ⟨pσ * pτ, mul_mem hpσ hpτ, fun x hx => ?_⟩
    rw [Perm.mul_apply, hτx x hx, hσx _ (h.P_mem hpτ hx)]
    rfl
  · rw [Perm.mul_apply]
    rcases hτ.2 x hx with h1 | h1
    · rw [h1]; exact hσ.2 x hx
    · rw [h1]
      rcases hσ.2 (ω x) (h.ω_not_mem hx) with h2 | h2
      · right; exact h2
      · left; rw [h2, h.ωω]

theorem Eprop_inv (h : E0Shape P ω Δ₀) {σ : Perm (Fin N)} (hσ : Eprop P ω Δ₀ σ) :
    Eprop P ω Δ₀ σ⁻¹ := by
  refine ⟨?_, fun x hx => ?_⟩
  · obtain ⟨p, hp, hpx⟩ := hσ.1
    refine ⟨p⁻¹, inv_mem hp, fun x hx => ?_⟩
    have hy : σ⁻¹ x ∈ Δ₀ := by
      by_contra hn
      have := Eprop_not_mem h hσ hn
      rw [perm_apply_inv_self] at this
      exact this hx
    have h1 : σ (σ⁻¹ x) = p (σ⁻¹ x) := hpx _ hy
    rw [perm_apply_inv_self] at h1
    exact ((Perm.inv_eq_iff_eq).2 h1).symm
  · have hy : σ⁻¹ x ∉ Δ₀ := by
      intro hn
      have := Eprop_mem_mono h hσ hn
      rw [perm_apply_inv_self] at this
      exact hx this
    rcases hσ.2 _ hy with h1 | h1
    · left
      rw [perm_apply_inv_self] at h1
      exact h1.symm
    · right
      rw [perm_apply_inv_self] at h1
      generalize σ⁻¹ x = y at h1 ⊢
      rw [h1, h.ωω]

theorem mem_E0grp_prop (h : E0Shape P ω Δ₀) {σ : Perm (Fin N)} (hσ : σ ∈ E0grp P ω Δ₀) :
    Eprop P ω Δ₀ σ := by
  have hcl : E0grp P ω Δ₀ = Subgroup.closure ((P : Set (Perm (Fin N))) ∪ pairSwaps ω Δ₀) := by
    rw [E0grp, Subgroup.closure_union, Subgroup.closure_eq]
  rw [hcl] at hσ
  refine Subgroup.closure_induction (p := fun σ _ => Eprop P ω Δ₀ σ) ?_ ?_ ?_ ?_ hσ
  · rintro σ (hσP | ⟨x₀, hx₀, rfl⟩)
    · exact ⟨⟨σ, hσP, fun _ _ => rfl⟩, fun x hx => Or.inl (h.Pfix σ hσP x hx)⟩
    · refine ⟨⟨1, one_mem _, fun y hy => ?_⟩, fun y hy => ?_⟩
      · have h1 : y ≠ x₀ := fun e => hx₀ (e ▸ hy)
        have h2 : y ≠ ω x₀ := fun e => h.ω_not_mem hx₀ (e ▸ hy)
        rw [swap_apply_of_ne_of_ne h1 h2]; rfl
      · by_cases h1 : y = x₀
        · right; rw [h1, swap_apply_left]
        · by_cases h2 : y = ω x₀
          · right; rw [h2, swap_apply_right, h.ωω]
          · left; exact swap_apply_of_ne_of_ne h1 h2
  · exact ⟨⟨1, one_mem _, fun _ _ => rfl⟩, fun _ _ => Or.inl rfl⟩
  · intro σ τ _ _ hσ hτ
    exact Eprop_mul h hσ hτ
  · intro σ _ hσ
    exact Eprop_inv h hσ

theorem swap_mem_E0grp {x : Fin N} (hx : x ∉ Δ₀) :
    swap x (ω x) ∈ E0grp P ω Δ₀ :=
  Subgroup.mem_sup_right (Subgroup.subset_closure ⟨x, hx, rfl⟩)

theorem P_le_E0grp : P ≤ E0grp P ω Δ₀ := le_sup_left

theorem conj_mem_E0grp (h : E0Shape P ω Δ₀) {σ : Perm (Fin N)} (hΔ : ∀ y ∈ Δ₀, σ y = y)
    (hω : ∀ y, y ∉ Δ₀ → σ (ω y) = ω (σ y)) {e : Perm (Fin N)} (he : e ∈ E0grp P ω Δ₀) :
    σ * e * σ⁻¹ ∈ E0grp P ω Δ₀ := by
  have hcl : E0grp P ω Δ₀ = Subgroup.closure ((P : Set (Perm (Fin N))) ∪ pairSwaps ω Δ₀) := by
    rw [E0grp, Subgroup.closure_union, Subgroup.closure_eq]
  have hnot : ∀ y, y ∉ Δ₀ → σ y ∉ Δ₀ := by
    intro y hy hmem
    apply hy
    have := hΔ _ hmem
    exact σ.injective this ▸ hmem
  rw [hcl] at he
  refine Subgroup.closure_induction (p := fun e _ => σ * e * σ⁻¹ ∈ E0grp P ω Δ₀) ?_ ?_ ?_ ?_ he
  · rintro e (heP | ⟨y, hy, rfl⟩)
    · have : σ * e * σ⁻¹ = e := by
        ext z
        simp only [Perm.mul_apply]
        by_cases hz : z ∈ Δ₀
        · have h1 : σ⁻¹ z = z := by rw [Perm.inv_eq_iff_eq]; exact (hΔ z hz).symm
          rw [h1, hΔ _ (h.P_mem heP hz)]
        · have h1 : σ⁻¹ z ∉ Δ₀ := by
            intro hmem
            apply hz
            have := hΔ _ hmem
            rw [perm_apply_inv_self] at this
            exact this ▸ hmem
          rw [h.Pfix e heP _ h1, perm_apply_inv_self, h.Pfix e heP _ hz]
      rw [this]; exact P_le_E0grp heP
    · rw [← swap_apply_apply, hω y hy]
      exact swap_mem_E0grp (hnot y hy)
  · simp
  · intro e f _ _ he hf
    have : σ * (e * f) * σ⁻¹ = (σ * e * σ⁻¹) * (σ * f * σ⁻¹) := by group
    rw [this]; exact mul_mem he hf
  · intro e _ he
    have : σ * e⁻¹ * σ⁻¹ = (σ * e * σ⁻¹)⁻¹ := by group
    rw [this]; exact inv_mem he

end E0Shape

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0
