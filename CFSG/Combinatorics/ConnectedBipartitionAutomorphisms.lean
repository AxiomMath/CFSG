module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Algebra.Order.Group.End
public import Mathlib.Data.Finite.Perm

public section

namespace CFSG.Combinatorics

variable {V : Type*} (Γ : SimpleGraph V)

theorem iff_mem_of_walk {X : Set V} (hedge : ∀ u v, Γ.Adj u v → (u ∈ X ↔ v ∉ X))
    (φ : Γ ≃g Γ) {u v : V} (p : Γ.Walk u v) : (φ u ∈ X ↔ u ∈ X) ↔ (φ v ∈ X ↔ v ∈ X) := by
  induction p with
  | nil => exact Iff.rfl
  | @cons a b c h _ ih =>
    rw [← ih, hedge a b h, hedge (φ a) (φ b) (φ.map_rel_iff.2 h)]
    tauto

theorem connected_bipartition_automorphism_action (hΓ : Γ.Connected) (X Y : Set V)
    (hXY : Disjoint X Y) (hcover : X ∪ Y = Set.univ) (_hX : X.Nonempty) (_hY : Y.Nonempty)
    (hedge : ∀ u v, Γ.Adj u v → (u ∈ X ∧ v ∈ Y) ∨ (u ∈ Y ∧ v ∈ X)) :
    (∀ φ : Γ ≃g Γ, (φ '' X = X ∧ φ '' Y = Y) ∨ (φ '' X = Y ∧ φ '' Y = X)) ∧
    ∃ ρ : (Γ ≃g Γ) →* Equiv.Perm ({X, Y} : Set (Set V)),
      (∀ (φ : Γ ≃g Γ) (S : ({X, Y} : Set (Set V))), (ρ φ S : Set V) = φ '' S) ∧
      (∀ φ : Γ ≃g Γ, φ ∈ ρ.ker ↔ φ '' X = X) ∧ ρ.ker.Normal ∧ ρ.ker.index ≤ 2 := by
  classical
  have hY : Y = Xᶜ := by
    ext v
    have hv : v ∈ X ∪ Y := hcover ▸ Set.mem_univ v
    have := fun h : v ∈ X => Set.disjoint_left.1 hXY h
    rw [Set.mem_union] at hv
    rw [Set.mem_compl_iff]
    tauto
  subst hY
  have hedge' : ∀ u v, Γ.Adj u v → (u ∈ X ↔ v ∉ X) := by
    intro u v h
    rcases hedge u v h with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact iff_of_true hu hv
    · exact iff_of_false hu (not_not.2 hv)
  have hconst : ∀ (φ : Γ ≃g Γ) (u v : V), (φ u ∈ X ↔ u ∈ X) ↔ (φ v ∈ X ↔ v ∈ X) :=
    fun φ u v => (hΓ.preconnected u v).elim (iff_mem_of_walk Γ hedge' φ)
  have himage : ∀ (φ : Γ ≃g Γ) (S : Set V), φ '' S = {v | φ⁻¹ v ∈ S} := by
    intro φ S
    ext v
    refine ⟨?_, fun hv => ⟨φ⁻¹ v, hv, RelIso.apply_inv_self φ v⟩⟩
    rintro ⟨w, hw, rfl⟩
    change φ⁻¹ (φ w) ∈ S
    rwa [RelIso.inv_apply_self]
  have hparts : ∀ φ : Γ ≃g Γ, (φ '' X = X ∧ φ '' Xᶜ = Xᶜ) ∨ (φ '' X = Xᶜ ∧ φ '' Xᶜ = X) := by
    intro φ
    obtain ⟨v₀⟩ := hΓ.nonempty
    by_cases h₀ : φ v₀ ∈ X ↔ v₀ ∈ X
    · have hall : ∀ v, φ v ∈ X ↔ v ∈ X := fun v => (hconst φ v₀ v).1 h₀
      have hX : φ '' X = X := by
        rw [himage]
        ext v
        change φ⁻¹ v ∈ X ↔ v ∈ X
        rw [← hall, RelIso.apply_inv_self]
      left
      exact ⟨hX, by rw [Set.image_compl_eq (f := (φ : V → V)) φ.bijective, hX]⟩
    · have hall : ∀ v, φ v ∈ X ↔ v ∉ X := fun v => by
        have := (not_congr (hconst φ v₀ v)).1 h₀
        tauto
      have hX : φ '' X = Xᶜ := by
        rw [himage]
        ext v
        change φ⁻¹ v ∈ X ↔ v ∉ X
        rw [← not_iff_not, not_not, ← hall, RelIso.apply_inv_self]
      right
      refine ⟨hX, ?_⟩
      rw [Set.image_compl_eq (f := (φ : V → V)) φ.bijective, hX, compl_compl]
  refine ⟨hparts, ?_⟩
  have hmem : ∀ (φ : Γ ≃g Γ) (S : ({X, Xᶜ} : Set (Set V))),
      φ '' (S : Set V) ∈ ({X, Xᶜ} : Set (Set V)) := by
    rintro φ ⟨S, hS⟩
    rcases hS with rfl | rfl <;> rcases hparts φ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl h1
    · exact Or.inr h1
    · exact Or.inr h2
    · exact Or.inl h2
  have hinvim : ∀ (φ : Γ ≃g Γ) (S : Set V), ⇑(φ⁻¹) '' (φ '' S) = S := by
    intro φ S
    rw [Set.image_image]
    simp only [RelIso.inv_apply_self, Set.image_id']
  let ρ : (Γ ≃g Γ) →* Equiv.Perm ({X, Xᶜ} : Set (Set V)) :=
    { toFun := fun φ =>
        { toFun := fun S => ⟨φ '' S, hmem φ S⟩
          invFun := fun S => ⟨⇑(φ⁻¹) '' S, hmem φ⁻¹ S⟩
          left_inv := fun S => Subtype.ext (hinvim φ S)
          right_inv := fun S => Subtype.ext (by
            simpa only [inv_inv] using hinvim φ⁻¹ (S : Set V)) }
      map_one' := Equiv.ext fun S => Subtype.ext (by
        change (fun v => v) '' (S : Set V) = S
        exact Set.image_id' _)
      map_mul' := fun φ ψ => Equiv.ext fun S => Subtype.ext (by
        change (fun v => φ (ψ v)) '' (S : Set V) = φ '' (ψ '' S)
        rw [Set.image_image]) }
  have hρ : ∀ (φ : Γ ≃g Γ) (S : ({X, Xᶜ} : Set (Set V))), (ρ φ S : Set V) = φ '' S :=
    fun _ _ => rfl
  have hker : ∀ φ : Γ ≃g Γ, φ ∈ ρ.ker ↔ φ '' X = X := by
    intro φ
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have := congrArg (fun σ : Equiv.Perm ({X, Xᶜ} : Set (Set V)) =>
        ((σ ⟨X, Or.inl rfl⟩ : ({X, Xᶜ} : Set (Set V))) : Set V)) h
      exact this
    · intro h
      have h' : φ '' Xᶜ = Xᶜ := by rw [Set.image_compl_eq (f := (φ : V → V)) φ.bijective, h]
      refine Equiv.ext fun ⟨S, hS⟩ => Subtype.ext ?_
      change φ '' S = S
      rcases hS with rfl | rfl
      · exact h
      · exact h'
  refine ⟨ρ, hρ, hker, MonoidHom.normal_ker ρ, ?_⟩
  have hfin : Finite ({X, Xᶜ} : Set (Set V)) := (Set.toFinite _)
  have hcard : Nat.card ({X, Xᶜ} : Set (Set V)) ≤ 2 := by
    rw [Nat.card_coe_set_eq]
    calc ({X, Xᶜ} : Set (Set V)).ncard ≤ ({Xᶜ} : Set (Set V)).ncard + 1 :=
          Set.ncard_insert_le _ _
      _ = 2 := by rw [Set.ncard_singleton]
  rw [Subgroup.index_ker]
  calc Nat.card ρ.range ≤ Nat.card (Equiv.Perm ({X, Xᶜ} : Set (Set V))) :=
        Subgroup.card_le_card_group _
    _ = (Nat.card ({X, Xᶜ} : Set (Set V))).factorial := Nat.card_perm
    _ ≤ (2 : ℕ).factorial := Nat.factorial_le hcard
    _ = 2 := rfl

end CFSG.Combinatorics
