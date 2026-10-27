module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.End

public section

namespace CFSG.EvenSporadicStandard.HNRecog.SideF4

private def P {Γ Y : Type*} [Group Γ] (act : Γ →* Equiv.Perm Y) {n : ℕ}
    (V : Fin n → Set Y) (x : Γ) (τ : Equiv.Perm (Fin n)) : Prop :=
  ∀ (i : Fin n) (y : Y), act x y ∈ V (τ i) ↔ y ∈ V i

private lemma P_one {Γ Y : Type*} [Group Γ] (act : Γ →* Equiv.Perm Y) {n : ℕ}
    (V : Fin n → Set Y) : P act V 1 1 := by
  intro i y
  rw [map_one act]
  exact Iff.rfl

private lemma P_mul {Γ Y : Type*} [Group Γ] (act : Γ →* Equiv.Perm Y) {n : ℕ}
    (V : Fin n → Set Y) {a b : Γ} {τ τ' : Equiv.Perm (Fin n)}
    (hτ : P act V a τ) (hτ' : P act V b τ') : P act V (a * b) (τ * τ') := by
  intro i y
  have h1 : act a (act b y) ∈ V (τ (τ' i)) ↔ act b y ∈ V (τ' i) := hτ (τ' i) (act b y)
  have h2 : act b y ∈ V (τ' i) ↔ y ∈ V i := hτ' i y
  rw [map_mul act a b, Equiv.Perm.mul_apply]
  exact h1.trans h2

private lemma P_inv {Γ Y : Type*} [Group Γ] (act : Γ →* Equiv.Perm Y) {n : ℕ}
    (V : Fin n → Set Y) {a : Γ} {τ : Equiv.Perm (Fin n)}
    (hτ : P act V a τ) : P act V a⁻¹ τ⁻¹ := by
  intro i y
  have h : act a (act a⁻¹ y) ∈ V (τ (τ⁻¹ i)) ↔ act a⁻¹ y ∈ V (τ⁻¹ i) :=
    hτ (τ⁻¹ i) (act a⁻¹ y)
  have hx : act a (act a⁻¹ y) = y := by
    rw [map_inv act a]
    exact Equiv.apply_symm_apply (act a) y
  have hτi : τ (τ⁻¹ i) = i := Equiv.apply_symm_apply τ i
  rw [hx, hτi] at h
  exact h.symm

private lemma P_unique {Γ Y : Type*} [Group Γ] {act : Γ →* Equiv.Perm Y} {n : ℕ}
    {V : Fin n → Set Y} (hV : Function.Injective V) {x : Γ} {τ τ' : Equiv.Perm (Fin n)}
    (hτ : P act V x τ) (hτ' : P act V x τ') : τ = τ' := by
  refine Equiv.ext (fun i => hV (Set.ext (fun z => ?_)))
  have h1 : act x ((act x).symm z) ∈ V (τ i) ↔ ((act x).symm z) ∈ V i := hτ i _
  have h2 : act x ((act x).symm z) ∈ V (τ' i) ↔ ((act x).symm z) ∈ V i := hτ' i _
  rw [Equiv.apply_symm_apply] at h1 h2
  exact h1.trans h2.symm

theorem exists_hom_of_permuted_family {Γ : Type*} [Group Γ] {ι : Type*} (g : ι → Γ)
    (hg : Subgroup.closure (Set.range g) = ⊤) {Y : Type*} (act : Γ →* Equiv.Perm Y) {n : ℕ}
    (V : Fin n → Set Y) (hV : Function.Injective V) (σ : ι → Equiv.Perm (Fin n))
    (hσ : ∀ (s : ι) (i : Fin n) (y : Y), act (g s) y ∈ V (σ s i) ↔ y ∈ V i) :
    ∃ φ : Γ →* Equiv.Perm (Fin n), (∀ s, φ (g s) = σ s) ∧
      ∀ (x : Γ) (i : Fin n) (y : Y), act x y ∈ V (φ x i) ↔ y ∈ V i := by
  have h_exists : ∀ x : Γ, ∃ τ : Equiv.Perm (Fin n), P act V x τ := by
    intro x
    refine Subgroup.closure_induction (k := Set.range g)
      (p := fun x _ => ∃ τ : Equiv.Perm (Fin n), P act V x τ) ?_ ?_ ?_ ?_ ?_
    · rintro x hx
      obtain ⟨s, hs⟩ := Set.mem_range.mp hx
      rw [← hs]
      exact ⟨σ s, hσ s⟩
    · exact ⟨1, P_one act V⟩
    · rintro a b _ _ ⟨τ, hτ⟩ ⟨τ', hτ'⟩
      exact ⟨τ * τ', P_mul act V hτ hτ'⟩
    · rintro a _ ⟨τ, hτ⟩
      exact ⟨τ⁻¹, P_inv act V hτ⟩
    · rw [hg]
      exact Subgroup.mem_top x
  let φ : Γ → Equiv.Perm (Fin n) := fun x => Classical.choose (h_exists x)
  have hφ : ∀ x, P act V x (φ x) := fun x => Classical.choose_spec (h_exists x)
  have hφ_one : φ 1 = 1 := P_unique hV (hφ 1) (P_one act V)
  have hφ_mul : ∀ a b, φ (a * b) = φ a * φ b := fun a b =>
    P_unique hV (hφ (a * b)) (P_mul act V (hφ a) (hφ b))
  refine ⟨{ toFun := φ, map_one' := hφ_one, map_mul' := hφ_mul }, ?_, ?_⟩
  · intro s
    exact P_unique hV (hφ (g s)) (hσ s)
  · intro x i y
    exact hφ x i y

end CFSG.EvenSporadicStandard.HNRecog.SideF4
