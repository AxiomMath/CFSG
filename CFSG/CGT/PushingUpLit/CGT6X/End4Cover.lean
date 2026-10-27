module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.CGT.PushingUpLit.CGT6X.End4

open scoped commutatorElement

theorem hom_central_trivial {Γ A : Type*} [Group Γ] [Group.IsPerfect Γ] [Group A]
    [IsMulCommutative A] (f : Γ →* A) (g : Γ) : f g = 1 := by
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have : Subsingleton f.range := inferInstance
  have h : (⟨f g, g, rfl⟩ : f.range) = 1 := Subsingleton.elim _ _
  exact congrArg Subtype.val h

theorem hom_eq_of_central {M L : Type*} [Group M] [Group L] [Group.IsPerfect M] (f₁ f₂ : M →* L)
    (h : ∀ m, f₁ m * (f₂ m)⁻¹ ∈ Subgroup.center L) : f₁ = f₂ := by
  let ψ : M →* Subgroup.center L :=
    { toFun := fun m => ⟨f₁ m * (f₂ m)⁻¹, h m⟩
      map_one' := by ext; simp
      map_mul' := fun m n => by
        apply Subtype.ext
        show f₁ (m * n) * (f₂ (m * n))⁻¹ = (f₁ m * (f₂ m)⁻¹) * (f₁ n * (f₂ n)⁻¹)
        have hz : f₁ m * (f₁ n * (f₂ n)⁻¹) = (f₁ n * (f₂ n)⁻¹) * f₁ m :=
          Subgroup.mem_center_iff.mp (h n) (f₁ m)
        have hc : (f₁ n * (f₂ n)⁻¹) * (f₁ m * (f₂ m)⁻¹) =
            (f₁ m * (f₂ m)⁻¹) * (f₁ n * (f₂ n)⁻¹) :=
          Subgroup.mem_center_iff.mp (h m) (f₁ n * (f₂ n)⁻¹)
        calc f₁ (m * n) * (f₂ (m * n))⁻¹ = f₁ m * (f₁ n * (f₂ n)⁻¹) * (f₂ m)⁻¹ := by
              simp only [map_mul, mul_inv_rev]; group
          _ = (f₁ n * (f₂ n)⁻¹) * f₁ m * (f₂ m)⁻¹ := by rw [hz]
          _ = (f₁ n * (f₂ n)⁻¹) * (f₁ m * (f₂ m)⁻¹) := by group
          _ = (f₁ m * (f₂ m)⁻¹) * (f₁ n * (f₂ n)⁻¹) := hc }
  ext m
  have h1 := hom_central_trivial ψ m
  have h2 : f₁ m * (f₂ m)⁻¹ = 1 := congrArg Subtype.val h1
  exact mul_inv_eq_one.mp h2

theorem exists_cover {L M P : Type} [Group L] [Group M] [Group P] [Finite L] [Finite M]
    (e : L ⧸ Subgroup.center L ≃* P) (q : M →* P)
    (hsplit : ∀ (E : Type) [Group E] [Finite E] (π : E →* M), Function.Surjective π →
      π.ker ≤ Subgroup.center E → ∃ σ : M →* E, ∀ g, π (σ g) = g) :
    ∃ ρ : M →* L, ∀ m, e (QuotientGroup.mk (ρ m)) = q m := by
  let f1 : L →* P := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  let E : Subgroup (L × M) :=
    MonoidHom.eqLocus (f1.comp (MonoidHom.fst L M)) (q.comp (MonoidHom.snd L M))
  let π : E →* M := (MonoidHom.snd L M).comp E.subtype
  have hf1 : Function.Surjective f1 := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπ : Function.Surjective π := by
    intro m
    obtain ⟨l, hl⟩ := hf1 (q m)
    exact ⟨⟨(l, m), hl⟩, rfl⟩
  have hker : π.ker ≤ Subgroup.center E := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨⟨l, m⟩, hlm⟩ := x
    have hm : m = 1 := hx
    subst hm
    have hl1 : f1 l = 1 := by
      have : f1 l = q 1 := hlm
      rwa [map_one] at this
    have hl : l ∈ Subgroup.center L := by
      have h1 : e (QuotientGroup.mk l) = 1 := hl1
      have h2 : (QuotientGroup.mk l : L ⧸ Subgroup.center L) = 1 := by
        apply e.injective
        rw [h1, map_one]
      exact (QuotientGroup.eq_one_iff _).mp h2
    obtain ⟨⟨l', m'⟩, hlm'⟩ := y
    apply Subtype.ext
    show (l' * l, m' * 1) = (l * l', 1 * m')
    rw [Subgroup.mem_center_iff.mp hl l', mul_one, one_mul]
  obtain ⟨σ, hσ⟩ := hsplit E π hπ hker
  refine ⟨(MonoidHom.fst L M).comp (E.subtype.comp σ), fun m => ?_⟩
  have h1 : ((σ m : E) : L × M).2 = m := hσ m
  have h2 := (σ m).2
  have h3 : f1 ((σ m : L × M).1) = q ((σ m : L × M).2) := h2
  rw [h1] at h3
  exact h3

theorem cover_intertwine {L M P : Type*} [Group L] [Group M] [Group P] [Group.IsPerfect M]
    (e : L ⧸ Subgroup.center L ≃* P) (q : M →* P) (ρ : M →* L)
    (hρ : ∀ m, e (QuotientGroup.mk (ρ m)) = q m) (τ : L →* L) (δ : P →* P) (γ : M →* M)
    (hτ : ∀ y : L, e (QuotientGroup.mk (τ y)) = δ (e (QuotientGroup.mk y)))
    (hγ : ∀ m, q (γ m) = δ (q m)) : τ.comp ρ = ρ.comp γ := by
  apply hom_eq_of_central
  intro m
  show τ (ρ m) * (ρ (γ m))⁻¹ ∈ Subgroup.center L
  have h : (QuotientGroup.mk (τ (ρ m)) : L ⧸ Subgroup.center L) = QuotientGroup.mk (ρ (γ m)) := by
    apply e.injective
    rw [hτ, hρ, hρ, hγ]
  have := QuotientGroup.eq_iff_div_mem.mp h
  rwa [div_eq_mul_inv] at this

theorem eq_map_of_perfect {L M P : Type*} [Group L] [Group M] [Group P] [Finite M]
    (e : L ⧸ Subgroup.center L ≃* P) (q : M →* P) (ρ : M →* L)
    (hρ : ∀ m, e (QuotientGroup.mk (ρ m)) = q m) (Y : Subgroup L) (hY : ⁅Y, Y⁆ = Y)
    (O : Subgroup M) (hYO : ∀ y ∈ Y, ∃ o ∈ O, e (QuotientGroup.mk y) = q o)
    (hcard : Nat.card O ≤ Nat.card Y) : Y = O.map ρ := by
  have hcomm : ∀ {a b z w : L}, (∀ g, g * z = z * g) → (∀ g, g * w = w * g) →
      ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
    intro a b z w hz hw
    have h1 : z * (b * w) * z⁻¹ = b * w := by
      rw [← hz (b * w)]; group
    have h2 : w * a⁻¹ * w⁻¹ = a⁻¹ := by
      rw [← hw a⁻¹]; group
    calc ⁅a * z, b * w⁆ = a * (z * (b * w) * z⁻¹) * a⁻¹ * w⁻¹ * b⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = a * (b * w) * a⁻¹ * w⁻¹ * b⁻¹ := by rw [h1]
      _ = a * b * (w * a⁻¹ * w⁻¹) * b⁻¹ := by group
      _ = ⁅a, b⁆ := by rw [h2]; simp only [commutatorElement_def]
  have hdecomp : ∀ y ∈ Y, ∃ o ∈ O, ∃ z ∈ Subgroup.center L, y = ρ o * z := by
    intro y hy
    obtain ⟨o, ho, h⟩ := hYO y hy
    refine ⟨o, ho, (ρ o)⁻¹ * y, ?_, by group⟩
    have h1 : (QuotientGroup.mk (ρ o) : L ⧸ Subgroup.center L) = QuotientGroup.mk y := by
      apply e.injective
      rw [hρ, h]
    exact QuotientGroup.eq.mp h1
  have hle : Y ≤ O.map ρ := by
    have hY' : ⁅Y, Y⁆ ≤ O.map ρ := by
      rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      obtain ⟨o₁, ho₁, z₁, hz₁, rfl⟩ := hdecomp g₁ hg₁
      obtain ⟨o₂, ho₂, z₂, hz₂, rfl⟩ := hdecomp g₂ hg₂
      rw [hcomm (Subgroup.mem_center_iff.mp hz₁) (Subgroup.mem_center_iff.mp hz₂)]
      refine ⟨⁅o₁, o₂⁆, ?_, map_commutatorElement ρ o₁ o₂⟩
      simp only [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ho₁ ho₂) (inv_mem ho₁)) (inv_mem ho₂)
    rwa [hY] at hY'
  have : Finite (O.map ρ) := Finite.of_surjective _ (ρ.subgroupMap_surjective O)
  have hcard' : Nat.card (O.map ρ) ≤ Nat.card Y := by
    refine le_trans ?_ hcard
    exact Nat.card_le_card_of_surjective _ (ρ.subgroupMap_surjective O)
  exact Subgroup.eq_of_le_of_card_ge hle hcard'

end CFSG.CGT.PushingUpLit.CGT6X.End4
