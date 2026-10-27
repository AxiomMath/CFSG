module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.Uniqueness.Dihedral
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

namespace XDataAut

@[expose] def conjSubHom {X : Type*} [Group X] (D : Subgroup X) (g : X)
    (h : ∀ d ∈ D, g * d * g⁻¹ ∈ D) : ↥D →* ↥D where
  toFun d := ⟨g * d * g⁻¹, h d d.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    change g * ((a : X) * (b : X)) * g⁻¹ = (g * (a : X) * g⁻¹) * (g * (b : X) * g⁻¹)
    group

theorem exists_mulAut_of_map_ker {G K : Type*} [Group G] [Group K] (φ : G →* K)
    (hφ : Function.Surjective φ) (σ τ : G →* G) (hστ : ∀ x, τ (σ x) = x) (hτσ : ∀ x, σ (τ x) = x)
    (hσ : ∀ x, φ x = 1 → φ (σ x) = 1) (hτ : ∀ x, φ x = 1 → φ (τ x) = 1) :
    ∃ α : MulAut K, ∀ x, α (φ x) = φ (σ x) := by
  have hσk : φ.ker ≤ (φ.comp σ).ker := fun x hx => hσ x hx
  have hτk : φ.ker ≤ (φ.comp τ).ker := fun x hx => hτ x hx
  let α₀ : K →* K := φ.liftOfSurjective hφ ⟨φ.comp σ, hσk⟩
  let α₁ : K →* K := φ.liftOfSurjective hφ ⟨φ.comp τ, hτk⟩
  have h₀ : ∀ x, α₀ (φ x) = φ (σ x) := fun x =>
    φ.liftOfRightInverse_comp_apply _ _ ⟨φ.comp σ, hσk⟩ x
  have h₁ : ∀ x, α₁ (φ x) = φ (τ x) := fun x =>
    φ.liftOfRightInverse_comp_apply _ _ ⟨φ.comp τ, hτk⟩ x
  refine ⟨MonoidHom.toMulEquiv α₀ α₁ ?_ ?_, h₀⟩
  · ext k
    obtain ⟨x, rfl⟩ := hφ k
    simp [h₀, h₁, hστ]
  · ext k
    obtain ⟨x, rfl⟩ := hφ k
    simp [h₀, h₁, hτσ]

theorem exists_mulAut_of_conj {X K : Type*} [Group X] [Group K] {D O : Subgroup X} (φ : ↥D →* K)
    (hφ : Function.Surjective φ) (hker : φ.ker = O.subgroupOf D) {g : X}
    (hgD : ∀ d ∈ D, g * d * g⁻¹ ∈ D) (hgD' : ∀ d ∈ D, g⁻¹ * d * g ∈ D)
    (hgO : ∀ o ∈ O, g * o * g⁻¹ ∈ O) (hgO' : ∀ o ∈ O, g⁻¹ * o * g ∈ O) :
    ∃ α : MulAut K, ∀ d e : ↥D, (e : X) = g * d * g⁻¹ → α (φ d) = φ e := by
  have hgD'' : ∀ d ∈ D, g⁻¹ * d * g⁻¹⁻¹ ∈ D := fun d hd => by simpa using hgD' d hd
  let σ := conjSubHom D g hgD
  let τ := conjSubHom D g⁻¹ hgD''
  have hστ : ∀ x, τ (σ x) = x := fun x => by
    apply Subtype.ext
    change g⁻¹ * (g * (x : X) * g⁻¹) * g⁻¹⁻¹ = x
    group
  have hτσ : ∀ x, σ (τ x) = x := fun x => by
    apply Subtype.ext
    change g * (g⁻¹ * (x : X) * g⁻¹⁻¹) * g⁻¹ = x
    group
  have hσ : ∀ x, φ x = 1 → φ (σ x) = 1 := by
    intro x hx
    have hx' : x ∈ φ.ker := hx
    rw [hker, mem_subgroupOf] at hx'
    have : σ x ∈ φ.ker := by
      rw [hker, mem_subgroupOf]
      exact hgO _ hx'
    exact this
  have hτ : ∀ x, φ x = 1 → φ (τ x) = 1 := by
    intro x hx
    have hx' : x ∈ φ.ker := hx
    rw [hker, mem_subgroupOf] at hx'
    have : τ x ∈ φ.ker := by
      rw [hker, mem_subgroupOf]
      change g⁻¹ * (x : X) * g⁻¹⁻¹ ∈ O
      rw [inv_inv]
      exact hgO' _ hx'
    exact this
  obtain ⟨α, hα⟩ := exists_mulAut_of_map_ker φ hφ σ τ hστ hτσ hσ hτ
  refine ⟨α, fun d e he => ?_⟩
  have : σ d = e := Subtype.ext he.symm
  rw [hα d, this]

theorem mulAut_mul_self_eq_one {X K : Type*} [Group X] [Group K] {D : Subgroup X} {φ : ↥D →* K}
    (hφ : Function.Surjective φ) {g : X} (hgD : ∀ d ∈ D, g * d * g⁻¹ ∈ D) (hg2 : g * g = 1)
    {α : MulAut K} (hα : ∀ d e : ↥D, (e : X) = g * d * g⁻¹ → α (φ d) = φ e) : α * α = 1 := by
  have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  ext k
  obtain ⟨d, rfl⟩ := hφ k
  have h1 := hα d ⟨g * d * g⁻¹, hgD d d.2⟩ rfl
  have h2 := hα ⟨g * d * g⁻¹, hgD d d.2⟩ d (by
    change (d : X) = g * (g * (d : X) * g⁻¹) * g⁻¹
    rw [hgi]
    calc (d : X) = (g * g) * d * (g * g) := by rw [hg2]; group
      _ = g * (g * (d : X) * g) * g := by group)
  rw [MulAut.mul_apply, h1, h2, MulAut.one_apply]

theorem mulAut_mul_eq {X K : Type*} [Group X] [Group K] {D : Subgroup X} {φ : ↥D →* K}
    (hφ : Function.Surjective φ) {g h : X} (hgD : ∀ d ∈ D, g * d * g⁻¹ ∈ D)
    (hhD : ∀ d ∈ D, h * d * h⁻¹ ∈ D) {α β γ : MulAut K}
    (hα : ∀ d e : ↥D, (e : X) = g * d * g⁻¹ → α (φ d) = φ e)
    (hβ : ∀ d e : ↥D, (e : X) = h * d * h⁻¹ → β (φ d) = φ e)
    (hγ : ∀ d e : ↥D, (e : X) = (g * h) * d * (g * h)⁻¹ → γ (φ d) = φ e) : γ = α * β := by
  ext k
  obtain ⟨d, rfl⟩ := hφ k
  have h1 := hβ d ⟨h * d * h⁻¹, hhD d d.2⟩ rfl
  have h2 := hα ⟨h * d * h⁻¹, hhD d d.2⟩ ⟨g * (h * d * h⁻¹) * g⁻¹, hgD _ (hhD d d.2)⟩ rfl
  have h3 := hγ d ⟨g * (h * d * h⁻¹) * g⁻¹, hgD _ (hhD d d.2)⟩ (by
    change g * (h * (d : X) * h⁻¹) * g⁻¹ = (g * h) * d * (g * h)⁻¹
    group)
  rw [h3, MulAut.mul_apply, h1, h2]

theorem mulAut_eq_conj_of_inner {X K : Type*} [Group X] [Group K] {D : Subgroup X} {φ : ↥D →* K}
    (hφ : Function.Surjective φ) {g e : X} (heD : e ∈ D) (he : ∀ d ∈ D, g * d * g⁻¹ = e * d * e⁻¹)
    {α : MulAut K} (hα : ∀ d e : ↥D, (e : X) = g * d * g⁻¹ → α (φ d) = φ e) :
    ∀ k : K, α k = φ ⟨e, heD⟩ * k * (φ ⟨e, heD⟩)⁻¹ := by
  intro k
  obtain ⟨d, rfl⟩ := hφ k
  have hmem : e * (d : X) * e⁻¹ ∈ D := D.mul_mem (D.mul_mem heD d.2) (D.inv_mem heD)
  rw [hα d ⟨e * d * e⁻¹, hmem⟩ (he d d.2).symm, ← map_inv, ← map_mul, ← map_mul]
  rfl

end XDataAut

end CFSG.GH74.Uniqueness
