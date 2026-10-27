module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.Phi6RouteW
public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Struct

set_option linter.unusedSectionVars false

public section

open Subgroup
open scoped commutatorElement

theorem perfect_le_of_abelian_complement {G : Type*} [Group G] (S M T D : Subgroup G)
    (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a)
    (hS : ∀ x ∈ S, ∃ t ∈ T, ∃ m ∈ M, x = t * m)
    (hMn : ∀ t ∈ T, t ∈ Subgroup.normalizer (M : Set G)) (hMM : M ≤ Subgroup.normalizer (M : Set G))
    (hDS : D ≤ S) (hperf : ⁅D, D⁆ = D) : D ≤ M := by
  classical
  set N := Subgroup.normalizer (M : Set G) with hN
  have : (M.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  let f : N →* N ⧸ M.subgroupOf N := QuotientGroup.mk' (M.subgroupOf N)
  have hSN : ∀ x ∈ S, x ∈ N := fun x hx => by
    obtain ⟨t, ht, m, hm, rfl⟩ := hS x hx
    exact mul_mem (hMn t ht) (hMM hm)
  have hker : ∀ (x : G) (hx : x ∈ N), f ⟨x, hx⟩ = 1 ↔ x ∈ M := fun x hx => by
    change (QuotientGroup.mk' (M.subgroupOf N)) ⟨x, hx⟩ = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Iff.rfl
  have hcomm : ∀ x ∈ S, ∀ y ∈ S, ⁅x, y⁆ ∈ M := by
    intro x hx y hy
    obtain ⟨t₁, ht₁, m₁, hm₁, rfl⟩ := hS x hx
    obtain ⟨t₂, ht₂, m₂, hm₂, rfl⟩ := hS y hy
    have hx' := hSN _ hx
    have hy' := hSN _ hy
    have hx1 : f ⟨t₁ * m₁, hx'⟩ = f ⟨t₁, hMn t₁ ht₁⟩ := by
      have : (⟨t₁ * m₁, hx'⟩ : N) = ⟨t₁, hMn t₁ ht₁⟩ * ⟨m₁, hMM hm₁⟩ := rfl
      rw [this, map_mul, (hker m₁ (hMM hm₁)).2 hm₁, mul_one]
    have hy1 : f ⟨t₂ * m₂, hy'⟩ = f ⟨t₂, hMn t₂ ht₂⟩ := by
      have : (⟨t₂ * m₂, hy'⟩ : N) = ⟨t₂, hMn t₂ ht₂⟩ * ⟨m₂, hMM hm₂⟩ := rfl
      rw [this, map_mul, (hker m₂ (hMM hm₂)).2 hm₂, mul_one]
    have hc : f ⟨t₁, hMn t₁ ht₁⟩ * f ⟨t₂, hMn t₂ ht₂⟩ = f ⟨t₂, hMn t₂ ht₂⟩ * f ⟨t₁, hMn t₁ ht₁⟩ := by
      rw [← map_mul, ← map_mul]
      exact congrArg f (Subtype.ext (hT t₁ ht₁ t₂ ht₂))
    have hfc : f ⟨⁅t₁ * m₁, t₂ * m₂⁆, mul_mem (mul_mem (mul_mem hx' hy') (inv_mem hx')) (inv_mem hy')⟩ = 1 := by
      have : (⟨⁅t₁ * m₁, t₂ * m₂⁆, mul_mem (mul_mem (mul_mem hx' hy') (inv_mem hx')) (inv_mem hy')⟩ : N) =
          ⟨t₁ * m₁, hx'⟩ * ⟨t₂ * m₂, hy'⟩ * (⟨t₁ * m₁, hx'⟩)⁻¹ * (⟨t₂ * m₂, hy'⟩)⁻¹ := rfl
      rw [this]
      simp only [map_mul, map_inv]
      rw [hx1, hy1, hc]
      group
    exact (hker _ _).1 hfc
  have : ⁅D, D⁆ ≤ M := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    exact hcomm x (hDS hx) y (hDS hy)
  rw [hperf] at this
  exact this

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator

open TauCeti CFSG.LieType.SeitzGeneration CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartOne.SEITZ11.G2Seven CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.ModelFacts


variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem TK_conj_mem_invCentGroup {t : twistedGroup σ} (ht : t ∈ TK σ) {h : twistedGroup σ}
    (hh : h ∈ invCentGroup σ hσ) : t * h * t⁻¹ ∈ invCentGroup σ hσ := by
  have key : (invCentGroup σ hσ).map (MulAut.conj t).toMonoidHom ≤ invCentGroup σ hσ := by
    rw [invCentGroup, Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩
      obtain ⟨A', hA'⟩ := TK_conj_slLong hσ ht A
      exact ⟨A', hA'.symm⟩
    · rintro _ ⟨_, ⟨B, rfl⟩, rfl⟩
      obtain ⟨B', hB'⟩ := TK_conj_slB hσ ht B
      exact ⟨B', hB'.symm⟩
  exact key ⟨h, hh, rfl⟩

include hσ in
theorem TK_comm {a b : twistedGroup σ} (ha : a ∈ TK σ) (hb : b ∈ TK σ) : a * b = b * a := by
  obtain ⟨c, hc⟩ := ha
  obtain ⟨d, hd⟩ := hb
  apply twistedIncl_injective σ
  rw [map_mul, map_mul, hc, hd, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

include hσ in
theorem perfect_centralizer_le_invCentGroup (hK : (-1 : Kˣ) ≠ 1)
    (hC₀ : graphFixedRootGroup TwistTag.D4 K σ ≤ (twistedIncl σ).range)
    (hgF : ∀ g : twistedGroup σ, twistedIncl σ g ∈ graphFixedRootGroup TwistTag.D4 K σ)
    {D : Subgroup (twistedGroup σ)}
    (hD : ∀ x ∈ D, x * slLong σ hσ (-1) = slLong σ hσ (-1) * x) (hperf : ⁅D, D⁆ = D) :
    D ≤ invCentGroup σ hσ := by
  refine perfect_le_of_abelian_complement (SProd σ hσ) (invCentGroup σ hσ) (TK σ) D
    (fun a ha b hb => TK_comm hσ ha hb) ?_ ?_ (Subgroup.le_normalizer) ?_ hperf
  · rintro _ ⟨t, ht, A, B, rfl⟩
    refine ⟨t, ht, slLong σ hσ A * slB σ hσ B, ?_, by group⟩
    exact mul_mem (Subgroup.mem_sup_left ⟨A, rfl⟩) (Subgroup.mem_sup_right ⟨B, rfl⟩)
  · intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => TK_conj_mem_invCentGroup hσ ht hh, fun hh => ?_⟩
    have := TK_conj_mem_invCentGroup hσ (inv_mem ht) hh
    simpa [mul_assoc] using this
  · intro x hx
    exact mem_SProd_of_centralizes hσ hK hC₀ hgF (hD x hx)

end CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator
