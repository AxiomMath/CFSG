module

public import CFSG.LieType.AlgebraicGroups.IdentityComponentLang
import CFSG.GroupTheory.NormalOddInversion

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups
open Subgroup CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

theorem mem_closedIdentityComponent_of_two_pow_eq_one
    {τ : Tag} {k : Type} [Field k]
    (Z : Subgroup (ModGL τ k)) {g : ModGL τ k} (hg : g ∈ Z)
    {m : ℕ} (hg2 : g ^ (2 ^ m) = 1)
    (hcomponents : IsPGroup 3 (Z ⧸ (closedIdentityComponent Z).subgroupOf Z)) :
    g ∈ closedIdentityComponent Z := by
  let gZ : Z := ⟨g, hg⟩
  let π := QuotientGroup.mk' ((closedIdentityComponent Z).subgroupOf Z)
  have hq2 : (π gZ) ^ (2 ^ m) = 1 := by
    rw [← map_pow]
    have h : gZ ^ (2 ^ m) = 1 := Subtype.ext hg2
    rw [h, map_one]
  have hc : Nat.Coprime 3 (2 ^ m) := (by decide : Nat.Coprime 3 2).pow_right m
  have hq : π gZ = 1 := by
    apply (hcomponents.powEquiv hc).injective
    simpa only [IsPGroup.powEquiv_apply, one_pow] using hq2
  exact (QuotientGroup.eq_one_iff gZ).mp hq

theorem exists_three_power_mem_closedIdentityComponent_of_involutive_action
    {τ : Tag} {k : Type} [Field k]
    (Z A : Subgroup (ModGL τ k)) (g : ModGL τ k)
    (hgZ : g ∈ Z) (hgA : g ∈ normalizer (A : Set (ModGL τ k)))
    (hφ : (A.normalizerMonoidHom ⟨g, hgA⟩) ^ 2 = 1)
    (hcomponents : IsPGroup 3 (Z ⧸ (closedIdentityComponent Z).subgroupOf Z)) :
    ∃ j : ℕ, g ^ (3 ^ j) ∈ closedIdentityComponent Z ∧
      ∀ a ∈ A, g ^ (3 ^ j) * a * (g ^ (3 ^ j))⁻¹ = g * a * g⁻¹ := by
  let gZ : Z := ⟨g, hgZ⟩
  obtain ⟨j, hj⟩ := hcomponents (QuotientGroup.mk' ((closedIdentityComponent Z).subgroupOf Z) gZ)
  have hmem : g ^ (3 ^ j) ∈ closedIdentityComponent Z := by
    have hq : QuotientGroup.mk' ((closedIdentityComponent Z).subgroupOf Z) (gZ ^ (3 ^ j)) = 1 := by
      rw [map_pow]
      exact hj
    have hm : gZ ^ (3 ^ j) ∈ (closedIdentityComponent Z).subgroupOf Z :=
      (QuotientGroup.eq_one_iff (gZ ^ (3 ^ j))).mp hq
    exact hm
  let γ : (normalizer (A : Set (ModGL τ k))) →* MulAut A := A.normalizerMonoidHom
  have hφpow : (γ ⟨g, hgA⟩) ^ (3 ^ j) = γ ⟨g, hgA⟩ := by
    obtain ⟨m, hm⟩ := (by simpa using (show Odd (3 : ℕ) from by decide).pow (n := j) : Odd (3 ^ j))
    rw [hm, pow_add, pow_mul, hφ, one_pow, pow_one, one_mul]
  refine ⟨j, hmem, ?_⟩
  intro a ha
  have h := congrArg (fun f : MulAut A => ((f ⟨a, ha⟩ : A) : ModGL τ k)) hφpow
  rw [← map_pow] at h
  exact h

theorem mem_closedIdentityComponent_of_order_three_of_inverted
    {τ : Tag} {k : Type} [Field k]
    (Z : Subgroup (ModGL τ k)) (g e : ModGL τ k)
    (hg : g ∈ closedIdentityComponent Z) (heZ : e ∈ Z)
    (he : e ^ 3 = 1) (hinv : g * e * g⁻¹ = e⁻¹) :
    e ∈ closedIdentityComponent Z := by
  let g0 : Z := ⟨g, closedIdentityComponent_le Z hg⟩
  let e0 : Z := ⟨e, heZ⟩
  have he0 : e0 ^ 3 = 1 := Subtype.ext he
  have hg0 : g0 ∈ (closedIdentityComponent Z).subgroupOf Z := hg
  have hinv0 : g0 * e0 * g0⁻¹ = e0⁻¹ := Subtype.ext hinv
  have hm := CFSG.GroupTheory.mem_of_normal_of_odd_pow_eq_one_of_conj_eq_inv hg0
    (by decide : Odd (3 : ℕ)) he0 hinv0
  exact hm

theorem exists_three_power_reflection_connected_hyperplane
    {τ : Tag} {k : Type} [Field k]
    (A H : Subgroup (ModGL τ k)) (g e : ModGL τ k)
    (hgG : g ∈ adjointGroup τ k)
    (hgH : g ∈ centralizer (H : Set (ModGL τ k)))
    (hgA : g ∈ normalizer (A : Set (ModGL τ k)))
    (hφ : (A.normalizerMonoidHom ⟨g, hgA⟩) ^ 2 = 1)
    (heG : e ∈ adjointGroup τ k) (heH : e ∈ centralizer (H : Set (ModGL τ k)))
    (heA : e ∈ A) (he : e ^ 3 = 1) (hinv : g * e * g⁻¹ = e⁻¹)
    (hcomponents : IsPGroup 3
      (↥(adjointGroup τ k ⊓ centralizer (H : Set (ModGL τ k))) ⧸
        (closedIdentityComponent
          (adjointGroup τ k ⊓ centralizer (H : Set (ModGL τ k)))).subgroupOf
            (adjointGroup τ k ⊓ centralizer (H : Set (ModGL τ k))))) :
    ∃ j : ℕ,
      g ^ (3 ^ j) ∈ closedIdentityComponent
        (adjointGroup τ k ⊓ centralizer (H : Set (ModGL τ k))) ∧
      (∀ a ∈ A, g ^ (3 ^ j) * a * (g ^ (3 ^ j))⁻¹ = g * a * g⁻¹) ∧
      e ∈ closedIdentityComponent
        (adjointGroup τ k ⊓ centralizer (H : Set (ModGL τ k))) := by
  let Z := adjointGroup τ k ⊓ centralizer (H : Set (ModGL τ k))
  obtain ⟨j, hj, ha⟩ := exists_three_power_mem_closedIdentityComponent_of_involutive_action
    Z A g ⟨hgG, hgH⟩ hgA hφ hcomponents
  refine ⟨j, hj, ha, ?_⟩
  exact mem_closedIdentityComponent_of_order_three_of_inverted Z (g ^ (3 ^ j)) e hj ⟨heG, heH⟩ he
    ((ha e heA).trans hinv)

end CFSG.LieType.AlgebraicGroups
