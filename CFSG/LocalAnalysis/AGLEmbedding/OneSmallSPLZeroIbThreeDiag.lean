module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore
import CFSG.LocalAnalysis.AGLEmbedding.SPLMSideOrbit
import CFSG.GroupTheory.LocalCores.Components
import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.AGLEmbedding

open CFSG.RankThreeCoreUniqueness.Helpers

section Diag

variable {Y : Type} [Group Y]

theorem diag_mul_of_commute {u a b : Y}
    (k1 : b * (u * a * u⁻¹) = (u * a * u⁻¹) * b)
    (k2 : b * (u ^ 2 * a * (u ^ 2)⁻¹) = (u ^ 2 * a * (u ^ 2)⁻¹) * b)
    (k3 : (u * b * u⁻¹) * (u ^ 2 * a * (u ^ 2)⁻¹) = (u ^ 2 * a * (u ^ 2)⁻¹) * (u * b * u⁻¹)) :
    (a * b) * (u * (a * b) * u⁻¹) * (u ^ 2 * (a * b) * (u ^ 2)⁻¹) =
      (a * (u * a * u⁻¹) * (u ^ 2 * a * (u ^ 2)⁻¹)) *
        (b * (u * b * u⁻¹) * (u ^ 2 * b * (u ^ 2)⁻¹)) := by
  have e1 : u * (a * b) * u⁻¹ = (u * a * u⁻¹) * (u * b * u⁻¹) := by group
  have e2 : u ^ 2 * (a * b) * (u ^ 2)⁻¹ =
      (u ^ 2 * a * (u ^ 2)⁻¹) * (u ^ 2 * b * (u ^ 2)⁻¹) := by group
  rw [e1, e2]
  calc a * b * ((u * a * u⁻¹) * (u * b * u⁻¹)) *
        ((u ^ 2 * a * (u ^ 2)⁻¹) * (u ^ 2 * b * (u ^ 2)⁻¹))
      = a * (b * (u * a * u⁻¹)) * ((u * b * u⁻¹) * (u ^ 2 * a * (u ^ 2)⁻¹)) *
          (u ^ 2 * b * (u ^ 2)⁻¹) := by group
    _ = a * ((u * a * u⁻¹) * b) * ((u ^ 2 * a * (u ^ 2)⁻¹) * (u * b * u⁻¹)) *
          (u ^ 2 * b * (u ^ 2)⁻¹) := by rw [k1, k3]
    _ = a * (u * a * u⁻¹) * (b * (u ^ 2 * a * (u ^ 2)⁻¹)) * (u * b * u⁻¹) *
          (u ^ 2 * b * (u ^ 2)⁻¹) := by group
    _ = a * (u * a * u⁻¹) * ((u ^ 2 * a * (u ^ 2)⁻¹) * b) * (u * b * u⁻¹) *
          (u ^ 2 * b * (u ^ 2)⁻¹) := by rw [k2]
    _ = (a * (u * a * u⁻¹) * (u ^ 2 * a * (u ^ 2)⁻¹)) *
          (b * (u * b * u⁻¹) * (u ^ 2 * b * (u ^ 2)⁻¹)) := by group

theorem diag_commute_of_pow_three {u y : Y} (hu3 : u ^ 3 = 1)
    (k1 : y * (u * y * u⁻¹) = (u * y * u⁻¹) * y)
    (k2 : y * (u ^ 2 * y * (u ^ 2)⁻¹) = (u ^ 2 * y * (u ^ 2)⁻¹) * y) :
    u * (y * (u * y * u⁻¹) * (u ^ 2 * y * (u ^ 2)⁻¹)) =
      y * (u * y * u⁻¹) * (u ^ 2 * y * (u ^ 2)⁻¹) * u := by
  have e3 : u * (u ^ 2 * y * (u ^ 2)⁻¹) * u⁻¹ = y := by
    have h1 : u * u ^ 2 = 1 := by rw [← pow_succ', hu3]
    calc u * (u ^ 2 * y * (u ^ 2)⁻¹) * u⁻¹ = (u * u ^ 2) * y * (u * u ^ 2)⁻¹ := by group
      _ = y := by rw [h1]; group
  have e4 : u * (u * y * u⁻¹) * u⁻¹ = u ^ 2 * y * (u ^ 2)⁻¹ := by
    rw [sq, mul_inv_rev]; group
  calc u * (y * (u * y * u⁻¹) * (u ^ 2 * y * (u ^ 2)⁻¹))
      = (u * y * u⁻¹) * (u * (u * y * u⁻¹) * u⁻¹) *
          (u * (u ^ 2 * y * (u ^ 2)⁻¹) * u⁻¹) * u := by group
    _ = (u * y * u⁻¹) * (u ^ 2 * y * (u ^ 2)⁻¹) * y * u := by rw [e3, e4]
    _ = y * (u * y * u⁻¹) * (u ^ 2 * y * (u ^ 2)⁻¹) * u := by
        rw [mul_assoc (u * y * u⁻¹), ← k2, ← mul_assoc, ← k1]

theorem mul_comm_of_diag_eq_one {u : Y} {Λ Λ₁ Λ₂ : Subgroup Y}
    (c01 : ∀ a ∈ Λ, ∀ b ∈ Λ₁, a * b = b * a) (c02 : ∀ a ∈ Λ, ∀ b ∈ Λ₂, a * b = b * a)
    (hm₁ : ∀ l ∈ Λ, u * l * u⁻¹ ∈ Λ₁) (hm₂ : ∀ l ∈ Λ, u ^ 2 * l * (u ^ 2)⁻¹ ∈ Λ₂)
    (hall : ∀ l : Λ, (l : Y) * (u * l * u⁻¹) * (u ^ 2 * l * (u ^ 2)⁻¹) = 1) (l m : Λ) :
    l * m = m * l := by
  have hl := l.2
  have hm := m.2
  have hl' : (l : Y) = ((u * l * u⁻¹) * (u ^ 2 * l * (u ^ 2)⁻¹))⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← mul_assoc]
    exact hall l
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [hl', mul_inv_rev]
  have k1 := c01 m hm _ (Subgroup.inv_mem _ (hm₁ l hl))
  have k2 := c02 m hm _ (Subgroup.inv_mem _ (hm₂ l hl))
  calc (u ^ 2 * l * (u ^ 2)⁻¹)⁻¹ * (u * l * u⁻¹)⁻¹ * (m : Y)
      = (u ^ 2 * l * (u ^ 2)⁻¹)⁻¹ * ((u * l * u⁻¹)⁻¹ * m) := by group
    _ = (u ^ 2 * l * (u ^ 2)⁻¹)⁻¹ * (m * (u * l * u⁻¹)⁻¹) := by rw [k1]
    _ = ((u ^ 2 * l * (u ^ 2)⁻¹)⁻¹ * m) * (u * l * u⁻¹)⁻¹ := by group
    _ = (m * (u ^ 2 * l * (u ^ 2)⁻¹)⁻¹) * (u * l * u⁻¹)⁻¹ := by rw [k2]
    _ = m * ((u ^ 2 * l * (u ^ 2)⁻¹)⁻¹ * (u * l * u⁻¹)⁻¹) := by group

variable [Finite Y]

theorem exists_perfect_diag {Λ : Subgroup Y} (hΛ : CFSG.IsComponent Λ) {u : Y}
    (hu3 : u ^ 3 = 1) (hun : u ∉ Subgroup.normalizer (Λ : Set Y)) :
    ∃ W : Subgroup Y, ⁅W, W⁆ = W ∧ W ≤ Subgroup.centralizer ({u} : Set Y) ∧ W ≠ ⊥ := by
  set Λ₁ := Λ.map (MulAut.conj u).toMonoidHom with hΛ₁
  set Λ₂ := Λ.map (MulAut.conj (u ^ 2)).toMonoidHom with hΛ₂
  have hc₁ : CFSG.IsComponent Λ₁ := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj u) hΛ
  have hc₂ : CFSG.IsComponent Λ₂ :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (u ^ 2)) hΛ
  have hmap : ∀ (a b : Y) (X : Subgroup Y), X.map (MulAut.conj (a * b)).toMonoidHom =
      (X.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
    intro a b X
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hne₁ : Λ₁ ≠ Λ := fun h => hun (SPLMSide.mem_normalizer_of_map_conj_eq h)
  have hne₂ : Λ₂ ≠ Λ := by
    intro h
    apply hun
    have h2 : u ^ 2 ∈ Subgroup.normalizer (Λ : Set Y) := SPLMSide.mem_normalizer_of_map_conj_eq h
    have : u = (u ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hu3, one_mul, pow_one]
    rw [this]
    exact Subgroup.pow_mem _ h2 2
  have hne₁₂ : Λ₂ ≠ Λ₁ := by
    intro h
    apply hne₁
    have h' : Λ₂ = Λ₁.map (MulAut.conj u).toMonoidHom := by
      rw [hΛ₂, sq, hmap]
    rw [h'] at h
    have hinj : Function.Injective (Subgroup.map (MulAut.conj u).toMonoidHom) :=
      Subgroup.map_injective (MulAut.conj u).injective
    exact hinj h
  have c01 := SPLMSide.commute_of_ne hΛ hc₁ hne₁
  have c02 := SPLMSide.commute_of_ne hΛ hc₂ hne₂
  have c12 := SPLMSide.commute_of_ne hc₁ hc₂ hne₁₂
  have hm₁ : ∀ l ∈ Λ, u * l * u⁻¹ ∈ Λ₁ := fun l hl => ⟨l, hl, MulAut.conj_apply _ _⟩
  have hm₂ : ∀ l ∈ Λ, u ^ 2 * l * (u ^ 2)⁻¹ ∈ Λ₂ := fun l hl => ⟨l, hl, MulAut.conj_apply _ _⟩
  let δ : Λ →* Y :=
    { toFun := fun l => (l : Y) * (u * l * u⁻¹) * (u ^ 2 * l * (u ^ 2)⁻¹)
      map_one' := by simp
      map_mul' := by
        rintro ⟨a, ha⟩ ⟨b, hb⟩
        exact diag_mul_of_commute (c01 b hb _ (hm₁ a ha)) (c02 b hb _ (hm₂ a ha))
          (c12 _ (hm₁ b hb) _ (hm₂ a ha)) }
  have hδ : ∀ l : Λ, δ l = (l : Y) * (u * l * u⁻¹) * (u ^ 2 * l * (u ^ 2)⁻¹) := fun _ => rfl
  refine ⟨δ.range, ?_, ?_, ?_⟩
  · have hperf : ⁅(⊤ : Subgroup Λ), ⊤⁆ = ⊤ := hΛ.1.1.commutator_eq_top
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hperf]
  · rintro _ ⟨⟨y, hy⟩, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hδ]
    exact (diag_commute_of_pow_three hu3 (c01 y hy _ (hm₁ y hy)) (c02 y hy _ (hm₂ y hy))).symm
  · intro hbot
    have hall : ∀ l : Λ, (l : Y) * (u * l * u⁻¹) * (u ^ 2 * l * (u ^ 2)⁻¹) = 1 := by
      intro l
      rw [← hδ]
      have : δ l ∈ δ.range := ⟨l, rfl⟩
      rw [hbot] at this
      exact Subgroup.mem_bot.mp this
    obtain ⟨a, b, hab⟩ := hΛ.1.2.2
    apply hab
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b => rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
          mul_comm_of_diag_eq_one c01 c02 hm₁ hm₂ hall a b]

end Diag

theorem le_primeComplementCore_three_of_subnormal {Y : Type} [Group Y] [Finite Y]
    {N : Subgroup Y} (hN : N.IsSubnormal) (h3 : Nat.Coprime 3 (Nat.card N)) :
    N ≤ primeComplementCore (G := Y) 3 := by
  set π3 : Set Nat.Primes := {q | (q : ℕ) ≠ 3} with hπ3
  have hNπ : CFSG.IsPiSubgroup π3 (⊤ : Subgroup N) := by
    intro q hq
    change (q : ℕ) ≠ 3
    intro hq3
    rw [Subgroup.card_top, hq3] at hq
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp h3 hq
  have htop : CFSG.piCore π3 N = ⊤ :=
    top_unique (CFSG.LocalCores.le_piCore_of_normal inferInstance hNπ)
  have h := CFSG.LocalCores.prime_set_core_subnormal_intersection π3 hN
  rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  have hle : N ≤ CFSG.piCore π3 Y := inf_eq_left.mp h.symm
  refine hle.trans (normal_coprime_le_primeComplementCore 3 _ inferInstance ?_)
  have hπ := CFSG.LocalCores.piCore_isPiSubgroup (G := Y) π3
  refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3' => ?_
  exact hπ ⟨3, Nat.prime_three⟩ h3' rfl

end CFSG.AGLEmbedding
