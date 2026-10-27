module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812

open Subgroup

private lemma card_mulAut_zpowers_of_orderOf_eq_three {X : Type*} [Group X] {x : X}
    (hx : orderOf x = 3) : Nat.card (MulAut ↥(zpowers x)) = 2 := by
  have hcard : Nat.card ↥(zpowers x) = 3 := by rw [Nat.card_zpowers, hx]
  have : Finite ↥(zpowers x) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  rw [IsCyclic.card_mulAut, hcard]
  exact Nat.totient_prime Nat.prime_three

private lemma exists_hom_ker_le_centralizer {X : Type*} [Group X] {x : X} {A : Subgroup X}
    (hA : A ≤ normalizer (zpowers x : Set X)) :
    ∃ ψ : ↥A →* MulAut ↥(zpowers x), ∀ a : ↥A, ψ a = 1 → (a : X) ∈ centralizer ({x} : Set X) := by
  refine ⟨(zpowers x).normalizerMonoidHom.comp (Subgroup.inclusion hA), fun a ha => ?_⟩
  have h2 : (a : X) * x * (a : X)⁻¹ = x := by
    have := congrArg (fun φ : MulAut ↥(zpowers x) => (φ ⟨x, mem_zpowers x⟩ : X)) ha
    simpa using this
  rw [mem_centralizer_singleton_iff]
  calc (a : X) * x = ((a : X) * x * (a : X)⁻¹) * a := by group
    _ = x * a := by rw [h2]

theorem le_centralizer_of_isPGroup_three {X : Type*} [Group X] {x : X} (hx : orderOf x = 3)
    {W : Subgroup X} (hW : IsPGroup 3 ↥W)
    (hn : W ≤ normalizer (zpowers x : Set X)) : W ≤ centralizer ({x} : Set X) := by
  obtain ⟨ψ, hψ⟩ := exists_hom_ker_le_centralizer hn
  intro w hw
  refine hψ ⟨w, hw⟩ ?_
  obtain ⟨k, hk⟩ := hW ⟨w, hw⟩
  have h1 : orderOf (ψ ⟨w, hw⟩) ∣ 3 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hk, map_one])
  have h2 : orderOf (ψ ⟨w, hw⟩) ∣ 2 := by
    rw [← card_mulAut_zpowers_of_orderOf_eq_three hx]
    exact orderOf_dvd_natCard _
  have h3 : Nat.Coprime (3 ^ k) 2 := Nat.Coprime.pow_left k (by norm_num)
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes h3 h1 h2)

theorem card_le_two_mul_card_inf_centralizer {X : Type*} [Group X] [Finite X] {x : X}
    (hx : orderOf x = 3) {A : Subgroup X}
    (hA : A ≤ normalizer (zpowers x : Set X)) :
    Nat.card ↥A ≤ 2 * Nat.card ↥(A ⊓ centralizer ({x} : Set X)) := by
  obtain ⟨ψ, hψ⟩ := exists_hom_ker_le_centralizer hA
  have hcard := card_mulAut_zpowers_of_orderOf_eq_three hx
  have : Finite (MulAut ↥(zpowers x)) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hrange : Nat.card ↥ψ.range ≤ 2 := by
    rw [← hcard]
    exact Subgroup.card_le_card_group _
  have hle : ψ.ker ≤ (A ⊓ centralizer ({x} : Set X)).subgroupOf A := fun a ha =>
    mem_subgroupOf.2 (mem_inf.2 ⟨a.2, hψ a (MonoidHom.mem_ker.1 ha)⟩)
  have hker : Nat.card ↥ψ.ker ≤ Nat.card ↥(A ⊓ centralizer ({x} : Set X)) :=
    (Subgroup.card_le_of_le hle).trans_eq
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv)
  calc Nat.card ↥A = Nat.card ↥ψ.ker * Nat.card ↥ψ.range := (card_ker_mul_card_range ψ).symm
    _ ≤ Nat.card ↥(A ⊓ centralizer ({x} : Set X)) * 2 := Nat.mul_le_mul hker hrange
    _ = 2 * Nat.card ↥(A ⊓ centralizer ({x} : Set X)) := Nat.mul_comm _ _

end CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812
