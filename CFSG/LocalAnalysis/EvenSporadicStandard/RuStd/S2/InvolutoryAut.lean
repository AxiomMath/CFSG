module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2.Close

open Subgroup

theorem map_eq_of_simple {Y : Type*} [Group Y] [Finite Y] (N : Subgroup Y) [hN : N.Normal]
    (hs : IsSimpleGroup N) (hC : ∀ x : Y, (∀ n ∈ N, x * n = n * x) → x = 1) (β : MulAut Y) :
    N.map β.toMonoidHom = N := by
  set M := N.map β.toMonoidHom with hM
  have hMn : M.Normal := hN.map _ β.surjective
  have hcard : Nat.card M = Nat.card N :=
    Subgroup.card_map_of_injective β.injective
  have hI : (N ⊓ M).Normal := inferInstance
  have hIN : ((N ⊓ M).subgroupOf N).Normal := hI.subgroupOf N
  haveI := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ M).subgroupOf N) with h | h
  · exfalso
    have hdisj : N ⊓ M = ⊥ := by
      rw [eq_bot_iff]; intro x hx
      have : (⟨x, hx.1⟩ : N) ∈ (N ⊓ M).subgroupOf N := hx
      rw [h, mem_bot] at this
      exact congrArg Subtype.val this
    have hcomm : ∀ m ∈ M, ∀ n ∈ N, m * n = n * m := by
      intro m hm n hn
      have hc : m * n * m⁻¹ * n⁻¹ ∈ N ⊓ M := ⟨
        N.mul_mem (hN.conj_mem n hn m) (N.inv_mem hn),
        by
          have := M.mul_mem hm (hMn.conj_mem m⁻¹ (M.inv_mem hm) n)
          simpa [mul_assoc] using this⟩
      rw [hdisj, mem_bot] at hc
      calc m * n = m * n * m⁻¹ * n⁻¹ * (n * m) := by group
        _ = n * m := by rw [hc, one_mul]
    have hMbot : M = ⊥ := by
      rw [eq_bot_iff]; intro m hm; exact (mem_bot).mpr (hC m (hcomm m hm))
    have hN1 : Nat.card N = 1 := by rw [← hcard, hMbot, Subgroup.card_bot]
    have : Nontrivial N := hs.toNontrivial
    exact absurd hN1 (Finite.one_lt_card).ne'
  · have hle : N ≤ M := by
      intro x hx
      have : (⟨x, hx⟩ : N) ∈ (N ⊓ M).subgroupOf N := by rw [h]; trivial
      exact this.2
    exact (Subgroup.eq_of_le_of_card_ge hle hcard.le).symm

theorem exists_restrict_involution {Y : Type*} [Group Y] (N : Subgroup Y) (φ : MulAut Y)
    (hφ : ∀ y, φ (φ y) = y) (hN : ∀ n ∈ N, φ n ∈ N) :
    ∃ γ : MulAut N, γ * γ = 1 ∧ ∀ n : N, ((γ n : N) : Y) = φ (n : Y) := by
  refine ⟨{ toFun := fun n => ⟨φ (n : Y), hN n n.2⟩
            invFun := fun n => ⟨φ (n : Y), hN n n.2⟩
            left_inv := fun n => Subtype.ext (hφ (n : Y))
            right_inv := fun n => Subtype.ext (hφ (n : Y))
            map_mul' := fun a b => Subtype.ext (map_mul φ (a : Y) (b : Y)) }, ?_, fun n => rfl⟩
  ext n
  exact hφ (n : Y)

theorem exists_fix_of_fix_mod {X : Type*} [Group X] (Z : Subgroup X)
    (hZ : ∀ z ∈ Z, Odd (orderOf z)) (α : X ≃* X) (hα : ∀ x, α (α x) = x) (q : X)
    (hq : q⁻¹ * α q ∈ Z) : ∃ z ∈ Z, α (q * z) = q * z := by
  set z₀ := q⁻¹ * α q with hz₀
  have hq' : α q = q * z₀ := by rw [hz₀]; group
  have hinv : α z₀ = z₀⁻¹ := by
    have h := hα q
    rw [hq', map_mul, hq'] at h
    have : z₀ * α z₀ = 1 := by
      have := congrArg (q⁻¹ * ·) h
      simpa [mul_assoc] using this
    exact eq_inv_of_mul_eq_one_right this
  obtain ⟨k, hk⟩ := hZ z₀ hq
  refine ⟨z₀ ^ (k + 1), Z.pow_mem hq _, ?_⟩
  rw [map_mul, map_pow, hq', hinv, inv_pow, mul_assoc]
  congr 1
  have ho : z₀ ^ (2 * k + 1) = 1 := hk ▸ pow_orderOf_eq_one z₀
  rw [mul_inv_eq_iff_eq_mul, ← pow_add, show k + 1 + (k + 1) = (2 * k + 1) + 1 by ring, pow_succ,
    ho, one_mul]

end CFSG.EvenSporadicStandard.RuStd.S2.Close
