module

public import CFSG.GroupTheory.TitsSystem.Exchange
public import Mathlib.GroupTheory.Coxeter.Length
import CFSG.Monster.B.Geometry.CoxeterWords

public section

namespace CFSG.GroupTheory.TitsSystem

open CFSG.GH74.BNPair
open scoped Pointwise

variable {G : Type*} [Group G] {B N : Subgroup G} [(cartan B N).Normal] {S : Set (WeylGroup B N)}

namespace IsBNPair

theorem length_eq_wordLength (h : IsBNPair B N S)
    (cs : CoxeterSystem (orderMatrix h.orderOf_eq_two) (WeylGroup B N))
    (hcs : ∀ s : S, cs.simple s = s) (w : WeylGroup B N) : cs.length w = wordLength S w := by
  have hS : CFSG.Monster.B.Geometry.simpleSet cs = S := by ext x; simp [hcs]
  rw [← CFSG.Monster.B.Geometry.wordLength_simpleSet, hS, exchange_wordLength_eq]

omit [(cartan B N).Normal] in
private theorem dc_mul_B (w : WeylGroup B N) : dc B N w * (B : Set G) = dc B N w := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨y, hy, b, hb, rfl⟩
    simpa using mul_mem_dc hy B.one_mem hb
  · intro x hx
    exact Set.mem_mul.2 ⟨x, hx, 1, B.one_mem, by simp⟩

theorem dc_mul_dc_of_wordLength_add (h : IsBNPair B N S) {v u : WeylGroup B N}
    (hvu : wordLength S (v * u) = wordLength S v + wordLength S u) :
    dc B N v * dc B N u = dc B N (v * u) := by
  have key : ∀ n, ∀ u : WeylGroup B N, wordLength S u = n → ∀ v : WeylGroup B N,
      wordLength S (v * u) = wordLength S v + wordLength S u →
      dc B N v * dc B N u = dc B N (v * u) := by
    intro n
    induction n with
    | zero =>
      intro u hu v hvu
      have hu1 : u = 1 :=
        (wordLength_eq_zero_iff h.bnCore.mul_self_eq_one (h.mem_closure u)).1 hu
      rw [hu1, mul_one, dc_one]
      exact dc_mul_B v
    | succ n ih =>
      intro u hu v hvu
      rcases eq_or_ne u 1 with rfl | hu1
      · rw [mul_one, dc_one]
        exact dc_mul_B v
      · obtain ⟨t, ht, htlen⟩ :=
          exists_right_descent h.bnCore.mul_self_eq_one (h.mem_closure u) hu1
        set u' : WeylGroup B N := u * t with hu'def
        have hu'len : wordLength S u' = n := by omega
        have hu_eq : u' * t = u := by
          rw [hu'def, mul_assoc, h.mul_self_eq_one ht, mul_one]
        have h1 : wordLength S (v * u) ≤ wordLength S (v * u') + 1 := by
          have hle := wordLength_mul_gen_le h.bnCore.mul_self_eq_one ht
            (Subgroup.mul_mem _ (h.mem_closure v) (h.mem_closure u'))
          rwa [mul_assoc, hu_eq] at hle
        have h2 : wordLength S (v * u') ≤ wordLength S v + wordLength S u' :=
          wordLength_mul_le h.bnCore.mul_self_eq_one (h.mem_closure v) (h.mem_closure u')
        have huv' : wordLength S (v * u') = wordLength S v + wordLength S u' := by omega
        have ih' : dc B N v * dc B N u' = dc B N (v * u') := ih u' hu'len v huv'
        have e1 : dc B N u' * dc B N t = dc B N u := by
          have hlt : wordLength S u' < wordLength S (u' * t) := by rw [hu_eq]; omega
          simpa [hu_eq] using h.dc_mul_dc_of_lt_right ht hlt
        have e2 : dc B N (v * u') * dc B N t = dc B N (v * u) := by
          have hlt : wordLength S (v * u') < wordLength S ((v * u') * t) := by
            rw [mul_assoc, hu_eq]; omega
          simpa [mul_assoc, hu_eq] using h.dc_mul_dc_of_lt_right ht hlt
        calc dc B N v * dc B N u
            = dc B N v * (dc B N u' * dc B N t) := by rw [e1]
          _ = (dc B N v * dc B N u') * dc B N t := (mul_assoc _ _ _).symm
          _ = dc B N (v * u') * dc B N t := by rw [ih']
          _ = dc B N (v * u) := e2
  exact key _ u rfl v hvu

theorem exists_wordLength_mul_add (h : IsBNPair B N S) {J : Set (WeylGroup B N)} (hJ : J ⊆ S)
    (w : WeylGroup B N) :
    ∃ w₁ : WeylGroup B N, w₁⁻¹ * w ∈ Subgroup.closure J ∧
      ∀ u ∈ Subgroup.closure J, wordLength S (w₁ * u) = wordLength S w₁ + wordLength S u := by
  obtain ⟨cs, hcs⟩ := h.exists_coxeterSystem
  let J' : Set S := {s | (s : WeylGroup B N) ∈ J}
  have hpar : cs.parabolic J' = Subgroup.closure J := by
    refine le_antisymm ?_ ?_
    · rw [cs.parabolic_le_iff]
      intro i hi
      rw [hcs i]
      exact Subgroup.subset_closure hi
    · rw [Subgroup.closure_le]
      intro x hx
      have hxs : (⟨x, hJ hx⟩ : S) ∈ J' := hx
      have hmem := cs.simple_mem_parabolic hxs
      rwa [hcs ⟨x, hJ hx⟩] at hmem
  obtain ⟨v, hv, hmin⟩ := cs.exists_isMinimalCosetRep J' w
  refine ⟨w * v, ?_, ?_⟩
  · have hwv : (w * v)⁻¹ * w = v⁻¹ := by group
    rw [hwv]
    exact Subgroup.inv_mem _ (hpar ▸ hv)
  · intro u hu
    have hu' : u ∈ cs.parabolic J' := hpar.symm ▸ hu
    have hlen := cs.length_mul_of_isMinimalCosetRep hmin hu'
    simpa only [h.length_eq_wordLength cs hcs] using hlen

end IsBNPair

end CFSG.GroupTheory.TitsSystem
