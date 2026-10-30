module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.BaseEmb

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.Open

private theorem key : ∀ a : alternatingGroup (Fin 5), a ≠ 1 → a * a = 1 →
    ∃ x : alternatingGroup (Fin 5), x ≠ 1 ∧ x ^ 5 = 1 ∧ a * x * a⁻¹ = x⁻¹ := by
  decide +kernel

theorem L210_exists_inverted_component {u : A5WrTwo} (hu : u ∈ commutator A5WrTwo) (hu1 : u ≠ 1)
    (hu2 : u * u = 1) :
    ∃ x : alternatingGroup (Fin 5), orderOf x = 5 ∧
      (u * A5WrTwo.baseEmb (x, 1) * u⁻¹ = (A5WrTwo.baseEmb (x, 1))⁻¹ ∨
        u * A5WrTwo.baseEmb (1, x) * u⁻¹ = (A5WrTwo.baseEmb (1, x))⁻¹) := by
  have hu' : u ∈ A5WrTwo.baseEmb.range := by rwa [A5WrTwo.range_baseEmb]
  obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp hu'
  rw [← hp] at hu1 hu2 ⊢
  have hp2 : p * p = 1 := A5WrTwo.baseEmb_injective (by rw [map_mul, map_one, hu2])
  have hp1' : p.1 * p.1 = 1 := by simpa using congrArg Prod.fst hp2
  have hp2' : p.2 * p.2 = 1 := by simpa using congrArg Prod.snd hp2
  have hpne : p ≠ 1 := fun h => hu1 (by rw [h, map_one])
  have hpor : p.1 ≠ 1 ∨ p.2 ≠ 1 := by
    by_contra h
    push Not at h
    exact hpne (Prod.ext h.1 h.2)
  rcases hpor with ha | hb
  ·
    obtain ⟨x, hxne, hx5, hxconj⟩ := key p.1 ha hp1'
    refine ⟨x, ?_, Or.inl ?_⟩
    · haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
      exact orderOf_eq_prime hx5 hxne
    · have hconj : A5WrTwo.baseEmb p * A5WrTwo.baseEmb (x, 1) * (A5WrTwo.baseEmb p)⁻¹
          = A5WrTwo.baseEmb (x⁻¹, 1) := by
        rw [← map_mul, ← map_inv, ← map_mul]
        congr 1
        ext <;> simp [hxconj]
      rw [hconj, ← map_inv]
      simp
  ·
    obtain ⟨x, hxne, hx5, hxconj⟩ := key p.2 hb hp2'
    refine ⟨x, ?_, Or.inr ?_⟩
    · haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
      exact orderOf_eq_prime hx5 hxne
    · have hconj : A5WrTwo.baseEmb p * A5WrTwo.baseEmb (1, x) * (A5WrTwo.baseEmb p)⁻¹
          = A5WrTwo.baseEmb (1, x⁻¹) := by
        rw [← map_mul, ← map_inv, ← map_mul]
        congr 1
        ext <;> simp [hxconj]
      rw [hconj, ← map_inv]
      simp

end CFSG.EvenSporadicStandard.HNRecog.Harada
