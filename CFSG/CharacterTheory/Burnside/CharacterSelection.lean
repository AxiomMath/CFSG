module

public import CFSG.CharacterTheory.Burnside.RegularRelation
public import CFSG.CharacterTheory.Burnside.CharacterArithmetic
public import Mathlib.NumberTheory.Niven
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG

namespace Burnside

open CategoryTheory
open scoped BigOperators

namespace ClassFun

variable {G : Type} [Group G] [Fintype G]

theorem IrrepCharBasis.exists_char_ne_zero_not_dvd_finrank
    (B : ClassFun.IrrepCharBasis ℂ G) {x : G} (hx : x ≠ 1)
    {r : ℕ} (hr : Nat.Prime r) :
    ∃ i₀ i : B.ι,
      ClassFun.character (B.V i₀) = 1 ∧
      Module.finrank ℂ (B.V i₀) = 1 ∧
      i ≠ i₀ ∧
      (B.V i).character x ≠ 0 ∧
      ¬ r ∣ Module.finrank ℂ (B.V i) := by
  classical
  let T : FDRep ℂ G := FDRep.trivial ℂ G
  have hTsimple : Simple T := by
    rw [FDRep.simple_iff_char_is_norm_one]
    simp [T, FDRep.char_trivial]
  obtain ⟨i₀, ⟨e₀⟩⟩ := B.is_exhaustive T hTsimple
  have hi₀char : ClassFun.character (B.V i₀) = 1 := by
    calc
      ClassFun.character (B.V i₀) = ClassFun.character T :=
        (ClassFun.char_eq_of_iso e₀).symm
      _ = 1 := by simp [T]
  have hi₀dim : Module.finrank ℂ (B.V i₀) = 1 := by
    have hdim := FDRep.finrank_congr e₀
    change Module.finrank ℂ T = Module.finrank ℂ (B.V i₀) at hdim
    rw [← hdim]
    change Module.finrank ℂ ℂ = 1
    exact Module.finrank_self ℂ
  by_contra hnone
  have hbad : ∀ i : B.ι, i ≠ i₀ →
      (B.V i).character x = 0 ∨ r ∣ Module.finrank ℂ (B.V i) := by
    intro i hi
    by_cases hχ : (B.V i).character x = 0
    · exact Or.inl hχ
    · right
      by_contra hd
      apply hnone
      exact ⟨i₀, i, hi₀char, hi₀dim, hi, hχ, hd⟩
  let β : ℂ := ∑ i ∈ (Finset.univ.erase i₀),
    ((Module.finrank ℂ (B.V i) / r : ℕ) : ℂ) * (B.V i).character x
  have hχint : ∀ i : B.ι, IsIntegral ℤ ((B.V i).character x) := by
    intro i
    exact Representation.isIntegral_character_of_isOfFinOrder
      (B.V i).ρ x (isOfFinOrder_of_finite x)
  have hβint : IsIntegral ℤ β := by
    dsimp [β]
    apply IsIntegral.sum
    intro i hi
    simpa only [nsmul_eq_mul] using
      (hχint i).nsmul (Module.finrank ℂ (B.V i) / r)
  have hfactor :
      ∑ i ∈ (Finset.univ.erase i₀),
          (Module.finrank ℂ (B.V i) : ℂ) * (B.V i).character x =
        (r : ℂ) * β := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hii₀ : i ≠ i₀ := (Finset.mem_erase.mp hi).1
    rcases hbad i hii₀ with hzero | hdvd
    · simp [hzero]
    · obtain ⟨t, ht⟩ := hdvd
      rw [ht]
      simp [hr.ne_zero]
      ring
  have hreg :=
    Burnside.ClassFun.IrrepCharBasis.regular_character_relation B hx
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)] at hreg
  have hi₀eval : (B.V i₀).character x = 1 := by
    have h := DFunLike.congr_fun hi₀char x
    simpa using h
  have hreg' :
      1 + ∑ i ∈ (Finset.univ.erase i₀),
          (Module.finrank ℂ (B.V i) : ℂ) * (B.V i).character x = 0 := by
    simpa only [hi₀dim, Nat.cast_one, one_mul, hi₀eval] using hreg
  have hrβ : (r : ℂ) * (-β) = 1 := by
    rw [hfactor] at hreg'
    linear_combination -hreg'
  have hnegβint : IsIntegral ℤ (-β) := hβint.neg
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne_zero
  have hrat : -β = (((r : ℚ)⁻¹ : ℚ) : ℂ) := by
    apply (mul_left_cancel₀ hrC)
    rw [hrβ]
    norm_num [hr.ne_zero]
  obtain ⟨z, hz⟩ :=
    (hnegβint.exists_int_iff_exists_rat).mp ⟨(r : ℚ)⁻¹, hrat⟩
  have hrz : (r : ℤ) * z = 1 := by
    rw [hz] at hrβ
    exact_mod_cast hrβ
  exact (Nat.prime_iff_prime_int.mp hr).not_dvd_one ⟨z, hrz.symm⟩

end ClassFun

end Burnside

end CFSG
