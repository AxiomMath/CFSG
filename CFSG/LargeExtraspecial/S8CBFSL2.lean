module

public import CFSG.LargeExtraspecial.S8CorBStatement

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Matrix

variable {K : Type*} [Field K]

theorem commute_entries_of_commute_nonscalar_two {a b c d p q r s p' q' r' s' : K}
    (hN : b ≠ 0 ∨ c ≠ 0 ∨ a ≠ d)
    (hg00 : p * a + q * c = a * p + b * r) (hg01 : p * b + q * d = a * q + b * s)
    (hg10 : r * a + s * c = c * p + d * r)
    (hh00 : p' * a + q' * c = a * p' + b * r') (hh01 : p' * b + q' * d = a * q' + b * s')
    (hh10 : r' * a + s' * c = c * p' + d * r') :
    q * r' = q' * r ∧ q' * (p - s) = q * (p' - s') ∧ r * (p' - s') = r' * (p - s) := by
  rcases hN with hb | hc | had
  · have h1 : q * r' = q' * r := mul_left_cancel₀ hb (by linear_combination q' * hg00 - q * hh00)
    have h2 : q' * (p - s) = q * (p' - s') :=
      mul_left_cancel₀ hb (by linear_combination q' * hg01 - q * hh01)
    refine ⟨h1, h2, mul_left_cancel₀ hb ?_⟩
    linear_combination -(p' - s') * hg00 + (p - s) * hh00 - c * h2
  · have h1 : q * r' = q' * r := mul_left_cancel₀ hc (by linear_combination r' * hg00 - r * hh00)
    have h3 : r * (p' - s') = r' * (p - s) :=
      mul_left_cancel₀ hc (by linear_combination r' * hg10 - r * hh10)
    refine ⟨h1, mul_left_cancel₀ hc ?_, h3⟩
    linear_combination (p - s) * hh00 - (p' - s') * hg00 - b * h3
  · have had' : a - d ≠ 0 := sub_ne_zero.mpr had
    have h2 : q' * (p - s) = q * (p' - s') :=
      mul_left_cancel₀ had' (by linear_combination (p' - s') * hg01 - (p - s) * hh01)
    have h3 : r * (p' - s') = r' * (p - s) :=
      mul_left_cancel₀ had' (by linear_combination (p' - s') * hg10 - (p - s) * hh10)
    refine ⟨mul_left_cancel₀ (pow_ne_zero 2 had') ?_, h2, h3⟩
    linear_combination -(a - d) * c * h2 + (a - d) * q * hh10 - (a - d) * q' * hg10

theorem commute_of_commute_nonscalar_two {N g h : Matrix (Fin 2) (Fin 2) K}
    (hN : N 0 1 ≠ 0 ∨ N 1 0 ≠ 0 ∨ N 0 0 ≠ N 1 1) (hg : g * N = N * g) (hh : h * N = N * h) :
    g * h = h * g := by
  have e := fun (M : Matrix (Fin 2) (Fin 2) K) (hM : M * N = N * M) (i j : Fin 2) =>
    congrFun (congrFun hM i) j
  have hg00 := e g hg 0 0
  have hg01 := e g hg 0 1
  have hg10 := e g hg 1 0
  have hh00 := e h hh 0 0
  have hh01 := e h hh 0 1
  have hh10 := e h hh 1 0
  simp only [mul_apply, Fin.sum_univ_two] at hg00 hg01 hg10 hh00 hh01 hh10
  obtain ⟨k1, k2, k3⟩ :=
    commute_entries_of_commute_nonscalar_two hN hg00 hg01 hg10 hh00 hh01 hh10
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [mul_apply, Fin.sum_univ_two] <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one] <;>
    first
    | linear_combination k1
    | linear_combination k2
    | linear_combination k3
    | linear_combination -k1

variable [CharP K 2]

theorem sl2_nonscalar_of_ne_one {z : SpecialLinearGroup (Fin 2) K} (hz : z ≠ 1) :
    (z : Matrix (Fin 2) (Fin 2) K) 0 1 ≠ 0 ∨ (z : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 ∨
      (z : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ (z : Matrix (Fin 2) (Fin 2) K) 1 1 := by
  by_contra hc
  push Not at hc
  obtain ⟨h01, h10, h00⟩ := hc
  apply hz
  have hdet := z.2
  rw [det_fin_two, h01, h10, h00, mul_zero, sub_zero] at hdet
  have h1 : (z : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    have h2 : ((z : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) * ((z : Matrix (Fin 2) (Fin 2) K) 1 1 - 1)
        = 0 := by
      linear_combination hdet + (1 - (z : Matrix (Fin 2) (Fin 2) K) 1 1) *
        (CharTwo.two_eq_zero : (2 : K) = 0)
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h2)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h1]

theorem sl2_commute_of_commute_ne_one {z g h : SpecialLinearGroup (Fin 2) K} (hz : z ≠ 1)
    (hg : g * z = z * g) (hh : h * z = z * h) : g * h = h * g := by
  apply Subtype.ext
  have hg' : (g : Matrix (Fin 2) (Fin 2) K) * z = z * g := congrArg Subtype.val hg
  have hh' : (h : Matrix (Fin 2) (Fin 2) K) * z = z * h := congrArg Subtype.val hh
  simpa using commute_of_commute_nonscalar_two (sl2_nonscalar_of_ne_one hz) hg' hh'

theorem sl2_comm_of_isPGroup (P : Subgroup (SpecialLinearGroup (Fin 2) K)) [Finite P]
    (hP : IsPGroup 2 P) : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
  intro a ha b hb
  by_cases hnt : Nontrivial P
  · have := Fact.mk Nat.prime_two
    have := hP.center_nontrivial
    obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center P)
    have hz1 : ((z : P) : SpecialLinearGroup (Fin 2) K) ≠ 1 := by
      intro h
      apply hz
      exact Subtype.ext (Subtype.ext h)
    have hza := congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨a, ha⟩)
    have hzb := congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨b, hb⟩)
    exact sl2_commute_of_commute_ne_one hz1 hza hzb
  · rw [not_nontrivial_iff_subsingleton] at hnt
    have := congrArg Subtype.val (Subsingleton.elim (⟨a * b, P.mul_mem ha hb⟩ : P)
      ⟨b * a, P.mul_mem hb ha⟩)
    exact this

end CFSG.LargeExtraspecial.S8
