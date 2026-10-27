module

public import CFSG.ClassicalInvolution.Q3.Q3T8M11
public import CFSG.ClassicalInvolution.Q3.Q3T6CoreSec
public import CFSG.ClassicalInvolution.Asc77.AscT8S26UModL
public import CFSG.ClassicalInvolution.Uniform.U5Three

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups

private theorem factorization_two_24 : (24 : ℕ).factorization 2 = 3 := by
  have hv : padicValNat 2 24 = 3 := by
    have h : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
    rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow]
    have : padicValNat 2 3 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
    omega
  rw [Nat.factorization_def _ Nat.prime_two]
  exact hv

theorem s26_dich_of_sysDataU {Y : Type} [Group Y] {Φ : Set (Subgroup Y)}
    (D : LieSystemDataU 3 1 (Fin 1) Y Φ)
    (hcase : CompIs 3 1 (D.kind 0) .PSL 3 ∨ D.kind 0 = Q3.CompData.m11)
    {J' : Subgroup Y} (hJ' : J' ∈ Φ) {ū : Y} (hū : ū ∈ J') {n : ℕ} (hn : 1 ≤ n)
    (hord : orderOf ū = 2 ^ (n + 1))
    (hmax : (Nat.card SL(2, GaloisField 3 1)).factorization 2 = n + 2)
    (β : MulAut Y) (hβ : β ū = ū) (hβ2 : β ^ 2 ^ (n + 1) = 1) :
    β ^ 2 ^ n = 1 ∨ β ^ 2 ^ n = MulAut.conj (ū ^ 2 ^ n) := by
  have hsurj : Function.Surjective (D.hom 0) := Q3T6.lieSystemDataU_surjective_hom D 0
  obtain ⟨i', R', hR', hJR'⟩ := D.fundamental J' hJ'
  have hi' : i' = 0 := Subsingleton.elim _ _
  subst hi'
  rw [hJR'] at hū
  rcases hcase with hc | hc
  ·
    obtain ⟨e, he, hft, hadm, hc'⟩ := hc
    have he1 : e = 1 := by
      rcases he with h | ⟨h, -⟩
      · exact h
      · exact absurd h (by decide)
    subst he1
    obtain ⟨R'', hR'', hRR⟩ := exists_map_castHom hc' (D.hom 0) hR'
    rw [← hRR] at hū
    obtain ⟨s, hsR, hsū⟩ := Subgroup.mem_map.mp hū
    have hsurj' : Function.Surjective (castHom hc' (D.hom 0)) := by
      rw [← MonoidHom.range_eq_top, range_castHom, MonoidHom.range_eq_top]
      exact hsurj
    have key := s26_aut164L 3 1 hadm (by norm_num) Y (castHom hc' (D.hom 0))
      (castHom_ker_le_center hc' _ (D.ker_le_center 0)) hsurj' R'' hR'' s hsR n hn
      (by rw [hsū]; exact hord) β (by rw [hsū]; exact hβ) hβ2
    rw [hsū] at key
    exact key
  ·
    obtain ⟨R'', hR'', hRR⟩ := exists_map_castHom hc (D.hom 0) hR'
    rw [← hRR] at hū
    obtain ⟨s, hsR, hsū⟩ := Subgroup.mem_map.mp hū
    have hsurj' : Function.Surjective (castHom hc (D.hom 0)) := by
      rw [← MonoidHom.range_eq_top, range_castHom, MonoidHom.range_eq_top]
      exact hsurj
    have hn1 : n = 1 := by
      rw [natCard_sl2_galoisField_three, factorization_two_24] at hmax
      omega
    subst hn1
    have key := m11_dich (castHom hc (D.hom 0)) hsurj' (s := s)
      (by rw [hsū]; simpa using hord) β (by rw [hsū]; exact hβ) (by simpa using hβ2)
    rw [hsū] at key
    simpa using key

end CFSG.ClassicalInvolution.Q3.Q3T8
