
module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22TransitiveBase

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Hexads
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Count
public import CFSG.Sporadic.Schreier.M22Data
public meta import CFSG.Sporadic.Schreier.M22Data
public import Certificates.Certificate2035
public import Certificates.Data.CFSGNative.Mathieu.M22

public section

namespace CFSG.ComponentClassification.WittDesign

open MulAction CFSG.Sporadic.Mathieu

theorem count_stabilizer_triple : m22Count (fun g => g 0 = 0 ∧ g 1 = 1 ∧ g 2 = 2) = 48 :=
  Certificates.certificate2035

theorem card_stabilizer_baseTriple : Nat.card (stabilizer M22 baseTriple) = 48 := by
  rw [← count_stabilizer_triple, ← card_m22_subtype]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => mem_stabilizer_baseTriple_iff)

theorem isMultiplyPretransitive_M22 : IsMultiplyPretransitive M22 (Fin 22) 3 := by
  refine (isPretransitive_iff_orbit_eq_univ baseTriple).2 ?_
  have hcard : Nat.card (orbit M22 baseTriple) = 9240 := by
    have h := card_orbit_mul_card_stabilizer baseTriple
    rw [card_stabilizer_baseTriple, show (443520 : ℕ) = 9240 * 48 by norm_num] at h
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h
  have huniv : Nat.card (Fin 3 ↪ Fin 22) = 9240 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq]
    rfl
  refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ Set.finite_univ
  rw [Set.ncard_univ, huniv, ← Nat.card_coe_set_eq]
  exact hcard.ge

instance isPretransitive_M22 : IsPretransitive M22 (Fin 22) := by
  have := isMultiplyPretransitive_M22
  have h1 : IsMultiplyPretransitive M22 (Fin 22) 1 :=
    isMultiplyPretransitive_of_le (n := 3) (by norm_num) (by simp)
  exact is_one_pretransitive_iff.1 h1

theorem card_stabilizer_point (a : Fin 22) : Nat.card (stabilizer M22 a) = 20160 := by
  have h := card_orbit_mul_card_stabilizer a
  rw [orbit_eq_univ, Nat.card_coe_set_eq, Set.ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_fin, show (443520 : ℕ) = 22 * 20160 by norm_num] at h
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h

theorem exists_smul_eq_pair {a b c d : Fin 22} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ g : M22, g • a = c ∧ g • b = d := by
  have := isMultiplyPretransitive_M22
  have h2 : IsMultiplyPretransitive M22 (Fin 22) 2 :=
    isMultiplyPretransitive_of_le (n := 3) (by norm_num) (by simp)
  exact is_two_pretransitive_iff.1 h2 hab hcd

theorem exists_smul_eq_triple {a b c a' b' c' : Fin 22} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hab' : a' ≠ b') (hac' : a' ≠ c') (hbc' : b' ≠ c') :
    ∃ g : M22, g • a = a' ∧ g • b = b' ∧ g • c = c' := by
  have hι : Function.Injective ![a, b, c] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have hι' : Function.Injective ![a', b', c'] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  obtain ⟨g, hg⟩ := isMultiplyPretransitive_M22.exists_smul_eq ⟨_, hι⟩ ⟨_, hι'⟩
  refine ⟨g, ?_, ?_, ?_⟩
  · have := congrArg (fun f : Fin 3 ↪ Fin 22 => f 0) hg
    simpa using this
  · have := congrArg (fun f : Fin 3 ↪ Fin 22 => f 1) hg
    simpa using this
  · have := congrArg (fun f : Fin 3 ↪ Fin 22 => f 2) hg
    simpa using this

theorem exists_mem_stabilizer_smul_eq (a : Fin 22) {x y : Fin 22} (hx : x ≠ a) (hy : y ≠ a) :
    ∃ g ∈ stabilizer M22 a, g • x = y := by
  obtain ⟨g, hga, hgx⟩ := exists_smul_eq_pair (Ne.symm hx) (Ne.symm hy)
  exact ⟨g, hga, hgx⟩

end CFSG.ComponentClassification.WittDesign
