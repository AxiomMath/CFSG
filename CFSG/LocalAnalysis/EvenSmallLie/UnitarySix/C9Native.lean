module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeClasses
public meta import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeData
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.C9NativeInputs
public import Certificates.Certificate3180
public import Certificates.Certificate3142
public import Certificates.Certificate3010

public section

namespace CFSG.EvenSmallLie.UnitarySix

open CFSG.Certificates CFSG.Certificates.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Fischer

theorem sum_check : sumCheck = true :=
  Certificates.certificate3142

theorem c3_mem : c3 ∈ uA := evalCodes_mem _ aGens_mem _

theorem ncard_fixed_c3 :
    {p : Fin 693 | c3 p = p}.ncard = 181 ∧ {p : Fin 693 | (j3 * c3) p = p}.ncard = 21 := by
  have h := sum_check
  simp only [sumCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨(ncard_fixed c3).trans h.1, (ncard_fixed _).trans h.2⟩

theorem ncard_fixed_one : {p : Fin 693 | (1 : Equiv.Perm (Fin 693)) p = p}.ncard = 693 := by
  simp

theorem j2_ne_one :
    j2 ≠ 1 := fun h => by
  have := orbit_facts.2.2.2.2.2.1
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem j3_ne_one :
    j3 ≠ 1 := fun h => by
  have := orbit_facts.2.2.2.2.2.2.1
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem ncard_fixed_of_mem_conjClass
    {x : Equiv.Perm (Fin 693)} :
    (x ∈ conjClass uK j1 → {p : Fin 693 | x p = p}.ncard = 181) ∧
      (x ∈ conjClass uK j2 → {p : Fin 693 | x p = p}.ncard = 53) ∧
      (x ∈ conjClass uK j3 → {p : Fin 693 | x p = p}.ncard = 21) := by
  obtain ⟨-, -, -, -, -, -, -, hf1, hf2, hf3⟩ := orbit_facts
  exact ⟨fun h => (conjClass_facts j1_mem j1_ne_one x h).2.trans hf1,
    fun h => (conjClass_facts j2_mem j2_ne_one x h).2.trans hf2,
    fun h => (conjClass_facts j3_mem j3_ne_one x h).2.trans hf3⟩

theorem mem_conjClass_j1_of_ncard
    {x : Equiv.Perm (Fin 693)}
    (hx : x ∈ uA)
    (hfix : {p : Fin 693 | x p = p}.ncard = 181) : x ∈ conjClass uK j1 := by
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [ncard_fixed_one] at hfix
    exact absurd hfix (by norm_num)
  obtain ⟨-, h2, h3⟩ := ncard_fixed_of_mem_conjClass (x := x)
  rcases korbits.1 x hx hx1 with h | h | h
  · exact h
  · have := (h2 h).symm.trans hfix
    exact absurd this (by norm_num)
  · have := (h3 h).symm.trans hfix
    exact absurd this (by norm_num)

theorem mem_conjClass_j3_of_ncard
    {x : Equiv.Perm (Fin 693)}
    (hx : x ∈ uA)
    (hfix : {p : Fin 693 | x p = p}.ncard = 21) : x ∈ conjClass uK j3 := by
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [ncard_fixed_one] at hfix
    exact absurd hfix (by norm_num)
  obtain ⟨h1, h2, -⟩ := ncard_fixed_of_mem_conjClass (x := x)
  rcases korbits.1 x hx hx1 with h | h | h
  · have := (h1 h).symm.trans hfix
    exact absurd this (by norm_num)
  · have := (h2 h).symm.trans hfix
    exact absurd this (by norm_num)
  · exact h

theorem c3_mem_conjClass :
    c3 ∈ conjClass uK j1 :=
  mem_conjClass_j1_of_ncard c3_mem ncard_fixed_c3.1

theorem j3_mul_c3_mem_conjClass :
    j3 * c3 ∈ conjClass uK j3 :=
  mem_conjClass_j3_of_ncard (uA.mul_mem j3_mem c3_mem) ncard_fixed_c3.2

theorem j3_eq : j3 = aGens.getD 0 1 * j2 := by
  simp [j3, j2, evalCodes]

theorem j1_eq : j1 = aGens.getD 0 1 := by
  simp [j1, evalCodes]

theorem j3_mul_j1 : j3 * j1 = j2 := by
  have hg : aGens.getD 0 1 ∈ uA := by
    rw [← j1_eq]
    exact j1_mem
  rw [j3_eq, j1_eq, mul_assoc, ← uA_comm _ hg _ j2_mem, ← mul_assoc, ← sq, uA_sq _ hg, one_mul]

end CFSG.EvenSmallLie.UnitarySix
