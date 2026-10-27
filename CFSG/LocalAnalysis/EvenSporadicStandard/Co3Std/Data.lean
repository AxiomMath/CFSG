module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Data
public import CFSG.Sporadic.SmallOddCore.Co3Classes
public import Certificates.Certificate25000

public section

namespace CFSG.EvenSporadicStandard.Co3Std

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Co3
open CFSG.Sporadic.SmallOddCore (ctuc_co3_complete_inner_involution_classes)

section Square


theorem co3TGen_zero_sq : co3TGen 0 * co3TGen 0 = co3Z :=
  eq_of_eqA (rep_compA (rep_co3TGen (by norm_num)) (rep_co3TGen (by norm_num))) rep_co3Z
    Certificates.certificate25000

end Square

section Data


theorem sylowData_co3P : Fin76b.SylowData co3P := by
  have hsub : ∀ x : co3P, x ∈ co3T.subgroupOf co3P ↔ (x : Equiv.Perm (Fin 276)) ∈ co3T :=
    fun x => mem_subgroupOf
  refine ⟨co3T.subgroupOf co3P, ⟨co3Z, co3Z_mem_P⟩, ⟨co3Tt, co3Tt_mem_P⟩, co3T_isPGroup,
    ⟨484147125, by decide, by rw [card_co3P, card_co3T_subgroupOf]⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Subtype.ext co3Z_mul_self
  · exact fun h => co3Z_ne_one (congrArg Subtype.val h)
  · exact (hsub _).2 co3Z_mem_T
  · intro x hx
    have h := mem_centralizer_singleton_iff.1 (co3T_le_centralizer_Z ((hsub x).1 hx))
    exact Subtype.ext h
  · intro y hy hc
    have hcen := (co3T_center_iff (y : Equiv.Perm (Fin 276))).1 ⟨(hsub y).1 hy, fun w hw =>
      (congrArg Subtype.val (hc ⟨w, co3T_le_P hw⟩ ((hsub _).2 hw))).symm⟩
    rcases hcen with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · exact ⟨⟨co3TGen 0, co3T_le_P (co3TGen_mem (by norm_num))⟩, Subtype.ext co3TGen_zero_sq⟩
  · intro a ha2 ha1
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hord : orderOf (a : Equiv.Perm (Fin 276)) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_eq_prime (by rw [pow_two]; exact ha2) ha1
    have hcl := (ctuc_co3_complete_inner_involution_classes.2.2.2.1 (a : Equiv.Perm (Fin 276))
      a.2 hord)
    by_cases hz : ∃ g ∈ co3P, (a : Equiv.Perm (Fin 276)) = g * co3Z * g⁻¹
    · obtain ⟨g, hg, hga⟩ := hz
      exact Or.inl ⟨⟨g, hg⟩, Subtype.ext hga⟩
    · have ht : ∃ g ∈ co3P, (a : Equiv.Perm (Fin 276)) = g * co3Tt * g⁻¹ := by
        by_contra hn
        exact hz (hcl.2 hn)
      obtain ⟨g, hg, hga⟩ := ht
      exact Or.inr ⟨⟨g, hg⟩, Subtype.ext hga⟩

end Data

end CFSG.EvenSporadicStandard.Co3Std
