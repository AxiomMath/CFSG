module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsRigid
public import Certificates.Certificate24590
public import Certificates.Certificate24592

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J2

open Subgroup CFSG.ComponentClassification.J2Cover.Models

theorem sylowEData_P :
    SylowEData P := by
  have hchk := Certificates.certificate24590
  simp only [j2SylowCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    Bool.or_eq_true, Bool.not_eq_true'] at hchk
  obtain ⟨⟨hcomm, hcen⟩, hsq⟩ := hchk
  have hcen' : ∀ a, a < 128 → (∀ d, d < 128 → mulIdx a d = mulIdx d a) → a = 0 ∨ a = 4 := by
    intro a ha hd
    have htrue : ((List.range 128).all fun d => mulIdx a d == mulIdx d a) = true :=
      List.all_eq_true.2 fun d hd' => beq_iff_eq.2 (hd d (List.mem_range.1 hd'))
    rcases hcen a ha with (h1 | h1) | h1
    · rw [htrue] at h1; exact absurd h1 (by decide)
    · exact Or.inl h1
    · exact Or.inr h1
  have h4sq : elt 4 * elt 4 = (1 : S) := by
    rw [← sq]
    have := pow_orderOf_eq_one (elt 4)
    rwa [orderOf_elt_four] at this
  have h4ne : elt 4 ≠ (1 : S) := fun h1 => by
    have := orderOf_elt_four
    rw [h1, orderOf_one] at this
    omega
  have hinc : Function.Injective (incl : S →* P) := Subgroup.inclusion_injective S_le_P
  have hmem : ∀ s : S, incl s ∈ S.subgroupOf P := fun s => by
    rw [mem_subgroupOf, incl_coe]; exact s.2
  have hS : ∀ x ∈ S.subgroupOf P, ∃ a : ℕ, a < 128 ∧ x = incl (elt a) := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := elt_surjective ⟨(x : Perm315), mem_subgroupOf.1 hx⟩
    refine ⟨a, ha, ?_⟩
    rw [hax]
    exact Subtype.ext (by simp [incl_coe])
  have hmul : ∀ a b : ℕ, b < 128 → elt a * elt b = elt (mulIdx a b) := fun a b hb =>
    ((mulIdx_spec hb).2).symm
  have hE := Certificates.certificate24592
  rw [j2ECheck, Bool.and_eq_true] at hE
  obtain ⟨hcheck, hfix⟩ := hE
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    Bool.not_eq_true', beq_iff_eq] at hfix
  refine TableE.sylowEData_of_table (T := S.subgroupOf P) (t := incl (elt 4))
    (b := incl (elt 2)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ 128 (fun a => incl (elt a)) mulIdx 4
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.of_card (n := 7) (by rw [card_subgroupOf_S]; norm_num)
  · exact ⟨4725, by decide, by rw [card_P, card_subgroupOf_S]⟩
  · rw [← map_mul, h4sq, map_one]
  · exact fun h1 => h4ne (hinc (by rw [h1, map_one]))
  · exact hmem _
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := hS x hx
    rw [← map_mul, ← map_mul, hmul a 4 (by norm_num), hmul 4 a ha, hcomm a ha]
  · intro y hy hc
    obtain ⟨a, ha, rfl⟩ := hS y hy
    have hcd : ∀ d, d < 128 → mulIdx a d = mulIdx d a := fun d hd => by
      have h1 := hc (incl (elt d)) (hmem _)
      rw [← map_mul, ← map_mul, hmul d a ha, hmul a d hd] at h1
      exact (elt_injective (mulIdx_spec (a := d) ha).1 (mulIdx_spec (a := a) hd).1 (hinc h1)).symm
    rcases hcen' a ha hcd with h0 | h0
    · left; rw [h0, elt_zero, map_one]
    · right; rw [h0]
  · refine ⟨incl (elt 1), ?_⟩
    rw [← map_mul, hmul 1 1 (by norm_num), hsq]
  · intro a ha2 ha1
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hx : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha2) ha1
    obtain ⟨g, ⟨-, hg⟩ | ⟨-, hg⟩⟩ := involution_conj_rep a hx
    · exact Or.inl ⟨g⁻¹, by rw [inv_inv, ← hg]; group⟩
    · exact Or.inr ⟨g⁻¹, by rw [inv_inv, ← hg]; group⟩
  · exact fun a _ => hmem _
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := hS x hx
    exact ⟨a, ha, rfl⟩
  · exact fun a b ha hb h => elt_injective ha hb (hinc h)
  · intro a b _ hb
    exact ⟨(mulIdx_spec hb).1, by
      show incl (elt a) * incl (elt b) = incl (elt (mulIdx a b))
      rw [← map_mul, hmul a b hb]⟩
  · show incl (elt 0) = 1
    rw [elt_zero, map_one]
  · exact ⟨by norm_num, rfl⟩
  · norm_num
  · intro a ha haa ha0
    obtain ⟨halt, hfa⟩ := hfix a ha
    have hfa' : fixCountArr eltArrs[a]! = 11 := by
      rcases hfa with h1 | h1
      · exact absurd h1 (by simp [haa, ha0])
      · exact h1
    have hsqa : elt a * elt a = (1 : S) := by
      rw [hmul a a halt, haa, elt_zero]
    have hne : elt a ≠ (1 : S) := fun h1 =>
      ha0 (elt_injective halt (by norm_num) (h1.trans elt_zero.symm))
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hx : orderOf (incl (elt a) : P) = 2 :=
      orderOf_eq_prime (by rw [pow_two, ← map_mul, hsqa, map_one])
        (fun h1 => hne (hinc (by rw [h1, map_one])))
    obtain ⟨g, ⟨-, hg⟩ | ⟨h15, -⟩⟩ := involution_conj_rep (incl (elt a)) hx
    · exact ⟨g⁻¹, by rw [inv_inv, ← hg]; group⟩
    · rw [incl_coe, fixCount_elt halt, hfa'] at h15
      omega
  · exact hcheck

end CFSG.EvenSporadicStandard.Fin76b.J2
