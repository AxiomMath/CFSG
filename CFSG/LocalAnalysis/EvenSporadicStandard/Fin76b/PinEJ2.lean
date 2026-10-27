module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.PinModel
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsRigid
public import Certificates.Certificate24590
public import Certificates.Certificate24606

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J2

open Subgroup CFSG.ComponentClassification.J2Cover.Models

theorem tableSpec_P :
    TablePin.TableSpec (S.subgroupOf P) (incl (elt 4)) 128 (fun a => incl (elt a)) mulJ2 4 := by
  have hinc : Function.Injective (incl : S →* P) := Subgroup.inclusion_injective S_le_P
  have hmem : ∀ s : S, incl s ∈ S.subgroupOf P := fun s => by
    rw [mem_subgroupOf, incl_coe]; exact s.2
  refine ⟨fun a _ => hmem _, ?_, fun a b ha hb h => elt_injective ha hb (hinc h), ?_, ?_,
    by norm_num, rfl, by norm_num⟩
  · intro x hx
    obtain ⟨a, ha, hax⟩ := elt_surjective ⟨(x : Perm315), mem_subgroupOf.1 hx⟩
    refine ⟨a, ha, ?_⟩
    rw [hax]
    exact Subtype.ext (by simp [incl_coe])
  · intro a b ha hb
    have h1 := mulIdx_spec (a := a) hb
    rw [mulJ2, mulTab_get ha hb]
    exact ⟨h1.1, by rw [← map_mul, ← h1.2]⟩
  · rw [elt_zero, map_one]

theorem pinModel_P :
    ∃ (T E : Subgroup P) (t : P), PinModel P T E t := by
  have hchk := Certificates.certificate24590
  simp only [j2SylowCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    Bool.or_eq_true, Bool.not_eq_true'] at hchk
  obtain ⟨⟨hcomm, hcen⟩, -⟩ := hchk
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
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨S.subgroupOf P, _, incl (elt 4), PinModel.of_table (tableSpec_P)
    Certificates.certificate24606
    (IsPGroup.of_card (n := 7) (by rw [card_subgroupOf_S]; norm_num))
    ⟨4725, by decide, by rw [card_P, card_subgroupOf_S]⟩ (by rw [← map_mul, h4sq, map_one])
    (fun h1 => h4ne (hinc (by rw [h1, map_one]))) ?_ ?_⟩
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

end CFSG.EvenSporadicStandard.Fin76b.J2
