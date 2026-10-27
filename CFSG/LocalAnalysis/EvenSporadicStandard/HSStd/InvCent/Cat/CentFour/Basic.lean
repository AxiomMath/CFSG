module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
import CFSG.GroupTheory.CyclicSylowNormalOddComplement

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.CentFour

open Subgroup

theorem exists_sylow_eq {S : Type*} [Group S] [Finite S] {V : Subgroup S} (hV : Nat.card V = 4)
    (hC : ∀ w ∈ V, w ≠ 1 → centralizer ({w} : Set S) = V) :
    ∃ P : Sylow 2 S, (P : Subgroup S) = V := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVp : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV]; norm_num)
  obtain ⟨P, hVP⟩ := hVp.exists_le_sylow
  haveI : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by rw [hV]; norm_num)
  obtain ⟨⟨w₀, hw₀⟩, hw₀1⟩ := exists_ne (1 : V)
  have hw₀1' : w₀ ≠ 1 := fun h => hw₀1 (Subtype.ext h)
  refine ⟨P, le_antisymm ?_ hVP⟩
  haveI : Nontrivial (P : Subgroup S) :=
    ⟨⟨⟨w₀, hVP hw₀⟩, 1, fun h => hw₀1' (congrArg Subtype.val h)⟩⟩
  haveI : Nontrivial (center (P : Subgroup S)) := P.isPGroup'.center_nontrivial
  obtain ⟨⟨z, hzc⟩, hz1⟩ := exists_ne (1 : center (P : Subgroup S))
  have hz1' : (z : S) ≠ 1 := fun h => hz1 (Subtype.ext (Subtype.ext h))
  have hzcomm : ∀ g : (P : Subgroup S), g * z = z * g := fun g => Subgroup.mem_center_iff.mp hzc g
  have hzV : (z : S) ∈ V := by
    have h : (z : S) ∈ centralizer ({w₀} : Set S) := by
      rw [mem_centralizer_singleton_iff]
      exact (congrArg Subtype.val (hzcomm ⟨w₀, hVP hw₀⟩)).symm
    rwa [hC w₀ hw₀ hw₀1'] at h
  intro g hg
  have hgz : g ∈ centralizer ({(z : S)} : Set S) := by
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hzcomm ⟨g, hg⟩)
  rwa [hC (z : S) hzV hz1'] at hgz

theorem not_isCyclic_sylow_of_card_four {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (P : Sylow 2 S) (hP : Nat.card P = 4) : ¬ IsCyclic P := by
  intro hcyc
  obtain ⟨N, hN, hcompl⟩ := CFSG.exists_normal_isComplement'_of_isCyclic_sylow_two P hcyc
  have hcard := hcompl.card_mul_card
  haveI := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  ·
    have h4 : Nat.card S = 2 ^ 2 := by
      rw [h, Subgroup.card_bot, hP] at hcard
      omega
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨a, b, hab⟩ := hna
    exact hab ((IsPGroup.isMulCommutative_of_card_eq_prime_sq h4).is_comm.comm a b)
  ·
    rw [h, Subgroup.card_top, hP] at hcard
    have := Nat.card_pos (α := S)
    omega

theorem isKleinFour_of_not_isCyclic {H : Type*} [Group H] (h4 : Nat.card H = 4)
    (hncyc : ¬ IsCyclic H) : IsKleinFour H := by
  have hfin : Finite H := Nat.finite_of_card_ne_zero (by omega)
  have hsq : ∀ x : H, x ^ 2 = 1 := by
    intro x
    by_contra hx
    apply hncyc
    refine isCyclic_of_orderOf_eq_card x ?_
    have hdvd : orderOf x ∣ 2 ^ 2 := by simpa [h4] using orderOf_dvd_natCard x
    have hnd : ¬ orderOf x ∣ 2 := fun h => hx (orderOf_dvd_iff_pow_eq_one.mp h)
    rcases (Nat.dvd_prime_pow Nat.prime_two).mp hdvd with ⟨i, hi, hxi⟩
    rw [h4]
    interval_cases i
    · exact absurd (by rw [hxi]; norm_num) hnd
    · exact absurd (by rw [hxi]; norm_num) hnd
    · simpa using hxi
  refine ⟨h4, ?_⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp (Monoid.exponent_dvd_of_forall_pow_eq_one hsq) with
    h | h
  · exfalso
    have : Subsingleton H := Monoid.exp_eq_one_iff.mp h
    have := Nat.card_of_subsingleton (1 : H)
    omega
  · exact h

end CFSG.EvenSporadicStandard.HSStd.InvCent.CentFour
