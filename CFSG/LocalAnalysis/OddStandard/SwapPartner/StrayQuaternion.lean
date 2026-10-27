module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
import CFSG.Milestones.LR_Brauer_Suzuki_central_involution

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

theorem false_of_quaternion_sylow_of_simple {L : Type*} [Group L] [Finite L]
    (hL : IsSimpleGroup L) (hnab : ∃ x y : L, x * y ≠ y * x) (T : Sylow 2 L) {n : ℕ}
    (hn : 3 ≤ n) (e : Nonempty (↥(T : Subgroup L) ≃* QuaternionGroup (2 ^ (n - 2)))) :
    False := by
  haveI : IsSimpleGroup L := hL
  have hNpos : 0 < 2 ^ (n - 2) := pow_pos (by norm_num) _
  haveI : NeZero (2 ^ (n - 2)) := ⟨hNpos.ne'⟩
  have hcard : Nat.card ↥(T : Subgroup L) = 4 * 2 ^ (n - 2) := by
    obtain ⟨e'⟩ := e
    calc Nat.card ↥(T : Subgroup L)
        = Nat.card (QuaternionGroup (2 ^ (n - 2))) := Nat.card_congr e'.toEquiv
      _ = Fintype.card (QuaternionGroup (2 ^ (n - 2))) := Nat.card_eq_fintype_card
      _ = 4 * 2 ^ (n - 2) := QuaternionGroup.card
  have h2dvd : 2 ∣ Nat.card ↥(T : Subgroup L) := by
    rw [hcard]
    exact ⟨2 * 2 ^ (n - 2), by ring⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥(T : Subgroup L)) 2 h2dvd
  let t : L := (u : L)
  have ht_mem : t ∈ (T : Subgroup L) := u.2
  have ht_ord : orderOf t = 2 := by
    have h : orderOf t = orderOf u := (Subgroup.orderOf_mk (u : L) u.2).symm
    rw [hu] at h
    exact h
  have hmem := CFSG.Milestones.brauer_suzuki n hn T e t ht_mem ht_ord
  have hodd : CFSG.oddCore L = ⊥ := by
    refine eq_bot_iff.mpr (sSup_le fun N ⟨hN, hNodd⟩ => ?_)
    haveI := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact h.le
    · subst h
      rw [Subgroup.card_top] at hNodd
      obtain ⟨m, hm⟩ := hNodd
      obtain ⟨c, hc⟩ := (ht_ord ▸ orderOf_dvd_natCard t : 2 ∣ Nat.card L)
      omega
  have hcomm : ∀ g : L, g * t = t * g := by
    intro g
    have h1 := Subgroup.mem_center_iff.mp hmem (QuotientGroup.mk g)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hodd,
      Subgroup.mem_bot] at h1
    exact inv_mul_eq_one.mp h1
  have hcenter : Subgroup.center L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hnab
      exact (hab (isMulCommutative_iff.mp (Subgroup.center_eq_top_iff.mp h) a b)).elim
  have ht1 : t = 1 := by
    have : t ∈ Subgroup.center L := Subgroup.mem_center_iff.mpr hcomm
    rwa [hcenter, Subgroup.mem_bot] at this
  rw [ht1, orderOf_one] at ht_ord
  omega

end CFSG.OddStandard.AltStdSec.SwapPartner
