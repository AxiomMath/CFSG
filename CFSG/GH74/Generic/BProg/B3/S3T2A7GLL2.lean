module

public import CFSG.GH74.Generic.BProg.B3.S3T2A7GLL2D
public import CFSG.GH74.Generic.BProg.B2.FamilyL2
public import CFSG.GH74.Generic.BProg.B3.S3T2A7GLBasic

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T2A7

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup


theorem cell125_l2 : Cell125 OddL2 := by
  intro Y _ _ L B X₀ z hs hP hsig hcut
  obtain ⟨p, f, hp, hp2, -, hm⟩ := hP
  by_cases hBN : B ≤ normalizer (L : Set Y)
  · exact false_of_weakSig2NormG4 hs hsig hBN
      (B2.weakSig2NormG4_of_psl2Cover hs.comp.1 hp hp2 hm)
  rcases B2.l2_cover_cases hs.comp.1 hp hp2 hm with ⟨u, hu1, huc, huo⟩ | ⟨hZ, -⟩ |
      ⟨-, K, _, _, hK, ⟨ψ⟩⟩
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hu : u ∈ center ↥L := mem_center_iff.mpr huc
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp (GLR.isPGroup_center hs)) ⟨u, hu⟩
    rw [Subgroup.orderOf_mk] at hk
    rcases k with _ | k
    · exact hu1 (orderOf_eq_one_iff.mp (by simpa using hk))
    · rw [hk] at huo
      exact (Nat.not_even_iff_odd.mpr huo) (Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero k⟩)
  ·
    have := hs.comp.1.2.1
    exact hBN fun b _ =>
      normal_of_rankCertified_one hs hZ (GLR.rankCertified_one_of_simple hs.comp.1.2.2) b
  ·
    obtain ⟨D, hDB, hDz, hDsup⟩ := exists_compl_zpowers hs.B_el hs.z_mem
    obtain ⟨s, hsD, hsN⟩ : ∃ s ∈ D, s ∉ normalizer (L : Set Y) := by
      by_contra hcon
      push Not at hcon
      apply hBN
      intro b hb
      obtain ⟨d, hd, w, hw, rfl⟩ := GLR.exists_mul_of_mem hs hDB hDsup hb
      have hwc : ∀ g : Y, g * w = w * g := fun g =>
        Subgroup.mem_center_iff.mp ((zpowers_le.mpr hs.z_cent) hw) g
      have hwN : w ∈ normalizer (L : Set Y) := mem_normalizer_iff.mpr fun h => by
        rw [← hwc h, mul_inv_cancel_right]
      exact mul_mem (hcon d hd) hwN
    by_cases h4 : ∃ t ∈ D, t ∉ normalizer (L : Set Y) ∧ s * t ∉ normalizer (L : Set Y)
    · obtain ⟨t, htD, htN, hstN⟩ := h4
      exact GLR.false_of_orbit_four hs hsig hDB hDz hDsup hsD htD hsN htN hstN
    · push Not at h4
      exact GLR.false_of_orbit_two hs hsig hcut hDB hDz hDsup hsD hsN h4 hp hp2 hm hK ψ

end CFSG.GH74.Generic.BProg.B3.S3T2A7
