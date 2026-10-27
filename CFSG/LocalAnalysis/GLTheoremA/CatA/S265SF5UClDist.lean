module

public import CFSG.Open.Defs
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatTypeDet

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

open CFSG.Open CFSG.Timmesfeld.Orders

theorem eq_four_of_ordTwistedA_eq {u g e : ℕ} (hu : 2 ≤ u) (hg : 1 ≤ g) (he : 1 ≤ e)
    (h : ordTwistedA u (2 ^ g) = ordTwistedA 4 (2 ^ e)) : u = 4 ∧ g = e := by
  by_cases hs : u = 2 ∧ g = 1
  · obtain ⟨rfl, rfl⟩ := hs
    exact (((profile_ordTwistedA (n := 4) (by norm_num) he).ne_small (by omega)
      (by omega)).1 (by simpa using h.symm)).elim
  exact CFSG.SeitzReduction.UnitaryPilot.ordTwistedA_inj_two_pow hu (by norm_num) hg he
    (fun h' => hs (Prod.ext_iff.1 h')) (by simp) h

theorem ordBC_ne_ordTwistedA_four {s f e : ℕ} (hs : 1 ≤ s) (hf : 1 ≤ f) (he : 1 ≤ e) :
    ordBC s (2 ^ f) ≠ ordTwistedA 4 (2 ^ e) := by
  rcases Nat.lt_or_ge s 3 with hs3 | hs3
  · obtain rfl | rfl : s = 1 ∨ s = 2 := by omega
    · refine ne_ordTwistedA_of_dvd_closed (profile_ordBC hf) zBC_dvd_closed ?_ (by norm_num) he
      by_cases hN : f = 3 ∨ f = 6
      · rcases hN with rfl | rfl <;> decide
      · have hP : Profile (ordBC 1 (2 ^ f)) f (zBC 1 f) := by
          simpa using profile_ordBC (n := 1) hf
        exact hP.ne_small (by omega) (by omega)
    · exact fun h => CFSG.RankThree.PartOne.S12K.ordTwistedA_ne_ordBC_two (by norm_num) he hf
        h.symm
  · exact ordBC_ne_ordTwistedA hs3 hf (by norm_num) he

theorem ordD_ne_ordTwistedA_four {s f e : ℕ} (hs : 1 ≤ s) (hf : 1 ≤ f) (he : 1 ≤ e) :
    ordD s (2 ^ f) ≠ ordTwistedA 4 (2 ^ e) := by
  rcases Nat.lt_or_ge s 4 with hs4 | hs4
  · refine ne_ordTwistedA_of_dvd_closed (profile_ordD hs hf) zD_dvd_closed ?_ (by norm_num) he
    interval_cases s
    · have hP : Profile (ordD 1 (2 ^ f)) 0 (zD 1 f) := by simpa using profile_ordD le_rfl hf
      exact hP.ne_small (by omega) (by omega)
    · by_cases hf3 : f = 3
      · subst hf3
        decide
      · have hP : Profile (ordD 2 (2 ^ f)) (f * 2) (zD 2 f) := profile_ordD (by norm_num) hf
        exact hP.ne_small (by omega) (by omega)
    · by_cases hf1 : f = 1
      · subst hf1
        decide
      · have hP : Profile (ordD 3 (2 ^ f)) (f * 6) (zD 3 f) := profile_ordD (by norm_num) hf
        exact hP.ne_small (by omega) (by omega)
  · exact ordD_ne_ordTwistedA hs4 hf (by norm_num) he

theorem ordTwistedD_ne_ordTwistedA_four {s f e : ℕ} (hs : 1 ≤ s) (hf : 1 ≤ f) (he : 1 ≤ e) :
    ordTwistedD s (2 ^ f) ≠ ordTwistedA 4 (2 ^ e) := by
  rcases Nat.lt_or_ge s 4 with hs4 | hs4
  · intro h
    have hq : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    interval_cases s
    · have hU := profile_ordTwistedA (n := 4) (by norm_num) he
      rw [← h] at hU
      have h0 := ((profile_ordTwistedD le_rfl hf).transfer hU).1
      norm_num at h0
      omega
    · have h2 : ordTwistedD 2 (2 ^ f) = ordA 1 (2 ^ (2 * f)) := by
        have hq2 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ hq
        have hq4 : 1 ≤ ((2 ^ f) ^ 2) ^ 2 := Nat.one_le_pow _ _ hq2
        rw [pow_mul', ordTwistedD, ordA, show Nat.gcd 4 ((2 ^ f) ^ 2 + 1) = 1 from
          Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr (odd_pow_add_one hf (by norm_num))),
          show Nat.gcd (1 + 1) ((2 ^ f) ^ 2 - 1) = 1 from
          Nat.coprime_two_left.mpr (odd_pow_sub_one hf (by norm_num)), Nat.div_one, Nat.div_one,
          show Finset.Icc 1 (2 - 1) = {1} from rfl, show Finset.Icc 2 (1 + 1) = {2} from rfl,
          Finset.prod_singleton, Finset.prod_singleton, show 2 * (2 - 1) = 2 from rfl,
          show 2 / 2 = 1 from rfl, pow_one]
        zify [hq2, hq4]
        ring
      exact ordA_ne_ordTwistedA le_rfl (by omega) (by norm_num) he (h2 ▸ h)
    · have h3 : ordTwistedD 3 (2 ^ f) = ordTwistedA 3 (2 ^ f) := by
        rw [ordTwistedD, ordTwistedA, show Nat.gcd 4 ((2 ^ f) ^ 3 + 1) = 1 from
          Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr (odd_pow_add_one hf (by norm_num))),
          show Nat.gcd (3 + 1) (2 ^ f + 1) = 1 from Nat.Coprime.pow_left 2
          (Nat.coprime_two_left.mpr ((Nat.even_pow' (by omega)).mpr even_two).add_one),
          Nat.div_one, Nat.div_one, show Finset.Icc 1 (3 - 1) = {1, 2} from rfl,
          show Finset.Icc 2 (3 + 1) = {2, 3, 4} from rfl, Finset.prod_pair (by norm_num),
          Finset.prod_insert (by decide), Finset.prod_pair (by norm_num),
          toNat_pow_sub_neg_one_pow_of_even hq (by decide : Even 2),
          toNat_pow_sub_neg_one_pow_of_odd (by decide : Odd 3),
          toNat_pow_sub_neg_one_pow_of_even hq (by decide : Even 4)]
        ring
      have := (eq_four_of_ordTwistedA_eq (by norm_num) hf he (h3 ▸ h)).1
      omega
  · exact ordTwistedD_ne_ordTwistedA hs4 hf (by norm_num) he

end CFSG.LocalAnalysis.GLTheoremA.S265.SF5U

end
