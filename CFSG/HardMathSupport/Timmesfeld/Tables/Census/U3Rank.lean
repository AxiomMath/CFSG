module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.TableL2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134EvenClassical

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

open CFSG.Assembly.LowTwoRank CFSG.SectionRank CFSG.SectionRank.ClassicalEven
open CFSG.QuasithinUnique.Vol2Native.EvenWit

theorem two_le_pRank_three_psu_three_two_pow_odd {S : Type} [Group S] [Finite S] {f : ℕ}
    (hfo : Odd f) (hm : StatedClassicalModel S .PSU 3 2 f) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
  have hq0 : 2 ^ f ≠ 0 := by positivity
  have hKu : Nat.card Kˣ = (2 ^ f + 1) * (2 ^ f - 1) := by
    rw [Nat.card_units, hK, ← Nat.sq_sub_sq, one_pow]
  obtain ⟨k, hk⟩ := hfo
  have hmod : 2 ^ f % 3 = 2 := by
    rw [hk, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have h3 : 3 ∣ 2 ^ f + 1 := by omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3
    (by rw [hKu]; exact h3.mul_right _)
  have hζq : ζ ^ (2 ^ f + 1) = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (by rw [hζ]; exact h3)
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
  refine two_le_pRank_of_mulEquiv Nat.prime_three e ?_
  refine two_le_pRank_three_of_cubic hζ (StatedSU 3 (2 ^ f) K) ?_ ?_ (cycGL_mem_SU K hq0)
  · refine torusDiag_mem_SU hq0 (by simp [Fin.prod_univ_three]) ?_
    funext i
    fin_cases i <;> simp [hζq, inv_pow]
  · refine torusDiag_mem_SU hq0 (by simp [Fin.prod_univ_three]) ?_
    funext i
    fin_cases i <;> simp [hζq, inv_pow]

theorem u3TwoPowOddRankTwo : U3TwoPowOddRankTwo := by
  intro G _ _ h
  obtain ⟨n, hn, -, -, hm⟩ := h
  exact two_le_pRank_three_psu_three_two_pow_odd hn hm

end CFSG.HardMathSupport.Timmesfeld.Tables.Census
