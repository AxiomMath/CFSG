module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2CoprimeSylowCyclic
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_Defs

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

open CFSG.HardMathSupport.Timmesfeld.ComponentBalance

theorem pRank_three_le_one_of_sylow_cyclic {X : Type} [Group X] [Finite X]
    (h : ∀ R : Sylow 3 X, IsCyclic R) : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine csSup_le' ?_
  rintro r ⟨E, -, hE, hcard⟩
  have hP : IsPGroup 3 E := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hE.2 x x.2)⟩
  obtain ⟨R, hER⟩ := hP.exists_le_sylow
  have : IsCyclic E := by
    have := h R
    exact Subgroup.isCyclic_of_le hER
  have hexp : Monoid.exponent E = Nat.card E := IsCyclic.exponent_eq_card
  have hdvd : Monoid.exponent E ∣ 3 := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
    exact Subtype.ext (hE.2 x x.2)
  have : 3 ^ r ∣ 3 ^ 1 := by
    rw [← hcard, ← hexp, pow_one]
    exact hdvd
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 this

theorem pRank_three_le_one_of_isL2TwoPowOdd {G : Type} [Group G] [Finite G]
    (hG : IsL2TwoPowOdd G) : CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 1 := by
  obtain ⟨n, hn, hn1, ⟨e⟩⟩ := hG
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn3 : 3 ≤ n := by
    obtain ⟨k, hk⟩ := hn
    omega
  have hK : Nat.card (GaloisField 2 n) = 2 ^ n := by
    exact GaloisField.card 2 n (by omega)
  have h7 : 7 ≤ Nat.card (GaloisField 2 n) := by
    rw [hK]
    calc 7 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  have hcop : Nat.Coprime 3 (Nat.card (GaloisField 2 n)) := by
    rw [hK]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hcyc := GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card
    (GaloisField 2 n) hK h7 3 (by norm_num) hcop
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
  exact pRank_three_le_one_of_sylow_cyclic hcyc

end CFSG.HardMathSupport.Timmesfeld.Tables.Census
