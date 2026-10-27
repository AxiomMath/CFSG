module

public import CFSG.GH74.Generic.BProg.B3.S3T5Facts
public import CFSG.GH74.Generic.BProg.B3.S3T5L3P
public import CFSG.GH74.Generic.BProg.B3.S3T5L3F
public import CFSG.GH74.Generic.BProg.B3.S3T5L3GF
public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3Cases

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T5L3

open Matrix Subgroup CFSG CFSG.Blueprint CFSG.Assembly.Dichotomy CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.GLS.Stage2.Signalizer CFSG.GH74.Generic

theorem l3OuterOddCore_proved : S3T5.L3OuterOddCore := by
  intro K _ _ hK H hH u hu hout
  obtain ⟨p, f, hp, hp2, hq, hmod⟩ := hK
  have : Fact p.Prime := ⟨hp⟩
  have hsimple : IsSimpleGroup K := isSimpleGroup_of_lieModel_L3' hmod
  have hu' : (u : MulAut K) * u = 1 := congrArg Subtype.val hu
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · rw [h, pow_zero] at hq; omega
    · exact h
  rcases hmod with hL | hU
  · obtain ⟨F, _, _, hF, ⟨e₀⟩⟩ :=
      CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hL
    have hperf : Group.IsPerfect K := by
      have := Odd87.isPerfect_projectiveSL3_fl3 F
      exact Group.IsPerfect.ofSurjective (f := e₀.symm.toMonoidHom) e₀.symm.surjective
    have hZ := center_trivial_of_simple_perfect hperf
    have hodd : Odd (Nat.card F) := by rw [hF]; exact (hp.odd_of_ne_two hp2).pow
    have hα2 : MulAut.congr e₀ (u : MulAut K) * MulAut.congr e₀ (u : MulAut K) = 1 := by
      rw [← map_mul, hu', map_one]
    have hne : MulAut.congr e₀ (u : MulAut K) ≠ 1 := fun h => hout ⟨1, by
      rw [map_one]
      exact ((MulAut.congr e₀).injective (h.trans (map_one _).symm)).symm⟩
    rcases Odd87.linear3_involution_cases (Odd87.fl3g_two_ne_zero hodd) _ hα2 hne with
      ⟨y, -, -, hy⟩ | ⟨A, σ, hσ, hA⟩ | ⟨B, hB, hBα⟩ | ⟨A, σ, hσ, hA⟩
    · refine (hout ⟨e₀.symm y, ?_⟩).elim
      ext x
      have h := congrArg (fun φ : MulAut (projectiveSL 3 F) => φ (e₀ x)) hy
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
        MulAut.conj_apply] at h
      rw [MulAut.conj_apply]
      apply e₀.injective
      rw [h, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    · exact oddCore_bot_linField hp hf hF e₀ hZ hH u hu A σ hσ hA
    · exact oddCore_bot_linGraph hodd (by rw [hF]; omega) e₀ hZ hH u B hB hBα
    · exact oddCore_bot_linGField hp hp2 hf hF e₀ hZ hH u hu A σ hσ hA
  · obtain ⟨-, -, F, _, _, hF, ⟨e₀⟩⟩ := lieModel_psu_data hU
    have := Fintype.ofFinite F
    have : CharP F p := charP_of_card_eq_prime_pow
      (by rw [← Nat.card_eq_fintype_card, hF, ← pow_mul])
    have hperf : Group.IsPerfect K := by
      have := Odd87.isPerfect_statedSU_three_odd hF hp2 (K := F)
      have : Group.IsPerfect (StatedProj (StatedSU 3 (p ^ f) F)) :=
        Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
      exact Group.IsPerfect.ofSurjective (f := e₀.symm.toMonoidHom) e₀.symm.surjective
    exact oddCore_bot_uni hp hp2 hf (by omega) hF e₀ (center_trivial_of_simple_perfect hperf) hH
      u hu hout

end CFSG.GH74.Generic.BProg.B3.S3T5L3
