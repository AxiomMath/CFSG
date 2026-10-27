module

public import CFSG.ClassicalInvolution.Q3.Q3ZLiftCover
public import CFSG.ClassicalInvolution.WeakCT.SpinMinus6Generated
public import CFSG.LieType.Steinberg.CentralExt.SpinMinus

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.CurtisTits
open scoped MatrixGroups

theorem card_sl2_three : Nat.card SL(2, GaloisField 3 1) = 24 := by
  have hF : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 one_ne_zero]
    norm_num
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF]
  norm_num


theorem spinMinus6_three_noCover {b c : GaloisField 3 1}
    (hirr : ∀ s : GaloisField 3 1, s ^ 2 + b * s + c ≠ 0) :
    NoCover.{0} (fun n => Odd n ∧ ¬ 3 ∣ n)
      (spinGroup (quadMinus 3 (GaloisField 3 1) b c)) := by
  intro E _ _ _ π hπ hcen hQ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : (2 : GaloisField 3 1) ≠ 0 :=
    Ring.two_ne_zero (by rw [ringChar.eq (GaloisField 3 1) 3]; norm_num)
  have := fact_shortField hirr
  have := finite_shortField (b := b) (c := c)
  have : CharP (ShortField b c) 3 :=
    charP_of_injective_algebraMap (algebraMap (GaloisField 3 1) (ShortField b c)).injective 3
  have hct := WeakCT.minusDatum_isCTGroupDatum_three hirr h2
  obtain ⟨σ, hσ⟩ : ∃ σ : spinGroup (quadMinus 3 (GaloisField 3 1) b c) →* E,
      ∀ x, π (σ x) = x := by
    refine (existsUnique_section_of_rankOne_lift (p := 3) hct (minusDatum_steinbergExtras 3 hirr)
      (fun _ hγ => isPGroup_minusRootGroup hirr hγ) hπ hcen hQ.2 fun i => ?_).exists
    by_cases hi : i.val + 1 < 3 - 1
    · have hcop : Nat.Coprime (Nat.card π.ker) (Nat.card SL(2, GaloisField 3 1)) := by
        rw [card_sl2_three, show (24 : ℕ) = 2 ^ 3 * 3 by norm_num]
        refine Nat.Coprime.mul_right (Nat.Coprime.pow_right 3 ?_) ?_
        · exact Nat.coprime_two_right.mpr hQ.1
        · exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hQ.2).symm
      obtain ⟨ρ', hρ'⟩ := Q3Z.exists_lift_of_coprime π hπ hcop
        ((minusFrame 3 b c).longSL2 (succ_ne_of_lt 3 hi) true false)
      exact exists_lift_of_injective (SpinFrame.longSL2_injective _ _ _ _)
        (rankOne_minusRootGroup_of_lt 3 hirr hi).le fun g => DFunLike.congr_fun hρ' g
    · exact exists_rankOne_lift_of_rankOneRels (minusDatum_steinbergExtras 3 hirr) i
        (shortRels 3 hirr i) (mem_minusRootGroup_single_iff hirr hi)
        (mem_minusRootGroup_neg_single_iff hirr hi) (shortRels_x_injective hirr i)
        (fun t ht h1 => shortRels_h_eq_one hirr h2 i ht h1) hπ hcen hQ.2
  have htop : σ.range = ⊤ := by
    refine eq_top_of_perfect_of_central hcen (S := σ.range) (Z := π.ker) fun e => ?_
    refine ⟨σ (π e), ⟨_, rfl⟩, (σ (π e))⁻¹ * e, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, inv_mul_cancel]
  rw [eq_bot_iff]
  intro c' hc'
  obtain ⟨x, rfl⟩ : c' ∈ σ.range := by rw [htop]; trivial
  rw [MonoidHom.mem_ker, hσ] at hc'
  rw [hc', map_one]
  exact Subgroup.one_mem _

end CFSG.ClassicalInvolution.Q3.Q3TY
