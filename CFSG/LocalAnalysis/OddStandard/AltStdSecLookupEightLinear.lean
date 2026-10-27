module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder
public import CFSG.RankThree.CentralLift.LinearScalarCover
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL scalars)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Matrix

variable {K : Type*} [Field K]

theorem pow_four_eq_zero_of_isNilpotent {M : Matrix (Fin 4) (Fin 4) K} (hM : IsNilpotent M) :
    M ^ 4 = 0 := by
  have h1 := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hM
  have h2 : M.charpoly = Polynomial.X ^ 4 := by
    have := h1.eq_zero
    rw [Fintype.card_fin] at this
    exact sub_eq_zero.1 this
  have h3 := Matrix.aeval_self_charpoly M
  rwa [h2, map_pow, Polynomial.aeval_X] at h3

theorem pow_four_eq_one_of_pow_eight_eq_one [CharP K 2] {g : Matrix (Fin 4) (Fin 4) K}
    (h8 : g ^ 8 = 1) : g ^ 4 = 1 := by
  have hc : Commute g 1 := Commute.one_right g
  have e8 : (g - 1) ^ 2 ^ 3 = g ^ 2 ^ 3 - 1 ^ 2 ^ 3 := sub_pow_char_pow_of_commute (p := 2) (n := 3) hc
  have e4 : (g - 1) ^ 2 ^ 2 = g ^ 2 ^ 2 - 1 ^ 2 ^ 2 := sub_pow_char_pow_of_commute (p := 2) (n := 2) hc
  rw [show (2 : ℕ) ^ 3 = 8 from rfl, one_pow, h8, sub_self] at e8
  rw [show (2 : ℕ) ^ 2 = 4 from rfl, one_pow] at e4
  have h4 := pow_four_eq_zero_of_isNilpotent ⟨8, e8⟩
  rw [e4] at h4
  exact sub_eq_zero.1 h4

end Matrix

section Projective

variable {K : Type} [Field K]

theorem scalars_four_eq_bot [Finite K] (hK : Nat.card K = 4) : scalars 4 K = ⊥ := by
  have h1 := CFSG.RankThree.CentralLift.card_scalars_dvd (k := K) (n := 4) 0
  have h2 := CFSG.RankThree.CentralLift.card_scalars_dvd_card_sub_one (k := K) (n := 4) 0
  rw [hK] at h2
  have h3 : Nat.card (scalars 4 K) ∣ Nat.gcd 4 (4 - 1) := Nat.dvd_gcd h1 h2
  rw [show Nat.gcd 4 (4 - 1) = 1 from rfl, Nat.dvd_one] at h3
  exact Subgroup.eq_bot_of_card_eq _ h3

theorem charP_two_of_card_four [Finite K] (hK : Nat.card K = 4) : CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have h0 : ((Fintype.card K : ℕ) : K) = 0 := FiniteField.cast_card_eq_zero K
  rw [← Nat.card_eq_fintype_card, hK] at h0
  have h4 : (2 : K) * 2 = 0 := by
    have e : ((4 : ℕ) : K) = 2 * 2 := by norm_num
    rw [← e]
    exact h0
  exact (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by exact_mod_cast mul_self_eq_zero.1 h4)

theorem orderOf_ne_eight_of_card_four [Finite K] (hK : Nat.card K = 4) (x : projectiveSL 4 K) :
    orderOf x ≠ 8 := by
  have := charP_two_of_card_four hK
  intro h8
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hx8 : (QuotientGroup.mk g : projectiveSL 4 K) ^ 8 = 1 := by
    rw [← h8]
    exact pow_orderOf_eq_one _
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, scalars_four_eq_bot hK, mem_bot] at hx8
  have hg4 : g ^ 4 = 1 := by
    have hm : (g : Matrix (Fin 4) (Fin 4) K) ^ 8 = 1 :=
      congrArg (fun h : SpecialLinearGroup (Fin 4) K => (h : Matrix (Fin 4) (Fin 4) K)) hx8
    exact Subtype.ext (pow_four_eq_one_of_pow_eight_eq_one hm)
  have hd : orderOf (QuotientGroup.mk g : projectiveSL 4 K) ∣ 4 :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hg4, QuotientGroup.mk_one])
  rw [h8] at hd
  norm_num at hd

theorem card_outer_dvd_four (hK : Nat.card K = 4) :
    Nat.card (Outer (projectiveSL 4 K)) ∣ 4 :=
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.higher_linear_outer_order_divides_field_gcd_bound
    (k := K) (p := 2) (f := 2) (n := 4) Nat.prime_two (by norm_num) (by norm_num)
    (by rw [hK]; norm_num)

theorem exists_projectiveSL_of_lieModel_four {W : Type} [Group W]
    (h : Blueprint.LieModel W .PSL 4 2 2) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
      Nonempty (W ≃* projectiveSL 4 K) := by
  rcases h with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · obtain ⟨-, -, -, K, hK, hfin, hcard, he⟩ :=
      CFSG.RankThree.PartOne.exists_projectiveSL_of_statedClassicalModel_PSL h
    exact ⟨K, hK, hfin, by rw [hcard]; norm_num, he⟩
  all_goals exact absurd h0 (by norm_num)

end Projective

end CFSG.OddStandard.AltStdSec
