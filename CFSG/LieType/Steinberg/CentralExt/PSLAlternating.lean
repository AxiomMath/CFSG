module

public import CFSG.LieType.Steinberg.CentralExt.MultiplierCongr
public import CFSG.LieType.Steinberg.CentralExt.PSLSmall
public import CFSG.Alternating.Multipliers.Main
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearFourTwo

public section

open Matrix
open scoped MatrixGroups

namespace CFSG.LieType.Steinberg.CentralExt.SLClosed

open CFSG.LocalAnalysis.ComponentInitial
  (unique_field_nine_projective_linear_alternating_six_isomorphism)

theorem psl_two_nine_hopfMultiplier :
    commutator PSL(2, GaloisField 3 2) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier PSL(2, GaloisField 3 2) ≃*
        Multiplicative (ZMod 2 × ZMod 3)) := by
  have : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Fintype.card (GaloisField 3 2) = 9 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 3 2 (by norm_num)]
    norm_num
  obtain ⟨e⟩ := unique_field_nine_projective_linear_alternating_six_isomorphism (GaloisField 3 2)
    hcard
  have hperf : Group.IsPerfect PSL(2, GaloisField 3 2) :=
    LinearGroups.linear_projective_perfect le_rfl (Or.inr (SL2Closed.exists_four_of_five_le
      (by rw [← Fintype.card_eq_nat_card, hcard]; norm_num)))
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
  obtain ⟨hcyc, hc6⟩ := CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_six
  have key : Nonempty (Multiplicative (ZMod (Nat.card
      (CFSG.RankThree.PerfectCover.hopfMultiplier (alternatingGroup (Fin 6))))) ≃*
        CFSG.RankThree.PerfectCover.hopfMultiplier (alternatingGroup (Fin 6))) :=
    ⟨zmodCyclicMulEquiv hcyc⟩
  rw [show Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (alternatingGroup (Fin 6))) =
    2 * 3 from hc6] at key
  obtain ⟨m2⟩ := key
  let crt : ZMod (2 * 3) ≃+ ZMod 2 × ZMod 3 :=
    (ZMod.chineseRemainder (by norm_num : Nat.Coprime 2 3)).toAddEquiv
  exact ⟨((griessHopfMultiplierCongr e).trans
    (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _)).trans
      (m2.symm.trans (AddEquiv.toMultiplicative crt))⟩

theorem psl_four_two_lieModel : CFSG.Blueprint.LieModel PSL(4, GaloisField 2 1) .PSL 4 2 1 :=
  Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩,
    GaloisField 2 1, inferInstance, inferInstance, GaloisField.card 2 1 one_ne_zero,
    ⟨CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 4 (GaloisField 2 1)⟩⟩

theorem psl_four_two_hopfMultiplier :
    commutator PSL(4, GaloisField 2 1) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier PSL(4, GaloisField 2 1) ≃*
        Multiplicative (ZMod 2)) := by
  obtain ⟨e⟩ := (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff
    PSL(4, GaloisField 2 1)).1 psl_four_two_lieModel
  have hperf : Group.IsPerfect PSL(4, GaloisField 2 1) :=
    LinearGroups.linear_projective_perfect (by norm_num) (Or.inl (by norm_num))
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
  have hc2 := CFSG.Alternating.Multipliers.card_hopfMultiplier_alternatingGroup (n := 8) le_rfl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc := isCyclic_of_prime_card hc2
  have key : Nonempty (Multiplicative (ZMod (Nat.card
      (CFSG.RankThree.PerfectCover.hopfMultiplier (alternatingGroup (Fin 8))))) ≃*
        CFSG.RankThree.PerfectCover.hopfMultiplier (alternatingGroup (Fin 8))) :=
    ⟨zmodCyclicMulEquiv hcyc⟩
  rw [hc2] at key
  obtain ⟨m2⟩ := key
  exact ⟨((griessHopfMultiplierCongr e).trans
    (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _)).trans m2.symm⟩

theorem griess_psl
    (p f n : ℕ) [Fact p.Prime]
    (hf : 0 < f) (hn : 2 ≤ n) (hsmall : n = 2 → 4 ≤ p ^ f) :
    commutator PSL(n, GaloisField p f) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier PSL(n, GaloisField p f) ≃*
        Multiplicative (ZMod (Nat.gcd n (p ^ f - 1)) ×
          ZMod (CFSG.Open.griessPSLExceptional n (p ^ f)).1 ×
            ZMod (CFSG.Open.griessPSLExceptional n (p ^ f)).2)) := by
  have hp := (Fact.out : p.Prime)
  by_cases h29 : n = 2 ∧ p ^ f = 9
  · obtain ⟨rfl, h9⟩ := h29
    have hp3 : p = 3 := by
      have hdvd : p ∣ 3 ^ 2 := by
        rw [show (3 : ℕ) ^ 2 = p ^ f by rw [h9]; norm_num]
        exact dvd_pow_self p hf.ne'
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow hdvd)
    subst hp3
    have hf2 : f = 2 := Nat.pow_right_injective (a := 3) (by norm_num)
      (show 3 ^ f = 3 ^ 2 by rw [h9])
    subst hf2
    obtain ⟨hperf, ⟨e⟩⟩ := psl_two_nine_hopfMultiplier
    refine ⟨hperf, ⟨e.trans (AddEquiv.toMultiplicative ?_)⟩⟩
    rw [show CFSG.Open.griessPSLExceptional 2 (3 ^ 2) = (3, 1) by decide,
      show Nat.gcd 2 (3 ^ 2 - 1) = 2 by norm_num]
    exact (AddEquiv.prodUnique (M := ZMod 2 × ZMod 3) (N := ZMod 1)).symm.trans
      AddEquiv.prodAssoc
  by_cases h42 : n = 4 ∧ p ^ f = 2
  · obtain ⟨rfl, h2⟩ := h42
    have hp2 := prime_eq_two_of_pow_eq hp hf (h2.trans (pow_one 2).symm)
    subst hp2
    have hf1 : f = 1 := Nat.pow_right_injective le_rfl (h2.trans (pow_one 2).symm)
    subst hf1
    obtain ⟨hperf, ⟨e⟩⟩ := psl_four_two_hopfMultiplier
    refine ⟨hperf, ⟨e.trans (AddEquiv.toMultiplicative ?_)⟩⟩
    rw [show CFSG.Open.griessPSLExceptional 4 (2 ^ 1) = (2, 1) by decide,
      show Nat.gcd 4 (2 ^ 1 - 1) = 1 by norm_num]
    exact zmodTwoEquivProd
  exact griess_psl_of_ne p f n hf hn hsmall h29 h42

end CFSG.LieType.Steinberg.CentralExt.SLClosed
