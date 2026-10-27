module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E7FrameFamily
public import CFSG.LieType.SeitzGeneration.ExcHigh.E7FrameProd
public import CFSG.LieType.SeitzGeneration.ExcHigh.E7TwoSevenLang
public import CFSG.RankThree.PartOne.KE.SuzukiDescent

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley
open scoped MatrixGroups


theorem frame_not_seven_dvd_two_pow_add_one (e : ℕ) : ¬ 7 ∣ 2 ^ e + 1 := by
  have h : 2 ^ e % 7 = 1 ∨ 2 ^ e % 7 = 2 ∨ 2 ^ e % 7 = 4 := by
    induction e with
    | zero => norm_num
    | succ n ih => rw [pow_succ]; omega
  intro hd
  generalize 2 ^ e = x at h hd
  omega

theorem e7SevenFrameDatum_holds : E7SevenFrameDatum := by
  refine ⟨frameW, frameW_smul, ?_⟩
  intro K _ _ h7 Fr hFr
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  have hq : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  haveI : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  have hfr : Fr = iterateFrobenius (AlgebraicClosure K) (ringChar K) (f : ℕ) :=
    RingHom.ext fun x => by rw [hFr, iterateFrobenius_def, hq]
  have hℓ2 : ringChar K ≠ 2 := by
    intro h2
    rw [hq, h2] at h7
    exact frame_not_seven_dvd_two_pow_add_one _ h7
  have h2L : (2 : AlgebraicClosure K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : AlgebraicClosure K) = 0 := by rw [Nat.cast_ofNat]; exact h
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1
      ((CharP.cast_eq_zero_iff (AlgebraicClosure K) (ringChar K) 2).1 h'))
  have hn : canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K) frameW ∈
      familyGroup (τ := Tag.E7) (K := AlgebraicClosure K) (frameFamily (AlgebraicClosure K)) :=
    canonicalRep_mem_familyGroup_of_closure_gen _ (frameW_mem_closure (AlgebraicClosure K))
  obtain ⟨z, hz, hzeq⟩ := lang_familyGroup (ringChar K) (frameFamily (AlgebraicClosure K))
    (f : ℕ) f.pos 1 (one_mem _) _ hn
  rw [one_mul, inv_one, mul_one] at hzeq
  have hFz : entrywiseFrobGL Tag.E7 (AlgebraicClosure K) (ringChar K) (f : ℕ) z =
      z * canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K) frameW := by
    rw [← hzeq, mul_inv_cancel_left]
  refine ⟨z, (mem_familyCentralizer.1 (familyGroup_le_familyCentralizer _ hz)).1, ?_, ?_⟩
  · rw [hfr]
    exact hFz
  · intro y hy7 hyT
    obtain ⟨t, ht, hty⟩ := Subgroup.mem_map.1 hyT
    have htT : t ∈ torusGroup Tag.E7 (AlgebraicClosure K) := (mem_twistedTorusOf.1 ht).1
    have hzS : z ∈ frameSpan (AlgebraicClosure K) := familyGroup_frameFamily_le_frameSpan h2L hz
    have htS : t ∈ frameSpan (AlgebraicClosure K) :=
      torusGroup_le_frameSpan (fun x => IsAlgClosed.exists_pow_nat_eq x two_pos) htT
    have hyS : baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL Tag.E7 K) ∈
        frameSpan (AlgebraicClosure K) := by
      rw [← hty]
      exact mul_mem (mul_mem hzS htS) (inv_mem hzS)
    refine mem_e7FrameGroup_of_frameSpan Fr (fun c => ?_)
      (fun c hc => RankThree.PartOne.KE.mem_range_algebraMap_of_pow_card_eq ((hFr c).symm.trans hc))
      (by rw [pow_succ, hy7, one_mul]) hyS
    rw [hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]

end CFSG.LieType.SeitzGeneration.ExcHigh
