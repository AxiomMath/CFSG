module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveMain
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FrameFamily
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FrameProd

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley
open scoped MatrixGroups


theorem e8FiveTwoFrameDatum_holds : E8FiveTwoFrameDatum := by
  intro K _ _ h5 Fr hFr w hw
  rw [eq_frameW8_of_smul_neg hw]
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  have hq : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  haveI : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  have hfr : Fr = iterateFrobenius (AlgebraicClosure K) (ringChar K) (f : ℕ) :=
    RingHom.ext fun x => by rw [hFr, iterateFrobenius_def, hq]
  have hn : canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) frameW8 ∈
      frameCore8 (AlgebraicClosure K) :=
    canonicalRep_mem_frameCore8_of_closure frameW8_mem_closure
  obtain ⟨z, hz, hzeq⟩ := lang_frameCore8 (L := AlgebraicClosure K) (ringChar K)
    (f : ℕ) f.pos _ hn
  have hFz : entrywiseFrobGL Tag.E8 (AlgebraicClosure K) (ringChar K) (f : ℕ) z =
      z * canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) frameW8 := by
    rw [← hzeq, mul_inv_cancel_left]
  refine ⟨z, frameCore8_le_adjointGroup hz, ?_, 1, ?_⟩
  · rw [hfr]
    exact hFz
  · intro y hy5 hyT
    obtain ⟨t, ht, hty⟩ := Subgroup.mem_map.1 hyT
    have htT : t ∈ torusGroup Tag.E8 (AlgebraicClosure K) := (mem_twistedTorusOf.1 ht).1
    have hzS : z ∈ frameSpan8 (AlgebraicClosure K) := frameCore8_le_frameSpan8 hz
    have htS : t ∈ frameSpan8 (AlgebraicClosure K) :=
      torusGroup_le_frameSpan8 (fun x => IsAlgClosed.exists_pow_nat_eq x two_pos) htT
    have hyS : baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL Tag.E8 K) ∈
        frameSpan8 (AlgebraicClosure K) := by
      rw [← hty]
      exact mul_mem (mul_mem hzS htS) (inv_mem hzS)
    rw [one_mul, inv_one, mul_one]
    refine mem_e8FrameGroup_of_frameSpan Fr (fun c => ?_)
      (fun c hc => RankThree.PartOne.KE.mem_range_algebraMap_of_pow_card_eq ((hFr c).symm.trans hc))
      (by rw [pow_succ, hy5, one_mul]) hyS
    rw [hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem seitzExcHighE8TwoFive_of_closing (hC : E8FiveTwoClosing) : SeitzExcHighE8TwoFive :=
  seitzExcHighE8TwoFive_of_inputs hC e8FiveTwoFrameDatum_holds

end CFSG.LieType.SeitzGeneration.ExcHigh
