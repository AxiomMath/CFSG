module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenElevenOneSLThreeOdd
public import CFSG.Open.PGLModelDefs
import CFSG.RankThree.PartTwo.Sec8.Item82ProofPSL3
import CFSG.RankThree.PartTwo.KFacts.K72SylowL3
import CFSG.RankThree.PartOne.S15K.ProjSLBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3E27

open CFSG.Open Subgroup
open CFSG.RankThree.PartTwo.Sec8.Item82Proof CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem nonempty_mulEquiv_projSL_of_odd {n : ℕ} (hn : Odd n) :
    Nonempty (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n) ≃*
      CFSG.PGLModel.projSL 3 (GaloisField 2 n)) := by
  have hbot : scalars 3 (GaloisField 2 n) = ⊥ := by
    rw [scalars_eq_center]
    exact center_eq_bot_of_odd hn
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).symm.trans
    (CFSG.RankThree.PartOne.S15K.projSLEquivProjectiveSL 3 _).symm⟩

theorem card_le_nine_of_isElemAbelian_mulAut {X : Type*} [Group X] [Finite X] {n : ℕ}
    (hn : Odd n) (e : X ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n))
    {Γ : Subgroup (MulAut X)} (hΓ : IsElemAbelian 3 Γ) : Nat.card Γ ≤ 9 := by
  obtain ⟨eP⟩ := nonempty_mulEquiv_projSL_of_odd hn
  have hK : Nat.card (GaloisField 2 n) % 3 = 2 := by
    obtain ⟨k, rfl⟩ := hn
    rw [GaloisField.card 2 _ (by omega), pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  by_cases hτ : ∃ τ ∈ Γ, ¬ IsInnerAut τ
  · exact (kF82TwoPSL3Odd n hn).of_mulEquiv (e.trans eP) Γ hΓ hτ
  · push Not at hτ
    exact (card_inf_inner_le_three (isCyclic_sylow_three_of_mulEquiv_projSL hK (e.trans eP))
      (fun α hα => hΓ.2 α hα) hτ).trans (by norm_num)

theorem kFactLThreeOddAutRank_holds : KFactLThreeOddAutRank := by
  intro Y _ _ L _ n hn ⟨e⟩ Q _ hQC
  unfold CFSG.Open.pRank
  refine csSup_le' ?_
  rintro k ⟨E, hEQ, hE, hk⟩
  set φ : Y →* MulAut ↥L := MulAut.conjNormal
  have hinj : Function.Injective (φ.comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxC : (x : Y) ∈ centralizer (L : Set Y) := by
      rw [mem_centralizer_iff]
      intro l hl
      have h := congrArg (fun α : MulAut ↥L => ((α ⟨l, hl⟩ : ↥L) : Y)) hx
      simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, φ,
        MulAut.conjNormal_apply, MulAut.one_apply] at h
      rw [mul_inv_eq_iff_eq_mul] at h
      exact h.symm
    have hx1 : (x : Y) ∈ Q ⊓ centralizer (L : Set Y) := ⟨hEQ x.2, hxC⟩
    rw [hQC, mem_bot] at hx1
    exact Subtype.ext hx1
  have hcard : Nat.card (E.map φ) = Nat.card E := by
    have hrange : E.map φ = (φ.comp E.subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hrange]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  have h9 := card_le_nine_of_isElemAbelian_mulAut hn e (isElemAbelian_map hE φ)
  rw [hcard, hk, show (9 : ℕ) = 3 ^ 2 by norm_num] at h9
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h9

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3E27
