module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRMat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQSz
public import CFSG.SignalizerFunctorTheorem.NearModels.Main

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FR

open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.FP CFSG.LocalAnalysis.GLTheoremA.FQ
open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Ree CFSG.Open
open CFSG.RankThree.PartOne.KE
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut)
open scoped commutatorElement


theorem subBody_suzuki {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (I F : Set (MulAut (LargeEvenCenterQuot (LargeEvenSzGroup a K)))) (hF : InnFree p F) :
    ∀ f ∈ F, orderOf f = p → p ∣ 2 * a + 1 ∧
      ∃ D : Subgroup (LargeEvenCenterQuot (LargeEvenSzGroup a K)), SubfieldGrp f D ∧
        (LargeEvenRecipeSuzuki (((2 * a + 1) / p - 1) / 2)
            (fun R' _ _ _ => Nonempty (↥D ≃* R')) ∨
          (2 * a + 1 = p ∧ Group.IsSolvable ↥D)) := by
  intro f hf hord
  obtain ⟨e⟩ := nonempty_szQuot_equiv ha hK
  have hαord : orderOf (MulAut.congr e f) = p := by
    rw [MulEquiv.orderOf_eq (MulAut.congr e) f, hord]
  have hαinn : MulAut.congr e f ∉
      CFSG.ComponentClassification.OuterAutomorphisms.inner (suzukiGroup a K) :=
    fun h => hF f hf hord ((congr_mem_range_conj e f).1 h)
  obtain ⟨σ, h, b, k, hkF, hkfin, hσp, hbp, hkcard, hconj, ⟨eH⟩⟩ :=
    suzukiPrimeFieldCosetDescent a ha K hK p hp hp2 (MulAut.congr e f) hαord hαinn
  have hpn : p ∣ 2 * a + 1 := ⟨2 * b + 1, by rw [← hbp, mul_comm]⟩
  have hdiv : (2 * a + 1) / p = 2 * b + 1 := by
    rw [← hbp, Nat.mul_div_cancel _ hp.pos]
  refine ⟨hpn, FP.fixSub f, ⟨le_rfl, ?_, ?_⟩, ?_⟩
  · exact Subgroup.commutator_le_of_le le_rfl le_rfl
  · rw [Subgroup.relIndex_self]; exact odd_one
  have e₁ : ↥(FP.fixSub f) ≃* suzukiGroup b k :=
    (fixSubEquivCongr e f).trans ((fixSubEquivConj (MulAut.conj h) (MulAut.congr e f)).trans
      ((MulEquiv.subgroupCongr (by rw [hconj]; rfl)).trans eH))
  rcases Nat.eq_zero_or_pos b with hb0 | hb1
  · subst hb0
    right
    refine ⟨by omega, ?_⟩
    have hc : Nat.card (suzukiGroup 0 k) = 20 := by
      rw [suzuki_order hkcard]
      norm_num [CFSG.Open.ordSuzuki]
    haveI : Finite (suzukiGroup 0 k) := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
    have : Group.IsSolvable (suzukiGroup 0 k) :=
      CFSG.SignalizerFunctorTheorem.NearModels.isSolvable_of_natCard (p := 2) (q := 5) (a := 2)
        (b := 1) Nat.prime_two (by norm_num) (by norm_num) (by rw [hc]; norm_num)
    exact CFSG.SignalizerFunctorTheorem.NearModels.isSolvable_of_mulEquiv e₁
  · left
    rw [hdiv]
    refine ⟨k, hkF, hkfin, ?_, ?_⟩
    · rw [show (2 * b + 1 - 1) / 2 = b by omega]; exact hkcard
    · obtain ⟨eZ⟩ := nonempty_szQuot_equiv hb1 hkcard
      rw [show (2 * b + 1 - 1) / 2 = b by omega]
      exact ⟨e₁.trans eZ.symm⟩

end FR

end CFSG.LocalAnalysis.GLTheoremA
