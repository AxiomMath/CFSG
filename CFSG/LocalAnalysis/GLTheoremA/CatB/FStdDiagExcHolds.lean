module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.FStdDiagExcOrd
public import CFSG.LocalAnalysis.GLTheoremA.CatB.FStdDiagExcTwo

public section

namespace CFSG.LocalAnalysis.GLTheoremA.FStdDiag

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti
open CFSG.HardMathSupport.Solomon.Coordinator (lieOrderBridge_holds)
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie
  (lieCompIdx_excUntwisted compIdxAt_cat_twistedE6_of_rational twistedE6RationalCatalogue_holds
    compIdxAt_of_mulEquiv CompIdxAt fieldSize)
open CFSG.LocalAnalysis.GLTheoremA.HStdExcl (SmallOrd)
open CFSG.HardMathSupport.Dickson.Sec6 (FamF4 FamE6 FamTwE6 FamE7 FamE8)
open CFSG.LieType.SeitzGeneration (exists_catEquiv_adjointGroup exists_catEquiv_twistedE6)

theorem smallExcRes_holds :
    SmallExcRes := by
  classical
  intro S _ _ d hd hc e α hα hα3 hα1 I hI hsmall
  obtain ⟨d, hv⟩ := d
  cases d with
  | F4 q =>
    have hq2 : q.p = 2 := (LieTypeIndex.characteristic_F4 q).symm.trans hc
    have hcomp : CompIdxAt 3 (.F4 q) S := compIdxAt_of_mulEquiv e.symm
      (lieCompIdx_excUntwisted ⟨_, hv⟩ 3 Nat.prime_three (by norm_num)
        (by rw [hc]; norm_num) trivial)
    have hfs : fieldSize (.F4 q) = 2 :=
      fstd_fieldSize_two_of_compIdx lieOrderBridge_holds ⟨_, hv⟩ hc hcomp hα hα3 hα1 hI hsmall
    have hq : q.card = 2 := hfs
    obtain ⟨F, _, _, hF, -, ⟨θ⟩⟩ := exists_catEquiv_adjointGroup (c := LieTypeIndex.F4)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 q hv
    exact fstdNoSmallInn_of_mulEquiv (e.trans θ)
      (fstdNoSmallInn_adjointGroup_two (Or.inl rfl) (hF.trans hq)) α hα hα3 hα1 I hI hsmall
  | E6 q =>
    have hq2 : q.p = 2 := (LieTypeIndex.characteristic_E6 q).symm.trans hc
    have hcomp : CompIdxAt 3 (.E6 q) S := compIdxAt_of_mulEquiv e.symm
      (lieCompIdx_excUntwisted ⟨_, hv⟩ 3 Nat.prime_three (by norm_num)
        (by rw [hc]; norm_num) trivial)
    have hfs : fieldSize (.E6 q) = 2 :=
      fstd_fieldSize_two_of_compIdx lieOrderBridge_holds ⟨_, hv⟩ hc hcomp hα hα3 hα1 hI hsmall
    have hq : q.card = 2 := hfs
    obtain ⟨F, _, _, hF, -, ⟨θ⟩⟩ := exists_catEquiv_adjointGroup (c := LieTypeIndex.E6)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
    exact fstdNoSmallInn_of_mulEquiv (e.trans θ)
      (fstdNoSmallInn_adjointGroup_two (Or.inr (Or.inl rfl)) (hF.trans hq)) α hα hα3 hα1 I hI
      hsmall
  | E7 q =>
    have hq2 : q.p = 2 := (LieTypeIndex.characteristic_E7 q).symm.trans hc
    have hcomp : CompIdxAt 3 (.E7 q) S := compIdxAt_of_mulEquiv e.symm
      (lieCompIdx_excUntwisted ⟨_, hv⟩ 3 Nat.prime_three (by norm_num)
        (by rw [hc]; norm_num) trivial)
    have hfs : fieldSize (.E7 q) = 2 :=
      fstd_fieldSize_two_of_compIdx lieOrderBridge_holds ⟨_, hv⟩ hc hcomp hα hα3 hα1 hI hsmall
    have hq : q.card = 2 := hfs
    obtain ⟨F, _, _, hF, -, ⟨θ⟩⟩ := exists_catEquiv_adjointGroup (c := LieTypeIndex.E7)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hv
    exact fstdNoSmallInn_of_mulEquiv (e.trans θ)
      (fstdNoSmallInn_adjointGroup_two (Or.inr (Or.inr (Or.inl rfl))) (hF.trans hq)) α hα hα3
      hα1 I hI hsmall
  | E8 q =>
    have hq2 : q.p = 2 := (LieTypeIndex.characteristic_E8 q).symm.trans hc
    have hcomp : CompIdxAt 3 (.E8 q) S := compIdxAt_of_mulEquiv e.symm
      (lieCompIdx_excUntwisted ⟨_, hv⟩ 3 Nat.prime_three (by norm_num)
        (by rw [hc]; norm_num) trivial)
    have hfs : fieldSize (.E8 q) = 2 :=
      fstd_fieldSize_two_of_compIdx lieOrderBridge_holds ⟨_, hv⟩ hc hcomp hα hα3 hα1 hI hsmall
    have hq : q.card = 2 := hfs
    obtain ⟨F, _, _, hF, -, ⟨θ⟩⟩ := exists_catEquiv_adjointGroup (c := LieTypeIndex.E8)
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv
    exact fstdNoSmallInn_of_mulEquiv (e.trans θ)
      (fstdNoSmallInn_adjointGroup_two (Or.inr (Or.inr (Or.inr rfl))) (hF.trans hq)) α hα hα3
      hα1 I hI hsmall
  | twistedE6 q =>
    have hq2 : q.p = 2 := (LieTypeIndex.characteristic_twistedE6 q).symm.trans hc
    have hcomp : CompIdxAt 3 (.twistedE6 q) S := compIdxAt_of_mulEquiv e.symm
      (compIdxAt_cat_twistedE6_of_rational twistedE6RationalCatalogue_holds q hv Nat.prime_three
        (by norm_num) (by omega))
    have hfs : fieldSize (.twistedE6 q) = 2 :=
      fstd_fieldSize_two_of_compIdx lieOrderBridge_holds ⟨_, hv⟩ hc hcomp hα hα3 hα1 hI hsmall
    have hq : q.p ^ q.exponent = 2 := by rw [← PrimePower.card_def]; exact hfs
    obtain ⟨K, _, σ, hK, hσ, ⟨eK⟩⟩ := exists_catEquiv_twistedE6 q hv
    rw [hq] at hK hσ
    haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
    exact fstdNoSmallInn_of_mulEquiv (e.trans eK)
      (fstdNoSmallInn_twistedE6_two σ (by rw [hK]; norm_num) hσ) α hα hα3 hα1 I hI hsmall
  | _ => rcases hd with h | h | h | h | h <;> exact h.elim

end CFSG.LocalAnalysis.GLTheoremA.FStdDiag

end
