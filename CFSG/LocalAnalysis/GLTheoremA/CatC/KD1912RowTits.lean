module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912Core
public import CFSG.Quasithin.Vol2.GoldschmidtTDOutAbs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTSolvable
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalTitsFive

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD1912

open CFSG.Open
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.HardMathSupport.Timmesfeld.Proving
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.Sporadic.Schreier.Tits

section Certificates


theorem oddCoreFact_five_titsD : OddCoreFact 5 titsD := by
  constructor
  ·
    have hcardOuter : Nat.card (Outer titsD) = 2 := card_outer_titsD
    have hP : IsPGroup 2 (Outer titsD) :=
      IsPGroup.of_card (n := 1) (by rw [hcardOuter]; norm_num)
    exact CFSG.Quasithin.H13.OutTwoNilp.outTwoNilpotent_of_twoNilpotent_outer
      (CFSG.Quasithin.H13.OutTwoNilp.twoNilpotent_of_isPGroup_two hP)
  · intro α hα
    have hα5 : α ^ 5 = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
    obtain ⟨k, rfl⟩ := titsD_mem_inner_of_pow_eq_one Nat.prime_five (by norm_num) hα5
    have hk5 : orderOf k = 5 := by
      rw [← orderOf_injective (MulAut.conj : titsD →* MulAut titsD)
        CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux.conj_injective_titsD k]
      exact hα
    let Y : Subgroup (MulAut titsD) :=
      GLAPPrimeCoreOf 5 (innerAut titsD ⊓
        Subgroup.centralizer ({MulAut.conj k} : Set (MulAut titsD)))
    change Odd (Nat.card Y)
    have hYX : Y ≤ innerAut titsD ⊓
        Subgroup.centralizer ({MulAut.conj k} : Set (MulAut titsD)) := by
      dsimp only [Y]
      exact Subgroup.map_subtype_le (pPrimeCore 5 ↥(innerAut titsD ⊓
        Subgroup.centralizer ({MulAut.conj k} : Set (MulAut titsD))))
    have hYk : ∀ y ∈ Y, y * MulAut.conj k = MulAut.conj k * y := by
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hYX hy)).2
    have hYnorm : innerAut titsD ⊓
        Subgroup.centralizer ({MulAut.conj k} : Set (MulAut titsD)) ≤
        Subgroup.normalizer (Y : Set (MulAut titsD)) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hYX).1 (gLAPPrimeCoreOf_normal 5 _)
    have hYn : ∀ q : titsD, q * k = k * q → ∀ y ∈ Y,
        MulAut.conj q * y * (MulAut.conj q)⁻¹ ∈ Y := by
      intro q hqk y hy
      have hmem : MulAut.conj q ∈ innerAut titsD ⊓
          Subgroup.centralizer ({MulAut.conj k} : Set (MulAut titsD)) := by
        refine Subgroup.mem_inf.2 ⟨⟨q, rfl⟩, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        simpa using congrArg (MulAut.conj : titsD →* MulAut titsD) hqk
      exact (Subgroup.mem_normalizer_iff.mp (hYnorm hmem) y).1 hy
    have hY5 : Nat.Coprime 5 (Nat.card Y) := by
      dsimp only [Y]
      exact coprime_card_GLAPPrimeCoreOf Nat.prime_five _
    have hYbot : Y = ⊥ :=
      CFSG.HardMathSupport.Dickson.Bal207.titsD_eq_bot_of_five hk5 hYk hYn hY5
    rw [hYbot, Subgroup.card_bot]
    exact odd_one

end Certificates

theorem oddCoreFact_five_of_tits
    {S : Type} [Group S] [Finite S]
    (hv : (TauCeti.LieTypeIndex.tits).Valid)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group) :
    OddCoreFact 5 S := by
  obtain ⟨eT⟩ := titsModelEquiv S 2 1
    (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits (S := S) ⟨hv, ⟨e⟩⟩)
  exact (oddCoreFact_congr (p := 5) eT).mpr oddCoreFact_five_titsD

end CFSG.LocalAnalysis.GLTheoremA.KD1912
