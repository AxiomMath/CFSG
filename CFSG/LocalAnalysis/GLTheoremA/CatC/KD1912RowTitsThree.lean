module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912Core
public import CFSG.GroupTheory.PCore.FixedSubgroupCore
public import CFSG.Quasithin.Vol2.GoldschmidtTDOutAbs
public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofTits
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03Core

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD1912

open CFSG.Open
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.Sporadic.Schreier.Tits
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

section Certificates


theorem pPrimeCore_three_centralizer_titsD {x : titsD} (hx : orderOf x = 3) :
    CFSG.pPrimeCore 3 ↥(Subgroup.centralizer ({x} : Set titsD)) = ⊥ := by
  classical
  set C := Subgroup.centralizer ({x} : Set titsD)
  obtain ⟨a, b, hcard, -⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Res417Seven.exists_card_centralizer_of_titsD hx
  by_contra hN
  have hNnormal : (CFSG.pPrimeCore 3 C).Normal := CFSG.pPrimeCore_normal
  have hN2 : IsPGroup 2 ↥(CFSG.pPrimeCore 3 C) :=
    CFSG.RankThree.PartTwo.Sec4.Res417Seven.isPGroup_two_of_coprime_three hcard
      (CFSG.coprime_card_pPrimeCore 3 C)
  have hinv : ∀ u v : C, orderOf u = 2 → orderOf v = 2 → u * v = v * u → u = v := by
    intro u v hu hv huv
    apply Subtype.ext
    exact CFSG.RankThree.PartTwo.Sec4.Item434RemTits.eq_of_commute_of_orderOf_three hx
      (by rw [Subgroup.orderOf_coe]; exact hu)
      (by rw [Subgroup.orderOf_coe]; exact hv)
      (Subgroup.mem_centralizer_singleton_iff.mp u.2)
      (Subgroup.mem_centralizer_singleton_iff.mp v.2)
      (congrArg Subtype.val huv)
  obtain ⟨u, hu2, huc⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Res417Seven.exists_central_involution
      (H := C) (N := CFSG.pPrimeCore 3 C) hNnormal hN2 hN hinv
  obtain ⟨y, hyx, hy3, hyz⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Res417Seven.exists_commute_of_titsD hx
  have hyC : y ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hyx
  obtain ⟨E, hE9, hEgen⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Res417Seven.exists_card_nine_of_commute hx hy3 hyz hyx.symm
  refine CFSG.RankThree.PartTwo.Sec4.Item434RemTits.false_of_commute_e9 hE9
    (by rwa [Subgroup.orderOf_coe]) ?_
  intro e he
  obtain ⟨i, j, rfl⟩ := hEgen e he
  have hux : (u : titsD) * x = x * (u : titsD) :=
    Subgroup.mem_centralizer_singleton_iff.mp u.2
  have huy : (u : titsD) * y = y * (u : titsD) := by
    have h := congrArg Subtype.val (huc ⟨y, hyC⟩)
    exact h.symm
  have hxi : ∀ i : ℤ, x ^ i * (u : titsD) = (u : titsD) * x ^ i :=
    fun i => (Commute.zpow_left (show Commute x (u : titsD) from hux.symm) i).eq
  have hyj : ∀ j : ℤ, y ^ j * (u : titsD) = (u : titsD) * y ^ j :=
    fun j => (Commute.zpow_left (show Commute y (u : titsD) from huy.symm) j).eq
  calc x ^ i * y ^ j * (u : titsD)
      = x ^ i * (y ^ j * (u : titsD)) := mul_assoc _ _ _
    _ = x ^ i * ((u : titsD) * y ^ j) := by rw [hyj j]
    _ = x ^ i * (u : titsD) * y ^ j := (mul_assoc _ _ _).symm
    _ = (u : titsD) * x ^ i * y ^ j := by rw [hxi i]
    _ = (u : titsD) * (x ^ i * y ^ j) := mul_assoc _ _ _

theorem oddCoreFact_three_titsD : OddCoreFact 3 titsD := by
  constructor
  ·
    have hP : IsPGroup 2 (Outer titsD) :=
      IsPGroup.of_card (n := 1) (by rw [CFSG.Sporadic.Schreier.Tits.card_outer_titsD]; norm_num)
    exact CFSG.Quasithin.H13.OutTwoNilp.outTwoNilpotent_of_twoNilpotent_outer
      (CFSG.Quasithin.H13.OutTwoNilp.twoNilpotent_of_isPGroup_two hP)
  · intro α hα
    have hα3 : α ^ 3 = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
    have hin : α ∈ innerAut titsD :=
      CFSG.LocalAnalysis.GLTheoremA.ys03_inner_of_pow_of_outer_le_two Nat.prime_three
        (by norm_num) (by rw [CFSG.Sporadic.Schreier.Tits.card_outer_titsD]) hα3
    obtain ⟨k, rfl⟩ := hin
    have hk3 : orderOf k = 3 := by
      rw [← orderOf_injective (MulAut.conj : titsD →* MulAut titsD)
        (CFSG.mulAutConj_injective_of_center_eq_bot
          (CFSG.Sporadic.Schreier.Tits.titsD_center)) k]
      exact hα
    have hcard : Nat.card (GLAPPrimeCoreOf 3 (innerAut titsD ⊓
        Subgroup.centralizer ({MulAut.conj k} : Set (MulAut titsD)))) =
        Nat.card (GLAPPrimeCoreOf 3 (Subgroup.centralizer ({k} : Set titsD))) := by
      rw [CFSG.innerAut_inf_centralizer_conj
          (CFSG.Sporadic.Schreier.Tits.titsD_center) k,
        CFSG.card_gLAPPrimeCoreOf_map_of_injective 3 _
          (CFSG.mulAutConj_injective_of_center_eq_bot
            (CFSG.Sporadic.Schreier.Tits.titsD_center))]
    rw [hcard, CFSG.gLAPPrimeCoreOf_eq_bot_iff_pPrimeCore.mpr
      (pPrimeCore_three_centralizer_titsD hk3), Subgroup.card_bot]
    exact odd_one

end Certificates

theorem oddCoreFact_three_of_tits
    {S : Type} [Group S] [Finite S]
    (hv : (TauCeti.LieTypeIndex.tits).Valid)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group) :
    OddCoreFact 3 S := by
  obtain ⟨eT⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv S 2 1
    (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits (S := S) ⟨hv, ⟨e⟩⟩)
  exact (oddCoreFact_congr (p := 3) eT).mpr oddCoreFact_three_titsD

end CFSG.LocalAnalysis.GLTheoremA.KD1912
