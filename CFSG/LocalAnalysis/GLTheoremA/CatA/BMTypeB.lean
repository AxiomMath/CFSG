module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMTypeGen
public import CFSG.HardMathSupport.Solomon.Coordinator.B3B.Assembly
import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMNum
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Shape
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMInvBData

public section

namespace CFSG.LocalAnalysis.GLTheoremA.BMType

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.Blueprint
open CFSG.Monster.GMS CFSG.Monster.Existence CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Dickson.Sec6.BM CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.B3B
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem glaPComponent_conj_type {X : Type} [Group X] [Finite X] {s : X} (c : X)
    {P : TauCeti.CFSGIndex → Prop} {J : Subgroup X}
    (hJ : GLAPComponent 3 (Subgroup.centralizer ({s} : Set X)) J)
    (hT : catalogIs (PSimple 3 J) P) :
    GLAPComponent 3 (Subgroup.centralizer ({MulAut.conj c s} : Set X))
        (J.map (MulAut.conj c).toMonoidHom) ∧
      catalogIs (PSimple 3 (J.map (MulAut.conj c).toMonoidHom)) P := by
  refine ⟨?_, ?_⟩
  · have h := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv Nat.prime_three
      (MulAut.conj c) hJ
    rwa [bmInv_map_centralizer_singleton] at h
  · exact catalogIs_of_mulEquiv
      (CFSG.HardMathSupport.Dickson.I271.pSimpleEquiv 3
        (J.equivMapOfInjective _ (MulAut.conj c).injective)).symm hT


set_option maxRecDepth 100000 in
theorem false_of_type_B {P : TauCeti.CFSGIndex → Prop} {n : ℕ} (hP : TypeHyp P n)
    {s : NativeSporadic.B} (hs : orderOf s = 3) {J : Subgroup NativeSporadic.B}
    (hJ : GLAPComponent 3 (Subgroup.centralizer ({s} : Set NativeSporadic.B)) J)
    (hT : catalogIs (PSimple 3 J) P) : False := by
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  have hG : Nat.card NativeSporadic.B = 4154781481226426191177580544000000 := by
    rw [card_nativeB, monsterBabyOrder_eq_numeral]
  have hO3 : OPrimeCoreTrivialAt 3 NativeSporadic.B := BThreeFi23.oPrimeCoreTrivialAt_B_three
  by_cases hinv : ∃ d : NativeSporadic.B, BabyInv 0 d ∧ d * s * d⁻¹ = s⁻¹
  · obtain ⟨d, hd, hdinv⟩ := hinv
    obtain ⟨H, hH, -, hcard, hHd, hHs, hHn, hCQ⟩ := B_inverted_data hs hd hdinv
    have hdd : d * d = 1 := by
      have := pow_orderOf_eq_one d
      rwa [hd.1, sq] at this
    have hO := hO3 s hs
    have key := @false_of_inverted_type NativeSporadic.B _ _ P n hP s d hdd hdinv hO
    refine key hH hHd hHs hHn hCQ ?_ ?_ hJ hT
    · intro k hk
      rw [hG] at hk
      rw [hcard]
      exact not_dvd_factorial_of_bound (K := 7) hP.big (by norm_num) (by decide) hk
    · rw [hcard]
      norm_num
  · have hunv : ∀ d : NativeSporadic.B, BabyInv 0 d → d * s * d⁻¹ ≠ s⁻¹ :=
      fun d hd h => hinv ⟨d, hd, h⟩
    obtain ⟨z, hz3, hzrk, hmain⟩ := exists_z_components_dvd
    have hzc : IsConj z (phiB (t3 1)) := isConj_phiB_t3_one_of_rk hz3 hzrk
    have hnot0 : ¬ IsConj s (phiB (t3 0)) := by
      intro hc
      obtain ⟨d, hd, hdr⟩ := phiB_t3_zero_inverted
      obtain ⟨c, hcx⟩ := isConj_iff.1 hc
      refine hunv (c⁻¹ * d * c) (CFSG.Monster.GMS.BabyInv.of_isConj hd
        (isConj_iff.2 ⟨c⁻¹, by simp⟩)) ?_
      have hx' : s = c⁻¹ * phiB (t3 0) * c := by rw [← hcx]; group
      calc c⁻¹ * d * c * s * (c⁻¹ * d * c)⁻¹
          = c⁻¹ * (d * phiB (t3 0) * d⁻¹) * c := by rw [hx']; group
        _ = s⁻¹ := by rw [hdr, hx']; group
    have hsc : IsConj s (phiB (t3 1)) := by
      obtain ⟨i, hi⟩ := bThree_classes s hs
      fin_cases i
      · exact absurd hi hnot0
      · exact hi
      · exact absurd (hi.trans bThreeRc_holds) hnot0
      · exact hi.trans bThreeRd_holds
    obtain ⟨c, hc⟩ := isConj_iff.1 (hsc.trans hzc.symm)
    obtain ⟨hJ', hT'⟩ := glaPComponent_conj_type c hJ hT
    rw [MulAut.conj_apply, hc] at hJ'
    have hOz := hO3 z hz3
    obtain ⟨hcomp, -, hidx, -, -⟩ := comp_data_of_type hP hOz hJ' hT'
    have h8 := hmain _ hcomp (by rw [hidx]; exact hP.nine)
    exact not_pow_six_dvd_card_mulAut hP hOz hJ' hT'
      ((pow_dvd_pow 3 (by norm_num : 6 ≤ 8)).trans h8)

end CFSG.LocalAnalysis.GLTheoremA.BMType

end
