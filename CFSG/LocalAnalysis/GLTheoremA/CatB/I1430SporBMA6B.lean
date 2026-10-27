module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430SporBMA6
import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMNum

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84.A6Spor

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.Blueprint
open CFSG.Monster.GMS CFSG.Monster.Existence CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Dickson.Sec6.BM CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.B3B
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal
open CFSG.Blueprint.NativeSporadic (Carrier)

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem false_of_isA6_B {s : NativeSporadic.B} (hs : orderOf s = 3)
    {J : Subgroup NativeSporadic.B}
    (hJ : GLAPComponent 3 (Subgroup.centralizer ({s} : Set NativeSporadic.B)) J)
    (hT : catalogIs (PSimple 3 J) S8.isA6) : False := by
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
    have hbig : ∀ k : ℕ, 360 ^ k ≤ Nat.card NativeSporadic.B → ¬ Nat.card ↥H ∣ k.factorial := by
      intro k hk hdvd
      rw [hG] at hk
      rw [hcard] at hdvd
      have hkK : k ≤ 13 := le_of_three_sixty_pow_le (by norm_num) hk
      have h1 := Nat.le_of_dvd (Nat.factorial_pos k) hdvd
      have h2 : k.factorial ≤ (13 : ℕ).factorial := Nat.factorial_le hkK
      have h3 : (13 : ℕ).factorial < 64561751654400 := by decide
      omega
    have key := @false_of_inverted_isA6 NativeSporadic.B _ _ s d hdd hdinv (hO3 s hs)
    exact key hH hHd hHs hHn hCQ hbig (q := 11) (by norm_num) (by rw [hcard]; norm_num)
      (by norm_num) (by norm_num) hJ hT
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
    obtain ⟨hJ', hT'⟩ := BMType.glaPComponent_conj_type c hJ hT
    rw [MulAut.conj_apply, hc] at hJ'
    have hOz := hO3 z hz3
    obtain ⟨hcomp, -, hidx, -, -⟩ := comp_data_of_isA6 hOz hJ' hT'
    exact not_pow_eight_dvd_card_mulAut_of_isA6 hOz hJ' hT'
      (hmain _ hcomp (by rw [hidx]; norm_num))


theorem typeRow_isA6_B : BMType.TypeRow S8.isA6 .B := by
  obtain ⟨hfin, hs, ⟨b⟩, hnc⟩ := CFSG.HardMathSupport.Dickson.BMRows.model_B
  exact @BMType.typeRow_of_model S8.isA6 .B (Carrier .B) _ hfin hs
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds b hnc
    fun k hk J hJ hT => false_of_isA6_B (s := k) hk hJ hT

theorem a6Row_B : A6Row .B :=
  a6Row_of_typeRow typeRow_isA6_B

end CFSG.LocalAnalysis.GLTheoremA.S8.L84.A6Spor

end
