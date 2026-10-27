module

import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMNum
public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMTypeGen3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMTypeRows

public section

namespace CFSG.LocalAnalysis.GLTheoremA.BMType

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Monster.Generated CFSG.Monster.Existence CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.AGLEmbedding.Norton.MON5_7


theorem false_of_type3_griess_inverted {P : TauCeti.CFSGIndex → Prop} {n : ℕ}
    (hP : TypeHyp3 P n)
    (q23 : ℕ) (h23 : q23.Prime) (h23F : q23 ∣ 4089470473293004800) (h23n : ¬ q23 ∣ n)
    (qTh : ℕ) (hTh : qTh.Prime) (hThF : qTh ∣ 90745943887872000) (hThn : ¬ qTh ∣ n)
    {G : Type} [Group G] (hE : MonsterExistenceStatement G) {s : G} (hs : orderOf s = 3)
    (hinv : InvertedByTwoA s) {J : Subgroup G}
    (hJ : GLAPComponent 3 (Subgroup.centralizer ({s} : Set G)) J)
    (hT : catalogIs (PSimple 3 J) P) : False := by
  haveI : Finite G := hE.1.1
  have hO := gLAPPrimeCoreOf_eq_bot_of_invertedByTwoA hE Nat.prime_three (by norm_num) hs hinv
  obtain ⟨α, H, hα, hαs, hH, -, hcard, hHα, hHs, hHn, hCQ⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.BM.M_inverted_data hE hs hinv
  have hG : Nat.card G = 808017424794512875886459904961710757005754368000000000 := by
    have := hE.1.2.2.2
    rw [CFSG.HardMathSupport.Dickson.Sec6.BM.monsterOrder_eq_numeral] at this
    exact this
  have key := @false_of_inverted_type3_prime G _ _ P n hP s α hα hαs hO
  have hbig : ∀ k : ℕ, n ^ k ≤ Nat.card G → ¬ Nat.card ↥H ∣ k.factorial := by
    intro k hk
    rw [hG] at hk
    rcases hcard with hc | hc <;> rw [hc] <;>
      exact not_dvd_factorial_of_bound (K := 12) hP.big (by norm_num) (by decide) hk
  rcases hcard with hc | hc
  · exact key hH hHα hHs hHn hCQ hbig h23 (by rw [hc]; exact h23F) h23n hJ hT
  · exact key hH hHα hHs hHn hCQ hbig hTh (by rw [hc]; exact hThF) hThn hJ hT


set_option maxRecDepth 100000 in
theorem false_of_type3_gmat {P : TauCeti.CFSGIndex → Prop} {n : ℕ} (hP : TypeHyp3 P n)
    (q23 : ℕ) (h23 : q23.Prime) (h23F : q23 ∣ 4089470473293004800) (h23n : ¬ q23 ∣ n)
    (qTh : ℕ) (hTh : qTh.Prime) (hThF : qTh ∣ 90745943887872000) (hThn : ¬ qTh ∣ n)
    {s : Gmat} (hs : orderOf s = 3) {J : Subgroup Gmat}
    (hJ : GLAPComponent 3 (Subgroup.centralizer ({s} : Set Gmat)) J)
    (hT : catalogIs (PSimple 3 J) P) : False := by
  haveI : Finite Gmat := ThreeBNF.finite_Gmat
  by_cases hinv : InvertedByTwoA s
  · have hE := CFSG.Milestones.cl_lit_monster_existence_griess_conway
    haveI : Finite MGriess := hE.1.1
    let φ : Gmat ≃* MGriess :=
      (CFSG.YGroups.Y443.griessEquivGmat CFSG.YGroups.Y443.Gmat_eq_AutO_of_stroth).symm
    have hs' : orderOf (φ s) = 3 := by rwa [MulEquiv.orderOf_eq]
    obtain ⟨hJ', hT'⟩ := glaPComponent_map_type φ hJ hT
    exact false_of_type3_griess_inverted hP q23 h23 h23F h23n qTh hTh hThF hThn hE hs'
      (hinv.map φ) hJ' hT'
  · have hOu : UninvertedOPrimeTrivial 3 Gmat :=
      uninvertedOPrimeTrivial_gmat_of_twoAPureKlein Nat.prime_three (by norm_num)
        BThreeFi23.oPrimeCoreTrivialAt_B_three ThreeBNF.twoAPureKlein_three_Gmat
    have hsc : IsConj s tbw := CFSG.HardMathSupport.Dickson.Sec6.BM2.m3bClass_holds s hs hinv
    obtain ⟨c, hc⟩ := isConj_iff.1 hsc
    obtain ⟨hJ', hT'⟩ := glaPComponent_conj_type c hJ hT
    rw [MulAut.conj_apply, hc] at hJ'
    have hw3 : orderOf tbw = 3 := by rw [← hc, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hs]
    have hwinv : ¬ InvertedByTwoA tbw := by
      intro hw
      apply hinv
      have h := hw.map (MulAut.conj c⁻¹)
      rwa [MulAut.conj_apply, ← hc, show c⁻¹ * (c * s * c⁻¹) * c⁻¹⁻¹ = s by group] at h
    have hOw := hOu tbw hw3 hwinv
    obtain ⟨hcomp, -, hidx, -, -⟩ := comp_data_of_type3 hP hOw hJ' hT'
    have hC : Subgroup.centralizer ((Subgroup.zpowers tbw : Subgroup Gmat) : Set Gmat) =
        Subgroup.centralizer ({tbw} : Set Gmat) := by
      rw [Subgroup.zpowers_eq_closure]
      exact Subgroup.centralizer_closure {tbw}
    rw [← hC] at hcomp
    have h12 := CFSG.HardMathSupport.MathTwE6.M3BIrr.components_dvd_card_mulAut_of_certificates _
      hcomp (by rw [hidx]; exact hP.nine)
    exact not_pow_eight_dvd_card_mulAut3 hP hOw hJ' hT'
      ((pow_dvd_pow 3 (by norm_num : 8 ≤ 12)).trans h12)


theorem typeRow3_M {P : TauCeti.CFSGIndex → Prop} {n : ℕ} (hP : TypeHyp3 P n)
    (q23 : ℕ) (h23 : q23.Prime) (h23F : q23 ∣ 4089470473293004800) (h23n : ¬ q23 ∣ n)
    (qTh : ℕ) (hTh : qTh.Prime) (hThF : qTh ∣ 90745943887872000) (hThn : ¬ qTh ∣ n) :
    TypeRow P .M := by
  obtain ⟨-, hs, hfin⟩ := CFSG.Monster.Generated.generated_rational_group_finite_simple
  obtain ⟨b⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_gmat_tauCeti
  have hnc : ∃ a c : CFSG.Monster.Generated.Gmat, a * c ≠ c * a :=
    CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by
      rw [CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder, CFSG.Open.monsterOrder]
      norm_num)
  exact @typeRow_of_model P .M CFSG.Monster.Generated.Gmat _ hfin hs
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds b hnc
    fun k hk J hJ hT =>
      false_of_type3_gmat hP q23 h23 h23F h23n qTh hTh hThF hThn (s := k) hk hJ hT

end CFSG.LocalAnalysis.GLTheoremA.BMType

end
