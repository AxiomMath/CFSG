module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430SporBMA6
import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMNum

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84.A6Spor

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Monster.Generated CFSG.Monster.Existence CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.AGLEmbedding.Norton.MON5_7


theorem false_of_isA6_griess_inverted {G : Type} [Group G] (hE : MonsterExistenceStatement G)
    {s : G} (hs : orderOf s = 3) (hinv : InvertedByTwoA s) {J : Subgroup G}
    (hJ : GLAPComponent 3 (Subgroup.centralizer ({s} : Set G)) J)
    (hT : catalogIs (PSimple 3 J) S8.isA6) : False := by
  haveI : Finite G := hE.1.1
  have hO := gLAPPrimeCoreOf_eq_bot_of_invertedByTwoA hE Nat.prime_three (by norm_num) hs hinv
  obtain ⟨α, H, hα, hαs, hH, -, hcard, hHα, hHs, hHn, hCQ⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.BM.M_inverted_data hE hs hinv
  have hG : Nat.card G = 808017424794512875886459904961710757005754368000000000 := by
    have := hE.1.2.2.2
    rw [CFSG.HardMathSupport.Dickson.Sec6.BM.monsterOrder_eq_numeral] at this
    exact this
  have key := @false_of_inverted_isA6 G _ _ s α hα hαs hO
  have hbig : ∀ p : ℕ, p.Prime → 21 < p → p ∣ Nat.card ↥H →
      ∀ k : ℕ, 360 ^ k ≤ Nat.card G → ¬ Nat.card ↥H ∣ k.factorial := by
    intro p hp hp21 hpH k hk hdvd
    rw [hG] at hk
    have hkK : k ≤ 21 := le_of_three_sixty_pow_le (by norm_num) hk
    have hpk := hp.dvd_factorial.1 (hpH.trans hdvd)
    omega
  rcases hcard with hc | hc
  · have h23 : 23 ∣ Nat.card ↥H := by rw [hc]; norm_num
    exact key hH hHα hHs hHn hCQ (hbig 23 (by norm_num) (by norm_num) h23) (q := 23)
      (by norm_num) h23 (by norm_num) (by norm_num) hJ hT
  · have h31 : 31 ∣ Nat.card ↥H := by rw [hc]; norm_num
    exact key hH hHα hHs hHn hCQ (hbig 31 (by norm_num) (by norm_num) h31) (q := 31)
      (by norm_num) h31 (by norm_num) (by norm_num) hJ hT


theorem false_of_isA6_gmat {s : Gmat} (hs : orderOf s = 3) {J : Subgroup Gmat}
    (hJ : GLAPComponent 3 (Subgroup.centralizer ({s} : Set Gmat)) J)
    (hT : catalogIs (PSimple 3 J) S8.isA6) : False := by
  haveI : Finite Gmat := ThreeBNF.finite_Gmat
  by_cases hinv : InvertedByTwoA s
  · have hE := CFSG.Milestones.cl_lit_monster_existence_griess_conway
    haveI : Finite MGriess := hE.1.1
    let φ : Gmat ≃* MGriess :=
      (CFSG.YGroups.Y443.griessEquivGmat CFSG.YGroups.Y443.Gmat_eq_AutO_of_stroth).symm
    have hs' : orderOf (φ s) = 3 := by rwa [MulEquiv.orderOf_eq]
    obtain ⟨hJ', hT'⟩ := BMType.glaPComponent_map_type φ hJ hT
    exact false_of_isA6_griess_inverted hE hs' (hinv.map φ) hJ' hT'
  · have hOu : UninvertedOPrimeTrivial 3 Gmat :=
      uninvertedOPrimeTrivial_gmat_of_twoAPureKlein Nat.prime_three (by norm_num)
        BThreeFi23.oPrimeCoreTrivialAt_B_three ThreeBNF.twoAPureKlein_three_Gmat
    have hsc : IsConj s tbw := CFSG.HardMathSupport.Dickson.Sec6.BM2.m3bClass_holds s hs hinv
    obtain ⟨c, hc⟩ := isConj_iff.1 hsc
    obtain ⟨hJ', hT'⟩ := BMType.glaPComponent_conj_type c hJ hT
    rw [MulAut.conj_apply, hc] at hJ'
    have hw3 : orderOf tbw = 3 := by rw [← hc, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hs]
    have hwinv : ¬ InvertedByTwoA tbw := by
      intro hw
      apply hinv
      have h := hw.map (MulAut.conj c⁻¹)
      rwa [MulAut.conj_apply, ← hc, show c⁻¹ * (c * s * c⁻¹) * c⁻¹⁻¹ = s by group] at h
    have hOw := hOu tbw hw3 hwinv
    obtain ⟨hcomp, -, hidx, -, -⟩ := comp_data_of_isA6 hOw hJ' hT'
    have hC : Subgroup.centralizer ((Subgroup.zpowers tbw : Subgroup Gmat) : Set Gmat) =
        Subgroup.centralizer ({tbw} : Set Gmat) := by
      rw [Subgroup.zpowers_eq_closure]
      exact Subgroup.centralizer_closure {tbw}
    rw [← hC] at hcomp
    have h12 := CFSG.HardMathSupport.MathTwE6.M3BIrr.components_dvd_card_mulAut_of_certificates _
      hcomp (by rw [hidx]; norm_num)
    exact not_pow_eight_dvd_card_mulAut_of_isA6 hOw hJ' hT'
      ((pow_dvd_pow 3 (by norm_num : 8 ≤ 12)).trans h12)


theorem typeRow_isA6_M : BMType.TypeRow S8.isA6 .M := by
  obtain ⟨-, hs, hfin⟩ := CFSG.Monster.Generated.generated_rational_group_finite_simple
  obtain ⟨b⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_gmat_tauCeti
  have hnc : ∃ a c : CFSG.Monster.Generated.Gmat, a * c ≠ c * a :=
    CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by
      rw [CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder, CFSG.Open.monsterOrder]
      norm_num)
  exact @BMType.typeRow_of_model S8.isA6 .M CFSG.Monster.Generated.Gmat _ hfin hs
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds b hnc
    fun k hk J hJ hT => false_of_isA6_gmat (s := k) hk hJ hT

theorem a6Row_M : A6Row .M :=
  a6Row_of_typeRow typeRow_isA6_M

end CFSG.LocalAnalysis.GLTheoremA.S8.L84.A6Spor

end
