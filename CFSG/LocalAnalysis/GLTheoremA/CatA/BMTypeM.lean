module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMTypeB
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMInvMData
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BM2Census
public import CFSG.HardMathSupport.MathTwE6.MonsterThreeBComponents
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterKleinFrontier
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBFinal
import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMNum

public section

namespace CFSG.LocalAnalysis.GLTheoremA.BMType

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Monster.Generated CFSG.Monster.Existence CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.AGLEmbedding.Norton.MON5_7

theorem glaPComponent_map_type {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (φ : X ≃* Y) {s : X} {P : TauCeti.CFSGIndex → Prop} {J : Subgroup X}
    (hJ : GLAPComponent 3 (Subgroup.centralizer ({s} : Set X)) J)
    (hT : catalogIs (PSimple 3 J) P) :
    GLAPComponent 3 (Subgroup.centralizer ({φ s} : Set Y)) (J.map φ.toMonoidHom) ∧
      catalogIs (PSimple 3 (J.map φ.toMonoidHom)) P := by
  refine ⟨?_, ?_⟩
  · have h := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv Nat.prime_three φ hJ
    rwa [bmInv_map_centralizer_singleton] at h
  · exact catalogIs_of_mulEquiv
      (CFSG.HardMathSupport.Dickson.I271.pSimpleEquiv 3
        (J.equivMapOfInjective _ φ.injective)).symm hT


theorem false_of_type_griess_inverted {P : TauCeti.CFSGIndex → Prop} {n : ℕ} (hP : TypeHyp P n)
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
  have key := @false_of_inverted_type G _ _ P n hP s α hα hαs hO
  refine key hH hHα hHs hHn hCQ ?_ ?_ hJ hT
  · intro k hk
    rw [hG] at hk
    rcases hcard with hc | hc <;> rw [hc] <;>
      exact not_dvd_factorial_of_bound (K := 12) hP.big (by norm_num) (by decide) hk
  · rcases hcard with hc | hc <;> rw [hc] <;> norm_num

set_option maxRecDepth 100000 in
theorem false_of_type_gmat {P : TauCeti.CFSGIndex → Prop} {n : ℕ} (hP : TypeHyp P n)
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
    exact false_of_type_griess_inverted hP hE hs' (hinv.map φ) hJ' hT'
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
    obtain ⟨hcomp, -, hidx, -, -⟩ := comp_data_of_type hP hOw hJ' hT'
    have hC : Subgroup.centralizer ((Subgroup.zpowers tbw : Subgroup Gmat) : Set Gmat) =
        Subgroup.centralizer ({tbw} : Set Gmat) := by
      rw [Subgroup.zpowers_eq_closure]
      exact Subgroup.centralizer_closure {tbw}
    rw [← hC] at hcomp
    have h12 := CFSG.HardMathSupport.MathTwE6.M3BIrr.components_dvd_card_mulAut_of_certificates _
      hcomp (by rw [hidx]; exact hP.nine)
    exact not_pow_six_dvd_card_mulAut hP hOw hJ' hT'
      ((pow_dvd_pow 3 (by norm_num : 6 ≤ 12)).trans h12)

end CFSG.LocalAnalysis.GLTheoremA.BMType

end
