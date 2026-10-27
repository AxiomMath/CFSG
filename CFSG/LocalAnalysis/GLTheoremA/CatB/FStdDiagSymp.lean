module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.FStdDiagDefs
import CFSG.LocalAnalysis.GLTheoremA.CatB.FStdDiagSympModels
import CFSG.LocalAnalysis.GLTheoremA.CatB.FStdDiagSympTrans
import CFSG.LocalAnalysis.GLTheoremA.CatB.FStdDiagSympB2
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSL
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSU
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSp
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Glue
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GCenterQuot

public section

namespace CFSG.LocalAnalysis.GLTheoremA.FStdDiag

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (InnDiagKind)
open CFSG.LocalAnalysis.GLTheoremA.HStdExcl (SmallOrd)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

theorem fstdSymp_bc
    {S : Type} [Group S] [Finite S] {labK : GLALabel}
    {α : MulAut S} {I : Subgroup S} (hcen : Subgroup.center S = ⊥)
    (hFam : labK.tag = .B ∨ labK.tag = .C) (hα3 : α ^ 3 = 1) (hin : InnDiagKind S labK α)
    (hI : CFSG.Open.IsComponentOf I (fixSubgroup α)) (hord : SmallOrd I) : SmallConcl I := by
  obtain ⟨K, _, _, n, m, x, e, hn, hK, hm, hmn, hx, hMEq⟩ :=
    fstdSymp_transport hcen hFam hα3 hin
  have hne : ¬(m = 2 ∧ 2 ^ n = 2) := fun h =>
    hmn ⟨h.1, Nat.pow_right_injective le_rfl (h.2.trans (pow_one 2).symm)⟩
  have hI' : CFSG.Open.IsComponentOf (I.map e.toMonoidHom)
      (fixSubgroup (MulAut.conj (proj m K x))) := by
    have h1 : CFSG.Open.IsComponentOf (I.map e.toMonoidHom)
        ((fixSubgroup α).map e.toMonoidHom) :=
      CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e hI
    rwa [CFSG.LocalAnalysis.GLTheoremA.Y10F.fixSubgroup_map_congr, hMEq] at h1
  obtain ⟨-, hcomps⟩ := lieCompsCore_conj_sp_card (a6 := False) slFactorFacts_holds
    suFactorFacts_holds spFactorFacts_holds spFourTwoFacts_holds (fun h => h.elim)
    (fun h => h.elim) (fun h => h.elim) Nat.prime_three (by decide) Nat.prime_two hn hK
    (by omega) (by decide) (fun h => h.elim) x hx
  obtain ⟨X, _, _, ⟨hXL, -⟩, hfac, g', hg', hker'⟩ := hcomps _ hI'
  let eI : ↥(I.map e.toMonoidHom) ≃* ↥I := (I.equivMapOfInjective e.toMonoidHom e.injective).symm
  let g : X →* ↥I := eI.toMonoidHom.comp g'
  have hg : Function.Surjective g := eI.surjective.comp hg'
  have hker : g.ker ≤ Subgroup.center X := by
    intro y hy
    apply hker'
    rw [MonoidHom.mem_ker] at hy ⊢
    apply eI.injective
    rw [map_one]
    exact hy
  have hQ := fstdSymp_quot_equiv hXL.perfect g hg hker
  unfold SpFactorOver at hfac
  rcases hfac with ⟨b, j, E, _, _, hb2, hj, -, hcard, hb4, ⟨eX⟩⟩ |
    ⟨b, j, q', E, _, _, hb3, hj, -, hq', hcard, hbq, ⟨eX⟩⟩ | ⟨-, -, s, hs2, hne', ⟨eX⟩⟩ |
    ⟨-, -, hK2, ⟨eX⟩⟩
  ·
    have hE : Nat.card E = 2 ^ (n * j) := by
      rw [Nat.card_eq_fintype_card, hcard, hK, pow_mul]
    exact (fstdSymp_sl_false hord hQ hb2 (Nat.mul_pos hn hj) hE
      (fun h => by rw [Nat.card_eq_fintype_card]; exact hb4 h) eX).elim
  ·
    have hq'' : q' = 2 ^ (n * j) := by rw [hq', hK, pow_mul]
    subst hq''
    have hE : Nat.card E = (2 ^ (n * j)) ^ 2 := by rw [Nat.card_eq_fintype_card, hcard]
    obtain ⟨-, -, hc, hZ⟩ := fstdSymp_su_case hord hQ hb3 (Nat.mul_pos hn hj) hbq hE eX
    refine ⟨?_, fun h360 => ?_⟩
    · rw [← map_center_of_surjective hXL.perfect g hg hker, hZ, Subgroup.map_bot]
    · rw [hc] at h360
      omega
  ·
    exact (fstdSymp_sp_false hord hQ hs2 hn hK (fun h => hne' (by rw [h.1, h.2])) eX).elim
  ·
    obtain ⟨hZ, ⟨eA⟩⟩ := fstdSymp_a6_case hXL.perfect g hg hker hK2 eX
    refine ⟨hZ, fun _ => ⟨⊤, le_top, ?_, ?_⟩⟩
    · have hne2 : ¬(m = 2 ∧ Nat.card K = 2) := fun h =>
        hmn ⟨h.1, Nat.pow_right_injective le_rfl ((hK.symm.trans h.2).trans (pow_one 2).symm)⟩
      haveI : IsSimpleGroup (StatedProj (StatedSp m K)) :=
        (CFSG.RankThree.PartOne.KCSpComm.simple_perfect_statedProj hm hne2).1
      haveI : IsSimpleGroup S := e.isSimpleGroup
      exact Subgroup.topEquiv.isSimpleGroup
    · refine fstdSymp_threeFree_top e ?_
      have hLC := lieCompExport_conj_sp slFactorFacts_holds slAltSixFacts_holds
        suFactorFacts_holds suAltSixFacts_holds spFactorFacts_holds spAltSixFacts_holds
        spFourTwoFacts_holds Nat.prime_two hn hK hm hne (by decide) x hx
      obtain ⟨eC⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_of_mulEquiv
        (I.equivMapOfInjective e.toMonoidHom e.injective)
      exact hLC.a6 ⟨I.map e.toMonoidHom, hI', ⟨eC.symm.trans eA⟩⟩

theorem smallFam_symp :
    SmallFam CFSG.LocalAnalysis.GLTheoremA.Y10GField.FamSymp := by
  intro S _ _ labK α I hFam hcen hα3 hα1 hin hI hord
  rcases hFam with htag | htag | htag
  · exact fstdSymp_bc hcen (Or.inl htag) hα3 hin hI hord
  · exact fstdSymp_bc hcen (Or.inr htag) hα3 hin hI hord
  · exact (fstdSymp_b2der_false htag hcen hα1 hin hI hord).elim

end CFSG.LocalAnalysis.GLTheoremA.FStdDiag

end
