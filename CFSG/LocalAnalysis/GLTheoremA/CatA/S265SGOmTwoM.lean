module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGOmTwoP
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.LocalAnalysis.ComponentClassification.CatFC.ResidualA8Gen
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTM5
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTQuot
import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
import CFSG.LocalAnalysis.StandardType.MarkingClassical
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFOm8
import CFSG.Blueprint.LieModelAPI
import CFSG.GH74.GLS.Balance.SolvAPIDefs
import CFSG.LargeExtraspecial.OfFStar
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerCover
import CFSG.LocalAnalysis.GLTheoremA.PartI.I1412Levels
import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
import CFSG.Models.Transport
import CFSG.Open.SplitBNPair
import CFSG.Quasithin.Vol2.Ch10StatementsE
import CFSG.Quasithin.Vol2.Ch10StatementsInputs
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
import CFSG.RankThree.PartTwo.Sec11.Inverter1118Proof
import CFSG.RankThree.PartTwo.Sec11.Inverter1118ProofSteps
import CFSG.RankThree.PartTwo.Sec11.Item1121Proof
import CFSG.RankThree.PartTwo.Sec11.Item119K
import CFSG.RankThree.PartTwo.Sec14.Item142ResProofPGL
import CFSG.RankThree.PartTwo.Sec19.Step1914E
import CFSG.RankThree.PartTwo.Sec20.OneSteps
import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf
import CFSG.RankThree.PartTwo.Sec4.Item41NarrowGriess
import CFSG.Walter.J1Props
import Certificates.Certificate8166

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.StandardType CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.RankThree.PartTwo.Sec4

theorem SG.conclB_rMinus_two (K : Type) [Field K] [Finite K] (b c : K) (hK : Nat.card K = 2)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∀ X : Subgroup (OrthRest.RMinus K 3 b c), IsElemAbelian 3 X → Nat.card X = 3 ^ 3 →
      ∀ d ∈ X, d ≠ 1 → ∀ J : Subgroup (OrthRest.RMinus K 3 b c),
      IsComponentOf J (Subgroup.centralizer ({d} : Set (OrthRest.RMinus K 3 b c))) →
      catalogIs (J ⧸ Subgroup.center J) (tyF 3) →
      ∃ Y ≤ X, d ∈ Y ∧ Nat.card Y = 3 ^ 2 ∧ ∃ A : Subgroup (OrthRest.RMinus K 3 b c),
        A ≤ Subgroup.centralizer (Y : Set (OrthRest.RMinus K 3 b c)) ∧ IsSimpleGroup A ∧
        (∃ a b : A, a * b ≠ b * a) ∧ 3 ∣ Nat.card A := by
  intro X hX _ d hdX hd1 J hJ hcat
  exfalso
  obtain ⟨φ⟩ := CatB.exists_ringEquiv_zmod_two hK
  have hφ : φ b = 1 ∧ φ c = 1 := by
    have key : ∀ b' c' : ZMod 2, (∀ s : ZMod 2, s ^ 2 + b' * s + c' ≠ 0) → b' = 1 ∧ c' = 1 := by
      decide
    refine key _ _ fun s hs => hbc (φ.symm s) (φ.injective ?_)
    simp only [map_add, map_mul, map_pow, RingEquiv.apply_symm_apply, map_zero]
    exact hs
  obtain ⟨e⟩ : Nonempty (OrthRest.RMinus K 3 b c ≃* RonanK429F.Om8) :=
    ⟨(omegaMinusProjEquiv 4 b c).trans (CatB.statedProjEquivZMod2 φ
      (CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ fun v =>
        CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp φ hφ.1 hφ.2 v))⟩
  have hirr : ∀ s : GaloisField 2 1, s ^ 2 + 1 * s + 1 ≠ 0 := fun s => by
    rcases RonanK429F.gf2_eq_zero_or_one s with rfl | rfl
    · simp
    · rw [one_pow, one_mul, RonanK429F.gf2_one_add_one, zero_add]
      exact one_ne_zero
  have hJdvd : Nat.card (J ⧸ Subgroup.center J) ∣ 2 ^ 12 * 3 ^ 4 * 5 * 7 * 17 := by
    have h2 := Subgroup.card_subgroup_dvd_card J
    rw [Nat.card_congr e.toEquiv, RonanK429F.Om8.card_Om8 hirr] at h2
    exact (Subgroup.card_quotient_dvd_card _).trans h2
  obtain ⟨hN, h15⟩ := SG.tyF_three_of_dvd hcat hJdvd
  have h7 : 7 ∣ Nat.card (Subgroup.centralizer ({e d} : Set RonanK429F.Om8)) := by
    have hle : J.map (e : OrthRest.RMinus K 3 b c →* RonanK429F.Om8) ≤
        Subgroup.centralizer ({e d} : Set RonanK429F.Om8) := by
      rw [← HSubT.map_centralizer_singleton e d]
      exact Subgroup.map_mono hJ.1
    have h2 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective (f := (e : OrthRest.RMinus K 3 b c →* RonanK429F.Om8))
      e.injective] at h2
    exact ((by rw [hN]; norm_num : 7 ∣ Nat.card (J ⧸ Subgroup.center J)).trans
      (Subgroup.card_quotient_dvd_card _)).trans h2
  obtain ⟨x, hx⟩ := RonanK429F.exists_conj_commute_of_dvd (by norm_num)
    RonanK429F.Om8.orderOf_y7 (RonanK429F.Om8.not_sq_seven_dvd hirr) h7
  set ψ : OrthRest.RMinus K 3 b c ≃* RonanK429F.Om8 := e.trans (MulAut.conj x⁻¹) with hψ
  have hψd : ψ d = x⁻¹ * e d * x := by
    rw [hψ, MulEquiv.trans_apply, MulAut.conj_apply, inv_inv]
  have hT : RonanK429F.Om8.IsTForm (ψ d) := RonanK429F.Om8.isTForm_of
    (RonanK429F.Om8.t_form (by rw [hψd]; exact hx) (by rw [← map_pow, hX.2 d hdX, map_one])
      fun h => hd1 (ψ.injective (h.trans (map_one ψ).symm)))
  have hJ' : IsComponentOf (J.map (ψ : OrthRest.RMinus K 3 b c →* RonanK429F.Om8))
      (Subgroup.centralizer ({ψ d} : Set RonanK429F.Om8)) := by
    have h := HSubT.isComponentOf_map_mulEquiv hJ ψ
    rwa [HSubT.map_centralizer_singleton ψ d] at h
  have hJD : J.map (ψ : OrthRest.RMinus K 3 b c →* RonanK429F.Om8) ≤
      RonanK429F.Om8.psiD.range :=
    RonanK429F.le_of_commutator_mem (C := Subgroup.centralizer ({ψ d} : Set RonanK429F.Om8))
      (fun a ha b hb => RonanK429F.Om8.comm_mem_D hT ha hb) hJ'.1 ⟨hJ'.2.2.1⟩
  have hJc : Nat.card J = Nat.card (J ⧸ Subgroup.center J) * Nat.card (Subgroup.center J) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hJ'c : Nat.card (J.map (ψ : OrthRest.RMinus K 3 b c →* RonanK429F.Om8)) = Nat.card J :=
    Subgroup.card_map_of_injective ψ.injective
  have hle := Subgroup.card_le_of_le hJD
  have hZpos : 0 < Nat.card (Subgroup.center J) := Nat.card_pos
  rw [RonanK429F.Om8.card_D, hJ'c, hJc, hN] at hle
  have hZ1 : Nat.card (Subgroup.center J) = 1 := by omega
  have hJD' := Subgroup.eq_of_le_of_card_ge hJD
    (le_of_eq (by rw [RonanK429F.Om8.card_D, hJ'c, hJc, hN, hZ1]))
  set eZ : J ⧸ Subgroup.center J ≃* J :=
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.eq_bot_of_card_eq _ hZ1)).trans
      QuotientGroup.quotientBot
  set f : ↥(alternatingGroup (Fin 8)) ≃* J ⧸ Subgroup.center J :=
    RonanK429F.Om8.ED.symm.trans ((MulEquiv.subgroupCongr hJD').symm.trans
      ((J.equivMapOfInjective _ ψ.injective).symm.trans eZ.symm))
  obtain ⟨g, hg⟩ := CFSG.ComponentClassification.CatFC.ResidualA8.alt_eight_exists_order_fifteen
  exact h15 (f g) (by rw [MulEquiv.orderOf_eq]; exact hg)

end CFSG.LocalAnalysis.GLTheoremA.S265

end
