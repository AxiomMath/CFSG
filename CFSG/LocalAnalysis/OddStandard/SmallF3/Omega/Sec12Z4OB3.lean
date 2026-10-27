module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z4ODefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11Steps
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Main
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z4OComp
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z4OType
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z4OCyc
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z4OL29
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L123aX
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L121A
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L124Z4Pow

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82StepZ4Comp_of (hp : Asc82Pre11) (h63 : Asc82Lemma63) (hH : ∀ (G : Type) [Group G]
    [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L → Asc82Hyp62 G)
    (h65 : Asc82Lemma65) (h6p : AschOmega6Plus) (h6m : AschOmega6Minus) (h7 : AschOmega7)
    (h8p : AschOmega8Plus) (h8m : AschOmega8Minus) (h6z : AschOmega6MinusZ2) :
    Asc82StepZ4Comp := by
  intro G _ _ t L S z K1 K2 E hctx hZ s0 hs0 hs0S hs0L h64
  have hS : Sec3SettingLB G t L := hctx.toSec10Z.toSec10Setting.toSec3SettingLB
  have F : Sec12Frame t L S := sec12Frame_of hp hctx.toSec10Ctx hctx.alt1
  obtain ⟨hpsp, -, -, -, hSN, hsyl⟩ := hp.basic G t L S z hctx.toSec10Z
  have hBL : secB S L ≤ L := F.bdata.1
  have hBV : secB S L ≤ secV t S L E := sec121_B_le_V F hctx.sylowE
  have hVc := sec124_z4_comm hZ
  have hs0B : s0 ∈ normalizer (secB S L : Set G) := sec123_mem_normalizer_B F (F.hSM hs0S)
  obtain ⟨b, hbB, hcomm, hJ, hJ29⟩ :=
    hp.facts.outerI4m G L hpsp (S ⊓ L) hsyl s0 ⟨hSN hs0S, hs0B⟩ hs0 hs0L
  have hbB' : b ∈ secB S L := hbB
  have hs02 : s0 * s0 = 1 := by rw [← sq, ← hs0, pow_orderOf_eq_one]
  have hbb : b * b = 1 := sec12E_B_sq F hbB'
  have hss : (s0 * b) * (s0 * b) = 1 := by
    calc s0 * b * (s0 * b) = s0 * (b * s0) * b := by group
      _ = s0 * (s0 * b) * b := by rw [← hcomm]
      _ = (s0 * s0) * (b * b) := by group
      _ = 1 := by rw [hs02, hbb, mul_one]
  have hsK : s0 * b ∉ L ⊔ centralizer (L : Set G) := by
    intro h
    apply hs0L
    have e : s0 = (s0 * b) * b⁻¹ := by group
    rw [e]
    exact mul_mem h (mem_sup_left (inv_mem (hBL hbB')))
  have hs1 : s0 * b ≠ 1 := fun h => hsK (h ▸ one_mem _)
  have hsord : orderOf (s0 * b) = 2 := orderOf_eq_prime (by rw [sq]; exact hss) hs1
  have hsS : s0 * b ∈ S := mul_mem hs0S (secB_le_S S L hbB')
  have hts : t * (s0 * b) = (s0 * b) * t :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hctx.sylow.1 hsS)).symm
  have hCV : secV t S L E ⊓ centralizer ({s0 * b} : Set G) =
      secV t S L E ⊓ centralizer ({s0} : Set G) := by
    ext v
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    refine ⟨fun ⟨hv, h⟩ => ⟨hv, ?_⟩, fun ⟨hv, h⟩ => ⟨hv, ?_⟩⟩
    · have hvb : v * b = b * v := hVc v hv b (hBV hbB')
      have e : v * s0 * b = s0 * v * b := by
        calc v * s0 * b = v * (s0 * b) := by group
          _ = s0 * b * v := h
          _ = s0 * (b * v) := by group
          _ = s0 * (v * b) := by rw [hvb]
          _ = s0 * v * b := by group
      exact mul_right_cancel e
    · have hvb : v * b = b * v := hVc v hv b (hBV hbB')
      calc v * (s0 * b) = v * s0 * b := by group
        _ = s0 * v * b := by rw [h]
        _ = s0 * (v * b) := by group
        _ = s0 * (b * v) := by rw [hvb]
        _ = s0 * b * v := by group
  have h64' : Nat.card ↥(secV t S L E ⊓ centralizer ({s0 * b} : Set G)) = 2 ^ 6 := by
    rw [hCV]
    exact h64
  obtain ⟨I, hIC, hIF, hIN, hJI⟩ :=
    sec123_comp' hp.s3.l36 h63 (hH G t L hS) hS hsord hts hJ hJ29
  have hJ360 : ctrQ (layerCent L (s0 * b)) = 360 := ctrQ_of_l29 hJ.isQuasisimple hJ29
  have h360 : 360 ∣ ctrQ I := by
    rw [← hJ360]
    exact ctrQ_dvd_of_le hJI
  rcases sec123z4_type h6p h6m h7 h8p h8m h6z hS hsord hIC hIF h360 with h5 | h29 | h81
  · exact sec123z4_false_of_cyclic hp.facts.autAb hctx F hZ hsord hsS hsK h64' hIC hIN
      (Or.inl h5)
      (hp.s3.l33 G t L hS I (inCStar_of_isOmega5 h6p h6m h7 h8p h8m h6z hS hsord hIC hIF h5) hIF)
  · have hIeq : layerCent L (s0 * b) = I :=
      eq_of_le_of_ctrQ_eq hIC.isQuasisimple hJI
        (by rw [hJ360, ctrQ_of_l29 hIC.isQuasisimple h29])
    have hCB : ¬ secB S L ≤ centralizer ({s0 * b} : Set G) := by
      intro hle
      apply hsK
      have hmem := F.centB (s0 * b) (mul_mem (hSN hs0S) (Subgroup.le_normalizer (hBL hbB')))
        (fun b' hb' => (Subgroup.mem_centralizer_singleton_iff.mp (hle hb')).symm)
      exact (sup_le_sup_right hBL _) hmem
    exact sec123z4_false_of_l29 h65 (hH G t L hS) hctx F hZ hsord hsS hsK h64' hCB hJ29
      (by rw [hIeq]; exact hIC) (by rw [hIeq]; exact hIN)
  · exact sec123z4_false_of_cyclic hp.facts.autAb hctx F hZ hsord hsS hsK h64' hIC hIN
      (Or.inr h81)
      (hp.s3.l33 G t L hS I (inCStar_of_isL281 h8m hS ⟨s0 * b, hsord, hIC⟩ hIF h81) hIF)

end CFSG.OddStandard.SmallF3.Omega
