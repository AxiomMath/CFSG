module

public import CFSG.LocalAnalysis.GL83PartI.I713.Basic
public import CFSG.LocalAnalysis.GL83PartI.I713.UnitaryDiag
public import CFSG.Open.StatedDefs
import CFSG.ClassicalGroups.UnitaryFlag.GroupData
import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.Quasithin.SteinbergUnitaryOuterPrimeControl
import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
import CFSG.LieType.BorelTits.CompleteFlag
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.Walter.Defs
import Certificates.Certificate1
import Certificates.Certificate2

public section

namespace GL83.I713

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

theorem outClauseFor_classical_PSU {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnonab : ∃ a b : S, a * b ≠ b * a) {n p f : ℕ}
    (h : CFSG.Open.StatedClassicalModel S .PSU n p f) : OutClauseFor S := by
  obtain ⟨⟨hp, hf, hn, hq⟩, K, _, _, hK, ⟨eT⟩⟩ := h
  have hU : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq' : ¬ (n = 3 ∧ p ^ f = 2) := fun ⟨h1, h2⟩ => hq (by rw [h1, h2])
  intro ℓ hℓ hℓ2 hSℓ
  by_cases hdvd : ℓ ∣ Nat.gcd n (p ^ f + 1)
  · exfalso
    obtain ⟨hℓn, hℓq⟩ := Nat.dvd_gcd_iff.1 hdvd
    have h2 := two_le_pRank_statedPSU_of_dvd hK hℓ hℓ2 hn hℓn hℓq
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hℓ.one_lt eT] at h2
    omega
  · have : Group.IsPerfect S := by
      rw [Group.isPerfect_def]
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with hc | hc
      · exfalso
        obtain ⟨a, b, hab⟩ := hnonab
        refine hab ?_
        have hmem : ⁅a, b⁆ ∈ commutator S :=
          Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
        rwa [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      · exact hc
    let e : S ⧸ Subgroup.center S ≃* unitaryPSU hU n :=
      (QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_simple hnonab)).trans
        (QuotientGroup.quotientBot.trans
          (eT.trans (unitaryPSUEquiv hU (by omega)).symm))
    have hout := (CFSG.Quasithin.OuterPrimeControl.perfect_unitary_central_quotient_outer_prime_control
      hU hn hq' S e).2.1 ℓ hℓ hdvd
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact hout.2

end GL83.I713
