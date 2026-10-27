module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10PkK
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.Goldschmidt.BasicG
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Lemma32
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Conj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Standard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesCplxConj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmegaConj
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import CFSG.Walter.Bender1970.S3.Setup
public import CFSG.Walter.JRFacts
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.ClassicalInvolution.Q3.TA3.Check

local notation "P45" => Equiv.Perm (Fin 45)

local notation "SL23" => Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

namespace Pk

theorem mem_E_iff {x : P45} :
    x ∈ KA ⊔ KB ↔ ∃ A B : SL23, rhoF A * Certificates.OmegaPk.cj gz (rhoF B) = x := by
  rw [mem_sup_KAB]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    obtain ⟨A, rfl⟩ := mem_KA.1 ha
    obtain ⟨B, rfl⟩ := mem_KB.1 hb
    exact ⟨A, B, rfl⟩
  · rintro ⟨A, B, rfl⟩
    exact ⟨_, mem_KA.2 ⟨A, rfl⟩, _, mem_KB.2 ⟨B, rfl⟩, rfl⟩

theorem E_le :
    KA ⊔ KB ≤ Cs := sup_le KA_le KB_le

theorem pow_nine_of_odd {x : P45}
    (hx : x ∈ Cs) (ho : Odd (orderOf x)) : x ^ 9 = 1 := by
  have h1 : orderOf x ∣ 2 ^ 6 * 9 := by
    have := Subgroup.orderOf_dvd_natCard Cs hx
    rwa [card_Cs, show (576 : ℕ) = 2 ^ 6 * 9 by norm_num] at this
  have hcop : Nat.Coprime (orderOf x) (2 ^ 6) :=
    Nat.Coprime.pow_right 6 (Nat.coprime_two_right.2 ho)
  exact orderOf_dvd_iff_pow_eq_one.1 (hcop.dvd_of_dvd_mul_left h1)

theorem odd_mem_E {x : P45}
    (hx : x ∈ Cs) (ho : Odd (orderOf x)) : x ∈ KA ⊔ KB := by
  obtain ⟨A, B, hAB⟩ := facts.e.1 x hx (pow_nine_of_odd hx ho)
  exact mem_E_iff.2 ⟨A, B, hAB⟩

theorem relIndex_E :
    (KA ⊔ KB).relIndex Cs = 2 := by
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨gz, gz_mem, fun b hb => ?_⟩
  have h := facts.e.2.2 b hb
  rw [← mem_E_iff, ← mem_E_iff] at h
  by_cases h1 : b ∈ KA ⊔ KB
  · exact Or.inr ⟨h1, h.1 h1⟩
  · exact Or.inl ⟨by_contra fun h2 => h1 (h.2 h2), h1⟩

theorem normal_E :
    ((KA ⊔ KB).subgroupOf Cs).Normal :=
  Subgroup.normal_of_index_eq_two relIndex_E

theorem conj_E {l c : P45}
    (hl : l ∈ KA ⊔ KB) (hc : c ∈ Cs) : c * l * c⁻¹ ∈ KA ⊔ KB :=
  normal_E.conj_mem (⟨l, E_le hl⟩ : ↥Cs) hl ⟨c, hc⟩

theorem conj_KA_E {h l : P45} (hh : h ∈ KA) (hl : l ∈ KA ⊔ KB) :
    l * h * l⁻¹ ∈ KA := by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_KAB.1 hl
  have e : a * b * h * (a * b)⁻¹ = a * h * a⁻¹ := by
    rw [show a * b * h * (a * b)⁻¹ = a * (b * h) * (b⁻¹ * a⁻¹) by group, ← comm_KAB hh hb]
    group
  rw [e]
  exact KA.mul_mem (KA.mul_mem ha hh) (KA.inv_mem ha)

theorem subnormal_KA :
    (KA.subgroupOf Cs).IsSubnormal :=
  isSubnormal_subgroupOf_of_two_step le_sup_left (fun _ hh _ hl => conj_KA_E hh hl)
    (fun _ hl _ hc => conj_E hl hc)

theorem sl23Pocket_KA :
    Sl23PocketIn P0 tA KA :=
  ⟨tA_mem_KA, KA_le, subnormal_KA, isSL23Mod_KA⟩

theorem conjugate_self_of_mem {G : Type} [Group G] {H : Subgroup G} {g : G} (hg : g ∈ H) :
    CFSG.conjugate H g = H := by
  ext x
  rw [mem_conjugate_iff']
  refine ⟨fun h => ?_, fun h => H.mul_mem (H.mul_mem hg h) (H.inv_mem hg)⟩
  have h2 := H.mul_mem (H.mul_mem (H.inv_mem hg) h) hg
  rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h2

theorem sl23Pocket_KB :
    Sl23PocketIn P0 tA KB := by
  have h := sl23Pocket_KA.conjugate gz
  have hc : Commute gz tA := gz_comm
  rw [conjugate_self_of_mem (Subgroup.mem_inf.1 gz_mem).1,
    show gz⁻¹ * tA * gz = tA by rw [hc.inv_left.eq]; exact inv_mul_cancel_right tA gz] at h
  exact h

end Pk

end CFSG.OddStandard.SmallF3.Omega
