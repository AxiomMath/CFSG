module

public import CFSG.LieType.ChevTwo.Defs
public import CFSG.Open.FusionDefs
public import Certificates.Certificate43
import CFSG.Goldschmidt.Steps.G3aBorel
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutOmega
import CFSG.StronglyEmbedded.Catalog.Suzuki
import CFSG.Models.BenderSuzuki
import CFSG.StronglyEmbedded.MatrixGroups.SzModel
import CFSG.Goldschmidt.Statements
import CFSG.Goldschmidt.StatementsH
import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.Walter.Bender1970.S3.Setup
import CFSG.Walter.JRFacts
import Certificates.Certificate1
import Certificates.Certificate10
import Certificates.Certificate100
import Certificates.Certificate101
import Certificates.Certificate102
import Certificates.Certificate103
import Certificates.Certificate104
import Certificates.Certificate105
import Certificates.Certificate106
import Certificates.Certificate107
import Certificates.Certificate108
import Certificates.Certificate109
import Certificates.Certificate11
import Certificates.Certificate113
import Certificates.Certificate12
import Certificates.Certificate2
import Certificates.Certificate3
import Certificates.Certificate4
import Certificates.Certificate42
import Certificates.Certificate44
import Certificates.Certificate5
import Certificates.Certificate6
import Certificates.Certificate7
import Certificates.Certificate8
import Certificates.Certificate9
import Certificates.Certificate96
import Certificates.Certificate97
import Certificates.Certificate98
import Certificates.Certificate99

public section

namespace CFSG.LieType.ChevTwo

open CFSG.Open
open CFSG.ComponentClassification.AschbacherToolkit.Bender.Omega (eq_one_of_mem_of_mem
  eq_one_of_mem_normalizer exists_smul_eq mem_smul_iff mem_conj_smul_iff smul_conj_smul)
open scoped Pointwise

theorem oppositeFixed_of_stronglyEmbedded {X : Type} [Group X] [Finite X]
    (hX : ∀ T : Sylow 2 X,
      fusionStronglyEmbedded (Subgroup.normalizer ((T : Subgroup X) : Set X)) ∧
        Nat.card (Sylow 2 X) = Nat.card (T : Subgroup X) + 1) :
    OppositeFixed X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro p hp hp2 R hR Q hQ hQ2 _ _ hRQ hCQ
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨U, hQU⟩ := hQ2.exists_le_sylow
  have huniq : ∀ P : Sylow 2 X, Q ≤ P → P = U := by
    intro P hQP
    by_contra hPU
    obtain ⟨q, hq, hq1⟩ := (Subgroup.bot_or_exists_ne_one Q).resolve_left hQ
    exact hq1 (eq_one_of_mem_of_mem (hX U).1 hPU (hQU hq) (hQP hq))
  have hRU : ∀ α ∈ R, α • U = U := by
    intro α hα
    refine huniq _ fun q hq => ?_
    rw [mem_smul_iff]
    have hq' : α⁻¹ q ∈ Q.map (α⁻¹).toMonoidHom := Subgroup.mem_map_of_mem _ hq
    rw [hRQ _ (R.inv_mem hα)] at hq'
    exact hQU hq'
  have hNQ : Subgroup.normalizer (Q : Set X) ≤
      Subgroup.normalizer ((U : Subgroup X) : Set X) := by
    intro g hg
    refine Sylow.smul_eq_iff_mem_normalizer.mp (huniq _ fun q hq => ?_)
    rw [mem_conj_smul_iff]
    have hq' := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) q).mp hq
    rw [inv_inv] at hq'
    exact hQU hq'
  obtain ⟨U', hU'R, hU'U⟩ : ∃ U' : Sylow 2 X, (∀ α ∈ R, α • U' = U') ∧ U' ≠ U := by
    by_contra hno
    push_neg at hno
    have hfix : MulAction.fixedPoints R (Sylow 2 X) = {U} := by
      ext P
      simp only [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
      constructor
      · exact fun hP => hno P fun α hα => hP ⟨α, hα⟩
      · rintro rfl α
        exact hRU α α.2
    have hmod := hR.card_modEq_card_fixedPoints (Sylow 2 X)
    rw [hfix, Nat.card_unique (α := ↥({U} : Set (Sylow 2 X))), (hX U).2] at hmod
    have hdvd : p ∣ Nat.card (U : Subgroup X) := by
      have := (Nat.modEq_iff_dvd' (by omega)).mp hmod.symm
      rwa [Nat.add_sub_cancel] at this
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp U.isPGroup'
    rw [hk] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
  have hCU : autCentralizer R ≤ Subgroup.normalizer ((U : Subgroup X) : Set X) := hCQ.trans hNQ
  have hthird : ∀ P : Sylow 2 X, (∀ α ∈ R, α • P = P) → P ≠ U' → P = U := by
    intro P hP hPU'
    obtain ⟨v, hv, rfl⟩ := exists_smul_eq (hX U').1 (hX U').2 hU'U.symm hPU'
    have hvC : v ∈ autCentralizer R := by
      show ∀ α ∈ R, α v = v
      intro α hα
      have h1 : α v • U = v • U := by
        calc α v • U = α v • (α • U) := by rw [hRU α hα]
          _ = α • (v • U) := (smul_conj_smul α v U).symm
          _ = v • U := hP α hα
      have h2 : (v⁻¹ * α v) • U = U := by rw [mul_smul, h1, inv_smul_smul]
      have h3 : α v ∈ (U' : Subgroup X) := by
        rw [← hU'R α hα, mem_smul_iff, MulAut.inv_apply_self]
        exact hv
      have h4 := eq_one_of_mem_normalizer (hX U').1 hU'U.symm
        ((U' : Subgroup X).mul_mem ((U' : Subgroup X).inv_mem hv) h3)
        (Sylow.smul_eq_iff_mem_normalizer.mp h2)
      exact (inv_mul_eq_one.mp h4).symm
    rw [eq_one_of_mem_normalizer (hX U').1 hU'U.symm hv (hCU hvC), one_smul]
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  obtain ⟨huC, huQ⟩ := Subgroup.mem_inf.mp hu
  have huU : u ∈ (U : Subgroup X) := hQU huQ
  have huC' : ∀ α ∈ R, α u = u := huC
  have hfix : ∀ α ∈ R, α • (u • U') = u • U' := by
    intro α hα
    rw [smul_conj_smul, huC' α hα, hU'R α hα]
  have hne : u • U' ≠ U := by
    intro h
    apply hU'U
    calc U' = u⁻¹ • (u • U') := (inv_smul_smul u U').symm
      _ = u⁻¹ • U := by rw [h]
      _ = U := Sylow.smul_eq_iff_mem_normalizer.mpr
        (Subgroup.le_normalizer ((U : Subgroup X).inv_mem huU))
  have heq : u • U' = U' := by
    by_contra h
    exact hne (hthird _ hfix h)
  exact eq_one_of_mem_normalizer (hX U).1 hU'U huU (Sylow.smul_eq_iff_mem_normalizer.mp heq)

theorem oppositeFixed_of_fusionIsBenderGroup {X : Type} [Group X]
    [Finite X] (hX : fusionIsBenderGroup X) : OppositeFixed X :=
  oppositeFixed_of_stronglyEmbedded fun T => by
    obtain ⟨D, h⟩ := CFSG.Goldschmidt.G3a.exists_borelSetup hX T
    exact ⟨h.se, h.card⟩

theorem oppositeFixed_of_valid_suzuki {S : Type} [Group S]
    [Finite S] (m : ℕ) (hv : (TauCeti.LieTypeIndex.suzuki m).Valid)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.suzuki m, hv⟩) : OppositeFixed S := by
  have hm : 1 ≤ m :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).mp ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  refine oppositeFixed_of_fusionIsBenderGroup (Or.inr (Or.inr ⟨m, hm, ⟨?_⟩⟩))
  exact (e.trans (CFSG.BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup hv)).trans
    (MulEquiv.subgroupCongr ((CFSG.Models.benderSzModel_eq_sz m).symm.trans
      (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup m))).symm

end CFSG.LieType.ChevTwo
