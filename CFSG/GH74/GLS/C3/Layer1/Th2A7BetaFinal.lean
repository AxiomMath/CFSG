module

public import CFSG.GH74.GLS.C3.Layer1.Th2A7BetaKGroup
public import CFSG.GH74.GLS.C3.Layer1.Th2A7BetaSetup
public import CFSG.GH74.GLS.C3.Layer1.Th2A7ExcAlpha
public import CFSG.GH74.E2.FactsK
public import CFSG.GH74.Generic.GKFFinal
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.AS16.E2.Pump2Tables
public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma21i
public import CFSG.GH74.GLS.C3.Layer1.BkA7Cent
public import CFSG.GH74.GLS.C3.Layer1.BkL113aSix
public import CFSG.GH74.GLS.C3.Layer1.EvenSelTop
public import CFSG.GH74.GLS.C3.Layer1.Thm1G33RFA7
public import CFSG.GH74.GLS.C3.Layer1.Thm1G33Rel
public import CFSG.GH74.GLS.C3.Layer1.Thm1G35Pre
public import CFSG.GH74.GLS.C3.Layer1.Thm1L3Pump
public import CFSG.GH74.GLS.C3.Layer1.Thm1P31cAut
public import CFSG.GH74.GLS.C3.Layer1.Thm1P31cC
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk412Dih
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic4
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic5
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic6
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic7
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic8
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic9
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.After
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Lemma12_7
public import CFSG.GH74.Generic.Front.Final
public import CFSG.GH74.Generic.FrontEnd
public import CFSG.GH74.Generic.S1.LinFull
public import CFSG.GH74.KGroups.L28Tables
public import CFSG.GH74.KGroups.L34Aut
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModels
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverExternal
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAllInvolutionFourGroup
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Sporadic.ThSchreier.AutCore
public import Certificates.Certificate10025

public section

namespace CFSG.GH74.GLS.Th2A7Beta

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.E2
  Equiv Equiv.Perm CFSG.LieType.SteinbergBR.SmallAlt

theorem false_of_exceptional_beta
    (hGKF : GenericKnownFacts) (hE2 : E2ComponentFacts)
    {G : Type} [Group G] [Finite G] (hG : C3Hyp G) {x y : G} {K T S : Subgroup G}
    (hs : Th2Std x y K T S) (he7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    {T' S' : Subgroup G} {a : G} (hw : IsExcA7Witness x K T' S' a)
    (hβ : ¬ (T' ⊓ CxK x K ≤ (T' ⊓ K).map (MulAut.conj a).toMonoidHom)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e7⟩ := he7
  obtain ⟨z, psi, A, hKN, cP, hrel⟩ := Th2.AlphaStep.exists_setup_of_witness hG hs e7 hw
  obtain ⟨-, -, -, hSsyl, -, -, haN, -, -, hSeq, -, -, -, ⟨eP⟩, ⟨eQ⟩⟩ := hw
  obtain ⟨s, hsPa, hss, hs1, -, hpsis⟩ := A.exists_refl_z_swap eP eQ hβ
  have hsT : s ∈ T' := A.Pa_le hsPa
  have heT : z * s ∈ T' := T'.mul_mem A.z_mem.1 hsT
  have heC : z * s ∈ centralizer ({x} : Set G) := A.T_le_C heT
  have hzs : z * s = s * z := A.z_central s hsT
  have hee : (z * s) * (z * s) = 1 := by
    calc (z * s) * (z * s) = z * (s * z) * s := by group
      _ = z * (z * s) * s := by rw [hzs]
      _ = (z * z) * (s * s) := by group
      _ = 1 := by rw [A.z_sq, hss, one_mul]
  have he1 : z * s ≠ 1 := by
    intro h
    have hzs' : z = s⁻¹ := by
      calc z = (z * s) * s⁻¹ := by group
        _ = s⁻¹ := by rw [h, one_mul]
    have hz : z ∈ (T' ⊓ K) ⊓ (T' ⊓ K).map (MulAut.conj a).toMonoidHom :=
      ⟨A.z_mem, hzs' ▸ Subgroup.inv_mem _ hsPa⟩
    rw [A.disj, Subgroup.mem_bot] at hz
    exact A.z_ne hz
  have he2 : orderOf (z * s) = 2 := orderOf_eq_prime (by rw [sq]; exact hee) he1
  have hx2 : orderOf x = 2 := hs.orderOf_x
  have hpsie : psi (z * s) = swap 5 6 := by
    rw [A.psiD.mul z (A.T_le_C A.z_mem.1) s (A.T_le_C hsT), A.psi_z, hpsis]
    decide
  have hct : (C3.Layer1.Thm1.psiEquiv e7
      (C3.Layer1.Back.actHom hKN ⟨z * s, heC⟩)).cycleType = {2} := by
    have h1 := hrel (z * s) heC
    rw [hpsie] at h1
    have h2 : C3.Layer1.Thm1.psiEquiv e7 (C3.Layer1.Back.actHom hKN ⟨z * s, heC⟩) =
        cP * swap 5 6 * cP⁻¹ := by
      rw [h1]; group
    rw [h2, Equiv.Perm.cycleType_conj]
    exact Equiv.Perm.isSwap_iff_cycleType.mp ⟨5, 6, by decide, rfl⟩
  obtain ⟨w, hwe⟩ := A.exists_conj_z_mul_eq_xz hsPa hss hs1
  have hZS := A.eq_one_or_eq_xz_of_central eP hSeq haN
  have hxc : ∀ t ∈ T', t * x = x * t := fun t ht => mem_centralizer_singleton_iff.1 (A.T_le_C ht)
  have hvT : ∀ t ∈ T', t * (x * z) = (x * z) * t := by
    intro t ht
    have h1 := hxc t ht
    have h2 : z * t = t * z := A.z_central t ht
    calc t * (x * z) = (t * x) * z := by group
      _ = (x * t) * z := by rw [h1]
      _ = x * (t * z) := by group
      _ = x * (z * t) := by rw [h2]
      _ = (x * z) * t := by group
  have hva : a ∈ centralizer ({x * z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have hxz : x * z = z * x := (hxc z A.z_mem.1).symm
    have h : a * (x * z) * a⁻¹ = x * z := by
      calc a * (x * z) * a⁻¹ = (a * x * a⁻¹) * (a * z * a⁻¹) := by group
        _ = z * x := by rw [A.hxa, A.hxz]
        _ = x * z := hxz.symm
    calc a * (x * z) = (a * (x * z) * a⁻¹) * a := by group
      _ = (x * z) * a := by rw [h]
  have hSv : S' ≤ centralizer ({x * z} : Set G) := by
    rw [hSeq]
    exact sup_le (fun t ht => mem_centralizer_singleton_iff.2 (hvT t ht))
      ((Subgroup.zpowers_le).2 hva)
  have hSv' : IsSylowOf 2 S' (centralizer ({x * z} : Set G)) := hSsyl.of_le hSv le_top
  have hR := C3.Layer1.Back.isSylowOf_conjugate hSv' w
  have hew : w⁻¹ * (x * z) * w = z * s := by rw [← hwe]; group
  rw [C3.Layer1.Back.conjugate_centralizer_singleton, hew] at hR
  refine false_of_transposition_central hGKF hE2 hG A.psiD.K_le hKN e7 hx2 he2 heC hct hR ?_
  intro r hr hrc
  rw [C3.Layer1.Back.mem_conjugate_iff'] at hr
  have hcen : ∀ t ∈ S', (w * r * w⁻¹) * t = t * (w * r * w⁻¹) := by
    intro t ht
    have htR : w⁻¹ * t * w ∈ CFSG.conjugate S' w := by
      rw [C3.Layer1.Back.mem_conjugate_iff']
      simpa [mul_assoc] using ht
    have h1 := hrc _ htR
    calc (w * r * w⁻¹) * t = w * (r * (w⁻¹ * t * w)) * w⁻¹ := by group
      _ = w * ((w⁻¹ * t * w) * r) * w⁻¹ := by rw [h1]
      _ = t * (w * r * w⁻¹) := by group
  rcases hZS _ hr hcen with h | h
  · left
    calc r = w⁻¹ * (w * r * w⁻¹) * w := by group
      _ = 1 := by rw [h]; group
  · right
    calc r = w⁻¹ * (w * r * w⁻¹) * w := by group
      _ = w⁻¹ * (x * z) * w := by rw [h]
      _ = z * s := hew

end CFSG.GH74.GLS.Th2A7Beta

namespace CFSG.GH74.GLS

open CFSG.GH74

theorem b_thm2_A7_exc_beta_of_facts
    (hGKF : Generic.GenericKnownFacts) (hE2 : E2.E2ComponentFacts) : B_thm2_A7_exc_beta := by
  intro G _ _ hG x y K T S hs _ he7 T' S' a hw hβ
  exact Th2A7Beta.false_of_exceptional_beta hGKF hE2 hG hs he7 hw hβ

theorem b_thm2_A7_exc_of_griess
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) :
    B_thm2_A7_exc_beta ∧ B_thm2_A7_exc :=
  have h := b_thm2_A7_exc_beta_of_facts (Generic.genericKnownFacts_of_griess hGA)
    E2.e2ComponentFacts
  ⟨h, b_thm2_A7_exc_of_beta h⟩

end CFSG.GH74.GLS
