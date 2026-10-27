module

public import CFSG.LocalAnalysis.GLTheoremA.S8.HNAlt12
public import CFSG.LocalAnalysis.GLTheoremA.S8.I1423Lift
public import CFSG.Sporadic.HNSchreier.ThreeCent
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census228Spor.Normalizer
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census228Spor.ON
public import CFSG.LocalAnalysis.GLTheoremA.S4.ModCore
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72
public import CFSG.RankThree.PartTwo.Sec11.Item1117ProofSwap
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofCube
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofTools
public import CFSG.RankThree.PartTwo.Sec21.Item22Res4ProofNarrow
public import CFSG.RankThree.PartTwo.Sec4.Item424Res2ProofTools
public import Certificates.Certificate8007
public import Certificates.Certificate8008

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.HNRows

open Equiv Equiv.Perm CFSG.Sporadic.HNSchreier CFSG.Open CFSG.Yardstones.Md0ec50421ce4
  CFSG.HardMathSupport.Dickson.I271

theorem orderOf_tri012A : orderOf tri012A = 3 := by
  refine orderOf_eq_prime ?_ ?_
  · exact Subtype.ext tri012_pow_three
  · intro h
    have := congrArg (fun σ : alternatingGroup (Fin 12) => (σ : Perm (Fin 12)) 0) h
    revert this
    unfold tri012A tri
    decide

theorem quasisimple_of_equiv_simple {S A : Type} [Group S] [Group A] [Finite A] [IsSimpleGroup S]
    (e : A ≃* S) (h : ¬ (Nat.card A).Prime) : CFSG.Open.IsQuasisimple A := by
  have : IsSimpleGroup A := e.isSimpleGroup_congr.2 inferInstance
  exact isQuasisimple_of_simple_nonab (exists_noncomm_of_simple h)

theorem hn_of_embedding {Y : Type} [Group Y] [Finite Y] (φ : alternatingGroup (Fin 12) →* Y)
    (hφ : Function.Injective φ)
    (hC : Subgroup.centralizer ({φ tri012A} : Set Y) = (Subgroup.centralizer {tri012A}).map φ) :
    ∃ (yb : Y) (Tb A9 A8 : Subgroup Y), orderOf yb = 3 ∧ IsPGroup 2 Tb ∧ Tb ≠ ⊥ ∧
      yb ∈ Subgroup.normalizer (Tb : Set Y) ∧ A8 ≤ A9 ∧
      UniqComp (Subgroup.centralizer ({yb} : Set Y)) A9 ∧
      Nonempty (A9 ≃* alternatingGroup (Fin 9)) ∧
      UniqComp (Subgroup.centralizer ({yb} : Set Y) ⊓ Subgroup.normalizer (Tb : Set Y)) A8 ∧
      Nonempty (A8 ≃* alternatingGroup (Fin 8)) := by
  have hCN := inf_normalizer_map φ hφ (V := kleinV) hC
  have h3t : IsPGroup 3 ((Subgroup.zpowers tri012A).map φ) :=
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_tri012A, pow_one])).map φ
  set A9 := alt3.map φ
  set A8 := alt4.map φ
  have e9 : A9 ≃* alternatingGroup (Fin 9) :=
    (alt3.equivMapOfInjective φ hφ).symm.trans alt9Equiv.symm
  have e8 : A8 ≃* alternatingGroup (Fin 8) :=
    (alt4.equivMapOfInjective φ hφ).symm.trans alt8Equiv.symm
  have hc9 : Nat.card A9 = 181440 := by
    rw [Nat.card_congr (alt3.equivMapOfInjective φ hφ).symm.toEquiv, card_alt3]
  have hc8 : Nat.card A8 = 20160 := by
    rw [Nat.card_congr (alt4.equivMapOfInjective φ hφ).symm.toEquiv, card_alt4]
  have := alt3_simple
  have := alt4_simple
  have hq9 : CFSG.Open.IsQuasisimple A9 :=
    quasisimple_of_equiv_simple (alt3.equivMapOfInjective φ hφ).symm (by rw [hc9]; norm_num)
  have hq8 : CFSG.Open.IsQuasisimple A8 :=
    quasisimple_of_equiv_simple (alt4.equivMapOfInjective φ hφ).symm (by rw [hc8]; norm_num)
  obtain ⟨hn9, hz9⟩ := map_facts φ hφ alt3_facts.1 alt3_facts.2
  obtain ⟨hn8, hz8⟩ := map_facts φ hφ alt4_facts.1 alt4_facts.2
  refine ⟨φ tri012A, kleinV.map φ, A9, A8, ?_, kleinV_isPGroup.map φ, ?_, ?_,
    Subgroup.map_mono alt4_le_alt3, ?_, ⟨e9⟩, ?_, ⟨e8⟩⟩
  · rw [orderOf_injective φ hφ, orderOf_tri012A]
  · intro h
    exact kleinV_ne_bot ((Subgroup.map_eq_bot_iff_of_injective _ hφ).1 h)
  · exact Subgroup.le_normalizer_map φ ⟨tri012A, tri012A_mem_normalizer, rfl⟩
  · rw [hC]
    exact uniqComp_of_normal (Subgroup.map_mono alt3_le_centralizer) hn9 hq9
      (by rw [hc9]; norm_num) (h3t.to_le hz9)
  · rw [hCN]
    exact uniqComp_of_normal (Subgroup.map_mono alt4_le_inf) hn8 hq8
      (by rw [hc8]; norm_num) (h3t.to_le hz8)


theorem hn_of_iso {Y Q : Type} [Group Y] [Finite Y] [Group Q] (e : Y ≃* Q)
    {ι : alternatingGroup (Fin 12) →* Q} (hι : Function.Injective ι) {s : Q} (hs : ι tri012A = s)
    (hCs : Subgroup.centralizer ({s} : Set Q) = (Subgroup.centralizer {tri012A}).map ι) :
    ∃ (yb : Y) (Tb A9 A8 : Subgroup Y), orderOf yb = 3 ∧ IsPGroup 2 Tb ∧ Tb ≠ ⊥ ∧
      yb ∈ Subgroup.normalizer (Tb : Set Y) ∧ A8 ≤ A9 ∧
      UniqComp (Subgroup.centralizer ({yb} : Set Y)) A9 ∧
      Nonempty (A9 ≃* alternatingGroup (Fin 9)) ∧
      UniqComp (Subgroup.centralizer ({yb} : Set Y) ⊓ Subgroup.normalizer (Tb : Set Y)) A8 ∧
      Nonempty (A8 ≃* alternatingGroup (Fin 8)) := by
  refine hn_of_embedding (e.symm.toMonoidHom.comp ι) (e.symm.injective.comp hι) ?_
  rw [MonoidHom.comp_apply, hs, MulEquiv.coe_toMonoidHom, centralizer_map_equiv e.symm, hCs,
    Subgroup.map_map]


set_option maxRecDepth 20000 in
theorem hn_native {Y : Type} [Group Y] [Finite Y] (e : Y ≃* JH) :
    ∃ (yb : Y) (Tb A9 A8 : Subgroup Y), orderOf yb = 3 ∧ IsPGroup 2 Tb ∧ Tb ≠ ⊥ ∧
      yb ∈ Subgroup.normalizer (Tb : Set Y) ∧ A8 ≤ A9 ∧
      UniqComp (Subgroup.centralizer ({yb} : Set Y)) A9 ∧
      Nonempty (A9 ≃* alternatingGroup (Fin 9)) ∧
      UniqComp (Subgroup.centralizer ({yb} : Set Y) ⊓ Subgroup.normalizer (Tb : Set Y)) A8 ∧
      Nonempty (A8 ≃* alternatingGroup (Fin 8)) := by
  exact @hn_of_iso Y ↥JH _ _ inferInstance e iotaA iotaA_injective (sJ 0) iotaA_tri012 CJ_s1_eq

end CFSG.LocalAnalysis.GLTheoremA.S8.HNRows
