module

public import CFSG.GH74.Generic.BProg.B2.GenLocU3E8Elem
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Certificates.Kernel.Th.Spec.GjBase
public import CFSG.Certificates.Kernel.Th.Spec.Ts2324
public import CFSG.GH74.GLS.C3.Layer1.Back112Iv2
public import CFSG.GH74.GLS.C3.Layer1.Th2Cent5
public import CFSG.GH74.GLS.C3.Layer1.Thm1P31s
public import CFSG.GH74.GLS.C3.Layer2.FusionTools
public import CFSG.GH74.GLS.C3.Layer3.Main
public import CFSG.GH74.GLS.IVK.L2.BN
public import CFSG.GH74.GLS.IVK.L2.BorelFive
public import CFSG.GH74.GLS.IVK.L2.Hilbert90Core
public import CFSG.GH74.GLS.IVK.L2.Lemma114
public import CFSG.GH74.GLS.IVK.L2.Lemma12ib
public import CFSG.GH74.GLS.IVK.L2.Lemma12j
public import CFSG.GH74.GLS.IVK.L2.Lemma13fc
public import CFSG.GH74.GLS.IVK.L2.Lemma14f
public import CFSG.GH74.GLS.IVK.L2.Lemma19b
public import CFSG.GH74.GLS.IVK.Prod.Lemma31
public import CFSG.GH74.GLS.IVK.Proofs
public import CFSG.GH74.GLS.IVK.Statements
public import CFSG.GH74.GLS.LU.Ident
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
public import CFSG.GH74.Generic.BProg.B1.Assembly2
public import CFSG.GH74.Generic.BProg.B2.GenLocBasicQuot
public import CFSG.GH74.Generic.BProg.B2.GenLocL3Lin
public import CFSG.GH74.Generic.BProg.B2.GenLocL3Pair
public import CFSG.GH74.Generic.BProg.B2.GenLocU3Seven
public import CFSG.GH74.Generic.BProg.Stage2Frozen
public import CFSG.GH74.Generic.BProg.Theta32
public import CFSG.GH74.Generic.Gen4LiftJ
public import CFSG.GH74.KGroups.L3EpsInvLin
public import CFSG.GH74.KGroups.L3EpsNoNormalThree
public import CFSG.GH74.KGroups.L3EpsOutExp
public import CFSG.LocalAnalysis.Asc75.Conj
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2CyclicFour
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartOne
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSquareProd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58Section
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubBasic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCentral
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Transfer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionConjugateHullOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityCoercions
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeIdentityTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorQuotientModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointClassFree
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremTwoFixedDegree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyBasic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.HullNativeRecognition
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsFrame
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.GroupTheory.SteinbergCEPrimeDimScalarCentralizer
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientRep
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic
public import CFSG.RankThree.PartOne.S9.StatementsTwoAction
public import CFSG.Sporadic.Th.Max3.Packet
public import CFSG.Sporadic.Th.Simple
public import CFSG.Sporadic.ThSchreier.AutCore
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjugatedInvertedSubgroup
public import CFSG.Walter.W67.Section5.Lemma57

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix CFSG CFSG.GH74 CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.GH74.Generic.BProg.B2.GenLocU3Blk CFSG.GH74.Generic.BProg.B2.GenLocU3Good
  CFSG.GH74.Generic.BProg.B2.GenLocU3E8Elem
open scoped MatrixGroups

namespace GenLocU3E8Gen

theorem sl2_eq_top_of_dvd {K₀ : Type} [Field K₀] [Finite K₀] (hK : Nat.card K₀ = 7)
    (N : Subgroup SL(2, K₀)) (h56 : 56 ∣ Nat.card N) : N = ⊤ := by
  classical
  have : Fintype K₀ := Fintype.ofFinite K₀
  have hG : Nat.card SL(2, K₀) = 336 := by
    rw [CFSG.RankThree.SubgroupLists.card_sl2_field, hK]
    norm_num
  have h7 : (7 : K₀) = 0 := by
    have := FiniteField.cast_card_eq_zero K₀
    rwa [← Nat.card_eq_fintype_card, hK] at this
  have h2 : (2 : K₀) ≠ 0 := by
    intro h2
    have : (1 : K₀) = 0 := by linear_combination h7 - 3 * h2
    exact one_ne_zero this
  have hquasi : CFSG.IsQuasisimple SL(2, K₀) := by
    refine CFSG.RankThree.Classical.isQuasisimple_SL2 ?_
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K₀)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK]; norm_num)
    exact ⟨s, hs⟩
  have hcenter : Nat.card (Subgroup.center SL(2, K₀)) = 2 :=
    CFSG.RankThree.SubgroupLists.natCard_center_sl2 h2
  by_contra hN
  set K : Subgroup SL(2, K₀) := N.normalCore with hKdef
  have hKN : K ≤ N := Subgroup.normalCore_le N
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hquasi (N := K) inferInstance with hK1 | hKc
  · exact hN (top_le_iff.1 (hK1 ▸ hKN))
  · have hKdvd : Nat.card K ∣ 2 := by
      have := Subgroup.card_dvd_of_le hKc
      rwa [hcenter] at this
    have hKmul := Subgroup.card_mul_index K
    rw [hG] at hKmul
    have hcop : Nat.Coprime (Nat.card K) 7 := by
      have : Nat.card K ∣ 2 := hKdvd
      have h2' : Nat.card K = 1 ∨ Nat.card K = 2 := by
        have := Nat.le_of_dvd (by norm_num) this
        have hpos : 0 < Nat.card K := Nat.card_pos
        omega
      rcases h2' with h | h <;> rw [h] <;> norm_num
    have h7dvd : 7 ∣ K.index := by
      have : 7 ∣ Nat.card K * K.index := by rw [hKmul]; norm_num
      exact (Nat.Coprime.symm hcop).dvd_of_dvd_mul_left this
    have hinj : Function.Injective (QuotientGroup.kerLift (MulAction.toPermHom SL(2, K₀) (SL(2, K₀) ⧸ N))) :=
      QuotientGroup.kerLift_injective _
    have hdvd := Subgroup.card_dvd_of_injective _ hinj
    rw [← Subgroup.normalCore_eq_ker, Nat.card_perm] at hdvd
    have hidx : Nat.card (SL(2, K₀) ⧸ K) = K.index := rfl
    have hmN : Nat.card (SL(2, K₀) ⧸ N) = N.index := rfl
    rw [hidx, hmN] at hdvd
    have hNmul := Subgroup.card_mul_index N
    rw [hG] at hNmul
    have hle : N.index ≤ 6 := by
      obtain ⟨k, hk⟩ := h56
      have hpos : 0 < N.index := Nat.pos_of_ne_zero (by
        intro h0; rw [h0] at hNmul; omega)
      have hk0 : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · rw [h] at hk; have := Nat.card_pos (α := N); omega
        · exact h
      rw [hk] at hNmul
      nlinarith
    have h7le : 7 ≤ N.index :=
      (Nat.Prime.dvd_factorial (by norm_num)).1 (h7dvd.trans hdvd)
    omega

variable {p f : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F] [CharP F p]

theorem su2_eq_top_of_dvd (h : UnitaryFieldData p f F) (hq : p ^ f = 7)
    (N : Subgroup (Su F p f 2)) (h56 : 56 ∣ Nat.card N) : N = ⊤ := by
  obtain ⟨e0⟩ := CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two (K := F) (r := p)
    (f := f) h.card_eq_sq
  let E : SL(2, CFSG.LieType.Steinberg.fixedSubfield F p f) ≃* Su F p f 2 :=
    e0.trans (suEquiv h 2).symm
  have hK : Nat.card (CFSG.LieType.Steinberg.fixedSubfield F p f) = 7 := by
    rw [CFSG.LieType.Steinberg.card_fixedSubfield h.card_eq_sq, hq]
  have hcomap : N.comap E.toMonoidHom = N.map E.symm.toMonoidHom :=
    Subgroup.comap_equiv_eq_map_symm E N
  have hcard : Nat.card (N.comap E.toMonoidHom) = Nat.card N := by
    rw [hcomap, Subgroup.card_map_of_injective E.symm.injective]
  have htop := sl2_eq_top_of_dvd hK (N.comap E.toMonoidHom) (by rw [hcard]; exact h56)
  have := Subgroup.map_comap_eq_self_of_surjective (f := E.toMonoidHom) E.surjective N
  rw [htop, Subgroup.map_top_of_surjective _ E.surjective] at this
  exact this.symm

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem conj_matrix (Y : Matrix (Fin 2) (Fin 2) F) :
    (!![1, 0, 0; 0, 0, 1; 0, -1, 0] * !![0, 1, 0; -1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) *
        !![1, 0, 0; 0, Y 0 0, Y 0 1; 0, Y 1 0, Y 1 1] =
      !![Y 0 0, Y 0 1, 0; Y 1 0, Y 1 1, 0; 0, 0, 1] *
        (!![1, 0, 0; 0, 0, 1; 0, -1, 0] * !![0, 1, 0; -1, 0, 0; 0, 0, 1]) := by
  simp only [Matrix.mul_fin_three]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] <;>
    ring

omit [Fact p.Prime] [Finite F] [CharP F p] in
theorem rMat_sq {h : UnitaryFieldData p f F} (D : Gauss h) :
    (rMat * rMat : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := by
  rw [rMat]
  simp only [Matrix.mul_fin_two]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one,
      Fin.isValue]
  · ring
  · linear_combination D.h7
  · linear_combination -D.h7
  · ring

theorem ym_rSu_sq {h : UnitaryFieldData p f F} (D : Gauss h) :
    ym (D.rSu * D.rSu) = !![0, 1; -1, 0] := by
  rw [ym_mul, D.ym_rSu]
  exact rMat_sq D

theorem eq_top_of_generators (h : UnitaryFieldData p f F) (hq : p ^ f = 7) (D : Gauss h)
    (H : Subgroup (Su F p f 3))
    (hT1 : blockEmb2 F p f 2 0 D.tSu ∈ H) (hT2 : blockEmb2 F p f 2 1 D.tSu ∈ H)
    (hR12 : blockEmb2 F p f 2 0 D.rSu ∈ H) (hR23 : blockEmb2 F p f 2 1 D.rSu ∈ H) : H = ⊤ := by
  set N : Subgroup (Su F p f 2) := H.comap (blockEmb2 F p f 2 1) with hN
  have htN : D.tSu ∈ N := hT2
  have hbN : D.bSu ∈ N := by
    show blockEmb2 F p f 2 1 D.bSu ∈ H
    rw [← D.word_eq, map_inv]
    exact mul_mem (mul_mem (mul_mem (mul_mem hR23 hT2) (inv_mem hT1)) hR23) hT1
  have h8 : 8 ∣ Nat.card N := by
    have := orderOf_dvd_natCard (⟨D.tSu, htN⟩ : N)
    rwa [Subgroup.orderOf_mk, D.tSu_orderOf] at this
  have h7 : 7 ∣ Nat.card N := by
    have := orderOf_dvd_natCard (⟨D.bSu, hbN⟩ : N)
    rwa [Subgroup.orderOf_mk, D.bSu_orderOf] at this
  have h56 : 56 ∣ Nat.card N := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 8 7) h8 h7
  have hNtop : N = ⊤ := su2_eq_top_of_dvd h hq N h56
  have hι1 : ∀ y : Su F p f 2, blockEmb2 F p f 2 1 y ∈ H := fun y => by
    have : y ∈ N := hNtop ▸ Subgroup.mem_top y
    exact this
  have hm : blockEmb2 F p f 2 1 (D.rSu * D.rSu) * blockEmb2 F p f 2 0 (D.rSu * D.rSu) ∈ H := by
    rw [map_mul, map_mul]
    exact mul_mem (mul_mem hR23 hR23) (mul_mem hR12 hR12)
  have hι0 : ∀ y : Su F p f 2, blockEmb2 F p f 2 0 y ∈ H := fun y => by
    have hcomm : (blockEmb2 F p f 2 1 (D.rSu * D.rSu) * blockEmb2 F p f 2 0 (D.rSu * D.rSu)) *
        blockEmb2 F p f 2 1 y = blockEmb2 F p f 2 0 y *
        (blockEmb2 F p f 2 1 (D.rSu * D.rSu) * blockEmb2 F p f 2 0 (D.rSu * D.rSu)) := by
      apply Subtype.ext
      apply Units.ext
      simp only [Subgroup.coe_mul, Units.val_mul, coe_iota0, coe_iota1, ym_rSu_sq D]
      simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
        Matrix.cons_val_fin_one]
      exact conj_matrix (ym y)
    have : blockEmb2 F p f 2 0 y = (blockEmb2 F p f 2 1 (D.rSu * D.rSu) *
        blockEmb2 F p f 2 0 (D.rSu * D.rSu)) * blockEmb2 F p f 2 1 y *
        (blockEmb2 F p f 2 1 (D.rSu * D.rSu) * blockEmb2 F p f 2 0 (D.rSu * D.rSu))⁻¹ := by
      rw [hcomm]; group
    rw [this]
    exact mul_mem (mul_mem hm (hι1 y)) (inv_mem hm)
  have hq2 : p ^ f ≠ 2 := by rw [hq]; norm_num
  refine eq_top_iff.2 ?_
  rw [← iSup_range_blockEmb2 (K := F) (p := p) (f := f) h.card_eq_sq hq2 2]
  refine iSup_le fun k => ?_
  rintro _ ⟨y, rfl⟩
  fin_cases k
  · exact hι0 y
  · exact hι1 y

end GenLocU3E8Gen

end CFSG.GH74.Generic.BProg.B2
