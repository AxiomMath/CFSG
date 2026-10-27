module

import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T1428

open Polynomial CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Open
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.Yardstones.Md0ec50421ce4

section Cases

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K}
  {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : V →ₛₗ[hK.bar] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}

theorem good_block_cases (hq : 2 ≤ ℓ ^ f) (H : UnitaryPrimaryData hK.bar B x)
    (a : primaryFactors (x : Module.End K V)) (ha : IsGoodBlock hK x a) :
    (dualPoly hK.bar (a : K[X]) = a ∧
        primaryMultiplicity (x : Module.End K V) (a : K[X]) = 2 ∧
        ∃ (F : Type) (_ : Field F) (_ : Fintype F), ringChar F = ℓ ∧
          Fintype.card F = ℓ ^ (f * (a : K[X]).natDegree) ∧ 4 ≤ Fintype.card F ∧
          Nonempty (↥(specialBlock B x (a : K[X])) ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∨
      (dualPoly hK.bar (a : K[X]) = a ∧
        3 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X]) ∧
        ∃ (E : Type) (_ : Field E) (_ : Fintype E) (m : ℕ), ringChar E = ℓ ∧
          Fintype.card E = (ℓ ^ (f * (a : K[X]).natDegree)) ^ 2 ∧ 3 ≤ m ∧
          (m, ℓ ^ (f * (a : K[X]).natDegree)) ≠ (3, 2) ∧
          Nonempty (↥(specialBlock B x (a : K[X])) ≃*
            ↥(StatedSU m (ℓ ^ (f * (a : K[X]).natDegree)) E))) ∨
      (¬ dualPoly hK.bar (a : K[X]) = a ∧
        ∃ (E : Type) (_ : Field E) (_ : Fintype E) (m : ℕ), ringChar E = ℓ ∧
          Fintype.card E = ℓ ^ (2 * (f * (a : K[X]).natDegree)) ∧ 2 ≤ m ∧
          4 ≤ Fintype.card E ∧
          Nonempty (↥(specialBlock B x (a : K[X])) ≃* Matrix.SpecialLinearGroup (Fin m) E)) := by
  haveI := hK.finite
  haveI : CharP K ℓ := hK.charP
  have hd : 1 ≤ (a : K[X]).natDegree :=
    Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors a.2)
  have hfd : 1 ≤ f * (a : K[X]).natDegree := Nat.mul_pos hK.one_le hd
  haveI : Finite (AdjoinRoot (a : K[X])) := Module.finite_of_finite K
  letI : Fintype (AdjoinRoot (a : K[X])) := Fintype.ofFinite _
  have hcharE : ringChar (AdjoinRoot (a : K[X])) = ℓ :=
    (Algebra.ringChar_eq K (AdjoinRoot (a : K[X]))).symm.trans (ringChar.eq K ℓ)
  have hm2 : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X]) := ha.1
  by_cases hself : dualPoly hK.bar (a : K[X]) = a
  · obtain ⟨hE, Hf, hHf, hHfl, ⟨e⟩⟩ :=
      nonempty_specialBlock_mulEquiv_sesqSU hself (selfDualPrimaryBlock H a hself)
    have hnum := isGoodBlock_numeric hq hself ha
    have hcardE : Fintype.card (AdjoinRoot (a : K[X])) =
        (ℓ ^ (f * (a : K[X]).natDegree)) ^ 2 := by
      rw [← Nat.card_eq_fintype_card]
      exact hE.card_eq_sq
    rcases Nat.lt_or_ge (primaryMultiplicity (x : Module.End K V) (a : K[X])) 3 with hm | hm
    · have hV : Module.finrank (AdjoinRoot (a : K[X]))
          (primaryComponent (x : Module.End K V) (a : K[X])) = 2 := by
        have : primaryMultiplicity (x : Module.End K V) (a : K[X]) = 2 := by omega
        exact this
      obtain ⟨e2⟩ :=
        CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hE hHf hHfl hV
      haveI : Finite hE.fixedField := inferInstance
      letI : Fintype hE.fixedField := Fintype.ofFinite _
      have hcardF : Fintype.card hE.fixedField = ℓ ^ (f * (a : K[X]).natDegree) := by
        rw [← Nat.card_eq_fintype_card]
        exact hE.card_fixedField
      haveI : Fact ℓ.Prime := ⟨hK.prime⟩
      haveI : CharP hE.fixedField ℓ := charP_of_card_eq_prime_pow hcardF
      have hcharF : ringChar hE.fixedField = ℓ := ringChar.eq _ _
      have h4 : 4 ≤ Fintype.card hE.fixedField := by
        rw [hcardF]
        exact (hnum.1 (by omega))
      exact Or.inl ⟨hself, by omega, hE.fixedField, inferInstance, inferInstance, hcharF, hcardF,
        h4, ⟨e.trans e2⟩⟩
    · obtain ⟨b, hb⟩ := hE.exists_orthonormal_basis hHf hHfl
      obtain ⟨e3⟩ :=
        CFSG.RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU hE b
          (G := (1 : Matrix (Fin (Module.finrank (AdjoinRoot (a : K[X]))
            (primaryComponent (x : Module.End K V) (a : K[X]))))
            (Fin (Module.finrank (AdjoinRoot (a : K[X]))
            (primaryComponent (x : Module.End K V) (a : K[X])))) (AdjoinRoot (a : K[X]))))
          (fun i j => by rw [hb i j, Matrix.one_apply])
      let e4 := (e.trans e3).trans (MulEquiv.subgroupCongr (unitarySU_eq_gramSU hE _).symm)
      have hne : (primaryMultiplicity (x : Module.End K V) (a : K[X]),
          ℓ ^ (f * (a : K[X]).natDegree)) ≠ (3, 2) := by
        intro hc
        have h1 := congrArg Prod.fst hc
        have h2 := congrArg Prod.snd hc
        simp only at h1 h2
        have := hnum.2 h1
        omega
      exact Or.inr (Or.inl ⟨hself, hm, AdjoinRoot (a : K[X]), inferInstance, inferInstance,
        primaryMultiplicity (x : Module.End K V) (a : K[X]), hcharE, hcardE, hm, hne, ⟨e4⟩⟩)
  · obtain ⟨e⟩ := nonempty_specialBlock_mulEquiv_SL (pairedPrimaryBlock H a (Ne.symm hself))
    have hcard : Nat.card (AdjoinRoot (a : K[X])) = ℓ ^ (2 * (f * (a : K[X]).natDegree)) :=
      natCard_adjoinRoot hK
    have hcard' : Fintype.card (AdjoinRoot (a : K[X])) =
        ℓ ^ (2 * (f * (a : K[X]).natDegree)) := by
      rw [← Nat.card_eq_fintype_card]
      exact hcard
    have h4 : 4 ≤ Fintype.card (AdjoinRoot (a : K[X])) := by
      rw [hcard']
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ ℓ ^ 2 := Nat.pow_le_pow_left hK.prime.two_le 2
        _ ≤ ℓ ^ (2 * (f * (a : K[X]).natDegree)) :=
          Nat.pow_le_pow_right hK.prime.pos (by omega)
    exact Or.inr (Or.inr ⟨hself, AdjoinRoot (a : K[X]), inferInstance, inferInstance,
      primaryMultiplicity (x : Module.End K V) (a : K[X]), hcharE, hcard', hm2, h4, ⟨e⟩⟩)

end Cases

end CFSG.LocalAnalysis.GLTheoremA.T1428
