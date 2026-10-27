module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTFinOmega
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnSp8b
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
public import CFSG.RankThree.OrthogonalInvolutions.Dickson
public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.LieType.Universal.Spin.Forms
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerOmega
import CFSG.LinearAlgebra.ExtraspecialCyclotomicModule
import CFSG.RankThree.Literature.FSmithOrthogonal
import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.Goldschmidt.Steps.G310Comp
public import CFSG.LargeExtraspecial.S4CEA6Basic
public import CFSG.LargeExtraspecial.S4CESmallThree
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
public import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
public import CFSG.LieType.SeitzGeneration.UnitaryBlocks
public import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTCompU6
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Fix
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S4.ModCore
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs273d2
public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Bounded
public import CFSG.LocalAnalysis.SectionRank.QTK.EvenOrth
public import CFSG.LocalAnalysis.SectionRank.QTK.Exc
public import CFSG.LocalAnalysis.SectionRank.QTK.OddOrth
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSpRank
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.Milestones.ASVolI.A2OddAut
public import CFSG.Milestones.ASVolI.F48.Core
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Thm
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.GF2n.Stroth80.FrobClause
public import CFSG.RankThree.GF2n.Stroth80.Sec12Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec310Nt
public import CFSG.RankThree.GF2n.Stroth80.Sec310Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec4Rt
public import CFSG.RankThree.GF2n.Stroth80.Sec4Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5Main
public import CFSG.RankThree.GF2n.Stroth80.Sec6Stmt
public import CFSG.RankThree.GF2n.SupIndepDecomp
public import CFSG.RankThree.GF2n.Tim79CentC
public import CFSG.RankThree.GF2n.Tim79CentL
public import CFSG.RankThree.GF2n.Tim79Mod
public import CFSG.RankThree.OddKernel.CompleteRankComparison
public import CFSG.RankThree.PartOne.CTP.SpEven
public import CFSG.RankThree.PartOne.KC.OrthogonalNormPlaneFactors
public import CFSG.RankThree.PartOne.KF.ClsPSL
public import CFSG.RankThree.PartOne.KF.SU5Model
public import CFSG.RankThree.PartOne.KF.SymCtxMatrix
public import CFSG.RankThree.PartOne.KF.ToralQuot
public import CFSG.RankThree.PartOne.S11c.Sec66PSL
public import CFSG.RankThree.PartOne.S11c.SuFiveD
public import CFSG.RankThree.PartTwo.Sec11.Item1117ProofSwap
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofCube
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofTools
public import CFSG.RankThree.PartTwo.Sec11.Item118
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194SpBlocks
public import CFSG.RankThree.PartTwo.Sec4.Item426A6
public import CFSG.RankThree.PartTwo.Sec4.Statements423
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.PartTwo.Sec8.Steps
public import CFSG.SignalizerFunctorTheorem.NonLocal.Cross
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpData
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpTwoTwo
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.Recognition.JankoWongPSLNine
public import CFSG.Sporadic.Schreier.RuPair
public import CFSG.Sporadic.Schreier.RuSylow
public import Certificates.Certificate7233Base

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HSubT.OmegaCanon

open Polynomial Module CFSG.Open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  CFSG.LocalAnalysis.GLTheoremA.CatB.U4Sp8 CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.OrthogonalInvolutions
open CFSG.ClassicalInvolution.Models.SymplecticPairs (gram_mulVec sgn par sgn_inl sgn_inr
  par_inl par_inr)

noncomputable abbrev fixV (t : StatedSp 4 (ZMod 2)) : Submodule (ZMod 2) (Fin 4 ⊕ Fin 4 → ZMod 2) :=
  primaryComponent (spEnd t) (X - 1)

noncomputable abbrev movV (t : StatedSp 4 (ZMod 2)) : Submodule (ZMod 2) (Fin 4 ⊕ Fin 4 → ZMod 2) :=
  primaryComponent (spEnd t) q2

theorem q2_eq : q2 = X ^ 2 + X + 1 := by
  have h1 : (X ^ 3 - 1 : (ZMod 2)[X]) = (X - 1) * q2 := X_pow_three_sub_one
  have h2 : (X ^ 3 - 1 : (ZMod 2)[X]) = (X - 1) * (X ^ 2 + X + 1) := by ring
  have hne : (X - 1 : (ZMod 2)[X]) ≠ 0 := by
    rw [show (X - 1 : (ZMod 2)[X]) = X - C 1 by rw [C_1]]
    exact (monic_X_sub_C 1).ne_zero
  exact mul_left_cancel₀ hne (h1.symm.trans h2)

theorem fixV_eq_ker (t : StatedSp 4 (ZMod 2)) : fixV t = LinearMap.ker (spEnd t - 1) := by
  rw [fixV, primaryComponent, show (X - 1 : (ZMod 2)[X]) = X - C 1 by rw [C_1], map_sub,
    aeval_X, aeval_C]
  simp

theorem fixV_inf_movV (t : StatedSp 4 (ZMod 2)) : fixV t ⊓ movV t = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.mp hv
  have ht : spEnd t v = v := by
    rw [fixV_eq_ker, LinearMap.mem_ker] at hv1
    simpa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] using hv1
  have hq : (aeval (spEnd t) (X ^ 2 + X + 1 : (ZMod 2)[X])) v = 0 := by
    rw [movV, primaryComponent, LinearMap.mem_ker] at hv2
    rwa [q2_eq] at hv2
  have hsum : spEnd t (spEnd t v) + spEnd t v + v = 0 := by
    simpa [pow_two, Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply] using hq
  simp only [ht] at hsum
  have hvv : v + v = 0 := by
    rw [add_eq_zero_iff_eq_neg]
    exact (neg_eq_self_of_two_eq_zero (K := ZMod 2) (by decide) v).symm
  rw [hvv, zero_add] at hsum
  simpa using hsum

section ImplicitT

variable {t : StatedSp 4 (ZMod 2)}

theorem movV_le_range (ht3 : t ^ 3 = 1) : movV t ≤ LinearMap.range (spEnd t - 1) := by
  intro v hv
  refine LinearMap.mem_range.mpr ⟨spEnd t v, ?_⟩
  have hq : (aeval (spEnd t) (X ^ 2 + X + 1 : (ZMod 2)[X])) v = 0 := by
    rw [movV, primaryComponent, LinearMap.mem_ker] at hv
    rwa [q2_eq] at hv
  have hsum : spEnd t (spEnd t v) + spEnd t v + v = 0 := by
    simpa [pow_two, Module.End.mul_apply, LinearMap.add_apply, Module.End.one_apply] using hq
  have hvv : v + v = 0 := by
    rw [add_eq_zero_iff_eq_neg]
    exact (neg_eq_self_of_two_eq_zero (K := ZMod 2) (by decide) v).symm
  have hAB : spEnd t (spEnd t v) + spEnd t v = v := by
    have h4 : (spEnd t (spEnd t v) + spEnd t v + v) + v = 0 + v := by rw [hsum]
    simpa [add_assoc, hvv] using h4
  rw [LinearMap.sub_apply, Module.End.one_apply,
    show spEnd t (spEnd t v) - spEnd t v = spEnd t (spEnd t v) + spEnd t v from by
      rw [sub_eq_add_neg, neg_eq_self_of_two_eq_zero (K := ZMod 2) (by decide)]]
  exact hAB

theorem even_finrank_of_le_movV {t : StatedSp 4 (ZMod 2)}
    {W : Submodule (ZMod 2) (Fin 4 ⊕ Fin 4 → ZMod 2)} (hW : W ≤ movV t)
    (hinv : ∀ w ∈ W, spEnd t w ∈ W) : Even (Module.finrank (ZMod 2) W) := by
  classical
  haveI : Fact (Irreducible q2) := ⟨q2_irreducible⟩
  let T : Module.End (ZMod 2) ↥W := (spEnd t).restrict hinv
  have hTq : aeval T q2 = 0 := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    rw [CFSG.LinearAlgebra.coe_aeval_restrict_apply hinv q2 w]
    have hw : (w : Fin 4 ⊕ Fin 4 → ZMod 2) ∈ movV t := hW w.2
    rw [movV, primaryComponent, LinearMap.mem_ker] at hw
    exact hw
  let ψ : AdjoinRoot q2 →+* Module.End (ZMod 2) ↥W :=
    Ideal.Quotient.lift (Ideal.span {q2}) (aeval T).toRingHom (fun a ha => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      simp [hTq])
  letI : Module (AdjoinRoot q2) ↥W := Module.compHom ↥W ψ
  have hψ : ∀ c : ZMod 2, ψ (algebraMap (ZMod 2) (AdjoinRoot q2) c) = algebraMap _ _ c := by
    intro c
    change (aeval T) (C c) = _
    rw [aeval_C]
  haveI : IsScalarTower (ZMod 2) (AdjoinRoot q2) ↥W := by
    constructor
    intro c k m
    change ψ (c • k) m = c • ψ k m
    rw [Algebra.smul_def, map_mul, hψ]
    rfl
  haveI : Module.Finite (AdjoinRoot q2) ↥W :=
    Module.Finite.of_restrictScalars_finite (ZMod 2) _ _
  have hpb : Module.finrank (ZMod 2) (AdjoinRoot q2) = 2 := by
    rw [(AdjoinRoot.powerBasis q2_irreducible.ne_zero).finrank, AdjoinRoot.powerBasis_dim,
      natDegree_q2]
  have hmul := Module.finrank_mul_finrank (ZMod 2) (AdjoinRoot q2) ↥W
  rw [hpb] at hmul
  exact ⟨Module.finrank (AdjoinRoot q2) ↥W, by omega⟩

theorem fixV_sup_movV (ht3 : t ^ 3 = 1) : fixV t ⊔ movV t = ⊤ := by
  classical
  have hsq : Squarefree (minpoly (ZMod 2) (spEnd t)) := squarefree_minpoly_spEnd ht3
  have hsum := sum_primaryProjection (x := spEnd t) hsq
  rw [eq_top_iff]
  intro v _
  have hv : v = ∑ a ∈ primaryFactors (spEnd t), primaryProjection (spEnd t) a v := by
    have h := LinearMap.congr_fun hsum v
    rw [LinearMap.sum_apply] at h
    simpa using h.symm
  rw [hv]
  refine Submodule.sum_mem _ fun a ha => ?_
  have hmem := primaryProjection_mem hsq ha v
  rcases mem_primaryFactors_pow_three (spEnd_pow ht3) ha with h | h
  · rw [h] at hmem ⊢
    exact Submodule.mem_sup_left hmem
  · rw [h] at hmem ⊢
    exact Submodule.mem_sup_right hmem

theorem apply_mem_movV_of_commute {g : StatedSp 4 (ZMod 2)} (hg : g * t = t * g)
    {v : Fin 4 ⊕ Fin 4 → ZMod 2} (hv : v ∈ movV t) : spEnd g v ∈ movV t := by
  have hc : Commute (spEnd g) (spEnd t) := by
    have h := congrArg (spLin 4 (ZMod 2)) hg
    rw [map_mul, map_mul] at h
    exact congrArg Units.val h
  exact apply_mem_primaryComponent hc hv

theorem apply_mem_fixV_of_commute {g : StatedSp 4 (ZMod 2)} (hg : g * t = t * g)
    {v : Fin 4 ⊕ Fin 4 → ZMod 2} (hv : v ∈ fixV t) : spEnd g v ∈ fixV t := by
  have hc : Commute (spEnd g) (spEnd t) := by
    have h := congrArg (spLin 4 (ZMod 2)) hg
    rw [map_mul, map_mul] at h
    exact congrArg Units.val h
  exact apply_mem_primaryComponent hc hv

theorem mem_spSupported_q2_iff (ht3 : t ^ 3 = 1) {g : StatedSp 4 (ZMod 2)} :
    g ∈ spSupported t {q2} ↔ g * t = t * g ∧ ∀ v ∈ fixV t, spEnd g v = v := by
  constructor
  · intro hg
    obtain ⟨hcomm, htriv⟩ := mem_spSupported.1 hg
    refine ⟨hcomm, fun v hv => ?_⟩
    by_cases h1 : (X - 1 : (ZMod 2)[X]) ∈ primaryFactors (spEnd t)
    · exact htriv (X - 1) h1 (by rw [Set.mem_singleton_iff]; exact q2_ne_X_sub_one.symm) v hv
    · have hbot : fixV t = ⊥ :=
        primaryComponent_eq_bot_of_not_mem irreducible_X_sub_one monic_X_sub_one h1
      rw [hbot, Submodule.mem_bot] at hv
      rw [hv, map_zero]
  · rintro ⟨hcomm, hfix⟩
    refine mem_spSupported.2 ⟨hcomm, fun k hk hkq v hv => ?_⟩
    rcases mem_primaryFactors_pow_three (spEnd_pow ht3) hk with h | h
    · rw [h] at hv
      exact hfix v hv
    · exact absurd (Set.mem_singleton_iff.mpr h) hkq

theorem mem_spSupported_X_sub_one_iff (ht3 : t ^ 3 = 1) {g : StatedSp 4 (ZMod 2)} :
    g ∈ spSupported t {(X - 1 : (ZMod 2)[X])} ↔ g * t = t * g ∧ ∀ v ∈ movV t, spEnd g v = v := by
  constructor
  · intro hg
    obtain ⟨hcomm, htriv⟩ := mem_spSupported.1 hg
    refine ⟨hcomm, fun v hv => ?_⟩
    by_cases hq : q2 ∈ primaryFactors (spEnd t)
    · exact htriv q2 hq (by rw [Set.mem_singleton_iff]; exact q2_ne_X_sub_one) v hv
    · have hbot : movV t = ⊥ :=
        primaryComponent_eq_bot_of_not_mem q2_irreducible monic_q2 hq
      rw [hbot, Submodule.mem_bot] at hv
      rw [hv, map_zero]
  · rintro ⟨hcomm, hfix⟩
    refine mem_spSupported.2 ⟨hcomm, fun k hk hkq v hv => ?_⟩
    rcases mem_primaryFactors_pow_three (spEnd_pow ht3) hk with h | h
    · exact absurd (Set.mem_singleton_iff.mpr h) hkq
    · rw [h] at hv
      exact hfix v hv

end ImplicitT

noncomputable abbrev Q8 : QuadraticForm (ZMod 2) (Fin 4 ⊕ Fin 4 → ZMod 2) :=
  CFSG.LieType.Universal.Spin.quadPlus 4 (ZMod 2)

theorem polar_Q8 (u v : Fin 4 ⊕ Fin 4 → ZMod 2) :
    QuadraticMap.polar Q8 u v = spForm 4 (ZMod 2) u v := by
  rw [spForm_apply, gram_mulVec, CFSG.LieType.Universal.Spin.polar_quadPlus]
  change (∑ i : Fin 4, (u (Sum.inl i) * v (Sum.inr i) + v (Sum.inl i) * u (Sum.inr i)))
    = ∑ a : Fin 4 ⊕ Fin 4, u a * (sgn (ZMod 2) a * v (par a))
  rw [Fintype.sum_sum_type]
  simp only [sgn_inl, sgn_inr, par_inl, par_inr, show (-1 : ZMod 2) = 1 from by decide, one_mul,
    Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem Q8_nondegenerate : Q8.polarBilin.Nondegenerate :=
  CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus 4 (ZMod 2)

theorem toLinEquiv_apply (g : StatedSp 4 (ZMod 2)) (v : Fin 4 ⊕ Fin 4 → ZMod 2) :
    toLinEquiv (Fin 4 ⊕ Fin 4) (ZMod 2) (g : SpGL) v = spEnd g v :=
  rfl

theorem mem_Om8_iff_omegaGroup (g : SpGL) :
    g ∈ CFSG.AGLEmbedding.Om8 ↔
      toLinEquiv (Fin 4 ⊕ Fin 4) (ZMod 2) g ∈ omegaGroup Q8 Q8_nondegenerate := by
  have h6 : 6 ≤ Module.finrank (ZMod 2) (Fin 4 ⊕ Fin 4 → ZMod 2) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  rw [CFSG.AGLEmbedding.mem_Om8_iff,
    ← CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadPlus (n := 4) (K := ZMod 2)
      (by norm_num),
    ← CFSG.RankThree.Literature.FSmith.commutator_orthogonalGroup_eq_omegaGroup (Q := Q8)
      Q8_nondegenerate h6]

end CFSG.LocalAnalysis.GLTheoremA.HSubT.OmegaCanon

end
