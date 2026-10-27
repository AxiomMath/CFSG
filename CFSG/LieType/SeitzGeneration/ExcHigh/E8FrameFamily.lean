module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FrameTorus
public import CFSG.RankThree.PartOne.KE.EvenE7E8QPlusWeyl
public import CFSG.HardMathSupport.Timmesfeld.Torality.LangAssembly
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralWeylFive
public import CFSG.RankThree.Classical2.TwistedE6Phi3Centralizer
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.ClassicalInvolution.Generic.InductionMain
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCLayer
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.RouteD.MultiModelGlue
public import CFSG.ClassicalInvolution.RouteD.MultiStarStd
public import CFSG.ClassicalInvolution.RouteD.TypeAChain
public import CFSG.ClassicalInvolution.RouteD.TypeEModel
public import CFSG.HardMathSupport.Lang.AnisoE8.D8Planes
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralBlocks
public import CFSG.LieType.Chevalley.E7SupportedBruhat
public import CFSG.LieType.SeitzGeneration.OrthExLift
public import CFSG.LieType.SeitzGeneration.OrthNonsplitLow
public import CFSG.LieType.SeitzGeneration.UnitaryNonsplit
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality
public import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigiditySelfDual
public import CFSG.Sporadic.Schreier.J4SProfileNode

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley CFSG.StandardType.TableBExcTwo
  WithConv
open scoped MatrixGroups CFSG.ConvolutionPoints


@[expose] def frameCharAdd8 : (Fin Tag.E8.rank → ℤ) →+ (Fin 4 → ZMod 2) where
  toFun v s := ((v (![0, 3, 5, 7] s) : ℤ) : ZMod 2)
  map_zero' := by ext s; simp
  map_add' u v := by ext s; simp

@[expose] def frameChar8 :
    Multiplicative (Fin Tag.E8.rank → ℤ) →* Multiplicative (Fin 4 → ZMod 2) :=
  AddMonoidHom.toMultiplicative frameCharAdd8

theorem intCast_zmod_two_eq_zero_iff_E8 (n : ℤ) : ((n : ℤ) : ZMod 2) = 0 ↔ n % 2 = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  omega

theorem frameChar8_eq_one_iff (α : Fin Tag.E8.rank → ℤ) :
    frameChar8 (Multiplicative.ofAdd α) = 1 ↔
      α 0 % 2 = 0 ∧ α 3 % 2 = 0 ∧ α 5 % 2 = 0 ∧ α 7 % 2 = 0 := by
  have h : frameChar8 (Multiplicative.ofAdd α) = Multiplicative.ofAdd (frameCharAdd8 α) := rfl
  rw [h, ← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff, funext_iff]
  simp only [Pi.zero_apply, frameCharAdd8, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    intCast_zmod_two_eq_zero_iff_E8]
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3⟩
  · rintro ⟨h0, h1, h2, h3⟩ s
    fin_cases s
    · exact h0
    · exact h1
    · exact h2
    · exact h3

theorem frameE8Root_coord_even : ∀ i : Fin 8,
    frameE8Root i 0 % 2 = 0 ∧ frameE8Root i 3 % 2 = 0 ∧ frameE8Root i 5 % 2 = 0 ∧
      frameE8Root i 7 % 2 = 0 := by
  decide +kernel

theorem frameE8Root_mem_kernelRoots (i : Fin 8) : frameE8Root i ∈ kernelRoots frameChar8 :=
  ⟨e8Frame_isRoot i, (frameChar8_eq_one_iff _).2 (frameE8Root_coord_even i)⟩

theorem neg_mem_kernelRoots_frameChar8 {α : Fin Tag.E8.rank → ℤ}
    (hα : α ∈ kernelRoots frameChar8) : -α ∈ kernelRoots frameChar8 := by
  refine ⟨IsRoot.neg hα.1, ?_⟩
  obtain ⟨h0, h3, h5, h7⟩ := (frameChar8_eq_one_iff α).1 hα.2
  refine (frameChar8_eq_one_iff (-α)).2 ?_
  simp only [Pi.neg_apply]
  omega

theorem eq_frame_of_mem_kernelRoots {α : Fin Tag.E8.rank → ℤ}
    (hα : α ∈ kernelRoots frameChar8) :
    ∃ i : Fin 8, α = frameE8Root i ∨ α = -frameE8Root i := by
  obtain ⟨hroot, hker⟩ := hα
  obtain ⟨h0, h3, h5, h7⟩ := (frameChar8_eq_one_iff α).1 hker
  have key : ∀ β ∈ rootFinset .E8, β 0 % 2 = 0 → β 3 % 2 = 0 → β 5 % 2 = 0 → β 7 % 2 = 0 →
      ∃ i : Fin 8, β = frameE8Root i ∨ β = -frameE8Root i := by
    decide +kernel
  exact key α (mem_rootFinset.2 hroot) h0 h3 h5 h7

@[expose] def frameW8 : WeylGroup Tag.E8 :=
  ((List.finRange 8).map fun i => rootReflection (frameE8Root i)).prod

theorem frameW8_smul_foldr (l : List (Fin 8)) (v : Fin Tag.E8.rank → ℤ) :
    (l.map fun i => rootReflection (frameE8Root i)).prod • v =
      l.foldr (fun i u => u - iform (frameE8Root i) u • frameE8Root i) v := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, mul_smul, ih, List.foldr_cons,
      rootReflection_smul_SL (τ := Tag.E8) (fun γ hγ => iform_self_of_isRoot_E8Fr hγ)
        (e8Frame_isRoot a)]

theorem frameW8_fold_single : ∀ k : Fin Tag.E8.rank,
    (List.finRange 8).foldr (fun i u => u - iform (frameE8Root i) u • frameE8Root i)
      (Pi.single k 1 : Fin Tag.E8.rank → ℤ) = -Pi.single k 1 := by
  decide +kernel

theorem frameW8_smul_single (k : Fin Tag.E8.rank) :
    frameW8 • (Pi.single k 1 : Fin Tag.E8.rank → ℤ) = -Pi.single k 1 := by
  rw [frameW8, frameW8_smul_foldr]
  exact frameW8_fold_single k

theorem frameW8_eq_qplusW : frameW8 = qplusW Tag.E8 :=
  ext_single fun k => by
    rw [frameW8_smul_single, qplusW_smul_single (τ := Tag.E8) (Or.inr rfl) k]

theorem frameW8_smul (u : Fin Tag.E8.rank → ℤ) : frameW8 • u = -u := by
  rw [frameW8_eq_qplusW]
  exact qplusW_smul (τ := Tag.E8) (Or.inr rfl) u

theorem eq_frameW8_of_smul_neg {w : WeylGroup Tag.E8} (hw : ∀ u : Fin Tag.E8.rank → ℤ, w • u = -u) :
    w = frameW8 :=
  FaithfulSMul.eq_of_smul_eq_smul (α := Fin Tag.E8.rank → ℤ) fun u => by
    rw [hw u, frameW8_smul]

theorem frameW8_mem_closure :
    frameW8 ∈ Subgroup.closure ((fun α => rootReflection α) '' kernelRoots frameChar8) := by
  unfold frameW8
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact Subgroup.subset_closure ⟨frameE8Root i, frameE8Root_mem_kernelRoots i, rfl⟩

@[expose] def frameCore8 (L : Type) [Field L] : Subgroup (ModGL Tag.E8 L) :=
  torusGroup Tag.E8 L ⊔ rootSpan Tag.E8 L (kernelRoots frameChar8)

theorem frameCore8_le_frameSpan8 {L : Type} [Field L] [IsAlgClosed L] :
    frameCore8 L ≤ frameSpan8 L := by
  unfold frameCore8
  refine sup_le (torusGroup_le_frameSpan8 (L := L) fun x =>
    IsAlgClosed.exists_pow_nat_eq x two_pos) ?_
  unfold rootSpan
  refine iSup₂_le fun α hα => ?_
  have hrange : ∀ j : Fin 8, (rootSL2 Tag.E8 L (frameE8Root j)).range ≤ frameSpan8 L := fun j =>
    le_iSup (fun k : Fin 8 => (rootSL2 Tag.E8 L (frameE8Root k)).range) j
  obtain ⟨i, rfl | rfl⟩ := eq_frame_of_mem_kernelRoots hα
  · exact (le_sup_left.trans (range_rootSL2_of_isRoot (K := L)
      (e8Frame_isRoot i)).symm.le).trans (hrange i)
  · exact (le_sup_right.trans (range_rootSL2_of_isRoot (K := L)
      (e8Frame_isRoot i)).symm.le).trans (hrange i)

theorem frameCore8_le_adjointGroup {L : Type} [Field L] :
    frameCore8 L ≤ adjointGroup Tag.E8 L :=
  sup_le CFSG.RankThree.PartOne.KE.torusGroup_le_adjointGroup'
    (rootSpan_le_adjointGroup L _)

theorem canonicalRep_mem_frameCore8_of_closure {L : Type} [Field L] {y : WeylGroup Tag.E8}
    (hy : y ∈ Subgroup.closure ((fun α => rootReflection α) '' kernelRoots frameChar8)) :
    canonicalRep (coxeterSystem Tag.E8) L y ∈ frameCore8 L := by
  let R : Subgroup (WeylGroup Tag.E8) :=
    { carrier := {x | canonicalRep (coxeterSystem Tag.E8) L x ∈ frameCore8 L}
      mul_mem' := fun {x x'} hx hx' => by
        obtain ⟨k, hk, hkk⟩ := canonicalRep_mul_mem (τ := Tag.E8) (R := L) x x'
        have hmul : canonicalRep (coxeterSystem Tag.E8) L (x * x') =
            k⁻¹ * (canonicalRep (coxeterSystem Tag.E8) L x *
              canonicalRep (coxeterSystem Tag.E8) L x') := by
          rw [hkk]
          group
        show canonicalRep (coxeterSystem Tag.E8) L (x * x') ∈ frameCore8 L
        rw [hmul]
        exact mul_mem (inv_mem (Subgroup.mem_sup_left hk)) (mul_mem hx hx')
      one_mem' := by
        show canonicalRep (coxeterSystem Tag.E8) L 1 ∈ frameCore8 L
        rw [canonicalRep_one]
        exact one_mem _
      inv_mem' := fun {x} hx => by
        obtain ⟨k, hk, hkk⟩ := canonicalRep_mul_mem (τ := Tag.E8) (R := L) x x⁻¹
        rw [mul_inv_cancel, canonicalRep_one, mul_one] at hkk
        have hinv : canonicalRep (coxeterSystem Tag.E8) L x⁻¹ =
            (canonicalRep (coxeterSystem Tag.E8) L x)⁻¹ * k := by
          rw [← hkk]
          group
        show canonicalRep (coxeterSystem Tag.E8) L x⁻¹ ∈ frameCore8 L
        rw [hinv]
        exact mul_mem (inv_mem hx) (Subgroup.mem_sup_left hk) }
  have hgen : ∀ r ∈ (fun α => rootReflection α) '' kernelRoots frameChar8, r ∈ R := by
    rintro r ⟨α, hα, rfl⟩
    show canonicalRep (coxeterSystem Tag.E8) L (rootReflection α) ∈ frameCore8 L
    have hn := canonicalRep_rootReflection_mem (τ := Tag.E8) (K := L) hα.1
    have hsub : rootSubgroup Tag.E8 L α ⊔ rootSubgroup Tag.E8 L (-α) ≤ frameCore8 L :=
      sup_le ((rootSubgroup_le_rootSpan (τ := Tag.E8) (K := L) hα).trans le_sup_right)
        ((rootSubgroup_le_rootSpan (τ := Tag.E8) (K := L)
          (neg_mem_kernelRoots_frameChar8 hα)).trans le_sup_right)
    exact (sup_le le_sup_left hsub) hn
  exact (Subgroup.closure_le R).2 (fun r hr => hgen r hr) hy

section Lang

variable {L : Type} [Field L] [IsAlgClosed L] (ℓ : ℕ) [Fact ℓ.Prime] [CharP L ℓ]

theorem entrywiseFrobGL_mem_frameCore8 (e : ℕ) {g : ModGL Tag.E8 L} (hg : g ∈ frameCore8 L) :
    entrywiseFrobGL Tag.E8 L ℓ e g ∈ frameCore8 L := by
  have hmap : (frameCore8 L).map (entrywiseFrobGL Tag.E8 L ℓ e) ≤ frameCore8 L := by
    rw [frameCore8, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨h, hh, rfl⟩
      obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
      rw [entrywiseFrobGL_rootDiagUnit_eq_map]
      exact Subgroup.mem_sup_left (rootDiagUnit_mem_torusGroup _)
    · rw [rootSpan, Subgroup.map_iSup]
      refine iSup_le fun α => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hα => ?_
      rw [rootSubgroup, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
      exact Subgroup.mem_sup_right (le_iSup₂_of_le (f := fun β (_ : β ∈ kernelRoots frameChar8) =>
        rootSubgroup Tag.E8 L β) α hα le_rfl (Subgroup.subset_closure
          ⟨iterateFrobenius L ℓ e c, (entrywiseFrobGL_pinnedX ℓ e α c).symm⟩))
  exact hmap ⟨g, hg, rfl⟩

theorem lang_frameCore8 (e : ℕ) (he : 1 ≤ e) :
    ∀ c ∈ frameCore8 L, ∃ z ∈ frameCore8 L, z⁻¹ * entrywiseFrobGL Tag.E8 L ℓ e z = c := by
  have hZ :=
    isConnectedAlgebraicSubgroup_torus_sup_rootSpan_kernelRoots (τ := Tag.E8) (k := L) frameChar8
  have hst : ∀ g ∈ frameCore8 L, frobTwistGL Tag.E8 L ℓ e 1 g ∈ frameCore8 L := fun g hg => by
    rw [frobTwistGL_apply, one_mul, inv_one, mul_one]
    exact entrywiseFrobGL_mem_frameCore8 ℓ e hg
  obtain ⟨-, -, -, hlang⟩ := exists_frobTwist_restriction ℓ hZ he 1 hst
  intro c hc
  obtain ⟨z, hz, hzc⟩ := hlang c hc
  exact ⟨z, hz, by rw [frobTwistGL_apply, one_mul, inv_one, mul_one] at hzc; exact hzc⟩

end Lang

end CFSG.LieType.SeitzGeneration.ExcHigh
