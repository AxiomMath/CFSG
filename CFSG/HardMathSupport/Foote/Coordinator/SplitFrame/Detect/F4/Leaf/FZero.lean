module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.CaseData
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.F4.MPart
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.GroupTheory
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.NormalForm
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalPairing
public import CFSG.LieType.Chevalley.OrdinaryRootHyperplaneGeneration
public import CFSG.LieType.Chevalley.ParabolicRadicalNormalizer
public import CFSG.LieType.Chevalley.ParabolicRadicalsOpposite
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.SLnShape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open Heis
open scoped MatrixGroups

set_option linter.unusedSectionVars false

local notation "tv" => Matrix.SpecialLinearGroup.transvection

namespace FZero

section Mat

variable {K : Type} [Field K]

theorem ne10 : (1 : Fin 3) ≠ 0 := by decide
theorem ne20 : (2 : Fin 3) ≠ 0 := by decide
theorem ne21 : (2 : Fin 3) ≠ 1 := by decide
theorem ne02 : (0 : Fin 3) ≠ 2 := by decide

theorem tv_comm (k l : Fin 3) (hkl : k ≠ l) (hcase : (k = 1 ∧ l = 0) ∨ (k = 2 ∧ l = 1))
    (a f : K) : tv hkl a * tv ne20 f = tv ne20 f * tv hkl a := by
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> apply Subtype.ext <;>
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe] <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply]

theorem eq_zero_of_commute (k l : Fin 3) (hkl : k ≠ l)
    (hcase : (k = 1 ∧ l = 0) ∨ (k = 2 ∧ l = 1)) (a f : K)
    (h : Commute (tv ne02 (1 : K) * (tv hkl a * tv ne20 f) * (tv ne02 (1 : K))⁻¹ *
      (tv hkl a * tv ne20 f)⁻¹) (tv ne02 (1 : K))) : f = 0 := by
  have h1 := congrArg (fun X : SL(3, K) => (X : Matrix (Fin 3) (Fin 3) K) 0 0) h.eq
  simp only [mul_inv_rev, Matrix.SpecialLinearGroup.transvection_inv,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe] at h1
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    (simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply] at h1
     exact mul_self_eq_zero.1 (by linear_combination h1))

end Mat

end FZero


namespace FZero

open CFSG.RankThree.PartOne.KF4 CFSG.RankThree.E6 CFSG.RankThree.Lattice in
theorem exists_frame_pinned (K : Type) [Field K] :
    ∃ ψ : SL(3, K) →* ModGL Tag.F4 K, Function.Injective ψ ∧
      (∃ ε : Kˣ, ∀ t : K, ψ (tv ne02 t) = pinnedX Tag.F4 K theta ((ε : K) * t)) ∧
      (∃ ε : Kˣ, ∀ t : K, ψ (tv ne20 t) = pinnedX Tag.F4 K (-theta) ((ε : K) * t)) ∧
      (∃ ε : Kˣ, ∀ t : K, ψ (tv ne10 t) = pinnedX Tag.F4 K (-alpha1) ((ε : K) * t)) ∧
      (∃ ε : Kˣ, ∀ t : K, ψ (tv ne21 t) = pinnedX Tag.F4 K (-root1342) ((ε : K) * t)) := by
  have hA := (f4Long_frame (L := K)).transport f4LongV
  have hv : (wordMat Tag.F4 f4LongWord).mulVec (chainRoot f4chainLong (0 : Fin 3) 2) = theta ∧
      (wordMat Tag.F4 f4LongWord).mulVec (chainRoot f4chainLong (2 : Fin 3) 0) = -theta ∧
      (wordMat Tag.F4 f4LongWord).mulVec (chainRoot f4chainLong (1 : Fin 3) 0) = -alpha1 ∧
      (wordMat Tag.F4 f4LongWord).mulVec (chainRoot f4chainLong (2 : Fin 3) 1) = -root1342 := by
    decide +kernel
  obtain ⟨h1, h2, h3, h4⟩ := hv
  refine ⟨_, hA.injective, ?_, ?_, ?_, ?_⟩
  · obtain ⟨ε, h⟩ := hA.transv 0 2 ne02
    exact ⟨ε, fun t => by rw [h t, f4LongV_smul, h1]⟩
  · obtain ⟨ε, h⟩ := hA.transv 2 0 ne20
    exact ⟨ε, fun t => by rw [h t, f4LongV_smul, h2]⟩
  · obtain ⟨ε, h⟩ := hA.transv 1 0 ne10
    exact ⟨ε, fun t => by rw [h t, f4LongV_smul, h3]⟩
  · obtain ⟨ε, h⟩ := hA.transv 2 1 ne21
    exact ⟨ε, fun t => by rw [h t, f4LongV_smul, h4]⟩

end FZero

theorem eq_of_pure_class_two (K : Type) [Field K] [Finite K] {D : Subgroup (ModGL Tag.F4 K)}
    (hD : IsLongRootSubgroup Tag.F4 K D) {ν : Fin Tag.F4.rank → ℤ}
    (hν : ν = -alpha1 ∨ ν = -root1342) (hle : D ≤ rootSpan Tag.F4 K {ν, -theta})
    (hcl : ∀ u ∈ Uθ Tag.F4 K, ∀ d ∈ D, Commute (u * d * u⁻¹ * d⁻¹) u) :
    D = rootSubgroup Tag.F4 K ν := by
  obtain ⟨ψ, hinj, ⟨εθ, hθ⟩, ⟨εn, hn⟩, hα, hr⟩ := FZero.exists_frame_pinned K
  obtain ⟨k, l, hkl, ε, hε, hcase⟩ : ∃ (k l : Fin 3) (hkl : k ≠ l) (ε : Kˣ),
      (∀ t : K, ψ (tv hkl t) = pinnedX Tag.F4 K ν ((ε : K) * t)) ∧
        ((k = 1 ∧ l = 0) ∨ (k = 2 ∧ l = 1)) := by
    rcases hν with rfl | rfl
    · obtain ⟨ε, h⟩ := hα
      exact ⟨1, 0, FZero.ne10, ε, h, Or.inl ⟨rfl, rfl⟩⟩
    · obtain ⟨ε, h⟩ := hr
      exact ⟨2, 1, FZero.ne21, ε, h, Or.inr ⟨rfl, rfl⟩⟩
  have hrep : ∀ a : K, pinnedX Tag.F4 K ν a = ψ (tv hkl (((ε⁻¹ : Kˣ) : K) * a)) := fun a => by
    rw [hε, Units.mul_inv_cancel_left]
  have hrep' : ∀ f : K, pinnedX Tag.F4 K (-theta) f =
      ψ (tv FZero.ne20 (((εn⁻¹ : Kˣ) : K) * f)) := fun f => by
    rw [hn, Units.mul_inv_cancel_left]
  have hsup : rootSpan Tag.F4 K {ν, -theta} =
      rootSubgroup Tag.F4 K ν ⊔ rootSubgroup Tag.F4 K (-theta) := by
    simp only [rootSpan, iSup_insert, iSup_singleton]
  have hcomm : ∀ x ∈ rootSubgroup Tag.F4 K ν, ∀ y ∈ rootSubgroup Tag.F4 K (-theta),
      x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, rfl⟩ := mem_rootSubgroup.1 hx
    obtain ⟨f, rfl⟩ := mem_rootSubgroup.1 hy
    rw [hrep a, hrep' f, ← map_mul, ← map_mul, FZero.tv_comm k l hkl hcase]
  have hnorm : rootSubgroup Tag.F4 K ν ≤
      Subgroup.normalizer (rootSubgroup Tag.F4 K (-theta) : Set (ModGL Tag.F4 K)) :=
    fun x hx => mem_normalizer_of_forall_mul_eq fun y hy => hcomm x hx y hy
  have hDle : D ≤ rootSubgroup Tag.F4 K ν := by
    intro d hd
    have hd' : d ∈ (↑(rootSubgroup Tag.F4 K ν ⊔ rootSubgroup Tag.F4 K (-theta)) :
        Set (ModGL Tag.F4 K)) := by
      have := hle hd
      rwa [hsup] at this
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at hd'
    obtain ⟨x, hx, y, hy, rfl⟩ := hd'
    obtain ⟨a, rfl⟩ := mem_rootSubgroup.1 hx
    obtain ⟨f, rfl⟩ := mem_rootSubgroup.1 hy
    have hu : pinnedX Tag.F4 K theta ((εθ : K) * 1) ∈ Uθ Tag.F4 K :=
      mem_rootSubgroup.2 ⟨_, rfl⟩
    have h := hcl _ hu _ hd
    rw [← hθ 1, hrep a, hrep' f] at h
    have hf : (((εn⁻¹ : Kˣ) : K) * f) = 0 :=
      FZero.eq_zero_of_commute k l hkl hcase _ _
        (hinj (by simpa only [map_mul, map_inv] using h.eq))
    have hf0 : f = 0 := (mul_eq_zero.1 hf).resolve_left (Units.ne_zero _)
    beta_reduce
    rw [hf0, pinnedX_zero, mul_one]
    exact mem_rootSubgroup.2 ⟨a, rfl⟩
  haveI : Finite (rootSubgroup Tag.F4 K ν) :=
    Finite.of_equiv _ (rootSubgroupEquiv Tag.F4 K ν).toEquiv
  refine Subgroup.eq_of_le_of_card_ge hDle ?_
  obtain ⟨g, -, rfl⟩ := hD
  rw [card_rootSubgroup, conjSub, Subgroup.card_map_of_injective (MulAut.conj g).injective,
    card_rootSubgroup]

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectF4
