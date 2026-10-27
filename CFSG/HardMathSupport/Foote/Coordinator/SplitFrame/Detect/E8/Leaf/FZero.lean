module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.CaseData
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.ConjSub
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.MPart
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
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint Heis
open scoped MatrixGroups

set_option linter.unusedSectionVars false

local notation "tv" => Matrix.SpecialLinearGroup.transvection

namespace FZero

section Mat

variable {K : Type} [Field K]

theorem ne04 : (0 : Fin 5) ≠ 4 := by decide
theorem ne40 : (4 : Fin 5) ≠ 0 := by decide

theorem tv_comm (k l : Fin 5) (hkl : k ≠ l)
    (hcase : (l = 0 ∧ (k = 1 ∨ k = 2 ∨ k = 3)) ∨ (k = 4 ∧ (l = 1 ∨ l = 2 ∨ l = 3))) (a f : K) :
    tv hkl a * tv ne40 f = tv ne40 f * tv hkl a := by
  have hl : l ≠ 4 := by
    rcases hcase with ⟨rfl, _⟩ | ⟨rfl, h⟩ <;> [decide; rcases h with rfl | rfl | rfl <;> decide]
  have hk : (0 : Fin 5) ≠ k := by
    rcases hcase with ⟨rfl, h⟩ | ⟨rfl, _⟩ <;> [rcases h with rfl | rfl | rfl <;> decide; decide]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
    mul_add, add_mul, mul_one, one_mul]
  rw [Matrix.single_mul_single_of_ne a k l 4 hl f, Matrix.single_mul_single_of_ne f 4 0 k hk a]
  abel

theorem eq_zero_of_commute (k l : Fin 5) (hkl : k ≠ l)
    (hcase : (l = 0 ∧ (k = 1 ∨ k = 2 ∨ k = 3)) ∨ (k = 4 ∧ (l = 1 ∨ l = 2 ∨ l = 3))) (a f : K)
    (h : Commute (tv ne04 (1 : K) * (tv hkl a * tv ne40 f) * (tv ne04 (1 : K))⁻¹ *
      (tv hkl a * tv ne40 f)⁻¹) (tv ne04 (1 : K))) : f = 0 := by
  have h1 := congrArg (fun X : SL(5, K) => (X : Matrix (Fin 5) (Fin 5) K) 0 0) h.eq
  simp only [mul_inv_rev, Matrix.SpecialLinearGroup.transvection_inv,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe] at h1
  rcases hcase with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ <;>
    (simp [Matrix.mul_apply, Fin.sum_univ_five, Matrix.single_apply] at h1
     exact mul_self_eq_zero.1 (by linear_combination h1))

end Mat

open scoped Matrix in
open CFSG.RankThree.E6 CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice in
theorem deg_neg_one_pos : ∀ k l : Fin 5, k ≠ l →
    (wordMat Tag.E8 e8WordB *ᵥ chainRoot e8a4chain k l) 7 = -1 →
      (l = 0 ∧ (k = 1 ∨ k = 2 ∨ k = 3)) ∨ (k = 4 ∧ (l = 1 ∨ l = 2 ∨ l = 3)) := by
  decide +kernel

theorem e8ListA_deg : ∀ r ∈ e8ListA, r 7 = 0 := by decide +kernel

end FZero


namespace FZero

open scoped Matrix in
open CFSG.RankThree.E6 CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice in
theorem exists_frame_pinned (K : Type) [Field K] :
    ∃ ψ : SL(5, K) →* ModGL Tag.E8 K, Function.Injective ψ ∧
      (∃ ε : Kˣ, ∀ t : K, ψ (tv ne04 t) = pinnedX Tag.E8 K theta ((ε : K) * t)) ∧
      (∃ ε : Kˣ, ∀ t : K, ψ (tv ne40 t) = pinnedX Tag.E8 K (-theta) ((ε : K) * t)) ∧
      ∀ ν ∈ pureNegDirs, ∃ (k l : Fin 5) (hkl : k ≠ l) (ε : Kˣ),
        (∀ t : K, ψ (tv hkl t) = pinnedX Tag.E8 K ν ((ε : K) * t)) ∧
          ((l = 0 ∧ (k = 1 ∨ k = 2 ∨ k = 3)) ∨ (k = 4 ∧ (l = 1 ∨ l = 2 ∨ l = 3))) := by
  have hsig : ∀ i j : Fin 5, sigmaRootE8A4 e8VB i j =
      wordMat Tag.E8 e8WordB *ᵥ chainRoot e8a4chain i j := fun i j => by
    rw [sigmaRootE8A4_eq_smul, e8VB_smul]
  have h04 : sigmaRootE8A4 e8VB 0 4 = theta := by
    rw [hsig]
    decide +kernel
  have h40 : sigmaRootE8A4 e8VB 4 0 = -theta := by
    rw [hsig]
    decide +kernel
  refine ⟨rhoSigmaE8A4 K e8VB, rhoSigmaE8A4_injective e8VB, ?_, ?_, ?_⟩
  · obtain ⟨ε, h⟩ := rhoSigmaE8A4_transvection (L := K) e8VB 0 4 ne04
    exact ⟨ε, fun t => by rw [h t, h04]⟩
  · obtain ⟨ε, h⟩ := rhoSigmaE8A4_transvection (L := K) e8VB 4 0 ne40
    exact ⟨ε, fun t => by rw [h t, h40]⟩
  · intro ν hν
    obtain ⟨hroot, hdeg, h4⟩ := mem_pureNegDirs.1 hν
    have hB : ν ∈ e8ListB := by
      rcases S_data ν (mem_rootFinset.2 hroot) h4 with hA | hB
      · have := e8ListA_deg ν hA
        exact False.elim (by omega)
      · exact hB
    obtain ⟨k, l, hkl, hνkl⟩ := e8B_cover ν hB
    have hcase := deg_neg_one_pos k l hkl (by rw [← hνkl]; exact hdeg)
    obtain ⟨ε, h⟩ := rhoSigmaE8A4_transvection (L := K) e8VB k l hkl
    exact ⟨k, l, hkl, ε, fun t => by rw [h t, hsig, ← hνkl], hcase⟩

end FZero

theorem eq_of_pure_class_two (K : Type) [Field K] [Finite K] {D : Subgroup (ModGL Tag.E8 K)}
    (hD : IsLongRootSubgroup Tag.E8 K D) {ν : Fin Tag.E8.rank → ℤ} (hν : ν ∈ pureNegDirs)
    (hle : D ≤ rootSpan Tag.E8 K {ν, -theta})
    (hcl : ∀ u ∈ Uθ Tag.E8 K, ∀ d ∈ D, Commute (u * d * u⁻¹ * d⁻¹) u) :
    D = rootSubgroup Tag.E8 K ν := by
  obtain ⟨ψ, hinj, ⟨εθ, hθ⟩, ⟨εn, hn⟩, hpos⟩ := FZero.exists_frame_pinned K
  obtain ⟨k, l, hkl, ε, hε, hcase⟩ := hpos ν hν
  have hrep : ∀ a : K, pinnedX Tag.E8 K ν a = ψ (tv hkl (((ε⁻¹ : Kˣ) : K) * a)) := fun a => by
    rw [hε, Units.mul_inv_cancel_left]
  have hrep' : ∀ f : K, pinnedX Tag.E8 K (-theta) f =
      ψ (tv FZero.ne40 (((εn⁻¹ : Kˣ) : K) * f)) := fun f => by
    rw [hn, Units.mul_inv_cancel_left]
  have hsup : rootSpan Tag.E8 K {ν, -theta} =
      rootSubgroup Tag.E8 K ν ⊔ rootSubgroup Tag.E8 K (-theta) := by
    simp only [rootSpan, iSup_insert, iSup_singleton]
  have hcomm : ∀ x ∈ rootSubgroup Tag.E8 K ν, ∀ y ∈ rootSubgroup Tag.E8 K (-theta),
      x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, rfl⟩ := mem_rootSubgroup.1 hx
    obtain ⟨f, rfl⟩ := mem_rootSubgroup.1 hy
    rw [hrep a, hrep' f, ← map_mul, ← map_mul, FZero.tv_comm k l hkl hcase]
  have hnorm : rootSubgroup Tag.E8 K ν ≤
      Subgroup.normalizer (rootSubgroup Tag.E8 K (-theta) : Set (ModGL Tag.E8 K)) :=
    fun x hx => mem_normalizer_of_forall_mul_eq fun y hy => hcomm x hx y hy
  have hDle : D ≤ rootSubgroup Tag.E8 K ν := by
    intro d hd
    have hd' : d ∈ (↑(rootSubgroup Tag.E8 K ν ⊔ rootSubgroup Tag.E8 K (-theta)) :
        Set (ModGL Tag.E8 K)) := by
      have := hle hd
      rwa [hsup] at this
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at hd'
    obtain ⟨x, hx, y, hy, rfl⟩ := hd'
    obtain ⟨a, rfl⟩ := mem_rootSubgroup.1 hx
    obtain ⟨f, rfl⟩ := mem_rootSubgroup.1 hy
    have hu : pinnedX Tag.E8 K theta ((εθ : K) * 1) ∈ Uθ Tag.E8 K :=
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
  haveI : Finite (rootSubgroup Tag.E8 K ν) :=
    Finite.of_equiv _ (rootSubgroupEquiv Tag.E8 K ν).toEquiv
  refine Subgroup.eq_of_le_of_card_ge hDle ?_
  obtain ⟨g, -, rfl⟩ := hD
  rw [card_rootSubgroup, conjSub, Subgroup.card_map_of_injective (MulAut.conj g).injective,
    card_rootSubgroup]

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
