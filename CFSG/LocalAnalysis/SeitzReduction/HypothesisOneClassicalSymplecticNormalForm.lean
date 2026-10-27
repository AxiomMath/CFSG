module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalBasic
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpInner

public section

namespace CFSG.SeitzReduction

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.ComponentClassification.CatalogueBSymplecticB (semilinearCoordMap)

variable {r : ℕ} {K : Type} [Field K]

theorem spInner_mul_fieldAut_apply_proj (g : StatedSp r K) (φ : K ≃+* K) (c : StatedSp r K) :
    (spInner r K g * fieldAut r K φ) (proj r K c) = proj r K (g * fieldSp r K φ c * g⁻¹) := by
  rw [MulAut.mul_apply, fieldAut_proj, spInner_eq_conj, MulAut.conj_apply, ← map_inv, ← map_mul,
    ← map_mul]

theorem involutionCriterion_spInner_of_fixes [Finite K] [CharP K 2] (hr : 3 ≤ r)
    {s : StatedSp r K} {D : Subgroup (StatedSp r K)}
    (hD : D ≤ closure {c : StatedSp r K | c ∈ centralizer {s} ∧ Odd (orderOf c)})
    (h : ∀ (g : StatedSp r K) (φ : K ≃+* K), g * fieldSp r K φ s = s * g →
      (∀ d ∈ D, g * fieldSp r K φ d = d * g) → g * fieldSp r K φ g = 1 ∧ φ * φ = 1) :
    InvolutionCriterion (spInner r K s) := by
  have : NeZero r := ⟨by omega⟩
  have hπ : Function.Injective (proj r K) := UnitaryHigher.proj_bijective_of_charTwo.1
  intro β hβx hβc
  obtain ⟨g, φ, rfl⟩ := exists_eq_spInner_mul_fieldAut
    (show β ∈ spSemilinearAutGroup r K by rw [(automorphism_generation hr).1]; exact mem_top β)
  have hgs : g * fieldSp r K φ s = s * g := by
    have h1 : spInner r K g * fieldAut r K φ * spInner r K s *
        (spInner r K g * fieldAut r K φ)⁻¹ = spInner r K s := by
      rw [hβx, mul_inv_cancel_right]
    rw [conj_spInner] at h1
    have h2 := spInner_injective h1
    calc g * fieldSp r K φ s = g * fieldSp r K φ s * g⁻¹ * g := by group
      _ = s * g := by rw [h2]
  have hfix : ∀ d ∈ closure {c : StatedSp r K | c ∈ centralizer {s} ∧ Odd (orderOf c)},
      (spInner r K g * fieldAut r K φ) (proj r K d) = proj r K d := by
    intro d hd
    induction hd using closure_induction with
    | mem c hc =>
      refine hβc _ ?_ ?_
      · rw [spInner_eq_conj, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul,
          ← mem_centralizer_singleton_iff.1 hc.1, mul_inv_cancel_right]
      · rw [orderOf_injective _ hπ c]
        exact hc.2
    | one => rw [map_one, map_one]
    | mul c d _ _ hc hd => rw [map_mul, map_mul, hc, hd]
    | inv c _ hc => rw [map_inv, map_inv, hc]
  have hgd : ∀ d ∈ D, g * fieldSp r K φ d = d * g := by
    intro d hd
    have h1 := hfix d (hD hd)
    rw [spInner_mul_fieldAut_apply_proj] at h1
    have h2 := hπ h1
    calc g * fieldSp r K φ d = g * fieldSp r K φ d * g⁻¹ * g := by group
      _ = d * g := by rw [h2]
  obtain ⟨hgg, hφφ⟩ := h g φ hgs hgd
  rw [sq, spInner_mul_fieldAut_mul, hgg, hφφ, map_one, map_one, one_mul]

theorem involutionCriterion_spInner_of_semilinear [Finite K] [CharP K 2] (hr : 3 ≤ r)
    {s : StatedSp r K} {D : Subgroup (StatedSp r K)}
    (hD : D ≤ closure {c : StatedSp r K | c ∈ centralizer {s} ∧ Odd (orderOf c)})
    (h : ∀ (g : StatedSp r K) (φ : K ≃+* K),
      (∀ v, semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) φ (spMat s *ᵥ v) =
        spMat s *ᵥ semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) φ v) →
      (∀ d ∈ D, ∀ v, semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) φ (spMat d *ᵥ v) =
        spMat d *ᵥ semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) φ v) →
      (∀ a, φ a = a) ∧ ∀ v, semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) φ
        (semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) φ v) = v) :
    InvolutionCriterion (spInner r K s) := by
  refine involutionCriterion_spInner_of_fixes hr hD fun g φ hgs hgd => ?_
  obtain ⟨hφ, hTT⟩ := h g φ (semilinearCoordMap_mulVec_of_mul_eq hgs)
    fun d hd => semilinearCoordMap_mulVec_of_mul_eq (hgd d hd)
  obtain rfl : φ = 1 := RingEquiv.ext hφ
  have hT : ∀ w, semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) 1 w = spMat g *ᵥ w :=
    fun _ => rfl
  refine ⟨?_, mul_one 1⟩
  rw [map_one, MulAut.one_apply]
  refine statedSp_ext fun v => ?_
  rw [spMat_mul_mulVec, ← hT, ← hT, hTT]
  exact (one_mulVec v).symm

theorem mul_self_eq_one_of_spMat_mul_self_eq_smul [NeZero r] [CharP K 2] {g : StatedSp r K}
    {a : K} (h : spMat g * spMat g = a • 1) : g * g = 1 := by
  have hgg := SymplecticTorusWeyl.mem_statedSp_iff.mp (g * g).2
  have hsq : spMat (g * g) = a • 1 := h
  change (spMat (g * g))ᵀ * fromBlocks 0 1 (-1) 0 * spMat (g * g) = fromBlocks 0 1 (-1) 0 at hgg
  rw [hsq, Matrix.smul_one_eq_diagonal, ← Matrix.scalar_apply] at hgg
  have h1 : Matrix.scalar (Fin r ⊕ Fin r) a ∈ symplecticGroup (Fin r) K :=
    (CFSG.ClassicalGroups.Symplectic.blueprintGram_iff_mem_symplecticGroup _).mp hgg
  have h2 := (CFSG.ClassicalGroups.Symplectic.scalar_mem_symplecticGroup_iff
    (Nat.pos_of_neZero r) a).mp h1
  have ha : a = 1 := by
    rcases (mul_self_eq_one_iff (a := a)).mp (by rw [← sq]; exact h2) with h3 | h3
    · exact h3
    · rw [h3, CharTwo.neg_eq]
  refine statedSp_ext fun v => ?_
  rw [hsq, ha, one_smul]
  rfl

theorem semilinearCoordMap_symm_mulVec_of_commute {g s : StatedSp r K} {φ : K ≃+* K}
    (hT : ∀ v, semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) φ (spMat s *ᵥ v) =
      spMat s *ᵥ semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) φ v) (v : Fin r ⊕ Fin r → K) :
    (semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) φ).symm (spMat s *ᵥ v) =
      spMat s *ᵥ (semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) φ).symm v := by
  apply (semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) φ).injective
  rw [AddEquiv.apply_symm_apply, hT, AddEquiv.apply_symm_apply]

theorem semilinearCoordMap_mem_displacement {g s : StatedSp r K} {φ : K ≃+* K}
    (hT : ∀ v, semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) φ (spMat s *ᵥ v) =
      spMat s *ᵥ semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) φ v)
    {w : Fin r ⊕ Fin r → K} (hw : w ∈ displacement s) :
    semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) φ w ∈ displacement s := by
  obtain ⟨v, rfl⟩ := mem_displacement.mp hw
  exact mem_displacement.mpr ⟨semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) φ v, by
    rw [map_sub, hT]⟩

theorem semilinearCoordMap_symm_mem_displacement {g s : StatedSp r K} {φ : K ≃+* K}
    (hT : ∀ v, semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) φ (spMat s *ᵥ v) =
      spMat s *ᵥ semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) φ v)
    {w : Fin r ⊕ Fin r → K} (hw : w ∈ displacement s) :
    (semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) φ).symm w ∈ displacement s := by
  obtain ⟨v, rfl⟩ := mem_displacement.mp hw
  exact mem_displacement.mpr ⟨(semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) φ).symm v, by
    rw [map_sub, semilinearCoordMap_symm_mulVec_of_commute hT]⟩

theorem semilinearCoordMap_mem_orthogonal_displacement {g s : StatedSp r K} {φ : K ≃+* K}
    (hT : ∀ v, semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) φ (spMat s *ᵥ v) =
      spMat s *ᵥ semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) φ v)
    {l : Fin r ⊕ Fin r → K} (hl : l ∈ (pairedSympForm K r).orthogonal (displacement s)) :
    semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) φ l ∈
      (pairedSympForm K r).orthogonal (displacement s) := by
  refine LinearMap.BilinForm.mem_orthogonal_iff.mpr fun w hw => ?_
  have h1 := LinearMap.BilinForm.mem_orthogonal_iff.mp hl _
    (semilinearCoordMap_symm_mem_displacement hT hw)
  rw [← (semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) φ).apply_symm_apply w,
    pairedSympForm_semilinearCoordMap, h1, map_zero]

theorem displacement_ne_bot_of_ne_one {s : StatedSp r K} (hs1 : s ≠ 1) : displacement s ≠ ⊥ := by
  intro hbot
  refine hs1 (statedSp_ext fun v => ?_)
  have h1 : spMat s *ᵥ v - v ∈ displacement s := mem_displacement.mpr ⟨v, rfl⟩
  rw [hbot, Submodule.mem_bot, sub_eq_zero] at h1
  rw [h1]
  exact (one_mulVec v).symm

theorem exists_pairedSympForm_eq_one_of_ne [CharP K 2] {s : StatedSp r K} (hs : s * s = 1)
    (hWL : displacement s ≠ (pairedSympForm K r).orthogonal (displacement s)) :
    ∃ x ∈ (pairedSympForm K r).orthogonal (displacement s),
      ∃ u ∈ (pairedSympForm K r).orthogonal (displacement s), pairedSympForm K r x u = 1 := by
  have hWL' : displacement s ≤ (pairedSympForm K r).orthogonal (displacement s) :=
    fun w hw => LinearMap.BilinForm.mem_orthogonal_iff.mpr fun n hn =>
      isTotallyIsotropic_displacement hs n hn w hw
  have hLL : (pairedSympForm K r).orthogonal ((pairedSympForm K r).orthogonal (displacement s)) =
      displacement s :=
    LinearMap.BilinForm.orthogonal_orthogonal SymplecticFlag.pairedSympForm_nondegenerate
      SymplecticFlag.pairedSympForm_isAlt.isRefl _
  obtain ⟨l, hlL, hlW⟩ : ∃ l ∈ (pairedSympForm K r).orthogonal (displacement s),
      l ∉ displacement s := by
    by_contra hcon
    push Not at hcon
    exact hWL (le_antisymm hWL' hcon)
  rw [← hLL, LinearMap.BilinForm.mem_orthogonal_iff] at hlW
  push Not at hlW
  obtain ⟨x, hxL, hx⟩ := hlW
  refine ⟨x, hxL, (pairedSympForm K r x l)⁻¹ • l, Submodule.smul_mem _ _ hlL, ?_⟩
  rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hx]

end CFSG.SeitzReduction
