module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L3Frame
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.LieType.Steinberg.CentralExt.PerfectLift

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Q5L3

open CFSG CFSG.ClassicalInvolution Matrix Q5GL2
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.IVK.Proofs2 CFSG.RankThree.SubgroupLists
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem commutator_mem_linearAutGroup [Finite K] {n : ℕ} (hn : 3 ≤ n)
    (α β : MulAut (projectiveSL n K)) : α * β * α⁻¹ * β⁻¹ ∈ linearAutGroup n K :=
  CFSG.LocalAnalysis.ComponentInitial.OuterDerived.commutator_mem_linearAutGroup hn α β

theorem mem_inner_of_pow [Finite K] {δ : MulAut (projectiveSL 3 K)}
    (hδ : δ ∈ linearAutGroup 3 K) {k : ℕ} (hk : δ ^ 2 ^ k = 1) :
    δ ∈ inner (projectiveSL 3 K) := by
  refine RankThree.PartOne.OutStructure.linear_D2 Nat.prime_two le_rfl (fun h => ?_) δ hδ k
    (by rw [hk]; exact Subgroup.one_mem _)
  have := h.trans (Nat.gcd_dvd_left 3 _)
  omega

theorem mul_mem_semilinearAutGroup [Finite K] {α β : MulAut (projectiveSL 3 K)}
    (hα : α ∉ semilinearAutGroup 3 K) (hβ : β ∉ semilinearAutGroup 3 K) :
    α * β ∈ semilinearAutGroup 3 K := by
  obtain ⟨hgenTop, -⟩ := automorphism_generation (K := K) (n := 3) le_rfl
  obtain ⟨-, -, -, -, -, -, -, hidx, -⟩ := standard_outer_quotients (n := 3) (K := K)
  have : Finite (MulAut (projectiveSL 3 K)) := ProjectivePlane.finite_mulAut_projectiveSL 3
  have hidx' : (semilinearAutGroup 3 K).index ≤ 2 := by
    have h2 : (semilinearAutGroup 3 K).relIndex (standardAutGroup 3 K) ≤ 2 := hidx
    rwa [hgenTop, Subgroup.relIndex_top_right] at h2
  have h0 : (semilinearAutGroup 3 K).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : (semilinearAutGroup 3 K).index ≠ 1 := fun h =>
    hα (Subgroup.index_eq_one.mp h ▸ Subgroup.mem_top α)
  exact (Subgroup.mul_mem_iff_of_index_two (by omega)).mpr (iff_of_false hα hβ)

theorem eq_one_of_fix [Finite K] (h4 : 4 ≤ Nat.card K) (φ : SL(2, K) →* SL(3, K))
    (hφ : ∀ B : SL(2, K), trace (φ B : Matrix (Fin 3) (Fin 3) K) =
      trace (B : Matrix (Fin 2) (Fin 2) K) + 1)
    {A : GL (Fin 3) K} {τ : K ≃+* K}
    (h : ∀ B : SL(2, K), (conjAut 3 K A * fieldAut 3 K τ) (proj 3 K (φ B)) = proj 3 K (φ B)) :
    τ = 1 := by
  have : Group.IsPerfect SL(2, K) := sl2_isPerfect h4
  have hker : (proj 3 K).ker ≤ Subgroup.center (SpecialLinearGroup (Fin 3) K) := by
    rw [ker_proj, scalars_eq_center]
  let β : SL(3, K) →* SL(3, K) :=
    (ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K A).toMonoidHom.comp
      (SpecialLinearGroup.map τ.toRingHom)
  have hβ : ∀ g, (conjAut 3 K A * fieldAut 3 K τ) (proj 3 K g) = proj 3 K (β g) := fun g => by
    rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj]
    rfl
  have heq : β.comp φ = φ := LieType.Steinberg.eq_of_comp_eq_of_isPerfect hker
    (MonoidHom.ext fun B => by
      show proj 3 K (β (φ B)) = proj 3 K (φ B)
      rw [← hβ, h])
  refine RingEquiv.ext fun x => ?_
  let B : SL(2, K) := ⟨!![x, -1; 1, 0], by simp [Matrix.det_fin_two]⟩
  have hB := congrArg (fun g : SL(3, K) => trace (g : Matrix (Fin 3) (Fin 3) K))
    (DFunLike.congr_fun heq B)
  simp only [MonoidHom.comp_apply] at hB
  have hcoe : ((β (φ B) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      (A : Matrix (Fin 3) (Fin 3) K) * ((φ B : Matrix (Fin 3) (Fin 3) K).map τ) *
        ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    show ((ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K A
      (SpecialLinearGroup.map τ.toRingHom (φ B)) : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = _
    rw [LinearFlag.coe_slConjugation, SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
    rfl
  rw [hcoe, Matrix.trace_units_conj, ← AddMonoidHom.map_trace, hφ] at hB
  have htr : trace (B : Matrix (Fin 2) (Fin 2) K) = x := by
    simp [B, Matrix.trace_fin_two]
  rw [htr, map_add, map_one] at hB
  have hx : τ x = x := by simpa using hB
  exact hx

theorem mem_linearAutGroup_of_fix [Finite K] (h4 : 4 ≤ Nat.card K) (φ : SL(2, K) →* SL(3, K))
    (hφ : ∀ B : SL(2, K), trace (φ B : Matrix (Fin 3) (Fin 3) K) =
      trace (B : Matrix (Fin 2) (Fin 2) K) + 1)
    {α : MulAut (projectiveSL 3 K)} (hα : α ∈ semilinearAutGroup 3 K)
    (h : ∀ B : SL(2, K), α (proj 3 K (φ B)) = proj 3 K (φ B)) : α ∈ linearAutGroup 3 K := by
  obtain ⟨A, τ, rfl⟩ := mem_semilinearAutGroup_iff.mp hα
  rw [eq_one_of_fix h4 φ hφ h, map_one, mul_one]
  exact conjAut_mem_linearAutGroup A

theorem trace_blkP (Q : GL (Fin 3) K) (B : SL(2, K)) :
    trace (blkP Q (SpecialLinearGroup.toGL B) : Matrix (Fin 3) (Fin 3) K) =
      trace (B : Matrix (Fin 2) (Fin 2) K) + 1 := by
  show trace ((Q * Lemma41aL3.blk (SpecialLinearGroup.toGL B) * Q⁻¹ : GL (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) = _
  rw [Units.val_mul, Units.val_mul, Matrix.trace_units_conj, Lemma41aL3.coe_blk]
  simp [Lemma41aL3.blkMat, Matrix.trace_fin_three, Matrix.trace_fin_two, B.2]

end CFSG.ClassicalInvolution.Q3.TA3.Q5L3
