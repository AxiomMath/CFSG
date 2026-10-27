module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcParKindDefs
public import CFSG.LieType.Chevalley.KernelComponentRoots

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem exc_exists_linearExt {τ : Tag} (w : WeylGroup τ) :
    ∃ L : (Fin τ.rank → ℚ) →ₗ[ℚ] (Fin τ.rank → ℚ), ∀ x : Fin τ.rank → ℤ,
      L (excToQ x) = excToQ (w • x) := by
  refine ⟨Matrix.toLin' ((LinearMap.toMatrix'
    (CFSG.LieType.RootSystem.weylAction (isFiniteType_cartan τ) w)).map
    (Int.castRingHom ℚ)), ?_⟩
  intro x
  rw [Matrix.toLin'_apply]
  funext i
  change Matrix.mulVec ((LinearMap.toMatrix'
    (CFSG.LieType.RootSystem.weylAction (isFiniteType_cartan τ) w)).map
    (Int.castRingHom ℚ)) ((Int.castRingHom ℚ) ∘ x) i = excToQ (w • x) i
  rw [← RingHom.map_mulVec, LinearMap.toMatrix'_mulVec, smul_def]
  rfl

private theorem exc_reflection_det_aux1 {τ : Tag} {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (x : Fin τ.rank → ℤ) :
    corootPair γ x = ∑ i, x i * corootPair γ (Pi.single i 1) := by
  have hp : CFSG.LieType.Steinberg.Adjoint.iform γ γ ≠ 0 :=
    (iform_self_pos_of_isRoot hγ).ne'
  refine mul_right_cancel₀ hp ?_
  calc corootPair γ x * CFSG.LieType.Steinberg.Adjoint.iform γ γ
      = 2 * CFSG.LieType.Steinberg.Adjoint.iform γ x := corootPair_mul hγ x
    _ = 2 * (∑ i, x i * CFSG.LieType.Steinberg.Adjoint.iform γ (Pi.single i 1)) := by
          congr 1
          conv_lhs => rw [pi_eq_sum_univ' x]
          rw [iform_finset_sum_right]
          exact Finset.sum_congr rfl fun i _ =>
            by rw [CFSG.LieType.Steinberg.Adjoint.iform_smul_right]
    _ = (∑ i, x i * corootPair γ (Pi.single i 1)) *
          CFSG.LieType.Steinberg.Adjoint.iform γ γ := by
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [mul_assoc, corootPair_mul hγ (Pi.single i 1)]
          ring

theorem exc_reflection_det {τ : Tag} {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (L : (Fin τ.rank → ℚ) →ₗ[ℚ] (Fin τ.rank → ℚ))
    (hL : ∀ x : Fin τ.rank → ℤ, L (excToQ x) = excToQ (rootReflection γ • x)) :
    LinearMap.det L = -1 := by
  let c : Fin τ.rank → ℤ := fun i => corootPair γ (Pi.single i 1)
  let f : Module.Dual ℚ (Fin τ.rank → ℚ) :=
    -∑ i, (c i : ℚ) • (LinearMap.proj i : (Fin τ.rank → ℚ) →ₗ[ℚ] ℚ)
  have hf_apply : ∀ v : Fin τ.rank → ℚ, f v = -∑ i, (c i : ℚ) * v i := by
    intro v
    simp only [f, LinearMap.neg_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, smul_eq_mul]
  have hf_single : ∀ i, f (Pi.single i (1 : ℚ)) = -(c i : ℚ) := by
    intro i
    rw [hf_apply (Pi.single i (1 : ℚ)), Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hbase : ∀ i, L (Pi.single i (1 : ℚ)) =
      LinearMap.transvection f (excToQ γ) (Pi.single i (1 : ℚ)) := by
    intro i
    have hLi := hL (Pi.single i 1)
    rw [excToQ_single] at hLi
    rw [hLi, LinearMap.transvection.apply, rootReflection_smul hγ,
      excToQ_sub, excToQ_zsmul, excToQ_single, hf_single i, neg_smul, sub_eq_add_neg]
  have hLt : L = LinearMap.transvection f (excToQ γ) := by
    refine LinearMap.pi_ext fun i x => ?_
    have hx : (Pi.single i x : Fin τ.rank → ℚ) =
        x • (Pi.single i (1 : ℚ) : Fin τ.rank → ℚ) := by
      rw [← Pi.single_smul', smul_eq_mul, mul_one]
    rw [hx, map_smul, map_smul, hbase i]
  have hcc : corootPair γ γ = 2 :=
    mul_right_cancel₀ (iform_self_pos_of_isRoot hγ).ne' (corootPair_mul hγ γ)
  have hfγ : f (excToQ γ) = -2 := by
    rw [hf_apply (excToQ γ)]
    have hsum : (∑ i, (c i : ℚ) * (excToQ γ) i) = ((∑ i, γ i * c i : ℤ) : ℚ) := by
      simp only [excToQ_apply]
      push_cast
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsum, ← exc_reflection_det_aux1 hγ γ, hcc]
    norm_num
  rw [hLt, LinearMap.transvection.det, hfγ]
  norm_num

end CFSG.LocalAnalysis.GLTheoremA.I167

end
