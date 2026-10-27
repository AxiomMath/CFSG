module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoRootSL2
public import CFSG.LieType.SeitzGeneration.ExcHigh.NativeCond
import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LeviCatalogueCentralizer
import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootQ1

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LieType.SeitzGeneration.ExcWideThree


theorem normalizesRGroup_of_fixed_killed_root (q : ℕ) (K : Type) [Field K] [Finite K]
    (σ : K ≃+* K) (hK : Nat.card K = q ^ 2) (hσ : ∀ c : K, σ c = c ^ q) (hr : ringChar K ≠ 3)
    (E₀ : Subgroup (twistedE6RootGroup K σ))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ q)
    (v : WeylGroup TwistTag.E6.tag) (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β)
    (hvβ : v • permLattice TwistTag.E6.perm β = -β)
    (hfix : ∀ x ∈ E₀, ∀ y ∈ rootSpan TwistTag.E6.tag (AlgebraicClosure K) {β, -β},
      Commute (g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (x : ModGL TwistTag.E6.tag K) * g0) y) :
    NormalizesRGroup (ringChar K) E₀ := by
  classical
  obtain ⟨X, Xm, ⟨g, hX, -⟩, hS⟩ :=
    exists_longRootPair_of_negDatum q K σ hK hσ hr Fr hFr v g0 hg0C hg0 hβ hvβ
  set ι := baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K (AlgebraicClosure K)) with hι
  have hcomm : ∀ x ∈ E₀, ∀ u ∈ X, x * u * x⁻¹ = u := by
    intro x hx u hu
    have huS : ι (u : ModGL TwistTag.E6.tag K) ∈
        (rootSpan TwistTag.E6.tag (AlgebraicClosure K) {β, -β}).map
          (MulAut.conj g0).toMonoidHom :=
      (hS u).1 (Subgroup.subset_closure (Or.inl hu))
    obtain ⟨y, hy, hyu⟩ := Subgroup.mem_map.1 huS
    have hyu' : g0 * y * g0⁻¹ = ι (u : ModGL TwistTag.E6.tag K) := hyu
    have hc : g0⁻¹ * ι x * g0 * y = y * (g0⁻¹ * ι x * g0) := (hfix x hx y hy).eq
    apply Subtype.ext
    apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
    change ι ((x : ModGL TwistTag.E6.tag K) * u * (x : ModGL TwistTag.E6.tag K)⁻¹) =
      ι (u : ModGL TwistTag.E6.tag K)
    rw [map_mul, map_mul, map_inv, ← hyu']
    calc ι x * (g0 * y * g0⁻¹) * (ι x)⁻¹
        = g0 * (g0⁻¹ * ι x * g0 * y) * (g0⁻¹ * ι x * g0)⁻¹ * g0⁻¹ := by group
      _ = g0 * (y * (g0⁻¹ * ι x * g0)) * (g0⁻¹ * ι x * g0)⁻¹ * g0⁻¹ := by rw [hc]
      _ = g0 * y * g0⁻¹ := by group
  refine ⟨X, ?_, ?_, fun x hx => ?_⟩
  ·
    rw [hX]
    intro h
    apply (twE6RootSubgroup_ne_bot σ).1
    rw [eq_bot_iff]
    intro u hu
    have h1 : (MulAut.conj g).toMonoidHom u ∈
        (twE6RootSubgroup K σ e6HighestRoot).map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hu
    rw [h, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    simpa using h1
  · rw [hX]
    exact (TwE6LongRoot.isPGroup_twE6RootSubgroup σ e6HighestRoot).map _
  · ext u
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hcomm x hx w hw]
      exact hw
    · intro hu
      refine ⟨u, hu, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hcomm x hx u hu

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end
