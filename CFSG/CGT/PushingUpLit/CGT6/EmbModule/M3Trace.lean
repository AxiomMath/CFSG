module

public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.M3Steinberg
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cDCtx
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk111cDGalois

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.GH74.GLS.Stage4.Rest
open scoped TensorProduct MonoidAlgebra

section Trace

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F] [Algebra (ZMod p) F]
  {G : Type} [Group G] {W : Type} [AddCommGroup W] [Module (ZMod p) W]

omit [Finite F] in
theorem m3_traceTensor_baseChange (σ : Representation (ZMod p) G W) (g : G)
    (x : F ⊗[ZMod p] W) : traceTensor ((σ g).baseChange F x) = σ g (traceTensor x) := by
  induction x using TensorProduct.inductionOn with
  | tmul c w =>
    simp only [LinearMap.baseChange_tmul, traceTensor_tmul, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem m3_eq_zero_of_traceTensor (x : F ⊗[ZMod p] W) (hx : ∀ c : F, traceTensor (c • x) = 0) :
    x = 0 := by
  obtain ⟨b', b, hexp⟩ := exists_trace_expansion (p := p) (F := F) (W := W)
  rw [hexp x]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hx (b i), TensorProduct.tmul_zero, smul_zero]

variable (σ : Representation (ZMod p) G W)

theorem m3_exists_equivariant_hom {Y : Type} [AddCommGroup Y] [Module F Y]
    (ρ : Representation F G Y) [ρ.IsIrreducible]
    (ψ : ρ.IntertwiningMap (CFSG.Theory.Representation.extendScalars F σ)) (hψ : ψ ≠ 0)
    {M : Type} [AddCommGroup M] (τ : G → M → M) (Φ : M →+ Y)
    (hΦ : ∀ g m, Φ (τ g m) = ρ g (Φ m)) (hΦ0 : Φ ≠ 0) :
    ∃ T : M →+ W, (∀ g m, T (τ g m) = σ g (T m)) ∧ T ≠ 0 := by
  classical
  have hψg : ∀ g y, ψ.toLinearMap (ρ g y) = (σ g).baseChange F (ψ.toLinearMap y) := fun g y =>
    LinearMap.congr_fun (ψ.isIntertwining' g) y
  let T : F → M →+ W := fun c =>
    AddMonoidHom.mk' (fun m => traceTensor (ψ.toLinearMap (c • Φ m))) (by
      intro a b
      simp only [map_add, smul_add])
  have hTeq : ∀ c g m, T c (τ g m) = σ g (T c m) := by
    intro c g m
    show traceTensor (ψ.toLinearMap (c • Φ (τ g m))) =
      σ g (traceTensor (ψ.toLinearMap (c • Φ m)))
    rw [hΦ, ← map_smul, hψg, m3_traceTensor_baseChange]
  by_cases hnz : ∃ c, T c ≠ 0
  · obtain ⟨c, hc⟩ := hnz
    exact ⟨T c, hTeq c, hc⟩
  · exfalso
    push Not at hnz
    let U : Subrepresentation ρ :=
      { toSubmodule :=
          { carrier := {y | ∀ c : F, traceTensor (ψ.toLinearMap (c • y)) = 0}
            add_mem' := fun {a b} ha hb c => by
              rw [smul_add, map_add, map_add, ha c, hb c, add_zero]
            zero_mem' := fun c => by simp
            smul_mem' := fun a y hy c => by
              show traceTensor (ψ.toLinearMap (c • a • y)) = 0
              rw [smul_smul]
              exact hy (c * a) }
        apply_mem_toSubmodule := fun g y hy c => by
          show traceTensor (ψ.toLinearMap (c • ρ g y)) = 0
          rw [← map_smul, hψg, m3_traceTensor_baseChange]
          have := hy c
          rw [this, map_zero] }
    have hΦU : ∀ m, Φ m ∈ U := fun m c => by
      exact DFunLike.congr_fun (hnz c) m
    rcases @IsSimpleOrder.eq_bot_or_eq_top _ _ _ (inferInstance : ρ.IsIrreducible) U with h | h
    · apply hΦ0
      ext m
      have := hΦU m
      rw [h] at this
      exact (Submodule.mem_bot F).mp this
    · apply hψ
      ext y
      have hy : y ∈ U := by rw [h]; trivial
      show ψ.toLinearMap y = 0
      exact m3_eq_zero_of_traceTensor _ fun c => by rw [← map_smul]; exact hy c

end Trace

section FromLabel

variable {n : ℕ} {F : Type} [Field F] [Finite F] [Algebra (ZMod 2) F] [CharP F 2]
  {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  (σ : Representation (ZMod 2) (SLm F) W)

omit [CharP F 2] in
theorem m3_exists_intertwining (hF : Nat.card F = 2 ^ n)
    {N : Submodule (MonoidAlgebra F (SLm F)) (repXT σ).asModule} {A : ℕ} (hA : A < 2 ^ n)
    (ι : ↥N ≃ₗ[MonoidAlgebra F (SLm F)] (stRep F A).asModule) :
    ∃ ψ : (steinbergRep F F A).IntertwiningMap
        (CFSG.Theory.Representation.extendScalars F σ), ψ ≠ 0 := by
  have hsimp := m3_simple (F := F) (L := F) Nat.prime_two hF hA
  have hnt : Nontrivial (steinbergRep F F A).asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra F (SLm F)) _
  let f : (steinbergRep F F A).asModule →ₗ[MonoidAlgebra F (SLm F)]
      (CFSG.Theory.Representation.extendScalars F σ).asModule :=
    (xEquiv σ).symm.toLinearMap ∘ₗ N.subtype ∘ₗ ι.symm.toLinearMap ∘ₗ (stEquiv F A).toLinearMap
  have hinj : Function.Injective f :=
    (xEquiv σ).symm.injective.comp (N.injective_subtype.comp
      (ι.symm.injective.comp (stEquiv F A).injective))
  refine ⟨(Representation.IntertwiningMap.equivLinearMapAsModule (steinbergRep F F A)
    (CFSG.Theory.Representation.extendScalars F σ)).symm f, ?_⟩
  intro h0
  obtain ⟨x, hx⟩ := exists_ne (0 : (steinbergRep F F A).asModule)
  apply hx
  have h1 : f = 0 := by
    have := congrArg (Representation.IntertwiningMap.equivLinearMapAsModule (steinbergRep F F A)
      (CFSG.Theory.Representation.extendScalars F σ)) h0
    simpa using this
  exact hinj (by rw [map_zero]; exact LinearMap.congr_fun h1 x)

end FromLabel

end CFSG.CGT.PushingUpLit.CGT6
