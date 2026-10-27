module

public import CFSG.LieType.SpecialLinear.Stage.Actor
public import CFSG.LieType.SpecialLinear.BorelTwist.Hecke

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
open CFSG.Theory.Representation
open scoped TensorProduct

noncomputable section

section Actor

variable {F : Type} [Field F]
  {E : Type} [Field E] {k : Type} [Field k] [Algebra E k]
  {D : Type} [Group D]
  {n : ℕ} {X : Type} [AddCommGroup X] [Module (ZMod 2) X] [Module E X]

theorem stage_actor_intertwine
    (σ : Representation E (SpecialLinearGroup (Fin (n + 1)) F) X)
    (δ : Representation (ZMod 2) D X)
    (hδE : ∀ d (c : E) (x : X), δ d (c • x) = c • δ d x)
    (hD2 : ∀ d, δ d * δ d = 1)
    {d : D} {β : SpecialLinearGroup (Fin (n + 1)) F → SpecialLinearGroup (Fin (n + 1)) F}
    (hd : ∀ g x, δ d (σ g x) = σ (β g) (δ d x)) :
    ∃ T : (k ⊗[E] X) ≃ₗ[k] (k ⊗[E] X), (∀ a x, T (a ⊗ₜ x) = a ⊗ₜ δ d x) ∧
      ∀ g v, T (extendScalars k σ g v) = extendScalars k σ (β g) (T v) := by
  classical
  let f : X →ₗ[E] X := actorLin δ hδE d
  have hf : Function.Involutive f := by
    intro x
    have h := congrArg (fun e : X →ₗ[ZMod 2] X => e x) (hD2 d)
    simpa only [f, actorLin_apply, Module.End.mul_apply, Module.End.one_apply] using h
  let T : (k ⊗[E] X) ≃ₗ[k] (k ⊗[E] X) := (LinearEquiv.ofInvolutive f hf).baseChange E k
  refine ⟨T, ?_, ?_⟩
  · intro a x
    simp only [T, LinearEquiv.baseChange_tmul, LinearEquiv.coe_ofInvolutive]
    change a ⊗ₜ[E] actorLin δ hδE d x = a ⊗ₜ[E] δ d x
    rw [actorLin_apply]
  · intro g v
    induction v using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a x =>
        simp only [T, extendScalars_apply, LinearMap.baseChange_tmul,
          LinearEquiv.baseChange_tmul, LinearEquiv.coe_ofInvolutive]
        change a ⊗ₜ[E] actorLin δ hδE d ((σ g) x) =
          a ⊗ₜ[E] (σ (β g)) (actorLin δ hδE d x)
        rw [actorLin_apply, hd, actorLin_apply]
    | add x y hx hy => simp only [map_add, hx, hy]

end Actor

variable {F : Type} [Field F] [Fintype F] [CharP F 2]
  {E : Type} [Field E]
  {k : Type} [Field k] [CharP k 2] [Algebra E k] [Algebra F k]
  {D : Type} [Group D]
  {n : ℕ} {X : Type} [AddCommGroup X] [Module (ZMod 2) X] [Module E X]

theorem stage_mem_iff_rev_mem
    (σ : Representation E (SpecialLinearGroup (Fin (n + 1)) F) X)
    (hsimp : IsSimpleRep (extendScalars k σ))
    {y : k ⊗[E] X} {χ : SpecialLinearGroup (Fin (n + 1)) F → k} {J : Finset (Fin n)}
    (ht : IsCoverType (rankOne n F 2) (extendScalars k σ) y χ J)
    (δ : Representation (ZMod 2) D X)
    (hδE : ∀ d (c : E) (x : X), δ d (c • x) = c • δ d x)
    (hD2 : ∀ d, δ d * δ d = 1)
    (hgraph : ∃ d, ∃ A : GL (Fin (n + 1)) F, IsUpperGL A ∧ ∃ τ : F ≃+* F,
      ∀ g x, δ d (σ g x) = σ (borelStd (n + 1) F A τ 1 g) (δ d x))
    (s : Fin n) :
    s ∈ J ↔ Fin.rev s ∈ J := by
  obtain ⟨d, A, hA, τ, hd⟩ := hgraph
  obtain ⟨T, -, hT⟩ := stage_actor_intertwine (k := k) σ δ hδE hD2 hd
  exact mem_iff_rev_mem_of_intertwine (m := n) (F := F) (k := k) (V := k ⊗[E] X)
    A hA τ rfl hsimp hT ht s

end

end CFSG.LieType.SpecialLinear
