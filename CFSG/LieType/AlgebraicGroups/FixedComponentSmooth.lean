module

public import CFSG.LieType.AlgebraicGroups.FixedComponentNorm
public import CFSG.LieType.AlgebraicGroups.ThreeFixedQuotient

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
theorem smooth_fixedCoordinate_three
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [Algebra.Smooth k M]
    (h3 : (3 : k) ≠ 0) (σ : M →ₐc[k] M)
    (hσ : (σ.comp σ).comp σ = BialgHom.id k M) :
    Algebra.Smooth k (fixedCoordinate M σ) := by
  have hsurj : Function.Surjective σ := by
    intro x
    refine ⟨σ (σ x), ?_⟩
    exact congrArg (fun f : M →ₐc[k] M => f x) hσ
  have hinj : Function.Injective σ := by
    intro x y hxy
    have h := congrArg (fun x => σ (σ x)) hxy
    have hx := congrArg (fun f : M →ₐc[k] M => f x) hσ
    have hy := congrArg (fun f : M →ₐc[k] M => f y) hσ
    exact hx.symm.trans (h.trans hy)
  let e := (BialgEquiv.ofBijective σ ⟨hinj, hsurj⟩).toAlgEquiv
  have he : ∀ a, e (e (e a)) = a := by
    intro a
    exact congrArg (fun f : M →ₐc[k] M => f a) hσ
  have hI : (fixedHopfIdeal M σ).toIdeal = Ideal.span (Set.range fun a : M => e a - a) := by
    rw [fixedHopfIdeal, TauCeti.HopfIdeal.equalizer_toIdeal]
    apply le_antisymm
    · apply TauCeti.HopfIdeal.equalizerIdeal_le_iff.2
      intro a
      exact Ideal.subset_span ⟨a, rfl⟩
    · rw [Ideal.span_le]
      rintro _ ⟨a, rfl⟩
      exact TauCeti.HopfIdeal.sub_mem_equalizerIdeal σ (BialgHom.id k M) a
  change Algebra.Smooth k (M ⧸ (fixedHopfIdeal M σ).toIdeal)
  rw [hI]
  exact smooth_three_fixed_quotient (k := k) (A := M) h3 e he

end CFSG.LieType.AlgebraicGroups
