module

public import CFSG.LieType.AlgebraicGroups.CocharacterBorelCentralizer
public import CFSG.LieType.AlgebraicGroups.SemisimpleFixedCoordinatesThree

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open TauCeti WithConv

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

namespace StableTriangularCoordinates

variable {H : FiniteTypeCommHopfAlgCat.{u,u} k} {σ : H →ₐc[k] H}
variable (D : StableTriangularCoordinates H σ)

theorem mem_borel_of_commute_pointsHom [Algebra.Smooth k H] [IsDomain H]
    (B : HopfIdeal k H) (hB : HopfIdeal.IsBorelOverAlgClosed k H B)
    (hTB : D.torus ≤ CommHopfAlgCat.quotientPointsSubgroup H.obj B (CommAlgCat.of k k))
    {W : Type u} [AddCommGroup W] [Module k W] [Comodule k H W] {ω : W}
    (hstab : ∀ g : WithConv (H →ₐ[k] k),
      g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj B (CommAlgCat.of k k) ↔
        Comodule.basePointsRepresentation (H := H) W g ω ∈ k ∙ ω)
    (l : H →ₐc[k] LaurentPolynomial k) (hl : ∀ t : kˣ, Cocharacter.pointsHom k l t ∈ D.torus)
    (hle : ∀ n : ℤ, n ≤ 0 → ∀ x ∈ Derivation.adjointWeightSpace
        ((AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp l)
        (Multiplicative.ofAdd n),
      Derivation.cotangentDualLieEquiv (R := k) (H := H) x ∈ B.lieSubalgebra (B := k))
    {z : RationalGroup H} (hz : ∀ t : kˣ, Commute z (Cocharacter.pointsHom k l t)) :
    z ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj B (CommAlgCat.of k k) := by
  obtain ⟨m, hm⟩ := CocharacterBorel.exists_mem_weightSpace_of_forall_pointsHom_mem_span l
    fun t => (hstab _).mp (hTB (hl t))
  exact CocharacterBorel.mem_quotientPointsSubgroup_of_commute_pointsHom_of_nonpos H B
    ((HopfIdeal.isBorelOverAlgClosed_iff k H B).mp hB).2.1.smooth hstab l hm hle hz

theorem mem_torus_of_commute_pointsHom [Algebra.Smooth k H] [IsDomain H]
    {Wp : Type u} [AddCommGroup Wp] [Module k Wp] [Comodule k H Wp] {ωp : Wp}
    (hstabp : ∀ g : WithConv (H →ₐ[k] k),
      g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj D.positiveBorel (CommAlgCat.of k k) ↔
        Comodule.basePointsRepresentation (H := H) Wp g ωp ∈ k ∙ ωp)
    {Wn : Type u} [AddCommGroup Wn] [Module k Wn] [Comodule k H Wn] {ωn : Wn}
    (hstabn : ∀ g : WithConv (H →ₐ[k] k),
      g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj D.negativeBorel (CommAlgCat.of k k) ↔
        Comodule.basePointsRepresentation (H := H) Wn g ωn ∈ k ∙ ωn)
    (lp ln : H →ₐc[k] LaurentPolynomial k)
    (hlp : ∀ t : kˣ, Cocharacter.pointsHom k lp t ∈ D.torus)
    (hln : ∀ t : kˣ, Cocharacter.pointsHom k ln t ∈ D.torus)
    (hlep : ∀ n : ℤ, n ≤ 0 → ∀ x ∈ Derivation.adjointWeightSpace
        ((AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp lp)
        (Multiplicative.ofAdd n),
      Derivation.cotangentDualLieEquiv (R := k) (H := H) x ∈ D.positiveBorel.lieSubalgebra (B := k))
    (hlen : ∀ n : ℤ, n ≤ 0 → ∀ x ∈ Derivation.adjointWeightSpace
        ((AddMonoidAlgebra.toMultiplicativeBialgEquiv k k ℤ).toBialgHom.comp ln)
        (Multiplicative.ofAdd n),
      Derivation.cotangentDualLieEquiv (R := k) (H := H) x ∈ D.negativeBorel.lieSubalgebra (B := k))
    {z : RationalGroup H} (hzp : ∀ t : kˣ, Commute z (Cocharacter.pointsHom k lp t))
    (hzn : ∀ t : kˣ, Commute z (Cocharacter.pointsHom k ln t)) :
    z ∈ D.torus := by
  have hTp : D.torus ≤ CommHopfAlgCat.quotientPointsSubgroup H.obj D.positiveBorel
      (CommAlgCat.of k k) := by
    rw [D.positiveBorelPoints]
    exact le_sup_left
  have hTn : D.torus ≤ CommHopfAlgCat.quotientPointsSubgroup H.obj D.negativeBorel
      (CommAlgCat.of k k) := by
    rw [D.negativeBorelPoints]
    exact le_sup_left
  show z ∈ coordinateImage D.torusMap
  rw [← D.opposite]
  exact ⟨D.mem_borel_of_commute_pointsHom _ D.isPositiveBorel hTp hstabp lp hlp hlep hzp,
    D.mem_borel_of_commute_pointsHom _ D.isNegativeBorel hTn hstabn ln hln hlen hzn⟩

end StableTriangularCoordinates

end CFSG.LieType.AlgebraicGroups
