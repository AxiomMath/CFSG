module

public import CFSG.LieType.AlgebraicGroups.FixedCoordinateEmbedding
public import TauCeti.Algebra.AlgebraicGroup.Borel.Conjugation
public import TauCeti.RingTheory.Smooth.GeometricallyReduced

public noncomputable section

open CategoryTheory WithConv

namespace CFSG.LieType.AlgebraicGroups

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

theorem exists_stableBorel_of_innerTwist_factor
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (σ : H →ₐc[k] H)
    (B : TauCeti.HopfIdeal k H)
    (hB : TauCeti.HopfIdeal.IsBorelOverAlgClosed k H B)
    (y : WithConv (H →ₐ[k] k))
    (hstable : ∀ a ∈ B,
      (σ.comp (TauCeti.HopfAlgebra.pointConjugationBialgEquiv y).toBialgHom) a ∈ B)
    (x b : WithConv (H →ₐ[k] k))
    (hb : b ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj B (CommAlgCat.of k k))
    (hfactor : TauCeti.AlgHom.mapDomain σ x = x * b * y) :
    ∃ J : TauCeti.HopfIdeal k H,
      TauCeti.HopfIdeal.IsBorelOverAlgClosed k H J ∧ ∀ a ∈ J, σ a ∈ J := by
  let τ := σ.comp (TauCeti.HopfAlgebra.pointConjugationBialgEquiv y).toBialgHom
  let J := B.conjugate x
  have hJ : TauCeti.HopfIdeal.IsBorelOverAlgClosed k H J := hB.conjugate x
  have hcandidate := ((TauCeti.HopfIdeal.isBorelOverAlgClosed_iff k H J).mp hJ).2.1
  let : Algebra.Smooth k (TauCeti.FiniteTypeCommHopfAlgCat.quotient H J) :=
    (TauCeti.smoothCommHopfAlgProperty_iff _).mp hcandidate.smooth
  let : IsReduced (TauCeti.FiniteTypeCommHopfAlgCat.quotient H J) :=
    TauCeti.isReduced_of_smooth k _
  have hself (g : WithConv (H →ₐ[k] k)) :
      TauCeti.AlgHom.mapValue (H := H) (Algebra.ofId k k) g = g := by
    apply WithConv.ext
    ext a
    simp
  have hτpoint (g : WithConv (H →ₐ[k] k)) :
      TauCeti.AlgHom.mapDomain τ g = y * TauCeti.AlgHom.mapDomain σ g * y⁻¹ := by
    rw [TauCeti.AlgHom.mapDomain_comp, MonoidHom.comp_apply,
      TauCeti.HopfAlgebra.mapDomain_pointConjugationBialgEquiv, hself]
  have hτB : ∀ z ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj B (CommAlgCat.of k k),
      TauCeti.AlgHom.mapDomain τ z ∈
        TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj B (CommAlgCat.of k k) := by
    intro z hz
    rw [TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hz ⊢
    intro a ha
    change z.ofConv (τ a) = 0
    exact hz _ (hstable a ha)
  refine ⟨J, hJ, mem_ideal_map_of_points_stable H J σ ?_⟩
  intro z hz
  let u := x⁻¹ * z * x
  have hzu : x * u * x⁻¹ = z := by dsimp only [u]; group
  have hu : u ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj B (CommAlgCat.of k k) := by
    have h := TauCeti.CommHopfAlgCat.pointConjugation_mem_conjugate_iff B x
      (CommAlgCat.of k k) u
    rw [hself, hzu] at h
    exact h.mp hz
  have hw := (TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj B (CommAlgCat.of k k)).mul_mem
    ((TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj B (CommAlgCat.of k k)).mul_mem hb (hτB u hu))
    ((TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj B (CommAlgCat.of k k)).inv_mem hb)
  have hσz : TauCeti.AlgHom.mapDomain σ z =
      x * (b * TauCeti.AlgHom.mapDomain τ u * b⁻¹) * x⁻¹ := by
    rw [← hzu, map_mul, map_mul, map_inv, hfactor, hτpoint]
    group
  have h := (TauCeti.CommHopfAlgCat.pointConjugation_mem_conjugate_iff B x
    (CommAlgCat.of k k) (b * TauCeti.AlgHom.mapDomain τ u * b⁻¹)).mpr hw
  rw [hself, ← hσz] at h
  exact h

end CFSG.LieType.AlgebraicGroups
