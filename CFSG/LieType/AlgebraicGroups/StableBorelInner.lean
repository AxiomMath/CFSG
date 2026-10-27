module

public import TauCeti.Algebra.AlgebraicGroup.Borel.Torus
public import TauCeti.Algebra.AlgebraicGroup.Hopf.PointConjugation
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order

public noncomputable section

open CategoryTheory WithConv

namespace CFSG.LieType.AlgebraicGroups

universe u
variable {k : Type u} [Field k]

theorem pointConjugationAlgHom_mem_of_mem_quotientPointsSubgroup
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (I : TauCeti.HopfIdeal k H)
    (g : WithConv (H →ₐ[k] k))
    (hg : g ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) :
    ∀ a ∈ I, TauCeti.HopfAlgebra.pointConjugationAlgHom g a ∈ I := by
  let A := TauCeti.CommHopfAlgCat.quotient H.obj I
  let q : H →ₐ[k] A := (TauCeti.CommHopfAlgCat.mkQuotient H.obj I).hom
  let x : WithConv (H →ₐ[k] A) := toConv q
  let P := TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k A)
  have hx : x ∈ P := by
    rw [TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    intro a ha
    change (TauCeti.CommHopfAlgCat.mkQuotient H.obj I).hom a = 0
    exact (TauCeti.CommHopfAlgCat.mkQuotient_eq_zero_iff H.obj I a).mpr
      (TauCeti.HopfIdeal.mem_toIdeal.mpr ha)
  have hgA : TauCeti.AlgHom.mapValue (Algebra.ofId k A) g ∈ P :=
    TauCeti.CommHopfAlgCat.mapValue_mem_quotientPointsSubgroup H.obj I
      (Algebra.ofId k A) hg
  have hconj := P.mul_mem (P.mul_mem hgA hx) (P.inv_mem hgA)
  rw [← TauCeti.HopfAlgebra.comp_pointConjugationAlgHom g x] at hconj
  intro a ha
  have h := (TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff
    H.obj I (CommAlgCat.of k A) _).mp hconj a ha
  apply TauCeti.HopfIdeal.mem_toIdeal.mp
  apply (TauCeti.CommHopfAlgCat.mkQuotient_eq_zero_iff H.obj I _).mp
  simpa [A, x, q] using h

theorem exists_stableBorel_of_toral_inner
    [IsAlgClosed k] (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (σ : H →ₐc[k] H) (I : TauCeti.HopfIdeal k H)
    (hI : TauCeti.torusCommHopfAlgProperty k
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I))
    (g : WithConv (H →ₐ[k] k))
    (hg : g ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k))
    (hσ : σ.toAlgHom = TauCeti.HopfAlgebra.pointConjugationAlgHom g) :
    ∃ B : TauCeti.HopfIdeal k H,
      TauCeti.HopfIdeal.IsBorelOverAlgClosed k H B ∧ ∀ a ∈ B, σ a ∈ B := by
  obtain ⟨B, hBI, hB⟩ := TauCeti.HopfIdeal.exists_isBorelOverAlgClosed_le_of_torus H hI
  have hgB := TauCeti.CommHopfAlgCat.quotientPointsSubgroup_le_of_le H.obj hBI
    (CommAlgCat.of k k) hg
  refine ⟨B, hB, ?_⟩
  intro a ha
  change σ.toAlgHom a ∈ B
  rw [hσ]
  exact pointConjugationAlgHom_mem_of_mem_quotientPointsSubgroup H B g hgB a ha

end CFSG.LieType.AlgebraicGroups
