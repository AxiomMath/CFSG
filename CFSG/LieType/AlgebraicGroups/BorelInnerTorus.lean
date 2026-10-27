module

public import CFSG.LieType.AlgebraicGroups.SolvableTorusConjugacy
public import CFSG.LieType.AlgebraicGroups.InnerTwistAffineCoordinates
public import CFSG.LieType.AlgebraicGroups.SolvableSemisimple
public import CFSG.LieType.AlgebraicGroups.FixedCoordinateEmbedding
public import TauCeti.Algebra.AlgebraicGroup.Borel.Basic

public noncomputable section

open CategoryTheory WithConv

namespace CFSG.LieType.AlgebraicGroups

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
theorem borel_comap_eq_of_stable
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (τ : H →ₐc[k] H)
    (hτ : Function.Bijective τ) (B : TauCeti.HopfIdeal k H)
    (hB : TauCeti.HopfIdeal.IsBorelOverAlgClosed k H B)
    (hs : ∀ a ∈ B, τ a ∈ B) : B.comapOfSurjective τ hτ.2 = B := by
  let e : H ≅ H := (TauCeti.finiteTypeCommHopfAlgProperty (R := k)).isoMk
    (_root_.CommHopfAlgCat.isoMk (BialgEquiv.ofBijective τ hτ))
  have he : TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom e.hom = τ := rfl
  let J := B.comapOfSurjective (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom e.hom)
    (ConcreteCategory.bijective_of_isIso e.hom).2
  have hJ : TauCeti.HopfIdeal.IsBorelOverAlgClosed k H J := hB.comapOfIso e
  have hBJ : B ≤ J := by
    intro a ha
    exact TauCeti.HopfIdeal.mem_comapOfSurjective.mpr (by rw [he]; exact hs a ha)
  have hJM := ((TauCeti.HopfIdeal.isBorelOverAlgClosed_iff k H J).mp hJ).2
  have hBM := ((TauCeti.HopfIdeal.isBorelOverAlgClosed_iff k H B).mp hB).2
  have hJB : J ≤ B := hJM.2 hBM.1 hBJ
  have hEq : J = B := le_antisymm hJB hBJ
  have hJ' : J = B.comapOfSurjective τ hτ.2 := by
    apply SetLike.ext
    intro a
    simp only [J, TauCeti.HopfIdeal.mem_comapOfSurjective]
    rw [he]
  exact hJ'.symm.trans hEq

omit [IsAlgClosed k] in
theorem quotientCoordinateEnd_bijective
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (τ : H →ₐc[k] H) (hτ : Function.Bijective τ) (I : TauCeti.HopfIdeal k H)
    (hI : ∀ a : H, τ a ∈ I ↔ a ∈ I) :
    Function.Bijective (quotientCoordinateEnd H I τ (fun a ha => (hI a).mpr ha)) := by
  let e : H.obj ≅ H.obj := _root_.CommHopfAlgCat.isoMk (BialgEquiv.ofBijective τ hτ)
  have he : e.hom.hom = τ := rfl
  have hi : I.comapOfSurjective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom).2 = I := by
    apply SetLike.ext
    intro a
    rw [TauCeti.HopfIdeal.mem_comapOfSurjective, he]
    exact hI a
  let eQ := TauCeti.CommHopfAlgCat.quotientIsoOfComapEq e I hi
  let q := TauCeti.CommHopfAlgCat.mkQuotient H.obj I
  have hcomm : eQ.hom.hom.comp q.hom = q.hom.comp τ := by
    have h := congrArg _root_.CommHopfAlgCat.Hom.hom
      (TauCeti.CommHopfAlgCat.mkQuotient_comp_quotientIsoOfComapEq_hom e I hi)
    simpa only [eQ, q, _root_.CommHopfAlgCat.hom_comp, he] using h
  have hq : Function.Surjective q.hom := TauCeti.CommHopfAlgCat.mkQuotient_surjective H.obj I
  have hmap : eQ.hom.hom = quotientCoordinateEnd H I τ (fun a ha => (hI a).mpr ha) := by
    apply BialgHom.ext
    intro x
    obtain ⟨a, rfl⟩ := hq x
    have h := congrArg (fun f => f a) hcomm
    have h' := congrArg (fun f => f a)
      (quotientCoordinateEnd_equivariant H I τ (fun a ha => (hI a).mpr ha))
    exact h.trans h'
  rw [← hmap]
  exact ConcreteCategory.bijective_of_isIso eQ.hom

theorem exists_unipotent_innerTwist_preserving_torus
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced H]
    [ConnectedSpace (PrimeSpectrum H)] [Group.IsSolvable (WithConv (H →ₐ[k] k))]
    (τ : H →ₐc[k] H) (hτ : Function.Bijective τ) (T : MaximalTorusIdeals H) :
    ∃ u : WithConv (TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadical H →ₐ[k] k),
      let g := unipotentRadicalPointsHom H u
      T.val.comapOfSurjective
          (τ.comp (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom)
          (innerTwist_bijective τ hτ g).2 = T.val := by
  let e : H ≅ H := (TauCeti.finiteTypeCommHopfAlgProperty (R := k)).isoMk
    (_root_.CommHopfAlgCat.isoMk (BialgEquiv.ofBijective τ hτ))
  have he : TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom e.hom = τ := rfl
  let J : MaximalTorusIdeals H := ⟨T.val.comapOfSurjective
      (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom e.hom)
      (ConcreteCategory.bijective_of_isIso e.hom).2, T.property.comapOfIso e⟩
  obtain ⟨u, hu⟩ := unipotent_conjugacy_maximalTorusIdeals_of_isSolvable H T J
  refine ⟨u⁻¹, ?_⟩
  have hback : J.val.conjugate (unipotentRadicalPointsHom H u)⁻¹ = T.val := by
    rw [← hu, TauCeti.HopfIdeal.conjugate_inv_conjugate]
  have hJ : J.val = T.val.comapOfSurjective τ hτ.2 := by
    dsimp only [J]
    apply SetLike.ext
    intro a
    simp only [TauCeti.HopfIdeal.mem_comapOfSurjective]
    rw [he]
  rw [hJ, TauCeti.HopfIdeal.conjugate_eq_comapOfSurjective,
    TauCeti.HopfIdeal.comapOfSurjective_comapOfSurjective] at hback
  simpa only [map_inv] using hback

theorem exists_maximalTorus_unipotent_innerTwist
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced H]
    [ConnectedSpace (PrimeSpectrum H)] [Group.IsSolvable (WithConv (H →ₐ[k] k))]
    (τ : H →ₐc[k] H) (hτ : Function.Bijective τ) :
    ∃ (T : MaximalTorusIdeals H)
      (u : WithConv (TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadical H →ₐ[k] k)),
      let g := unipotentRadicalPointsHom H u
      T.val.comapOfSurjective
          (τ.comp (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom)
          (innerTwist_bijective τ hτ g).2 = T.val := by
  obtain ⟨I, hI, -⟩ := SolvableSemisimple.exists_isMaximalTorus_of_pow_eq_one_of_solvable
    H (n := 1) (by simp) 1 (by simp)
  obtain ⟨u, hu⟩ := exists_unipotent_innerTwist_preserving_torus H τ hτ ⟨I, hI⟩
  exact ⟨⟨I, hI⟩, u, hu⟩

theorem exists_borel_quotient_torus_innerTwist
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (τ : H →ₐc[k] H) (hτ : Function.Bijective τ)
    (B : TauCeti.HopfIdeal k H)
    (hB : TauCeti.HopfIdeal.IsBorelOverAlgClosed k H B)
    (hs : ∀ a ∈ B, τ a ∈ B) :
    let Q := TauCeti.FiniteTypeCommHopfAlgCat.quotient H B
    let τQ := quotientCoordinateEnd H B τ hs
    ∃ (T : MaximalTorusIdeals Q)
      (u : WithConv (TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadical Q →ₐ[k] k)),
      let g := unipotentRadicalPointsHom Q u
      ∀ a : Q,
        (τQ.comp (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom) a ∈ T.val ↔
          a ∈ T.val := by
  let Q := TauCeti.FiniteTypeCommHopfAlgCat.quotient H B
  have hc := ((TauCeti.HopfIdeal.isBorelOverAlgClosed_iff k H B).mp hB).2.1
  let : Algebra.Smooth k Q := (TauCeti.smoothCommHopfAlgProperty_iff Q.obj).mp hc.smooth
  let : IsReduced Q := TauCeti.isReduced_of_smooth k Q
  let : ConnectedSpace (PrimeSpectrum Q) :=
    TauCeti.geometricallyConnectedCommHopfAlgProperty.connectedSpace k Q.obj hc.geometricallyConnected
  have hsolv := hc.geometricallySolvable
  rw [TauCeti.geometricallySolvablePointsCommHopfAlgProperty_iff] at hsolv
  let : Group.IsSolvable (WithConv (Q →ₐ[k] k)) :=
    Group.isSolvable_of_isSolvable_injective
      (TauCeti.AlgHom.mapValue_injective (Algebra.ofId k (AlgebraicClosure k)).injective)
  have hEq := borel_comap_eq_of_stable H τ hτ B hB hs
  have hBI (a : H) : τ a ∈ B ↔ a ∈ B := by
    have h : a ∈ B.comapOfSurjective τ hτ.2 ↔ a ∈ B := by rw [hEq]
    exact TauCeti.HopfIdeal.mem_comapOfSurjective.symm.trans h
  have hτQ := quotientCoordinateEnd_bijective H τ hτ B hBI
  obtain ⟨T, u, hu⟩ := exists_maximalTorus_unipotent_innerTwist Q
    (quotientCoordinateEnd H B τ hs) hτQ
  refine ⟨T, u, ?_⟩
  dsimp only
  intro a
  have h : a ∈ T.val.comapOfSurjective
      ((quotientCoordinateEnd H B τ hs).comp
        (TauCeti.HopfAlgebra.pointConjugationBialgEquiv (unipotentRadicalPointsHom Q u)).toBialgHom)
      (innerTwist_bijective (quotientCoordinateEnd H B τ hs) hτQ
        (unipotentRadicalPointsHom Q u)).2 ↔ a ∈ T.val := by rw [hu]
  exact TauCeti.HopfIdeal.mem_comapOfSurjective.symm.trans h

end CFSG.LieType.AlgebraicGroups
