module

public import CFSG.LieType.AlgebraicGroups.SolvableTorusSection
public import CFSG.LieType.AlgebraicGroups.MaximalTorusSections
public import TauCeti.Algebra.AlgebraicGroup.Solvable.UpperTriangular

public noncomputable section

open CategoryTheory WithConv

namespace CFSG.LieType.AlgebraicGroups

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

theorem exists_torus_quotient_sections_of_upperTriangular_embedding
    (B : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    [IsReduced B] [ConnectedSpace (PrimeSpectrum B)] {n : ℕ}
    (f : TauCeti.GeneralLinear.UpperTriangular.coordinateHopfAlgebra k n ⟶ B.obj)
    (hf : Function.Surjective f.hom) (I J : MaximalTorusIdeals B) :
    ∃ (T : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k),
      TauCeti.torusCommHopfAlgProperty k T ∧
      ∃ (p : T →ₐc[k] B) (j j' : B →ₐc[k] T),
        TauCeti.CommHopfAlgCat.kernelHopfIdeal (_root_.CommHopfAlgCat.ofHom p) =
          TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal B ∧
        j.comp p = BialgHom.id k T ∧ j'.comp p = BialgHom.id k T ∧
        (TauCeti.AlgHom.mapDomain (A := k) j).range =
          TauCeti.CommHopfAlgCat.quotientPointsSubgroup B.obj I.val (CommAlgCat.of k k) ∧
        (TauCeti.AlgHom.mapDomain (A := k) j').range =
          TauCeti.CommHopfAlgCat.quotientPointsSubgroup B.obj J.val (CommAlgCat.of k k) := by
  let ρ := TauCeti.AlgHom.mapDomain (A := k) f.hom
  have hρ : Function.Injective ρ := by
    intro g h heq
    apply WithConv.ext
    apply AlgHom.ext
    intro x
    obtain ⟨a, rfl⟩ := hf x
    have h := congrArg (fun t => t.ofConv a) heq
    simpa only [ρ, TauCeti.AlgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply,
      BialgHom.coe_toAlgHom] using h
  let : Group.IsSolvable (WithConv
      (TauCeti.GeneralLinear.UpperTriangular.coordinateHopfAlgebra k n →ₐ[k] k)) :=
    TauCeti.GeneralLinear.UpperTriangular.isSolvable_points k k n
  let : Group.IsSolvable (WithConv (B →ₐ[k] k)) :=
    Group.isSolvable_of_isSolvable_injective hρ
  obtain ⟨T, p, j, hT, hp, hRad, hj, hrestrict⟩ := exists_torus_quotient_section_of_solvable B
  let TI := TauCeti.FiniteTypeCommHopfAlgCat.quotient B I.val
  let TJ := TauCeti.FiniteTypeCommHopfAlgCat.quotient B J.val
  have hTI : TauCeti.torusCommHopfAlgProperty k TI :=
    ((TauCeti.HopfIdeal.isMaximalTorus_iff k B.obj I.val).mp I.property).1
  have hTJ : TauCeti.torusCommHopfAlgProperty k TJ :=
    ((TauCeti.HopfIdeal.isMaximalTorus_iff k B.obj J.val).mp J.property).1
  have hresI := hrestrict TI hTI (TauCeti.CommHopfAlgCat.mkQuotient B.obj I.val).hom
    (TauCeti.CommHopfAlgCat.mkQuotient_surjective B.obj I.val)
  have hresJ := hrestrict TJ hTJ (TauCeti.CommHopfAlgCat.mkQuotient B.obj J.val).hom
    (TauCeti.CommHopfAlgCat.mkQuotient_surjective B.obj J.val)
  obtain ⟨jI, hjI, hI⟩ := exists_section_with_maximalTorus_image_of_section B T hT p hRad j hj I hresI
  obtain ⟨jJ, hjJ, hJ⟩ := exists_section_with_maximalTorus_image_of_section B T hT p hRad j hj J hresJ
  exact ⟨T, hT, p, jI, jJ, hRad, hjI, hjJ, hI, hJ⟩


theorem unipotent_conjugacy_maximalTorusIdeals_of_upperTriangular_embedding
    (B : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    [IsReduced B] [ConnectedSpace (PrimeSpectrum B)] {n : ℕ}
    (f : TauCeti.GeneralLinear.UpperTriangular.coordinateHopfAlgebra k n ⟶ B.obj)
    (hf : Function.Surjective f.hom) (I J : MaximalTorusIdeals B) :
    ∃ u : WithConv (TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadical B →ₐ[k] k),
      I.val.conjugate (unipotentRadicalPointsHom B u) = J.val := by
  obtain ⟨T, hT, p, j, j', hp, hj, hj', hi, hi'⟩ :=
    exists_torus_quotient_sections_of_upperTriangular_embedding B f hf I J
  obtain ⟨u, hu⟩ := exists_unipotentRadical_conjugator_of_torus_quotient_sections B T
    hT p hp j j' hj hj'
  let g := unipotentRadicalPointsHom B u
  let IC := I.val.conjugate g⁻¹
  have hICtor : TauCeti.torusCommHopfAlgProperty k
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient B IC) :=
    ((TauCeti.HopfIdeal.isMaximalTorus_iff k B.obj IC).mp (I.property.conjugate g⁻¹)).1
  have hJtor : TauCeti.torusCommHopfAlgProperty k
      (TauCeti.FiniteTypeCommHopfAlgCat.quotient B J.val) :=
    ((TauCeti.HopfIdeal.isMaximalTorus_iff k B.obj J.val).mp J.property).1
  let : Algebra.Smooth k (TauCeti.FiniteTypeCommHopfAlgCat.quotient B IC) :=
    (TauCeti.smoothCommHopfAlgProperty_iff _).mp (hICtor.smooth k _)
  let : Algebra.Smooth k (TauCeti.FiniteTypeCommHopfAlgCat.quotient B J.val) :=
    (TauCeti.smoothCommHopfAlgProperty_iff _).mp (hJtor.smooth k _)
  let : IsReduced (TauCeti.FiniteTypeCommHopfAlgCat.quotient B IC) := TauCeti.isReduced_of_smooth k _
  let : IsReduced (TauCeti.FiniteTypeCommHopfAlgCat.quotient B J.val) := TauCeti.isReduced_of_smooth k _
  have hIC : IC = J.val := by
    apply TauCeti.HopfIdeal.eq_of_quotientPointsSubgroup_eq (K := k)
    apply Subgroup.ext
    intro x
    have hconj : x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup B.obj IC (CommAlgCat.of k k) ↔
        g * x * g⁻¹ ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup B.obj I.val
          (CommAlgCat.of k k) := by
      have h := TauCeti.CommHopfAlgCat.pointConjugation_mem_conjugate_iff
        I.val g (CommAlgCat.of k k) x
      have h' := TauCeti.CommHopfAlgCat.pointConjugation_mem_conjugate_iff
        IC g (CommAlgCat.of k k) x
      have hself : TauCeti.AlgHom.mapValue (Algebra.ofId k k) g = g := by
        apply WithConv.ext
        ext a
        simp
      rw [hself] at h'
      change (g * x * g⁻¹ ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup B.obj
        (IC.conjugate g) (CommAlgCat.of k k) ↔ x ∈
        TauCeti.CommHopfAlgCat.quotientPointsSubgroup B.obj IC (CommAlgCat.of k k)) at h'
      simpa only [IC, TauCeti.HopfIdeal.conjugate_conjugate_inv] using h'.symm
    rw [hconj, ← hi, ← hi']
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      calc
        TauCeti.AlgHom.mapDomain j' t = g⁻¹ * TauCeti.AlgHom.mapDomain j t * g := hu t
        _ = x := by rw [ht]; group
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      rw [← ht, hu t]
      dsimp only [g]
      group
  exact ⟨u⁻¹, by simpa only [g, IC, map_inv] using hIC⟩

theorem unipotent_conjugacy_maximalTorusIdeals_of_isSolvable
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced H]
    [ConnectedSpace (PrimeSpectrum H)]
    [Group.IsSolvable (WithConv (H →ₐ[k] k))] (I J : MaximalTorusIdeals H) :
    ∃ u : WithConv (TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadical H →ₐ[k] k),
      I.val.conjugate (unipotentRadicalPointsHom H u) = J.val := by
  obtain ⟨n, f, hf⟩ := exists_upperTriangular_coordinateEmbedding H
  exact unipotent_conjugacy_maximalTorusIdeals_of_upperTriangular_embedding H f hf I J

end CFSG.LieType.AlgebraicGroups
