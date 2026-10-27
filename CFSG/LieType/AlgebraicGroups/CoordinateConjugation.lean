module

public import CFSG.LieType.AlgebraicGroups.G2ExceptionalComorphism
public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import TauCeti.Algebra.AlgebraicGroup.Hopf.PointConjugation
public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

public noncomputable section
namespace CFSG.LieType.AlgebraicGroups
open WithConv Subgroup CategoryTheory
open scoped CFSG.ConvolutionPoints

variable {k : Type} [Field k] [IsAlgClosed k]
  {A : Type} [CommRing A] [HopfAlgebra k A] [Algebra.FiniteType k A]

omit [IsAlgClosed k] [Algebra.FiniteType k A] in
theorem subgroupIdeal_map_conj
    (H : Subgroup (WithConv (A →ₐ[k] k))) (g : WithConv (A →ₐ[k] k)) :
    subgroupIdeal (H.map (MulAut.conj g).toMonoidHom) =
      (subgroupIdeal H).map ((innerCo g⁻¹).toRingHom) := by
  have hEq : subgroupIdeal (H.map (MulAut.conj g).toMonoidHom) =
      (subgroupIdeal H).comap ((innerCo g).toRingHom) := by
    ext a
    rw [mem_pointsIdeal, Ideal.mem_comap, mem_pointsIdeal]
    constructor
    · intro ha h hh
      have hm : toConv (h.comp (innerCo g)) ∈ H.map (MulAut.conj g).toMonoidHom := by
        rw [point_comp_innerCo]
        exact mem_map_of_mem _ hh
      exact ha _ hm
    · intro ha h hh
      obtain ⟨h0, hh0, heq⟩ := hh
      have hv := ha h0.ofConv hh0
      have hp := point_comp_innerCo h0 g
      have hp' : toConv (h0.ofConv.comp (innerCo g)) = toConv h := hp.trans heq
      have heval := congrArg (fun y : WithConv (A →ₐ[k] k) => y.ofConv a) hp'
      exact heval.symm.trans hv
  have hgc : (innerCo g).comp (innerCo g⁻¹) = AlgHom.id k A := by
    rw [innerCo_comp_innerCo, inv_mul_cancel, innerCo_one]
  have hcg : (innerCo g⁻¹).comp (innerCo g) = AlgHom.id k A := by
    rw [innerCo_comp_innerCo, mul_inv_cancel, innerCo_one]
  have hmaps : ((subgroupIdeal H).comap ((innerCo g).toRingHom)).map
      ((innerCo g).toRingHom) = subgroupIdeal H := by
    exact Ideal.map_comap_of_surjective (innerCo g).toRingHom (by
      intro x
      exact ⟨innerCo g⁻¹ x, congrArg (fun f : A →ₐ[k] A => f x) hgc⟩) _
  have he2 : ((innerCo g⁻¹).toRingHom).comp (innerCo g).toRingHom = RingHom.id A := by
    exact congrArg AlgHom.toRingHom hcg
  rw [hEq]
  calc _ = ((subgroupIdeal H).comap ((innerCo g).toRingHom)).map (RingHom.id A) := by simp
    _ = (((subgroupIdeal H).comap ((innerCo g).toRingHom)).map ((innerCo g).toRingHom)).map
        ((innerCo g⁻¹).toRingHom) := by rw [Ideal.map_map, he2]
    _ = _ := by rw [hmaps]

omit [IsAlgClosed k] [Algebra.FiniteType k A] in
theorem pointConjugationAlgHom_eq_innerCo
    (g : WithConv (A →ₐ[k] k)) :
    TauCeti.HopfAlgebra.pointConjugationAlgHom g = innerCo g := by
  apply toConv_injective
  have hc : TauCeti.AlgHom.mapValue (H := A) (Algebra.ofId k A) g = constPoint g := by
    rw [TauCeti.AlgHom.mapValue_apply]
    rfl
  have h := TauCeti.HopfAlgebra.toConv_pointConjugationAlgHom g
  rw [hc, tauCeti_inv_eq] at h
  exact h

omit [IsAlgClosed k] [Algebra.FiniteType k A] in
theorem pointConjugationBialgEquiv_toAlgHom_eq_innerCo
    (g : WithConv (A →ₐ[k] k)) :
    (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g : A →ₐ[k] A) = innerCo g := by
  exact (TauCeti.HopfAlgebra.pointConjugationBialgEquiv_toAlgHom g).trans
    (pointConjugationAlgHom_eq_innerCo g)

omit [IsAlgClosed k] [Algebra.FiniteType k A] in
theorem pointConjugationBialgEquiv_apply_eq_innerCo
    (g : WithConv (A →ₐ[k] k)) (a : A) :
    TauCeti.HopfAlgebra.pointConjugationBialgEquiv g a = innerCo g a := by
  change (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g : A →ₐ[k] A) a = innerCo g a
  exact DFunLike.congr_fun (pointConjugationBialgEquiv_toAlgHom_eq_innerCo g) a

noncomputable def conjugateCoordinateAlgEquiv
    (H : Subgroup (WithConv (A →ₐ[k] k))) (g : WithConv (A →ₐ[k] k)) :
    (A ⧸ subgroupIdeal H) ≃ₐ[k] (A ⧸ subgroupIdeal (H.map (MulAut.conj g).toMonoidHom)) := by
  let e : A ≃ₐ[k] A := (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g⁻¹).toAlgEquiv
  have he : (e : A →ₐ[k] A) = innerCo g⁻¹ := pointConjugationBialgEquiv_toAlgHom_eq_innerCo g⁻¹
  exact Ideal.quotientEquivAlg _ _ e (by
    change subgroupIdeal (H.map (MulAut.conj g).toMonoidHom) =
      (subgroupIdeal H).map ((e : A →ₐ[k] A).toRingHom)
    rw [he]
    exact subgroupIdeal_map_conj H g)

omit [IsAlgClosed k] [Algebra.FiniteType k A] in
theorem conjugateCoordinateAlgEquiv_mk
    (H : Subgroup (WithConv (A →ₐ[k] k))) (g : WithConv (A →ₐ[k] k)) (a : A) :
    conjugateCoordinateAlgEquiv H g (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (innerCo g⁻¹ a) := by
  exact (Ideal.quotientEquivAlg_mk _ _ _ a).trans
    (congrArg (Ideal.Quotient.mk _) (DFunLike.congr_fun
      (pointConjugationBialgEquiv_toAlgHom_eq_innerCo g⁻¹) a))

noncomputable def conjugateCoordinateBialgEquiv
    (H : Subgroup (WithConv (A →ₐ[k] k))) (g : WithConv (A →ₐ[k] k)) :
    (A ⧸ subgroupIdeal H) ≃ₐc[k] (A ⧸ subgroupIdeal (H.map (MulAut.conj g).toMonoidHom)) := by
  let H' : Subgroup (WithConv (A →ₐ[k] k)) := H.map (MulAut.conj g).toMonoidHom
  let f : A →ₐc[k] (A ⧸ subgroupIdeal H') :=
    (Bialgebra.Quotient.mkBialgHom (subgroupIdeal H')).comp
      (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g⁻¹).toBialgHom
  have hf : ∀ a ∈ subgroupIdeal H, f a = 0 := by
    intro a ha
    change Ideal.Quotient.mk (subgroupIdeal H')
      ((TauCeti.HopfAlgebra.pointConjugationBialgEquiv g⁻¹) a) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [pointConjugationBialgEquiv_apply_eq_innerCo]
    change innerCo g⁻¹ a ∈ subgroupIdeal (H.map (MulAut.conj g).toMonoidHom)
    rw [subgroupIdeal_map_conj H g]
    exact Ideal.mem_map_of_mem _ ha
  let f' : (A ⧸ subgroupIdeal H) →ₐc[k] (A ⧸ subgroupIdeal H') :=
    bialgHomQuotientLift (subgroupIdeal H) f hf
  have hfe : (f' : (A ⧸ subgroupIdeal H) →ₐ[k] (A ⧸ subgroupIdeal H')) =
      (conjugateCoordinateAlgEquiv H g :
        (A ⧸ subgroupIdeal H) →ₐ[k] (A ⧸ subgroupIdeal H')) := by
    apply Ideal.Quotient.algHom_ext k
    ext a
    change f a = conjugateCoordinateAlgEquiv H g (Ideal.Quotient.mk _ a)
    rw [conjugateCoordinateAlgEquiv_mk]
    change Ideal.Quotient.mk _ ((TauCeti.HopfAlgebra.pointConjugationBialgEquiv g⁻¹) a) = _
    rw [pointConjugationBialgEquiv_apply_eq_innerCo]
  exact BialgEquiv.ofBijective f' (by
    rw [show (f' : (A ⧸ subgroupIdeal H) → (A ⧸ subgroupIdeal H')) =
      conjugateCoordinateAlgEquiv H g from congrArg DFunLike.coe hfe]
    exact (conjugateCoordinateAlgEquiv H g).bijective)

theorem torusCommHopfAlgProperty_conjugate_iff
    (H : Subgroup (WithConv (A →ₐ[k] k))) (g : WithConv (A →ₐ[k] k)) :
    TauCeti.torusCommHopfAlgProperty k
        (TauCeti.FiniteTypeCommHopfAlgCat.of k (A ⧸ subgroupIdeal
          (H.map (MulAut.conj g).toMonoidHom))) ↔
      TauCeti.torusCommHopfAlgProperty k
        (TauCeti.FiniteTypeCommHopfAlgCat.of k (A ⧸ subgroupIdeal H)) := by
  let e : TauCeti.FiniteTypeCommHopfAlgCat.of k (A ⧸ subgroupIdeal H) ≅
      TauCeti.FiniteTypeCommHopfAlgCat.of k (A ⧸ subgroupIdeal
        (H.map (MulAut.conj g).toMonoidHom)) :=
    ObjectProperty.isoMk _ (CommHopfAlgCat.isoMk
      (conjugateCoordinateBialgEquiv H g))
  exact ⟨fun h => (TauCeti.torusCommHopfAlgProperty k).prop_of_iso e.symm h,
    fun h => (TauCeti.torusCommHopfAlgProperty k).prop_of_iso e h⟩

section CentralPoint
variable [IsReduced A]

theorem innerCo_eq_id_of_central_point
    (x : WithConv (A →ₐ[k] k)) (hx : x ∈ Subgroup.center (WithConv (A →ₐ[k] k))) :
    innerCo x = AlgHom.id k A := by
  ext a
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_algHom k A
  intro y
  rw [map_sub, sub_eq_zero]
  have h := point_comp_innerCo (toConv y) x
  have hc : x * toConv y = toConv y * x := (Subgroup.mem_center_iff.mp hx (toConv y)).symm
  rw [hc, mul_inv_cancel_right] at h
  exact congrArg (fun f : WithConv (A →ₐ[k] k) => f.ofConv a) h

theorem pointConjugation_cube_of_cube_central
    (x : WithConv (A →ₐ[k] k)) (hx : x ^ 3 ∈ Subgroup.center (WithConv (A →ₐ[k] k))) :
    let σ := (TauCeti.HopfAlgebra.pointConjugationBialgEquiv x).toBialgHom
    (σ.comp σ).comp σ = BialgHom.id k A := by
  let σ := (TauCeti.HopfAlgebra.pointConjugationBialgEquiv x).toBialgHom
  have hi : σ.toAlgHom = innerCo x := pointConjugationBialgEquiv_toAlgHom_eq_innerCo x
  apply BialgHom.ext
  intro a
  change σ (σ (σ a)) = a
  have h := innerCo_eq_id_of_central_point (x ^ 3) hx
  have hx3 : ((innerCo x).comp (innerCo x)).comp (innerCo x) = innerCo (x ^ 3) := by
    rw [innerCo_comp_innerCo, innerCo_comp_innerCo]
    congr 1
    simp [pow_succ, mul_assoc]
  have ha := DFunLike.congr_fun (hx3.trans h) a
  change (innerCo x) ((innerCo x) ((innerCo x) a)) = a at ha
  change (σ.toAlgHom) ((σ.toAlgHom) ((σ.toAlgHom) a)) = a
  rw [hi]
  exact ha

end CentralPoint

end CFSG.LieType.AlgebraicGroups
