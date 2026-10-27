module

public import CFSG.LieType.AlgebraicGroups.TorusCocycleConjugacy

public noncomputable section

open CategoryTheory WithConv TauCeti

namespace CFSG.LieType.AlgebraicGroups

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

theorem bijective_restriction_to_maximalTorus_of_section
    (H T : FiniteTypeCommHopfAlgCat.{u,u} k)
    (hT : torusCommHopfAlgProperty k T) (p : T →ₐc[k] H)
    (hp : CommHopfAlgCat.kernelHopfIdeal (_root_.CommHopfAlgCat.ofHom p) =
      FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal H)
    (j : H →ₐc[k] T) (hj : j.comp p = BialgHom.id k T)
    (I : MaximalTorusIdeals H)
    (hres : Function.Surjective
      ((CommHopfAlgCat.mkQuotient H.obj I.val).hom.comp p)) :
    Function.Bijective ((CommHopfAlgCat.mkQuotient H.obj I.val).hom.comp p) := by
  let S := FiniteTypeCommHopfAlgCat.quotient H I.val
  let q : H →ₐc[k] S := (CommHopfAlgCat.mkQuotient H.obj I.val).hom
  let r := q.comp p
  have hS : torusCommHopfAlgProperty k S :=
    ((HopfIdeal.isMaximalTorus_iff k H.obj I.val).mp I.property).1
  let : Algebra.Smooth k S := (smoothCommHopfAlgProperty_iff S.obj).mp (hS.smooth k S)
  let : IsReduced S := TauCeti.isReduced_of_smooth k S
  have hq : Function.Surjective q := CommHopfAlgCat.mkQuotient_surjective H.obj I.val
  have hjs : Function.Surjective j := by
    intro x
    exact ⟨p x, by simpa only [BialgHom.comp_apply, BialgHom.id_apply] using DFunLike.congr_fun hj x⟩
  let j' := r.comp j
  have hj's : Function.Surjective j' := hres.comp hjs
  have heq : q.comp p = j'.comp p := by
    change r = (r.comp j).comp p
    rw [BialgHom.comp_assoc, hj, BialgHom.comp_id]
  obtain ⟨u, hu⟩ := exists_unipotentRadical_conjugator_of_torus_maps H T S hS p hp q j' heq
  let g := unipotentRadicalPointsHom H u
  let qconj := q.comp (HopfAlgebra.pointConjugationBialgEquiv g⁻¹).toBialgHom
  have hconj (t : WithConv (S →ₐ[k] k)) :
      AlgHom.mapDomain qconj t = g⁻¹ * AlgHom.mapDomain q t * g := by
    have h := HopfAlgebra.comp_pointConjugationAlgHom g⁻¹ (AlgHom.mapDomain q t)
    have hid : AlgHom.mapValue (H := H) (Algebra.ofId k k) g⁻¹ = g⁻¹ := by
      apply WithConv.ext
      ext a
      simp
    rw [hid, inv_inv] at h
    simpa only [qconj, AlgHom.mapDomain_apply, ofConv_toConv, BialgHom.comp_toAlgHom,
      AlgHom.comp_assoc, BialgEquiv.toBialgHom_eq_coe,
      HopfAlgebra.pointConjugationBialgEquiv_toAlgHom] using h
  have hjconj : j' = qconj := by
    apply BialgHom.ext
    intro x
    apply TauCeti.eq_of_forall_algHom_apply_eq (k := k) (K := k)
    intro t
    have h := congrArg (fun z : WithConv (H →ₐ[k] k) => z.ofConv x)
      ((hu (toConv t)).trans (hconj (toConv t)).symm)
    simpa only [g, AlgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply,
      BialgHom.coe_toAlgHom] using h
  let J := HopfIdeal.kerOfSurjective j hjs
  let J' := HopfIdeal.kerOfSurjective j' hj's
  have hqker (x : H) : q x = 0 ↔ x ∈ I.val := by
    rw [show q x = Ideal.Quotient.mkₐ k I.val.toIdeal x from
      CommHopfAlgCat.mkQuotient_apply H.obj I.val x]
    exact Ideal.Quotient.eq_zero_iff_mem
  have hJconj : J' = I.val.conjugate g⁻¹ := by
    ext x
    rw [HopfIdeal.mem_kerOfSurjective, HopfIdeal.mem_conjugate]
    rw [hjconj]
    change q (HopfAlgebra.pointConjugationBialgEquiv g⁻¹ x) = 0 ↔ _
    rw [hqker]
    have hfun := congrArg (fun f : H →ₐ[k] H => f x)
      (HopfAlgebra.pointConjugationBialgEquiv_toAlgHom g⁻¹)
    exact Iff.of_eq (congrArg (fun z : H => z ∈ I.val) hfun)
  have hJmax : HopfIdeal.IsMaximalTorus k H.obj J' := hJconj ▸ I.property.conjugate g⁻¹
  have hJtor : torusCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient H J) := by
    let e := CommHopfAlgCat.quotientKerOfSurjectiveIso (_root_.CommHopfAlgCat.ofHom j) hjs
    exact (torusCommHopfAlgProperty k).prop_of_iso
      (ObjectProperty.isoMk (finiteTypeCommHopfAlgProperty k) e.symm) hT
  have hJJ : J ≤ J' := by
    intro x hx
    rw [HopfIdeal.mem_kerOfSurjective] at hx ⊢
    change r (j x) = 0
    rw [hx, map_zero]
  have hJeq : J' = J := le_antisymm
    (((HopfIdeal.isMaximalTorus_iff k H.obj J').mp hJmax).2 J hJtor hJJ) hJJ
  have hri : Function.Injective r := by
    intro x y hxy
    obtain ⟨a, ha⟩ := hjs (x-y)
    have haJ' : a ∈ J' := by
      rw [HopfIdeal.mem_kerOfSurjective]
      change r (j a) = 0
      rw [ha, map_sub, hxy, sub_self]
    have haJ : a ∈ J := hJeq ▸ haJ'
    have ha0 := (HopfIdeal.mem_kerOfSurjective j hjs).mp haJ
    rw [ha] at ha0
    exact sub_eq_zero.mp ha0
  exact ⟨hri, hres⟩

theorem exists_section_with_maximalTorus_image_of_section
    (H T : FiniteTypeCommHopfAlgCat.{u,u} k)
    (hT : torusCommHopfAlgProperty k T) (p : T →ₐc[k] H)
    (hp : CommHopfAlgCat.kernelHopfIdeal (_root_.CommHopfAlgCat.ofHom p) =
      FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal H)
    (j : H →ₐc[k] T) (hj : j.comp p = BialgHom.id k T)
    (I : MaximalTorusIdeals H)
    (hres : Function.Surjective
      ((CommHopfAlgCat.mkQuotient H.obj I.val).hom.comp p)) :
    ∃ jI : H →ₐc[k] T, jI.comp p = BialgHom.id k T ∧
      (AlgHom.mapDomain (A := k) jI).range =
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.val (CommAlgCat.of k k) := by
  let S := FiniteTypeCommHopfAlgCat.quotient H I.val
  let q : H →ₐc[k] S := (CommHopfAlgCat.mkQuotient H.obj I.val).hom
  let r := q.comp p
  have hr : Function.Bijective r :=
    bijective_restriction_to_maximalTorus_of_section H T hT p hp j hj I hres
  let e := BialgEquiv.ofBijective r hr
  let jI := e.symm.toBialgHom.comp q
  have hsect : jI.comp p = BialgHom.id k T := by
    apply BialgHom.ext
    intro x
    change e.symm (r x) = x
    change e.symm (e x) = x
    exact e.symm_apply_apply x
  refine ⟨jI, hsect, ?_⟩
  let E := AlgHom.mapDomainMulEquiv (A := k) e
  apply Subgroup.ext
  intro x
  constructor
  · rintro ⟨t, ht⟩
    have hmem := CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup H.obj I.val
      (CommAlgCat.of k k) (E.symm t)
    have hpoint : AlgHom.mapDomain jI t = AlgHom.mapDomain q (E.symm t) := rfl
    rw [← ht, hpoint]
    exact hmem
  · intro hx
    obtain ⟨s, hs⟩ := hx
    refine ⟨E s, ?_⟩
    change AlgHom.mapDomain q (E.symm (E s)) = x
    rw [E.symm_apply_apply]
    exact hs

end CFSG.LieType.AlgebraicGroups
