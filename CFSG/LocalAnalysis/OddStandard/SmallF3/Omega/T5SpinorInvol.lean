module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthList
public import CFSG.ClassicalInvolution.Orders.OrthogonalNeg
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesInvol

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open TauCeti QuadraticMap CFSG.ClassicalInvolution CFSG.ClassicalGroups.Orthogonal

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma aux_t5_list_prod_pair (l : List V) (f : V → (ZMod 3)ˣ) :
    (l.map (fun v => ((-1 : (ZMod 3)ˣ), squareClassHom (f v)))).prod =
      (((-1 : (ZMod 3)ˣ) ^ l.length, squareClassHom ((l.map f).prod))) := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.length_nil, pow_zero, map_one]
    rfl
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, ih, pow_succ, map_mul]
    exact Prod.ext (mul_comm _ _) rfl

private lemma aux_t5_prod_reflect_eq_of_span (hQ : Q.Nondegenerate) {t : OGroup Q}
    (htt : t * t = 1) {l : List V} (hl0 : ∀ a ∈ l, Q a ≠ 0)
    (hpair : l.Pairwise (fun a b => polar Q a b = 0))
    (hspan : Submodule.span (ZMod 3) {x | x ∈ l} = commSp t) :
    (l.map (fun v => reflect Q v)).prod = (t : V ≃ₗ[ZMod 3] V) := by
  have hsup : fixSp t ⊔ commSp t = ⊤ := (isCompl_fixSp_commSp htt).sup_eq_top
  refine LinearEquiv.ext fun x => ?_
  have hx : x ∈ fixSp t ⊔ commSp t := by rw [hsup]; trivial
  obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hx
  rw [← huw, map_add, map_add]
  have hfixu : (l.map (reflect Q)).prod u = u :=
    prod_map_reflect_apply_of_forall_polar_eq_zero (fun a ha => by
      rw [polar_comm]
      exact polar_fixSp_commSp htt hu (by rw [← hspan]; exact Submodule.subset_span ha))
  have hnegw : (l.map (reflect Q)).prod w = -w := by
    rw [← hspan] at hw
    refine Submodule.span_induction (p := fun z _ => (l.map (reflect Q)).prod z = -z)
      ?_ ?_ ?_ ?_ hw
    · intro y hy
      exact prod_map_reflect_apply_of_mem hl0 hpair hy
    · simp
    · intro y z _ _ hy hz
      rw [map_add, hy, hz, neg_add]
    · intro c y _ hy
      rw [map_smul, hy, smul_neg]
  rw [hfixu, hnegw, mem_fixSp_iff.mp hu, (mem_commSp_iff htt).mp hw]

theorem t5_detSpinorNorm_involution (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1) :
    detSpinorNorm hQ t =
      (((-1 : (ZMod 3)ˣ) ^ invDim t,
        Multiplicative.ofAdd (RegularFormClass.discr
          (TauCeti.formClass (Q.restrict (commSp t))
            (nondegenerate_restrict_commSp hQ htt))))) := by
  obtain ⟨l, hlen, hpair, hl0, hspan, hdisc⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.exists_orthogonal_list_restrict Q (commSp t)
      (nondegenerate_restrict_commSp hQ htt)
  have hpair' : l.Pairwise (fun a b => polar Q a b = 0) := hpair.imp fun h => h.polar_eq_zero
  let reflO : V → OGroup Q := fun v => ⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩
  let f : V → (ZMod 3)ˣ := fun v => if h : Q v = 0 then 1 else Units.mk0 (Q v) h
  have hprod : (l.map (fun v => reflect Q v)).prod = (t : V ≃ₗ[ZMod 3] V) :=
    aux_t5_prod_reflect_eq_of_span hQ htt hl0 hpair' hspan
  have hprodO : t = (l.map reflO).prod := by
    apply Subtype.ext
    rw [Subgroup.val_list_prod, List.map_map]
    exact hprod.symm
  have hper : ∀ v ∈ l, detSpinorNorm hQ (reflO v) =
      ((-1 : (ZMod 3)ˣ), squareClassHom (f v)) := by
    intro v hv
    have hv0 : Q v ≠ 0 := hl0 v hv
    let _ : Invertible (Q v) := invertibleOfNonzero hv0
    have hrefl : reflO v = reflectionOrthogonal Q v := by
      apply Subtype.ext
      rw [coe_reflectionOrthogonal_eq_reflect]
    rw [hrefl, detSpinorNorm_reflectionOrthogonal]
    congr 1
    apply congrArg squareClassHom
    apply Units.ext
    rw [val_unitOfInvertible]
    simp [f, hv0]
  have hdet : detSpinorNorm hQ t =
      (l.map (fun v => ((-1 : (ZMod 3)ˣ), squareClassHom (f v)))).prod := by
    rw [hprodO, map_list_prod, List.map_map]
    apply congrArg List.prod
    exact List.map_congr_left (fun v hv => hper v hv)
  have hval : (((l.map f).prod : (ZMod 3)ˣ) : ZMod 3) = (l.map Q).prod := by
    change (Units.coeHom (ZMod 3)) ((l.map f).prod) = (l.map Q).prod
    rw [map_list_prod (Units.coeHom (ZMod 3)) (l.map f), List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro v hv
    simp [f, hl0 v hv]
  have hdisc' := hdisc ((l.map f).prod) hval
  rw [hdet, aux_t5_list_prod_pair]
  refine Prod.ext ?_ ?_
  · rw [hlen]
    rfl
  · rw [squareClassHom_apply, ← hdisc']

theorem t5_invSign_eq_of_detSpinorNorm_eq (hQ : Q.Nondegenerate) {s g : OGroup Q}
    (hs : s * s = 1) (hg : g * g = 1) (hd : detSpinorNorm hQ s = detSpinorNorm hQ g)
    (hdim : invDim s = invDim g) : invSign s = invSign g := by
  set xs := TauCeti.formClass (Q.restrict (commSp s)) (nondegenerate_restrict_commSp hQ hs)
    with hxs_def
  set xg := TauCeti.formClass (Q.restrict (commSp g)) (nondegenerate_restrict_commSp hQ hg)
    with hxg_def
  have hpair : ((-1 : (ZMod 3)ˣ) ^ invDim s,
      Multiplicative.ofAdd (RegularFormClass.discr xs)) =
      ((-1 : (ZMod 3)ˣ) ^ invDim g,
      Multiplicative.ofAdd (RegularFormClass.discr xg)) := by
    rw [hxs_def, hxg_def, ← t5_detSpinorNorm_involution hQ hs,
      ← t5_detSpinorNorm_involution hQ hg]
    exact hd
  have hdiscr : RegularFormClass.discr xs = RegularFormClass.discr xg := by
    have h := hpair
    simp only [Prod.mk.injEq] at h
    exact Multiplicative.ofAdd.injective h.2
  have hrank_s : xs.rank = invDim s := by
    rw [hxs_def, rank_formClass, invDim]
  have hrank_g : xg.rank = invDim g := by
    rw [hxg_def, rank_formClass, invDim]
  have hrank : xs.rank = xg.rank := by rw [hrank_s, hrank_g, hdim]
  have hsd : RegularFormClass.signedDiscr xs = RegularFormClass.signedDiscr xg := by
    rw [RegularFormClass.signedDiscr_eq_sign_add_discr,
      RegularFormClass.signedDiscr_eq_sign_add_discr, hrank, hdiscr]
  have hsign : signOf xs = signOf xg := by
    rw [signOf, signOf, hsd]
  rw [invSign, invSign,
    quadSign_eq_signOf (Q.restrict (commSp s)) (nondegenerate_restrict_commSp hQ hs),
    quadSign_eq_signOf (Q.restrict (commSp g)) (nondegenerate_restrict_commSp hQ hg),
    ← hxs_def, ← hxg_def]
  exact hsign

end CFSG.OddStandard.SmallF3.Omega
