module

public import CFSG.LieType.AlgebraicGroups.UnipotentCoprimeTorsor
public import CFSG.LieType.AlgebraicGroups.TorusCocycle
public import CFSG.GroupTheory.FiniteNilpotentCocycle

public noncomputable section

open CategoryTheory WithConv TauCeti

namespace CFSG.LieType.AlgebraicGroups

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

theorem exists_coboundary_of_rational_torus_action
    (H U T : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced U]
    (hU : ∀ u : WithConv (U →ₐ[k] k), TauCeti.HopfAlgebra.IsUnipotentPoint u)
    (hT : TauCeti.torusCommHopfAlgProperty k T)
    (i : H →ₐc[k] U) (j : H →ₐc[k] T)
    (hi : Function.Injective (TauCeti.AlgHom.mapDomain (A := k) i))
    (α : WithConv (T →ₐ[k] k) →* MulAut (WithConv (U →ₐ[k] k)))
    (hα : ∀ t u, TauCeti.AlgHom.mapDomain i (α t u) =
      TauCeti.AlgHom.mapDomain j t * TauCeti.AlgHom.mapDomain i u *
        (TauCeti.AlgHom.mapDomain j t)⁻¹)
    (c : WithConv (T →ₐ[k] k) → WithConv (U →ₐ[k] k))
    (hcoc : ∀ s t, c (s * t) = c s * α s (c t))
    (hregular : ∀ u : WithConv (U →ₐ[k] k), ∃ f : U →ₐ[k] T,
      ∀ t : WithConv (T →ₐ[k] k), toConv (t.ofConv.comp f) =
        u * c t * (α t u)⁻¹) :
    ∃ u : WithConv (U →ₐ[k] k), ∀ t, c t = u⁻¹ * α t u := by
  let : Algebra.Smooth k T :=
    (TauCeti.smoothCommHopfAlgProperty_iff T.obj).mp (hT.smooth k T)
  let : IsReduced T := TauCeti.isReduced_of_smooth k T
  let : Group.IsNilpotent (WithConv (U →ₐ[k] k)) :=
    isNilpotent_points_of_forall_isUnipotentPoint U hU
  obtain ⟨p, hp, hpk⟩ : ∃ p : ℕ, p.Prime ∧ (p : k) ≠ 0 := by
    by_cases h2 : (2 : k) ≠ 0
    · exact ⟨2, Nat.prime_two, h2⟩
    · refine ⟨3, Nat.prime_three, ?_⟩
      have h2' : (2 : k) = 0 := not_ne_iff.mp h2
      have h3' : ((3 : ℕ) : k) = 1 := by
        calc
          ((3 : ℕ) : k) = (2 : k) + 1 := by norm_num
          _ = 1 := by rw [h2', zero_add]
      rw [h3']
      exact one_ne_zero
  obtain ⟨n, F, hn, hF, hmem, hrigid⟩ :=
    exists_primePower_torus_cocycle_eq_one H T hT (_root_.CommHopfAlgCat.ofHom j) hp hpk
  let : Finite F := hF
  let : Fact p.Prime := ⟨hp⟩
  have hFp : IsPGroup p F := by
    intro t
    refine ⟨n, Subtype.ext ?_⟩
    change (t : WithConv (T →ₐ[k] k)) ^ (p ^ n) = 1
    exact (hmem t).mp t.property
  obtain ⟨e, he⟩ := hFp.exists_card_eq
  have hmK : (Nat.card F : k) ≠ 0 := by
    rw [he, Nat.cast_pow]
    exact pow_ne_zero e hpk
  have hpow : Function.Bijective (fun u : WithConv (U →ₐ[k] k) => u ^ Nat.card F) :=
    pow_bijective_of_unipotent U hU hmK
  let αF : F →* MulAut (WithConv (U →ₐ[k] k)) := α.comp F.subtype
  obtain ⟨u, hu⟩ := CFSG.GroupTheory.exists_inv_mul_of_finite_actor αF hpow
    (fun s : F => c s) (fun s t => hcoc s t)
  let d : WithConv (T →ₐ[k] k) → WithConv (U →ₐ[k] k) :=
    fun t => u * c t * (α t u)⁻¹
  have hd : ∀ s t, d (s * t) = d s * α s (d t) :=
    CFSG.GroupTheory.cocycle_of_twist α c hcoc u
  have hdF : ∀ s ∈ F, d s = 1 := by
    intro s hs
    have h := hu ⟨s, hs⟩
    change c s = u⁻¹ * α s u at h
    dsimp only [d]
    rw [h]
    group
  obtain ⟨f, hf⟩ := hregular u
  let φ : H →ₐ[k] T := f.comp i.toAlgHom
  have hφ (t : WithConv (T →ₐ[k] k)) : toConv (t.ofConv.comp φ) =
      TauCeti.AlgHom.mapDomain i (d t) := by
    have ht : d t = toConv (t.ofConv.comp f) := (hf t).symm
    rw [ht]
    simp only [φ, TauCeti.AlgHom.mapDomain_apply, AlgHom.comp_assoc]
  have htrivH := hrigid φ
    (by
      intro s t
      dsimp only
      rw [hφ, hφ, hφ, hd, map_mul, hα]
      rfl)
    (by
      intro t ht
      dsimp only
      rw [hφ, hdF t ht, map_one])
    (by
      intro t
      dsimp only
      rw [hφ]
      exact (hU (d t)).mapDomain i)
  have htriv : ∀ t, d t = 1 := by
    intro t
    apply hi
    have ht := htrivH t
    dsimp only at ht
    rw [hφ] at ht
    exact ht.trans (map_one (TauCeti.AlgHom.mapDomain i)).symm
  refine ⟨u, fun t => ?_⟩
  have h := htriv t
  dsimp only [d] at h
  calc
    c t = u⁻¹ * ((u * c t * (α t u)⁻¹) * α t u) := by group
    _ = u⁻¹ * α t u := by rw [h, one_mul]

theorem exists_normal_subgroup_torus_orbit_coordinate
    (H T : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (I : TauCeti.HopfIdeal k H) (hI : I.IsNormal)
    (hT : TauCeti.torusCommHopfAlgProperty k T) (j : H →ₐc[k] T)
    (u : WithConv (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I →ₐ[k] k)) :
    ∃ b : TauCeti.FiniteTypeCommHopfAlgCat.quotient H I →ₐ[k] T,
      ∀ t : WithConv (T →ₐ[k] k),
        TauCeti.CommHopfAlgCat.quotientPointsHom H.obj I (CommAlgCat.of k k)
          (toConv (t.ofConv.comp b)) =
        TauCeti.AlgHom.mapDomain j t *
          TauCeti.CommHopfAlgCat.quotientPointsHom H.obj I (CommAlgCat.of k k) u *
          (TauCeti.AlgHom.mapDomain j t)⁻¹ := by
  let : Algebra.Smooth k T :=
    (TauCeti.smoothCommHopfAlgProperty_iff T.obj).mp (hT.smooth k T)
  let : IsReduced T := TauCeti.isReduced_of_smooth k T
  let q := TauCeti.CommHopfAlgCat.mkQuotient H.obj I
  let uH := TauCeti.CommHopfAlgCat.quotientPointsHom H.obj I (CommAlgCat.of k k) u
  let cu : H →ₐ[k] T := (Algebra.ofId k T).comp uH.ofConv
  let a : H →ₐ[k] T := (toConv j.toAlgHom * toConv cu * (toConv j.toAlgHom)⁻¹).ofConv
  have ha (t : WithConv (T →ₐ[k] k)) : toConv (t.ofConv.comp a) =
      TauCeti.AlgHom.mapDomain j t * uH * (TauCeti.AlgHom.mapDomain j t)⁻¹ := by
    have h : TauCeti.AlgHom.mapValue t.ofConv
        (toConv j.toAlgHom * toConv cu * (toConv j.toAlgHom)⁻¹) =
        TauCeti.AlgHom.mapValue t.ofConv (toConv j.toAlgHom) *
          TauCeti.AlgHom.mapValue t.ofConv (toConv cu) *
            (TauCeti.AlgHom.mapValue t.ofConv (toConv j.toAlgHom))⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    have hconst : TauCeti.AlgHom.mapValue t.ofConv (toConv cu) = uH := by
      apply WithConv.ext
      ext x
      simp [TauCeti.AlgHom.mapValue_apply, cu, AlgHom.comp_apply]
    rw [hconst] at h
    simpa only [a, TauCeti.AlgHom.mapValue_apply, ofConv_toConv,
      TauCeti.AlgHom.mapDomain_apply] using h
  have hkill (x : H) (hx : x ∈ I) : a x = 0 := by
    apply TauCeti.eq_of_forall_algHom_apply_eq (k := k) (K := k)
    intro t
    have hnormal : (TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I
        (CommAlgCat.of k k)).Normal :=
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup_normal H.obj I hI (CommAlgCat.of k k)
    let := hnormal
    have huH : uH ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I
        (CommAlgCat.of k k) :=
      TauCeti.CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup _ _ _ _
    have hmem := hnormal.conj_mem uH huH (TauCeti.AlgHom.mapDomain j (toConv t))
    have hz := (TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mp hmem x hx
    have hvalue := congrArg (fun g : WithConv (H →ₐ[k] k) => g.ofConv x) (ha (toConv t))
    simpa only [ofConv_toConv, AlgHom.comp_apply, map_zero] using hvalue.trans hz
  let b := Ideal.Quotient.liftₐ I.toIdeal a (fun x hx => hkill x hx)
  refine ⟨b, fun t => ?_⟩
  apply WithConv.ext
  apply AlgHom.ext
  intro x
  have hvalue := congrArg (fun g : WithConv (H →ₐ[k] k) => g.ofConv x) (ha t)
  change (TauCeti.CommHopfAlgCat.quotientPointsHom H.obj I (CommAlgCat.of k k)
    (toConv (t.ofConv.comp b))).ofConv x = _
  rw [TauCeti.CommHopfAlgCat.quotientPointsHom_apply_apply]
  change t.ofConv (a x) = _
  simpa only [ofConv_toConv, AlgHom.comp_apply, uH] using hvalue

theorem exists_coboundary_of_rational_normal_subgroup_cocycle
    (H T : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (I : TauCeti.HopfIdeal k H) (hI : I.IsNormal)
    [IsReduced (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I)]
    (hU : ∀ u : WithConv (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I →ₐ[k] k),
      TauCeti.HopfAlgebra.IsUnipotentPoint u)
    (hT : TauCeti.torusCommHopfAlgProperty k T)
    (j : H →ₐc[k] T)
    (α : WithConv (T →ₐ[k] k) →* MulAut
      (WithConv (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I →ₐ[k] k)))
    (hα : ∀ t u,
      TauCeti.CommHopfAlgCat.quotientPointsHom H.obj I (CommAlgCat.of k k) (α t u) =
        TauCeti.AlgHom.mapDomain j t *
          TauCeti.CommHopfAlgCat.quotientPointsHom H.obj I (CommAlgCat.of k k) u *
          (TauCeti.AlgHom.mapDomain j t)⁻¹)
    (b : TauCeti.FiniteTypeCommHopfAlgCat.quotient H I →ₐ[k] T)
    (hcoc : ∀ s t : WithConv (T →ₐ[k] k),
      toConv ((s * t).ofConv.comp b) =
        toConv (s.ofConv.comp b) * α s (toConv (t.ofConv.comp b))) :
    ∃ u : WithConv (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I →ₐ[k] k),
      ∀ t, toConv (t.ofConv.comp b) = u⁻¹ * α t u := by
  let U := TauCeti.FiniteTypeCommHopfAlgCat.quotient H I
  let q : H →ₐc[k] U := (TauCeti.CommHopfAlgCat.mkQuotient H.obj I).hom
  have hqpoint (u : WithConv (U →ₐ[k] k)) :
      TauCeti.AlgHom.mapDomain q u =
        TauCeti.CommHopfAlgCat.quotientPointsHom H.obj I (CommAlgCat.of k k) u := by
    rw [TauCeti.CommHopfAlgCat.quotientPointsHom_apply]
    exact TauCeti.AlgHom.mapDomain_apply _ _
  have hq : Function.Injective (TauCeti.AlgHom.mapDomain (A := k) q) := by
    intro u v heq
    apply WithConv.ext
    apply AlgHom.ext
    intro x
    obtain ⟨a, rfl⟩ := TauCeti.CommHopfAlgCat.mkQuotient_surjective H.obj I x
    have h := congrArg (fun p : WithConv (H →ₐ[k] k) => p.ofConv a) heq
    simpa only [q, TauCeti.AlgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply,
      BialgHom.coe_toAlgHom] using h
  have hα' : ∀ t u, TauCeti.AlgHom.mapDomain q (α t u) =
      TauCeti.AlgHom.mapDomain j t * TauCeti.AlgHom.mapDomain q u *
        (TauCeti.AlgHom.mapDomain j t)⁻¹ := by
    intro t u
    simpa only [hqpoint] using hα t u
  apply exists_coboundary_of_rational_torus_action H U T hU hT q j hq α hα'
    (fun t => toConv (t.ofConv.comp b)) hcoc
  intro u
  obtain ⟨a, ha⟩ := exists_normal_subgroup_torus_orbit_coordinate H T I hI hT j u
  have ha' (t : WithConv (T →ₐ[k] k)) : toConv (t.ofConv.comp a) = α t u := by
    apply hq
    simpa only [hqpoint] using (ha t).trans (hα t u).symm
  let cu : U →ₐ[k] T := (Algebra.ofId k T).comp u.ofConv
  let d : U →ₐ[k] T := (toConv cu * toConv b * (toConv a)⁻¹).ofConv
  refine ⟨d, fun t => ?_⟩
  have h : TauCeti.AlgHom.mapValue t.ofConv (toConv cu * toConv b * (toConv a)⁻¹) =
      TauCeti.AlgHom.mapValue t.ofConv (toConv cu) *
        TauCeti.AlgHom.mapValue t.ofConv (toConv b) *
          (TauCeti.AlgHom.mapValue t.ofConv (toConv a))⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  have hcu : TauCeti.AlgHom.mapValue t.ofConv (toConv cu) = u := by
    apply WithConv.ext
    ext x
    simp [TauCeti.AlgHom.mapValue_apply, cu, AlgHom.comp_apply]
  rw [hcu] at h
  simpa only [d, TauCeti.AlgHom.mapValue_apply, ofConv_toConv, ha'] using h

def normalSubgroupTorusActor
    (H T : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (I : TauCeti.HopfIdeal k H) (hI : I.IsNormal) (j : H →ₐc[k] T) :
    WithConv (T →ₐ[k] k) →* MulAut
      (WithConv (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I →ₐ[k] k)) := by
  let N := TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)
  let : N.Normal := TauCeti.CommHopfAlgCat.quotientPointsSubgroup_normal H.obj I hI
    (CommAlgCat.of k k)
  let q : WithConv (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I →ₐ[k] k) →*
      WithConv (H →ₐ[k] k) :=
    (TauCeti.CommHopfAlgCat.quotientPointsHom H.obj I (CommAlgCat.of k k)).hom
  let e : WithConv (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I →ₐ[k] k) ≃* N :=
    MonoidHom.ofInjective (TauCeti.CommHopfAlgCat.quotientPointsHom_injective _ _ _)
  exact ((MulAut.congr e).symm.toMonoidHom.comp
    (MulAut.conjNormal (H := N))).comp (TauCeti.AlgHom.mapDomain j)

omit [IsAlgClosed k] in
theorem normalSubgroupTorusActor_inclusion
    (H T : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (I : TauCeti.HopfIdeal k H) (hI : I.IsNormal) (j : H →ₐc[k] T)
    (t : WithConv (T →ₐ[k] k))
    (u : WithConv (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I →ₐ[k] k)) :
    TauCeti.CommHopfAlgCat.quotientPointsHom H.obj I (CommAlgCat.of k k)
      (normalSubgroupTorusActor H T I hI j t u) =
      TauCeti.AlgHom.mapDomain j t *
        TauCeti.CommHopfAlgCat.quotientPointsHom H.obj I (CommAlgCat.of k k) u *
        (TauCeti.AlgHom.mapDomain j t)⁻¹ := by
  let N := TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)
  let : N.Normal := TauCeti.CommHopfAlgCat.quotientPointsSubgroup_normal H.obj I hI
    (CommAlgCat.of k k)
  let e : WithConv (TauCeti.FiniteTypeCommHopfAlgCat.quotient H I →ₐ[k] k) ≃* N :=
    MonoidHom.ofInjective (TauCeti.CommHopfAlgCat.quotientPointsHom_injective _ _ _)
  have h := congrArg (fun z : N => (z : WithConv (H →ₐ[k] k)))
    (e.apply_symm_apply (MulAut.conjNormal (H := N) (TauCeti.AlgHom.mapDomain j t) (e u)))
  change (e (((MulAut.congr e).symm
    (MulAut.conjNormal (H := N) (TauCeti.AlgHom.mapDomain j t))) u) : WithConv (H →ₐ[k] k)) =
      TauCeti.AlgHom.mapDomain j t * (e u : WithConv (H →ₐ[k] k)) *
        (TauCeti.AlgHom.mapDomain j t)⁻¹
  rw [MulAut.congr_symm_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
  exact h

theorem exists_coboundary_unipotentRadical_torus
    (H T : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hT : TauCeti.torusCommHopfAlgProperty k T)
    (j : H →ₐc[k] T)
    (b : TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadical H →ₐ[k] T)
    (hcoc : ∀ s t : WithConv (T →ₐ[k] k),
      toConv ((s * t).ofConv.comp b) =
        toConv (s.ofConv.comp b) *
          normalSubgroupTorusActor H T
            (TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal H)
            (TauCeti.FiniteTypeCommHopfAlgCat.isNormal_unipotentRadicalDefiningIdeal H) j s
            (toConv (t.ofConv.comp b))) :
    ∃ u : WithConv (TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadical H →ₐ[k] k),
      ∀ t, toConv (t.ofConv.comp b) = u⁻¹ *
        normalSubgroupTorusActor H T
          (TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal H)
          (TauCeti.FiniteTypeCommHopfAlgCat.isNormal_unipotentRadicalDefiningIdeal H) j t u := by
  let : IsReduced (TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadical H) :=
    unipotentRadical_isReduced H
  exact exists_coboundary_of_rational_normal_subgroup_cocycle H T
    (TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal H)
    (TauCeti.FiniteTypeCommHopfAlgCat.isNormal_unipotentRadicalDefiningIdeal H)
    (unipotentRadical_points_unipotent H) hT j _
    (normalSubgroupTorusActor_inclusion H T _ _ j) b hcoc

theorem exists_unipotentRadical_conjugator_of_torus_sections
    (H T : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hT : TauCeti.torusCommHopfAlgProperty k T)
    (j j' : H →ₐc[k] T)
    (b : TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadical H →ₐ[k] T)
    (hb : ∀ t : WithConv (T →ₐ[k] k),
      unipotentRadicalPointsHom H (toConv (t.ofConv.comp b)) =
        TauCeti.AlgHom.mapDomain j' t * (TauCeti.AlgHom.mapDomain j t)⁻¹) :
    ∃ u : WithConv (TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadical H →ₐ[k] k),
      ∀ t : WithConv (T →ₐ[k] k), TauCeti.AlgHom.mapDomain j' t =
        (unipotentRadicalPointsHom H u)⁻¹ * TauCeti.AlgHom.mapDomain j t *
          unipotentRadicalPointsHom H u := by
  let I := TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal H
  let hI := TauCeti.FiniteTypeCommHopfAlgCat.isNormal_unipotentRadicalDefiningIdeal H
  let α := normalSubgroupTorusActor H T I hI j
  have hα (t : WithConv (T →ₐ[k] k))
      (u : WithConv (TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadical H →ₐ[k] k)) :
      unipotentRadicalPointsHom H (α t u) =
        TauCeti.AlgHom.mapDomain j t * unipotentRadicalPointsHom H u *
          (TauCeti.AlgHom.mapDomain j t)⁻¹ := by
    simp only [unipotentRadicalPointsHom,
      TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalCoordinateMap_def,
      TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom]
    change TauCeti.CommHopfAlgCat.quotientPointsHom H.obj I (CommAlgCat.of k k) (α t u) = _
    exact
      normalSubgroupTorusActor_inclusion H T I hI j t u
  have hcoc (s t : WithConv (T →ₐ[k] k)) :
      toConv ((s * t).ofConv.comp b) =
        toConv (s.ofConv.comp b) * α s (toConv (t.ofConv.comp b)) := by
    apply unipotentRadicalPointsHom_injective H
    rw [map_mul, hb, hb, hα, hb, map_mul, map_mul, mul_inv_rev]
    group
  obtain ⟨u, hu⟩ := exists_coboundary_unipotentRadical_torus H T hT j b hcoc
  refine ⟨u, fun t => ?_⟩
  have h := congrArg (unipotentRadicalPointsHom H) (hu t)
  rw [hb, map_mul, map_inv, hα] at h
  calc
    TauCeti.AlgHom.mapDomain j' t =
        (TauCeti.AlgHom.mapDomain j' t * (TauCeti.AlgHom.mapDomain j t)⁻¹) *
          TauCeti.AlgHom.mapDomain j t := by group
    _ = (unipotentRadicalPointsHom H u)⁻¹ * TauCeti.AlgHom.mapDomain j t *
        unipotentRadicalPointsHom H u := by rw [h]; group

theorem exists_coordinate_factor_of_point_mem_quotient
    (H T : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced T]
    (I : TauCeti.HopfIdeal k H) (a : H →ₐ[k] T)
    (ha : ∀ t : WithConv (T →ₐ[k] k),
      toConv (t.ofConv.comp a) ∈
        TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) :
    ∃ b : TauCeti.FiniteTypeCommHopfAlgCat.quotient H I →ₐ[k] T,
      b.comp (TauCeti.CommHopfAlgCat.mkQuotient H.obj I).hom.toAlgHom = a := by
  have hkill (x : H) (hx : x ∈ I) : a x = 0 := by
    apply TauCeti.eq_of_forall_algHom_apply_eq (k := k) (K := k)
    intro t
    have hz := (TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mp
      (ha (toConv t)) x hx
    simpa only [ofConv_toConv, AlgHom.comp_apply, map_zero] using hz
  let b := Ideal.Quotient.liftₐ I.toIdeal a (fun x hx => hkill x hx)
  exact ⟨b, AlgHom.ext fun x => rfl⟩

theorem exists_unipotentRadical_conjugator_of_torus_maps
    (H D T : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hT : TauCeti.torusCommHopfAlgProperty k T)
    (p : D →ₐc[k] H)
    (hp : TauCeti.CommHopfAlgCat.kernelHopfIdeal (_root_.CommHopfAlgCat.ofHom p) =
      TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal H)
    (j j' : H →ₐc[k] T)
    (heq : j.comp p = j'.comp p) :
    ∃ u : WithConv (TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadical H →ₐ[k] k),
      ∀ t : WithConv (T →ₐ[k] k), TauCeti.AlgHom.mapDomain j' t =
        (unipotentRadicalPointsHom H u)⁻¹ * TauCeti.AlgHom.mapDomain j t *
          unipotentRadicalPointsHom H u := by
  let : Algebra.Smooth k T :=
    (TauCeti.smoothCommHopfAlgProperty_iff T.obj).mp (hT.smooth k T)
  let : IsReduced T := TauCeti.isReduced_of_smooth k T
  let a : H →ₐ[k] T := (toConv j'.toAlgHom * (toConv j.toAlgHom)⁻¹).ofConv
  have hvalue (t : WithConv (T →ₐ[k] k)) : toConv (t.ofConv.comp a) =
      TauCeti.AlgHom.mapDomain j' t * (TauCeti.AlgHom.mapDomain j t)⁻¹ := by
    have h : TauCeti.AlgHom.mapValue t.ofConv
        (toConv j'.toAlgHom * (toConv j.toAlgHom)⁻¹) =
        TauCeti.AlgHom.mapValue t.ofConv (toConv j'.toAlgHom) *
          (TauCeti.AlgHom.mapValue t.ofConv (toConv j.toAlgHom))⁻¹ := by
      rw [map_mul, map_inv]
    simpa only [a, TauCeti.AlgHom.mapValue_apply, TauCeti.AlgHom.mapDomain_apply,
      ofConv_toConv] using h
  have hmaps (t : WithConv (T →ₐ[k] k)) :
      TauCeti.AlgHom.mapDomain p (TauCeti.AlgHom.mapDomain j' t) =
        TauCeti.AlgHom.mapDomain p (TauCeti.AlgHom.mapDomain j t) := by
    apply WithConv.ext
    apply AlgHom.ext
    intro x
    have hx := congrArg (fun f : D →ₐc[k] T => t.ofConv (f x)) heq.symm
    simpa only [TauCeti.AlgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply,
      BialgHom.comp_apply, BialgHom.coe_toAlgHom] using hx
  have ha (t : WithConv (T →ₐ[k] k)) : toConv (t.ofConv.comp a) ∈
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj
        (TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal H) (CommAlgCat.of k k) := by
    rw [← hp]
    apply (TauCeti.CommHopfAlgCat.mapPointsFunctor_app_eq_one_iff
      (_root_.CommHopfAlgCat.ofHom p) (CommAlgCat.of k k) _).mp
    change TauCeti.AlgHom.mapDomain p (toConv (t.ofConv.comp a)) = 1
    rw [hvalue, map_mul, map_inv, hmaps, mul_inv_cancel]
  obtain ⟨b, hb⟩ := exists_coordinate_factor_of_point_mem_quotient H T
    (TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal H) a ha
  apply exists_unipotentRadical_conjugator_of_torus_sections H T hT j j' b
  intro t
  have h := congrArg (fun f : H →ₐ[k] T => toConv (t.ofConv.comp f)) hb
  have hq : unipotentRadicalPointsHom H (toConv (t.ofConv.comp b)) =
      toConv (t.ofConv.comp a) := by
    simp only [unipotentRadicalPointsHom,
      TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalCoordinateMap_def,
      TauCeti.AlgHom.mapDomain_apply, AlgHom.comp_assoc]
    change toConv (t.ofConv.comp
      (b.comp (TauCeti.CommHopfAlgCat.mkQuotient H.obj
        (TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal H)).hom.toAlgHom)) = _
    exact h
  exact hq.trans (hvalue t)

theorem exists_unipotentRadical_conjugator_of_torus_quotient_sections
    (H T : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (hT : TauCeti.torusCommHopfAlgProperty k T)
    (p : T →ₐc[k] H)
    (hp : TauCeti.CommHopfAlgCat.kernelHopfIdeal (_root_.CommHopfAlgCat.ofHom p) =
      TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal H)
    (j j' : H →ₐc[k] T)
    (hj : j.comp p = BialgHom.id k T) (hj' : j'.comp p = BialgHom.id k T) :
    ∃ u : WithConv (TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadical H →ₐ[k] k),
      ∀ t : WithConv (T →ₐ[k] k), TauCeti.AlgHom.mapDomain j' t =
        (unipotentRadicalPointsHom H u)⁻¹ * TauCeti.AlgHom.mapDomain j t *
          unipotentRadicalPointsHom H u := by
  exact exists_unipotentRadical_conjugator_of_torus_maps H T T hT p hp j j'
    (hj.trans hj'.symm)

end CFSG.LieType.AlgebraicGroups
