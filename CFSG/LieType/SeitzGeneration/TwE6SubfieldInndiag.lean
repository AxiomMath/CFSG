module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwFieldCube
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutTorusNum

public section

namespace CFSG.LieType.SeitzGeneration.TwE6Subfield

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
open CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc
open CFSG.ClassicalInvolution.ModelFacts.ChevAut
open CFSG.RankThree.Chevalley (subfieldRootGroupImage)

theorem exists_ringEquiv_comp_subtype {k K : Type} [Field k] [Finite k] [Field K] [Finite K]
    (ι : k →+* K) (ρ : k ≃+* k) :
    ∃ ρ' : K ≃+* K, ∀ c, ρ' (ι c) = ι (ρ c) := by
  classical
  haveI : Fintype k := Fintype.ofFinite k
  obtain ⟨n, hp, hn⟩ := FiniteField.card k (ringChar k)
  have hk : Nat.card k = ringChar k ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hn
  obtain ⟨e, -, hρ⟩ := exists_ringEquiv_eq_frobenius_pow hp n.pos hk ρ
  have hcharP : CharP K (ringChar k) :=
    (RingHom.charP_iff ι ι.injective (ringChar k)).mp (ringChar.charP k)
  haveI : Fact (ringChar k).Prime := ⟨hp⟩
  haveI : CharP K (ringChar k) := hcharP
  refine ⟨iterateFrobeniusEquiv K (ringChar k) e, fun c => ?_⟩
  rw [iterateFrobeniusEquiv_apply, iterateFrobenius_def, hρ c, map_pow]

section Model

variable {K : Type} [Field K] [Finite K]

@[expose] noncomputable def twFJModelEquiv (σ η : K ≃+* K) :
    ↥(twistedE6RootGroup (fixSubfield η) (fixSubfieldRestrict σ η)) ≃* ↥(twFJ σ η) :=
  (Subgroup.equivMapOfInjective _ _
      (baseChangeGL_injective (τ := TwistTag.E6.tag) (fixSubfield η).subtype)).trans
    (Subgroup.subgroupOfEquivOfLe (subfieldRootGroupImage_le_twistedE6 σ η)).symm

theorem coe_twFJModelEquiv (σ η : K ≃+* K)
    (y : ↥(twistedE6RootGroup (fixSubfield η) (fixSubfieldRestrict σ η))) :
    ((twFJModelEquiv σ η y : twFJ σ η) : ModGL TwistTag.E6.tag K) =
      baseChangeGL (fixSubfield η).subtype
        (y : ModGL TwistTag.E6.tag (fixSubfield η)) := by
  rfl

theorem twFJModelEquiv_conj (σ η : K ≃+* K)
    (g y : ↥(twistedE6RootGroup (fixSubfield η) (fixSubfieldRestrict σ η))) :
    ((twFJModelEquiv σ η (MulAut.conj g y) : twFJ σ η) : ModGL TwistTag.E6.tag K) =
      ((MulAut.conj ((twFJModelEquiv σ η g : twFJ σ η) : twistedE6RootGroup K σ)
        ((twFJModelEquiv σ η y : twFJ σ η) : twistedE6RootGroup K σ) :
        twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) := by
  rw [MulAut.conj_apply, MulAut.conj_apply, coe_twFJModelEquiv,
    Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_twFJModelEquiv, coe_twFJModelEquiv, map_mul, map_mul, map_inv]

theorem fieldActor_twFJModelEquiv (σ η : K ≃+* K) (τ : K ≃+* K)
    (δ₀ : fixSubfield η ≃+* fixSubfield η)
    (hτ : ∀ c : fixSubfield η,
      τ ((fixSubfield η).subtype c) = (fixSubfield η).subtype (δ₀ c))
    (y : ↥(twistedE6RootGroup (fixSubfield η) (fixSubfieldRestrict σ η))) :
    ((twFJModelEquiv σ η
        (fieldActor (t := TwistTag.E6) (fixSubfieldRestrict σ η) δ₀ y) : twFJ σ η) :
        ModGL TwistTag.E6.tag K) =
      ((fieldActor (t := TwistTag.E6) σ τ
        ((twFJModelEquiv σ η y : twFJ σ η) : twistedE6RootGroup K σ) :
        twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) := by
  have hτcomp : (fixSubfield η).subtype.comp δ₀.toRingHom =
      τ.toRingHom.comp (fixSubfield η).subtype :=
    RingHom.ext fun c => (hτ c).symm
  have hδ0 : Units.map (entrywiseHom δ₀.toRingHom)
      (y : ModGL TwistTag.E6.tag (fixSubfield η)) =
      baseChangeGL δ₀.toRingHom (y : ModGL TwistTag.E6.tag (fixSubfield η)) := rfl
  have hτ0 : Units.map (entrywiseHom τ.toRingHom)
      ((twFJModelEquiv σ η y : twFJ σ η) : ModGL TwistTag.E6.tag K) =
      baseChangeGL τ.toRingHom
        ((twFJModelEquiv σ η y : twFJ σ η) : ModGL TwistTag.E6.tag K) := rfl
  rw [coe_twFJModelEquiv, coe_fieldActor, coe_fieldActor, hδ0, hτ0,
    coe_twFJModelEquiv, baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, hτcomp]

theorem coe_fixSubfieldRestrict_toRingHom_pow {K : Type} [Field K] [Finite K]
    (σ η : K ≃+* K) (n : ℕ) (c : fixSubfield η) :
    ((((fixSubfieldRestrict σ η).toRingHom ^ n) c : fixSubfield η) : K) =
      (σ.toRingHom ^ n) ((c : fixSubfield η) : K) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', RingHom.mul_def, RingHom.comp_apply]
    change (((fixSubfieldRestrict σ η)
      (((fixSubfieldRestrict σ η).toRingHom ^ n) c) : fixSubfield η) : K) = _
    rw [coe_fixSubfieldRestrict, ih, pow_succ', RingHom.mul_def, RingHom.comp_apply]
    rfl

theorem compatDiag_baseChange (σ η : K ≃+* K)
    (u' : (a : Fin TwistTag.E6.foldedTag.rank) →
      (orbitField TwistTag.E6 (fixSubfield η) (fixSubfieldRestrict σ η).toRingHom a)ˣ) :
    ∃ ũ : (a : Fin TwistTag.E6.foldedTag.rank) →
        (orbitField TwistTag.E6 K σ.toRingHom a)ˣ,
      compatDiag TwistTag.E6 σ.toRingHom ũ =
        fun i => Units.map (fixSubfield η).subtype.toMonoidHom
          (compatDiag TwistTag.E6 (fixSubfieldRestrict σ η).toRingHom u' i) := by
  have hσι : ∀ c : fixSubfield η,
      σ.toRingHom ((fixSubfield η).subtype c) =
        (fixSubfield η).subtype ((fixSubfieldRestrict σ η).toRingHom c) :=
    fun c => (coe_fixSubfieldRestrict σ η c).symm
  let ũ : (a : Fin TwistTag.E6.foldedTag.rank) →
      (orbitField TwistTag.E6 K σ.toRingHom a)ˣ := fun a =>
    Units.mk0 ⟨(fixSubfield η).subtype
        ((u' a : orbitField TwistTag.E6 (fixSubfield η)
          (fixSubfieldRestrict σ η).toRingHom a) : fixSubfield η),
      map_mem_orbitField_of_comm hσι (u' a).val.2⟩ fun h =>
      (u' a).ne_zero (Subtype.ext ((fixSubfield η).subtype.injective
        (congrArg Subtype.val h)))
  refine ⟨ũ, ?_⟩
  funext i
  set y0 : fixSubfield η :=
    ((u' (TwistTag.E6.orbitIndex i) : orbitField TwistTag.E6 (fixSubfield η)
      (fixSubfieldRestrict σ η).toRingHom (TwistTag.E6.orbitIndex i)) : fixSubfield η) with hy0
  obtain ⟨k, hk, hi⟩ := TwistTag.E6.exists_eq_perm_pow_orbitMin
    (TwistTag.E6.mem_orbit_orbitIndex i)
  rw [← hi, compatDiag_pow _ _ hk, compatDiag_pow _ _ hk]
  have hũa : ∀ a, ((ũ a : orbitField TwistTag.E6 K σ.toRingHom a) : K) =
      (fixSubfield η).subtype
        (((u' a : orbitField TwistTag.E6 (fixSubfield η)
          (fixSubfieldRestrict σ η).toRingHom a) : fixSubfield η)) := fun a => rfl
  refine Units.ext ?_
  rw [Units.coe_map, Units.coe_map, Units.coe_map, coe_orbitFieldUnit, coe_orbitFieldUnit,
    hũa]
  change (σ.toRingHom ^ k) ((fixSubfield η).subtype y0) =
    (fixSubfield η).subtype (((fixSubfieldRestrict σ η).toRingHom ^ k) y0)
  simpa only [Subfield.coe_subtype] using
    (coe_fixSubfieldRestrict_toRingHom_pow σ η k y0).symm

theorem exists_compatDiagAutHom_twFJModelEquiv (σ η : K ≃+* K)
    (u' : (a : Fin TwistTag.E6.foldedTag.rank) →
      (orbitField TwistTag.E6 (fixSubfield η) (fixSubfieldRestrict σ η).toRingHom a)ˣ) :
    ∃ ũ : (a : Fin TwistTag.E6.foldedTag.rank) →
        (orbitField TwistTag.E6 K σ.toRingHom a)ˣ,
      ∀ y : ↥(twistedE6RootGroup (fixSubfield η) (fixSubfieldRestrict σ η)),
        ((twFJModelEquiv σ η
          (compatDiagAutHom TwistTag.E6 (fixSubfield η)
            (fixSubfieldRestrict σ η).toRingHom u' y) : twFJ σ η) :
          ModGL TwistTag.E6.tag K) =
        ((compatDiagAutHom TwistTag.E6 K σ.toRingHom ũ
          ((twFJModelEquiv σ η y : twFJ σ η) : twistedE6RootGroup K σ) :
          twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) := by
  obtain ⟨ũ, hũ⟩ := compatDiag_baseChange σ η u'
  refine ⟨ũ, fun y => ?_⟩
  rw [coe_twFJModelEquiv, coe_compatDiagAutHom, map_mul, map_mul, map_inv,
    baseChangeGL_rootDiagUnit, ← hũ, coe_compatDiagAutHom, coe_twFJModelEquiv]

theorem exists_inndiag_restrict_twFJ {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {η : K ≃+* K} (hη : orderOf η = 3)
    {a : MulAut ↥(twistedE6RootGroup K σ)}
    (ha : a ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ)
    (haη : Commute a (fieldActor (t := TwistTag.E6) σ η)) :
    ∃ ψ ∈ twistedE6Inn (fixSubfield η) (fixSubfieldRestrict σ η) ⊔
        twistedE6Diag (fixSubfield η) (fixSubfieldRestrict σ η),
      ∀ y, a (twFJModelEquiv σ η y : twistedE6RootGroup K σ) =
        (twFJModelEquiv σ η (ψ y) : twistedE6RootGroup K σ) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  let C := twistedE6RootGroup K σ
  let C₀ := twistedE6RootGroup (fixSubfield η) (fixSubfieldRestrict σ η)
  let J := twFJ σ η
  let j : C₀ ≃* J := twFJModelEquiv σ η
  change ∃ ψ ∈ twistedE6Inn (fixSubfield η) (fixSubfieldRestrict σ η) ⊔
      twistedE6Diag (fixSubfield η) (fixSubfieldRestrict σ η),
    ∀ y : C₀, a (j y : C) = (j (ψ y) : C)
  let qp : TauCeti.PrimePower := ⟨ℓ, f, hℓ, hf⟩
  have hqp : qp.card = ℓ ^ f := TauCeti.PrimePower.card_def qp
  have hKq : Nat.card K = qp.card ^ 2 := by rw [hqp, hK]
  have hσq : ∀ c, σ c = c ^ qp.card := by intro c; rw [hqp]; exact hσ c
  obtain ⟨q₀, hq₀p, hqq, hF⟩ :=
    exists_primePower_fixSubfield_twisted (m := 2) (by norm_num) hKq η Nat.prime_three
      (by norm_num) hη
  have hK₀ : Nat.card (fixSubfield η) = (ℓ ^ q₀.exponent) ^ 2 := by
    rw [hF, TauCeti.PrimePower.card_def, hq₀p]
  have hσ₀ : ∀ c : fixSubfield η,
      fixSubfieldRestrict σ η c = c ^ (ℓ ^ q₀.exponent) := by
    intro c
    rw [fixSubfieldRestrict_eq_pow_twE6 hqq (by norm_num : Odd 3) σ hσq η hF c,
      TauCeti.PrimePower.card_def, hq₀p]
  obtain ⟨-, -, -, -, -, -, -, hnormal₀, ⟨Θ₀, hΘ₀, -, hker₀, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ q₀.exponent_pos
      (fixSubfield η) hK₀ (fixSubfieldRestrict σ η) hσ₀
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  have haJ : ∀ y ∈ J, a y ∈ J := fun y hy =>
    mem_twFJ_of_commute hℓ hf hK σ hσ Nat.prime_three (by norm_num) hη haη hy
  have haJ' : ∀ y ∈ J, a⁻¹ y ∈ J := fun y hy =>
    mem_twFJ_of_commute hℓ hf hK σ hσ Nat.prime_three (by norm_num) hη
      (Commute.inv_left haη) hy
  let aJ : MulAut J :=
    { toFun := fun y => ⟨a (y : C), haJ y y.2⟩
      invFun := fun y => ⟨a⁻¹ (y : C), haJ' y y.2⟩
      left_inv := fun y => Subtype.ext (MulAut.inv_apply_self C a (y : C))
      right_inv := fun y => Subtype.ext (MulAut.apply_inv_self C a (y : C))
      map_mul' := fun y z => Subtype.ext (map_mul a (y : C) (z : C)) }
  let ψ : MulAut C₀ := MulAut.congr j.symm aJ
  have hψ : ∀ y : C₀, ((j (ψ y) : J) : C) = a ((j y : J) : C) := by
    intro y
    have h1 : ψ y = j.symm (aJ (j y)) := by
      change (MulAut.congr j.symm aJ) y = j.symm (aJ (j y))
      rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
        MulEquiv.symm_symm]
    rw [h1, MulEquiv.apply_symm_apply]
    rfl
  obtain ⟨g', u', δ₀, hψnf⟩ := hnormal₀ ψ
  have hΘ₀ψ : Θ₀ ψ = δ₀ := hΘ₀ ψ g' u' δ₀ hψnf
  obtain ⟨τ, hτ⟩ := exists_ringEquiv_comp_subtype (fixSubfield η).subtype δ₀
  have hjconj : ∀ g y : C₀,
      ((j (MulAut.conj g y) : J) : C) =
        MulAut.conj ((j g : J) : C) ((j y : J) : C) := by
    intro g y
    refine Subtype.ext ?_
    exact twFJModelEquiv_conj σ η g y
  obtain ⟨ũ, hũ⟩ := exists_compatDiagAutHom_twFJModelEquiv σ η u'
  have hjdiag : ∀ y : C₀,
      ((j (compatDiagAutHom TwistTag.E6 (fixSubfield η)
          (fixSubfieldRestrict σ η).toRingHom u' y) : J) : C) =
        (compatDiagAutHom TwistTag.E6 K σ.toRingHom ũ ((j y : J) : C) : C) := by
    intro y
    refine Subtype.ext ?_
    exact hũ y
  have hjfield : ∀ (τ' : K ≃+* K) (δ' : fixSubfield η ≃+* fixSubfield η),
      (∀ c : fixSubfield η,
        τ' ((fixSubfield η).subtype c) = (fixSubfield η).subtype (δ' c)) →
      ∀ y : C₀,
        ((j (fieldActor (t := TwistTag.E6) (fixSubfieldRestrict σ η) δ' y) : J) : C) =
          fieldActor (t := TwistTag.E6) σ τ' ((j y : J) : C) := by
    intro τ' δ' hτ' y
    refine Subtype.ext ?_
    exact fieldActor_twFJModelEquiv σ η τ' δ' hτ' y
  let d' : MulAut C :=
    MulAut.conj ((j g' : J) : C) * compatDiagAutHom TwistTag.E6 K σ.toRingHom ũ
  have hd'D : d' ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
    have h1 : MulAut.conj ((j g' : J) : C) ∈ twistedE6Inn K σ :=
      MonoidHom.mem_range.2 ⟨((j g' : J) : C), rfl⟩
    have h2 : compatDiagAutHom TwistTag.E6 K σ.toRingHom ũ ∈ twistedE6Diag K σ :=
      MonoidHom.mem_range.2 ⟨ũ, rfl⟩
    exact Subgroup.mul_mem (H := twistedE6Inn K σ ⊔ twistedE6Diag K σ)
      (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right (S := twistedE6Inn K σ) h2)
  have happly : ∀ y : C₀, a ((j y : J) : C) =
      d' (fieldActor (t := TwistTag.E6) σ τ ((j y : J) : C)) := by
    intro y
    calc
      a ((j y : J) : C) = ((j (ψ y) : J) : C) := (hψ y).symm
      _ = ((j ((MulAut.conj g' * compatDiagAutHom TwistTag.E6 (fixSubfield η)
            (fixSubfieldRestrict σ η).toRingHom u' * fieldActor (t := TwistTag.E6)
            (fixSubfieldRestrict σ η) δ₀) y) : J) : C) := by rw [hψnf]
      _ = ((j (MulAut.conj g' (compatDiagAutHom TwistTag.E6 (fixSubfield η)
            (fixSubfieldRestrict σ η).toRingHom u' (fieldActor (t := TwistTag.E6)
            (fixSubfieldRestrict σ η) δ₀ y))) : J) : C) := by
          rw [MulAut.mul_apply, MulAut.mul_apply]
      _ = MulAut.conj ((j g' : J) : C)
            ((j (compatDiagAutHom TwistTag.E6 (fixSubfield η)
              (fixSubfieldRestrict σ η).toRingHom u' (fieldActor (t := TwistTag.E6)
              (fixSubfieldRestrict σ η) δ₀ y)) : J) : C) := hjconj g' _
      _ = MulAut.conj ((j g' : J) : C)
            (compatDiagAutHom TwistTag.E6 K σ.toRingHom ũ
              ((j (fieldActor (t := TwistTag.E6) (fixSubfieldRestrict σ η) δ₀ y) : J) : C)) := by
          rw [hjdiag]
      _ = MulAut.conj ((j g' : J) : C)
            (compatDiagAutHom TwistTag.E6 K σ.toRingHom ũ
              (fieldActor (t := TwistTag.E6) σ τ ((j y : J) : C))) := by
          rw [hjfield τ δ₀ hτ y]
      _ = d' (fieldActor (t := TwistTag.E6) σ τ ((j y : J) : C)) := rfl
  let β : MulAut C := d'⁻¹ * a * (fieldActor (t := TwistTag.E6) σ τ)⁻¹
  have hτinv : ∀ c : fixSubfield η,
      τ⁻¹ ((fixSubfield η).subtype c) = (fixSubfield η).subtype (δ₀⁻¹ c) := by
    intro c
    have h := hτ (δ₀⁻¹ c)
    simpa using (congrArg (fun z => τ⁻¹ z) h).symm
  have hfieldinv : (fieldActor (t := TwistTag.E6) σ τ)⁻¹ =
      fieldActor (t := TwistTag.E6) σ τ⁻¹ := by
    rw [← fieldActorHom_apply, ← fieldActorHom_apply, map_inv]
  have hcancel : (fieldActor (t := TwistTag.E6) (fixSubfieldRestrict σ η) δ₀ *
      fieldActor (t := TwistTag.E6) (fixSubfieldRestrict σ η) δ₀⁻¹) = 1 := by
    rw [← fieldActor_mul, mul_inv_cancel, fieldActor_one]
  have hcancel_apply : ∀ y : C₀,
      fieldActor (t := TwistTag.E6) (fixSubfieldRestrict σ η) δ₀
        (fieldActor (t := TwistTag.E6) (fixSubfieldRestrict σ η) δ₀⁻¹ y) = y := by
    intro y
    rw [← MulAut.mul_apply, hcancel, MulAut.one_apply]
  have hβfix : ∀ z ∈ J, β z = z := by
    intro z hz
    obtain ⟨y, hy⟩ := j.surjective ⟨z, hz⟩
    have hzy : ((j y : J) : C) = z := congrArg Subtype.val hy
    rw [← hzy]
    have hjfieldinv : ((j (fieldActor (t := TwistTag.E6) (fixSubfieldRestrict σ η)
          δ₀⁻¹ y) : J) : C) = (fieldActor (t := TwistTag.E6) σ τ)⁻¹ ((j y : J) : C) := by
      rw [hfieldinv]
      exact hjfield τ⁻¹ δ₀⁻¹ hτinv y
    calc
      β ((j y : J) : C) = d'⁻¹ (a ((fieldActor (t := TwistTag.E6) σ τ)⁻¹
          ((j y : J) : C))) := by simp only [β, MulAut.mul_apply]
      _ = d'⁻¹ (a ((j (fieldActor (t := TwistTag.E6) (fixSubfieldRestrict σ η)
            δ₀⁻¹ y) : J) : C)) := by rw [hjfieldinv]
      _ = d'⁻¹ (d' (fieldActor (t := TwistTag.E6) σ τ
            ((j (fieldActor (t := TwistTag.E6) (fixSubfieldRestrict σ η)
              δ₀⁻¹ y) : J) : C))) := by rw [happly]
      _ = d'⁻¹ (d' ((j y : J) : C)) := by
        rw [← hjfield τ δ₀ hτ (fieldActor (t := TwistTag.E6) (fixSubfieldRestrict σ η)
          δ₀⁻¹ y), hcancel_apply]
      _ = ((j y : J) : C) := by rw [MulAut.inv_apply_self]
  obtain ⟨η', hβeq⟩ := exists_fieldActor_eq_of_fix_twFJ hℓ hf hK σ hσ η hβfix
  have hΘd' : Θ d' = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    exact hd'D
  have hΘa : Θ a = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    exact ha
  have hΘτ : Θ (fieldActor (t := TwistTag.E6) σ τ) = τ :=
    hΘ _ 1 1 τ (by rw [map_one, map_one, one_mul, one_mul])
  have hΘτinv : Θ (fieldActor (t := TwistTag.E6) σ τ⁻¹) = τ⁻¹ :=
    hΘ _ 1 1 τ⁻¹ (by rw [map_one, map_one, one_mul, one_mul])
  have hΘβ : Θ β = τ⁻¹ := by
    change Θ (d'⁻¹ * a * (fieldActor (t := TwistTag.E6) σ τ)⁻¹) = τ⁻¹
    rw [hfieldinv, map_mul, map_mul, map_inv, hΘd', hΘa, hΘτinv]
    simp
  have hΘη' : Θ (fieldActor (t := TwistTag.E6) σ η') = η' :=
    hΘ _ 1 1 η' (by rw [map_one, map_one, one_mul, one_mul])
  have hη'eq : η' = τ⁻¹ := by
    rw [hβeq, hΘη'] at hΘβ
    exact hΘβ
  have hβeq' : β = fieldActor (t := TwistTag.E6) σ τ⁻¹ := by
    rw [hβeq, hη'eq]
  have hfix0 : ∀ y : C₀,
      fieldActor (t := TwistTag.E6) (fixSubfieldRestrict σ η) δ₀⁻¹ y = y := by
    intro y
    apply j.injective
    refine Subtype.ext ?_
    refine Subtype.ext ?_
    have hβy : (fieldActor (t := TwistTag.E6) σ τ⁻¹) ((j y : J) : C) = ((j y : J) : C) := by
      rw [← hβeq']
      exact hβfix ((j y : J) : C) (j y).2
    calc
      ((j (fieldActor (t := TwistTag.E6) (fixSubfieldRestrict σ η) δ₀⁻¹ y) : J) :
          ModGL TwistTag.E6.tag K) =
        ((fieldActor (t := TwistTag.E6) σ τ⁻¹ ((j y : J) : C) : C) :
          ModGL TwistTag.E6.tag K) :=
          congrArg (fun z : C => (z : ModGL TwistTag.E6.tag K))
            (hjfield τ⁻¹ δ₀⁻¹ hτinv y)
      _ = ((j y : J) : ModGL TwistTag.E6.tag K) :=
          congrArg (fun z : C => (z : ModGL TwistTag.E6.tag K)) hβy
  have hfield0 : (fieldActor (t := TwistTag.E6) (fixSubfieldRestrict σ η) δ₀⁻¹) = 1 := by
    apply MulEquiv.ext
    exact hfix0
  have hΘ₀field : Θ₀ (fieldActor (t := TwistTag.E6) (fixSubfieldRestrict σ η) δ₀⁻¹) =
      δ₀⁻¹ := hΘ₀ _ 1 1 δ₀⁻¹ (by rw [map_one, map_one, one_mul, one_mul])
  have hδ0inv : δ₀⁻¹ = 1 := by
    rw [hfield0, map_one] at hΘ₀field
    exact hΘ₀field.symm
  have hδ0 : δ₀ = 1 := by
    rw [← inv_inv δ₀, hδ0inv, inv_one]
  refine ⟨ψ, ?_, ?_⟩
  · have h1 : MulAut.conj g' ∈ twistedE6Inn (fixSubfield η) (fixSubfieldRestrict σ η) :=
      MonoidHom.mem_range.2 ⟨g', rfl⟩
    have h2 : compatDiagAutHom TwistTag.E6 (fixSubfield η)
        (fixSubfieldRestrict σ η).toRingHom u' ∈
        twistedE6Diag (fixSubfield η) (fixSubfieldRestrict σ η) :=
      MonoidHom.mem_range.2 ⟨u', rfl⟩
    rw [hψnf, hδ0, fieldActor_one, mul_one]
    exact Subgroup.mul_mem (H := twistedE6Inn (fixSubfield η)
        (fixSubfieldRestrict σ η) ⊔ twistedE6Diag (fixSubfield η) (fixSubfieldRestrict σ η))
      (Subgroup.mem_sup_left h1)
      (Subgroup.mem_sup_right (S := twistedE6Inn (fixSubfield η) (fixSubfieldRestrict σ η)) h2)
  · intro y
    exact (hψ y).symm

end Model
