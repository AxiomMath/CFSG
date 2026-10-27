module

public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveSymplecticLocalComponentSplit
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveUnitaryLocalComponentUnitary
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRestrictionCentralizer

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectiveSymplectic

open Module CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  {B : LinearMap.BilinForm K V}

theorem exists_centralizer_equiv_unitary {E : Type} [Field E] [Module E V] {σ : E →+* E}
    (Hf : V →ₛₗ[σ] V →ₗ[E] E) (T : sesqUnitaryGroup B)
    (hlin : ∀ g : Module.End K V, g * spOp T = spOp T * g →
      ∀ (c : E) (v : V), g (c • v) = c • g v)
    (hT : ∀ (g : V →ₗ[E] V) (v : V), g (spOp T v) = spOp T (g v))
    (hK : ∀ (g : V →ₗ[E] V) (a : K) (v : V), g (a • v) = a • g v)
    (hiff : ∀ g : LinearMap.GeneralLinearGroup K V,
      g ∈ similitudeCentralizer B (T : LinearMap.GeneralLinearGroup K V) ↔
        g ∈ Subgroup.centralizer {(T : LinearMap.GeneralLinearGroup K V)} ∧
          ∀ v w, Hf ((g : Module.End K V) v) ((g : Module.End K V) w) = Hf v w) :
    ∃ e : Subgroup.centralizer {T} ≃* sesqUnitaryGroup Hf,
      ∀ (x : Subgroup.centralizer {T}) (v : V),
        (((e x : sesqUnitaryGroup Hf) : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V) v =
          spOp (x : sesqUnitaryGroup B) v := by
  have hcx : ∀ x : Subgroup.centralizer {T},
      spOp (x : sesqUnitaryGroup B) * spOp T = spOp T * spOp (x : sesqUnitaryGroup B) :=
    fun x => congrArg (fun y : sesqUnitaryGroup B => spOp y)
      (Subgroup.mem_centralizer_singleton_iff.mp x.2)
  let mkE : ∀ g : Module.End K V, g * spOp T = spOp T * g → V →ₗ[E] V := fun g hg =>
    { toFun := g
      map_add' := g.map_add
      map_smul' := hlin g hg }
  let fwdFun : Subgroup.centralizer {T} → LinearMap.GeneralLinearGroup E V := fun x =>
    ⟨mkE _ (hcx x), mkE _ (hcx x⁻¹),
      LinearMap.ext fun v => summand_gl_inv_apply ((x : sesqUnitaryGroup B) :
        LinearMap.GeneralLinearGroup K V) v,
      LinearMap.ext fun v => summand_gl_apply_inv ((x : sesqUnitaryGroup B) :
        LinearMap.GeneralLinearGroup K V) v⟩
  let fwd : Subgroup.centralizer {T} →* sesqUnitaryGroup Hf :=
    { toFun := fun x => ⟨fwdFun x, fun v w => ((hiff _).mp (centralizerSimEquiv T x).2).2 v w⟩
      map_one' := Subtype.ext (Units.ext (LinearMap.ext fun _ => rfl))
      map_mul' := fun _ _ => Subtype.ext (Units.ext (LinearMap.ext fun _ => rfl)) }
  let mkK : (V →ₗ[E] V) → Module.End K V := fun φ =>
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := hK φ }
  have hinj : Function.Injective fwd := fun x y hxy => by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro v
    exact LinearMap.congr_fun (congrArg Units.val (congrArg Subtype.val hxy)) v
  have hsurj : Function.Surjective fwd := by
    intro g
    let gK : LinearMap.GeneralLinearGroup K V :=
      ⟨mkK ((g : LinearMap.GeneralLinearGroup E V) : V →ₗ[E] V),
        mkK (((g : LinearMap.GeneralLinearGroup E V)⁻¹ : LinearMap.GeneralLinearGroup E V) :
          V →ₗ[E] V),
        LinearMap.ext fun v => summand_gl_inv_apply (g : LinearMap.GeneralLinearGroup E V) v,
        LinearMap.ext fun v => summand_gl_apply_inv (g : LinearMap.GeneralLinearGroup E V) v⟩
    have hgT : gK ∈ Subgroup.centralizer {(T : LinearMap.GeneralLinearGroup K V)} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Units.ext (LinearMap.ext fun v => hT _ v)
    have hgS := (hiff gK).mpr ⟨hgT, fun v w => mem_sesqUnitaryGroup.mp g.2 v w⟩
    refine ⟨⟨⟨gK, hgS.1⟩, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hgS.2))⟩, ?_⟩
    exact Subtype.ext (Units.ext (LinearMap.ext fun _ => rfl))
  exact ⟨MulEquiv.ofBijective fwd ⟨hinj, hsurj⟩, fun _ _ => rfl⟩

theorem isSolvable_of_commute_specialUnitary {E : Type} [Field E] [Module E V] {p f : ℕ}
    (hU : UnitaryFieldData p f E) (hp : p ≠ 2) [FiniteDimensional E V] (hm : 2 ≤ finrank E V)
    {Hf : V →ₛₗ[hU.bar] V →ₗ[E] E} (hH : Hf.IsSymm) (hnd : Hf.Nondegenerate)
    (ι : K →+* hU.fixedField) (hι : ∀ (a : K) (v : V), ((ι a : hU.fixedField) : E) • v = a • v)
    (hιs : Function.Surjective ι) (hB : B.IsAlt) (hBnd : B.Nondegenerate)
    (hinv : ∀ g ∈ sesqSpecialUnitaryGroup Hf, ∀ u v,
      B ((g : V →ₗ[E] V) u) ((g : V →ₗ[E] V) v) = B u v)
    {R : Subgroup (sesqUnitaryGroup B)}
    (hRc : ∀ r ∈ R, ∀ g ∈ sesqSpecialUnitaryGroup Hf, ∀ v,
      spOp r ((g : V →ₗ[E] V) v) = (g : V →ₗ[E] V) (spOp r v)) :
    Group.IsSolvable R := by
  have hsmul : ∀ (g : Module.End K V) (c : hU.fixedField) (v : V), g (c • v) = c • g v := by
    intro g c v
    obtain ⟨a, rfl⟩ := hιs c
    change g (((ι a : hU.fixedField) : E) • v) = ((ι a : hU.fixedField) : E) • g v
    rw [hι, hι, map_smul]
  let mkF : Module.End K V → V →ₗ[hU.fixedField] V := fun g =>
    { toFun := g
      map_add' := g.map_add
      map_smul' := hsmul g }
  let B' : LinearMap.BilinForm hU.fixedField V := LinearMap.mk₂ hU.fixedField
    (fun v w => ι (B v w))
    (fun v₁ v₂ w => by rw [map_add, LinearMap.add_apply, map_add])
    (fun c v w => by
      obtain ⟨a, rfl⟩ := hιs c
      change ι (B (((ι a : hU.fixedField) : E) • v) w) = ι a • ι (B v w)
      rw [hι, map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, smul_eq_mul])
    (fun v w₁ w₂ => by rw [map_add, map_add])
    (fun c v w => by
      obtain ⟨a, rfl⟩ := hιs c
      change ι (B v (((ι a : hU.fixedField) : E) • w)) = ι a • ι (B v w)
      rw [hι, map_smul, smul_eq_mul, map_mul, smul_eq_mul])
  have hB' : ∀ v w, B' v w = ι (B v w) := fun _ _ => rfl
  have hB'nd : B'.Nondegenerate :=
    ⟨fun v hv => hBnd.1 v fun w => ι.injective (by rw [map_zero, ← hB']; exact hv w),
      fun w hw => hBnd.2 w fun v => ι.injective (by rw [map_zero, ← hB']; exact hw v)⟩
  have hB'alt : B'.IsAlt := fun v => by rw [hB', hB v, map_zero]
  have hinv' : ∀ g ∈ sesqSpecialUnitaryGroup Hf, ∀ u v,
      B' ((g : V →ₗ[E] V) u) ((g : V →ₗ[E] V) v) = B' u v := fun g hg u v => by
    rw [hB', hB', hinv g hg u v]
  have hsolv := (unitary_restriction_symplectic_centralizer_solvable hU hp hm hH hnd B' hB'nd
    hB'alt hinv').1
  let toF : R → LinearMap.GeneralLinearGroup hU.fixedField V := fun r =>
    ⟨mkF (spOp (r : sesqUnitaryGroup B)), mkF (spOp ((r⁻¹ : R) : sesqUnitaryGroup B)),
      LinearMap.ext fun v => summand_gl_inv_apply (((r : sesqUnitaryGroup B)) :
        LinearMap.GeneralLinearGroup K V) v,
      LinearMap.ext fun v => summand_gl_apply_inv (((r : sesqUnitaryGroup B)) :
        LinearMap.GeneralLinearGroup K V) v⟩
  have htoFB : ∀ r : R, toF r ∈ bilinIsometryGroup B' := fun r x y => by
    change B' (spOp (r : sesqUnitaryGroup B) x) (spOp (r : sesqUnitaryGroup B) y) = B' x y
    rw [hB', hB', mem_sesqUnitaryGroup.mp (r : sesqUnitaryGroup B).2 x y]
  have htoFc : ∀ r : R, (⟨toF r, htoFB r⟩ : bilinIsometryGroup B') ∈ Subgroup.centralizer
      ((((sesqSpecialUnitaryGroup Hf).map (glRestrictScalars hU.fixedField)).subgroupOf
        (bilinIsometryGroup B')) : Set (bilinIsometryGroup B')) := by
    intro r
    rw [Subgroup.mem_centralizer_iff]
    rintro ⟨y, hyB⟩ hy
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy
    obtain ⟨g, hg, rfl⟩ := hy
    refine Subtype.ext (Units.ext (LinearMap.ext fun v => ?_))
    change (g : V →ₗ[E] V) (spOp (r : sesqUnitaryGroup B) v) =
      spOp (r : sesqUnitaryGroup B) ((g : V →ₗ[E] V) v)
    exact (hRc _ r.2 g hg v).symm
  let ψ : R →* Subgroup.centralizer
      ((((sesqSpecialUnitaryGroup Hf).map (glRestrictScalars hU.fixedField)).subgroupOf
        (bilinIsometryGroup B')) : Set (bilinIsometryGroup B')) :=
    { toFun := fun r => ⟨⟨toF r, htoFB r⟩, htoFc r⟩
      map_one' := Subtype.ext (Subtype.ext (Units.ext (LinearMap.ext fun _ => rfl)))
      map_mul' := fun _ _ => Subtype.ext (Subtype.ext (Units.ext (LinearMap.ext fun _ => rfl))) }
  have hψ : Function.Injective ψ := fun r₁ r₂ h12 => by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro v
    exact LinearMap.congr_fun (congrArg Units.val (congrArg Subtype.val
      (congrArg Subtype.val h12))) v
  exact Group.isSolvable_of_isSolvable_injective hψ

theorem unitary_case {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) [FiniteDimensional K V] {r : ℕ} (hr : 1 ≤ r)
    (hdim : finrank K V = 2 * r) (hB : B.IsAlt) (hBnd : B.Nondegenerate)
    {T : sesqUnitaryGroup B} (hTns : ∀ c : K, spOp T ≠ c • 1)
    (hTT : spOp T * spOp T = (-1 : K) • 1) (hns : ∀ l : K, l ^ 2 ≠ -1)
    {L : Subgroup (Subgroup.centralizer {T})} (hL : CFSG.IsComponent L)
    {R : Subgroup (sesqUnitaryGroup B)}
    (hR : R ≤ Subgroup.centralizer ((L.map (Subgroup.centralizer {T}).subtype :
      Subgroup (sesqUnitaryGroup B)) : Set (sesqUnitaryGroup B)))
    (hRp : ⁅R, R⁆ = R) : R = ⊥ := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have h2 : (2 : K) ≠ 0 := by
    have hchar : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
    refine Ring.two_ne_zero ?_
    rw [ringChar.eq K ℓ]
    exact hℓ2
  obtain ⟨-, -, hnonsplit⟩ := odd_symplectic_scalar_square_centralizer_structure hℓ hℓ2 hf hK hr
    hdim hB hBnd (A := (T : LinearMap.GeneralLinearGroup K V)) hTns
    (neg_ne_zero.mpr one_ne_zero) hTT (μ := 1)
    (fun v w => by rw [one_mul]; exact mem_sesqUnitaryGroup.mp T.2 v w)
  obtain ⟨hmemE, hF, hcard, hfinrank, bar, hbar, hbarpow, -, -, hneg⟩ := hnonsplit hns
  obtain ⟨Hf, -, hsymm, hsep, hiff⟩ := hneg (by rw [div_neg, div_one])
  let : Field (scalarSquareField (spOp T)) := hF.toField
  have hU : UnitaryFieldData ℓ f (scalarSquareField (spOp T)) :=
    ⟨hℓ, hf, by rw [hcard, ← pow_mul, mul_comm]⟩
  have hbareq : bar = hU.bar := RingHom.ext fun x => by rw [hbarpow, UnitaryFieldData.bar_apply]
  subst hbareq
  have : Module.Finite (scalarSquareField (spOp T)) V :=
    CatalogueBOrthogonalScalarSquareField.evaluationModule_finite (spOp T)
  obtain ⟨e, he⟩ := exists_centralizer_equiv_unitary Hf T
    (fun g hg => (CatalogueBOrthogonalScalarSquareField.commute_iff_evaluation_linear
      (spOp T) g).mp hg)
    (fun g v => by
      have h1 := g.map_smul (CatalogueBOrthogonalScalarSquareField.generator (spOp T)) v
      rwa [CatalogueBOrthogonalScalarSquareField.evaluation_generator_smul,
        CatalogueBOrthogonalScalarSquareField.evaluation_generator_smul] at h1)
    (fun g a v => by
      have h1 := g.map_smul (algebraMap K (scalarSquareField (spOp T)) a) v
      rwa [CatalogueBOrthogonalScalarSquareField.evaluation_algebraMap_smul,
        CatalogueBOrthogonalScalarSquareField.evaluation_algebraMap_smul] at h1)
    hiff
  obtain ⟨hm, -, hSU⟩ := eq_unitarySpecial_of_isComponent hU hℓ2 (by rw [hfinrank]; exact hr)
    hsymm hsep (isComponent_map_of_isComponent e hL)
  have hcorr : ∀ g ∈ sesqSpecialUnitaryGroup Hf, ∃ x ∈ L, ∀ v,
      spOp (x : sesqUnitaryGroup B) v =
        ((g : LinearMap.GeneralLinearGroup (scalarSquareField (spOp T)) V) :
          V →ₗ[scalarSquareField (spOp T)] V) v := by
    intro g hg
    have hgU := (mem_sesqSpecialUnitaryGroup.mp hg).1
    have hmem : (⟨g, hgU⟩ : sesqUnitaryGroup Hf) ∈ L.map e.toMonoidHom := by
      rw [hSU, mem_unitarySpecial]
      exact (mem_sesqSpecialUnitaryGroup.mp hg).2
    obtain ⟨x, hx, hxg⟩ := hmem
    refine ⟨x, hx, fun v => ?_⟩
    rw [← he x v]
    exact congrArg (fun y : sesqUnitaryGroup Hf =>
      ((y : LinearMap.GeneralLinearGroup (scalarSquareField (spOp T)) V) :
        V →ₗ[scalarSquareField (spOp T)] V) v) hxg
  have hinv : ∀ g ∈ sesqSpecialUnitaryGroup Hf, ∀ u v,
      B (((g : LinearMap.GeneralLinearGroup (scalarSquareField (spOp T)) V) :
        V →ₗ[scalarSquareField (spOp T)] V) u)
        (((g : LinearMap.GeneralLinearGroup (scalarSquareField (spOp T)) V) :
          V →ₗ[scalarSquareField (spOp T)] V) v) = B u v := by
    intro g hg u v
    obtain ⟨x, -, hx⟩ := hcorr g hg
    rw [← hx, ← hx]
    exact mem_sesqUnitaryGroup.mp (x : sesqUnitaryGroup B).2 u v
  have hRc : ∀ r' ∈ R, ∀ g ∈ sesqSpecialUnitaryGroup Hf, ∀ v,
      spOp r' (((g : LinearMap.GeneralLinearGroup (scalarSquareField (spOp T)) V) :
        V →ₗ[scalarSquareField (spOp T)] V) v) =
        ((g : LinearMap.GeneralLinearGroup (scalarSquareField (spOp T)) V) :
          V →ₗ[scalarSquareField (spOp T)] V) (spOp r' v) := by
    intro r' hr' g hg v
    obtain ⟨x, hx, hxg⟩ := hcorr g hg
    rw [← hxg, ← hxg]
    have h1 := Subgroup.mem_centralizer_iff.mp (hR hr') _ (Subgroup.mem_map_of_mem _ hx)
    exact (LinearMap.congr_fun (congrArg (fun y : sesqUnitaryGroup B => spOp y) h1) v).symm
  have hfixK : ∀ a : K, algebraMap K (scalarSquareField (spOp T)) a ∈ hU.fixedField := by
    intro a
    rw [UnitaryFieldData.mem_fixedField]
    apply Subtype.ext
    rw [hbar (algebraMap K (scalarSquareField (spOp T)) a) a 0
      (by rw [zero_smul, add_zero]; exact Algebra.algebraMap_eq_smul_one a),
      zero_smul, sub_zero]
    exact (Algebra.algebraMap_eq_smul_one a).symm
  let ι : K →+* hU.fixedField :=
    (algebraMap K (scalarSquareField (spOp T))).codRestrict hU.fixedField hfixK
  have hι : ∀ (a : K) (v : V), ((ι a : hU.fixedField) : scalarSquareField (spOp T)) • v =
      a • v := fun a v =>
    CatalogueBOrthogonalScalarSquareField.evaluation_algebraMap_smul (spOp T) a v
  have hιs : Function.Surjective ι := by
    intro c
    obtain ⟨a, b, hab⟩ := (hmemE ((c : scalarSquareField (spOp T)) : Module.End K V)).mp
      (c : scalarSquareField (spOp T)).2
    have hc := (hU.mem_fixedField).mp c.2
    have h1 := hbar (c : scalarSquareField (spOp T)) a b hab
    rw [hc, hab] at h1
    have hb : b = 0 := by
      by_contra hb0
      have h3 : (2 * b) • spOp T = 0 := by
        rw [mul_smul, two_smul]
        linear_combination (norm := module) h1
      have h4 : spOp T = 0 := (smul_eq_zero.mp h3).resolve_left (mul_ne_zero h2 hb0)
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      apply hv
      have h6 := summand_gl_apply_inv (T : LinearMap.GeneralLinearGroup K V) v
      rw [show ((T : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = 0 from by
        change spOp T v = 0
        rw [h4]
        rfl, map_zero] at h6
      exact h6.symm
    refine ⟨a, Subtype.ext (Subtype.ext ?_)⟩
    change algebraMap K (Module.End K V) a = _
    rw [hab, hb, zero_smul, add_zero, Algebra.algebraMap_eq_smul_one]
  have hsolv : Group.IsSolvable R :=
    isSolvable_of_commute_specialUnitary hU hℓ2 (by rw [hfinrank] at hm ⊢; exact hm) hsymm
      (CatalogueBUnitaryB.nondegenerate_of_isSymm hsymm hsep) ι hι hιs hB hBnd hinv hRc
  by_contra hne
  have : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).mpr hne
  have : Group.IsPerfect R := Subgroup.isPerfect_iff.mpr hRp
  exact Group.IsPerfect.not_isSolvable R inferInstance

end CFSG.LocalAnalysis.ComponentInitial.ProjectiveSymplectic
