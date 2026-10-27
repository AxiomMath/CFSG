module

public import CFSG.LinearAlgebra.FixedPointFreeOrderThreeCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataFaithful
public import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Semilin
public import CFSG.HardMathSupport.Dickson.Bal207.OrthFixedType
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LinearAlgebra

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.HardMathSupport.Dickson.Bal207.OrthFix

variable {W : Type*} [CommGroup W]

@[expose] noncomputable def coordinateAddEquiv
    (e : W ≃* Multiplicative (Fin 3 → OmegaField)) :
    Additive W ≃+ (Fin 3 → OmegaField) :=
  MulEquiv.toAdditiveLeft e

@[expose] noncomputable def coordinateConj
    (e : W ≃* Multiplicative (Fin 3 → OmegaField)) (g : MulAut W) :
    (Fin 3 → OmegaField) ≃+ (Fin 3 → OmegaField) :=
  ((coordinateAddEquiv e).symm.trans (MulEquiv.toAdditive g)).trans (coordinateAddEquiv e)

@[simp] theorem coordinateAddEquiv_ofMul
    (e : W ≃* Multiplicative (Fin 3 → OmegaField)) (w : W) :
    coordinateAddEquiv e (Additive.ofMul w) = Multiplicative.toAdd (e w) :=
  rfl

@[simp] theorem coordinateAddEquiv_symm_ofMul
    (e : W ≃* Multiplicative (Fin 3 → OmegaField)) (w : W) :
    (coordinateAddEquiv e).symm (Multiplicative.toAdd (e w)) = Additive.ofMul w := by
  rw [← coordinateAddEquiv_ofMul e w]
  exact AddEquiv.symm_apply_apply _ _

@[simp] theorem coordinateConj_apply
    (e : W ≃* Multiplicative (Fin 3 → OmegaField)) (g : MulAut W)
    (x : Fin 3 → OmegaField) :
    coordinateConj e g x =
      coordinateAddEquiv e (MulEquiv.toAdditive g ((coordinateAddEquiv e).symm x)) :=
  rfl

theorem coordinateConj_ofMul
    (e : W ≃* Multiplicative (Fin 3 → OmegaField)) (g : MulAut W) (w : W) :
    coordinateConj e g (coordinateAddEquiv e (Additive.ofMul w)) =
      coordinateAddEquiv e (Additive.ofMul (g w)) := by
  simp [coordinateConj]

theorem coordinateConj_z_eq_omega_smul
    (e : W ≃* Multiplicative (Fin 3 → OmegaField))
    {z : MulAut W}
    (he : ∀ w : W,
      Multiplicative.toAdd (e (z w)) = omega • Multiplicative.toAdd (e w))
    (x : Fin 3 → OmegaField) :
    coordinateConj e z x = omega • x := by
  obtain ⟨a, rfl⟩ := (coordinateAddEquiv e).surjective x
  set w : W := Additive.toMul a with hw
  have ha : a = Additive.ofMul w := by rw [hw]; rfl
  rw [ha, coordinateConj_ofMul, coordinateAddEquiv_ofMul, he, coordinateAddEquiv_ofMul]

theorem coordinateConj_omega_of_commute
    (e : W ≃* Multiplicative (Fin 3 → OmegaField))
    {z g : MulAut W}
    (he : ∀ w : W,
      Multiplicative.toAdd (e (z w)) = omega • Multiplicative.toAdd (e w))
    (hgz : g * z = z * g) (x : Fin 3 → OmegaField) :
    coordinateConj e g (omega • x) = omega • coordinateConj e g x := by
  obtain ⟨a, rfl⟩ := (coordinateAddEquiv e).surjective x
  set w : W := Additive.toMul a with hw
  have ha : a = Additive.ofMul w := by rw [hw]; rfl
  rw [ha]
  have hgz' : ∀ v : W, g (z v) = z (g v) := by
    intro v
    have := congrArg (fun h : MulAut W => h v) hgz
    simpa [MulAut.mul_apply] using this
  have hstep : ∀ v : W, coordinateAddEquiv e (Additive.ofMul (z v)) =
      omega • coordinateAddEquiv e (Additive.ofMul v) := by
    intro v
    rw [coordinateAddEquiv_ofMul, he v, coordinateAddEquiv_ofMul]
  rw [show omega • coordinateAddEquiv e (Additive.ofMul w) =
      coordinateAddEquiv e (Additive.ofMul (z w)) from (hstep w).symm]
  rw [coordinateConj_ofMul, hgz' w, hstep (g w), coordinateConj_ofMul]

theorem coordinateConj_omega_of_conj_sq
    (e : W ≃* Multiplicative (Fin 3 → OmegaField))
    {z g : MulAut W}
    (he : ∀ w : W,
      Multiplicative.toAdd (e (z w)) = omega • Multiplicative.toAdd (e w))
    (hgz : g * z * g⁻¹ = z ^ 2) (x : Fin 3 → OmegaField) :
    coordinateConj e g (omega • x) = omega ^ 2 • coordinateConj e g x := by
  obtain ⟨a, rfl⟩ := (coordinateAddEquiv e).surjective x
  set w : W := Additive.toMul a with hw
  have ha : a = Additive.ofMul w := by rw [hw]; rfl
  rw [ha]
  have hgz' : ∀ v : W, g (z v) = z (z (g v)) := by
    intro v
    have h' : g * z = z ^ 2 * g := by
      have := congrArg (fun h : MulAut W => h * g) hgz
      simpa [mul_assoc] using this
    have := congrArg (fun h : MulAut W => h v) h'
    simpa [MulAut.mul_apply, pow_two] using this
  have hstep : ∀ v : W, coordinateAddEquiv e (Additive.ofMul (z v)) =
      omega • coordinateAddEquiv e (Additive.ofMul v) := by
    intro v
    rw [coordinateAddEquiv_ofMul, he v, coordinateAddEquiv_ofMul]
  rw [show omega • coordinateAddEquiv e (Additive.ofMul w) =
      coordinateAddEquiv e (Additive.ofMul (z w)) from (hstep w).symm]
  rw [coordinateConj_ofMul, hgz' w, hstep (z (g w)), hstep (g w), pow_two, smul_smul,
    coordinateConj_ofMul]

@[expose] noncomputable def coordinateConjLin
    (e : W ≃* Multiplicative (Fin 3 → OmegaField)) (g : MulAut W) :
    (Fin 3 → OmegaField) ≃ₗ[ZMod 2] (Fin 3 → OmegaField) :=
  LinearEquiv.ofBijective
    ((coordinateConj e g).toAddMonoidHom.toZModLinearMap 2)
    (coordinateConj e g).bijective

@[simp] theorem coordinateConjLin_apply
    (e : W ≃* Multiplicative (Fin 3 → OmegaField)) (g : MulAut W)
    (x : Fin 3 → OmegaField) :
    coordinateConjLin e g x = coordinateConj e g x :=
  rfl

@[simp] theorem coordinateConjLin_symm_apply
    (e : W ≃* Multiplicative (Fin 3 → OmegaField)) (g : MulAut W)
    (x : Fin 3 → OmegaField) :
    (coordinateConjLin e g).symm x = (coordinateConj e g).symm x := by
  apply (coordinateConjLin e g).injective
  rw [LinearEquiv.apply_symm_apply, coordinateConjLin_apply,
    AddEquiv.apply_symm_apply]

@[expose] noncomputable def coordinateConjGL
    (e : W ≃* Multiplicative (Fin 3 → OmegaField)) (g : MulAut W) :
    LinearMap.GeneralLinearGroup (ZMod 2) (Fin 3 → OmegaField) :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv (coordinateConjLin e g)

@[simp] theorem coordinateConjGL_apply
    (e : W ≃* Multiplicative (Fin 3 → OmegaField)) (g : MulAut W)
    (x : Fin 3 → OmegaField) :
    (coordinateConjGL e g :
      (Fin 3 → OmegaField) →ₗ[ZMod 2] (Fin 3 → OmegaField)) x =
      coordinateConj e g x := by
  rw [coordinateConjGL, LinearMap.GeneralLinearGroup.coe_ofLinearEquiv,
    coordinateConjLin_apply]

theorem coordinateConjGL_z_apply
    (e : W ≃* Multiplicative (Fin 3 → OmegaField))
    {z : MulAut W}
    (he : ∀ w : W,
      Multiplicative.toAdd (e (z w)) = omega • Multiplicative.toAdd (e w))
    (x : Fin 3 → OmegaField) :
    (coordinateConjGL e z :
      (Fin 3 → OmegaField) →ₗ[ZMod 2] (Fin 3 → OmegaField)) x = omega • x := by
  rw [coordinateConjGL_apply, coordinateConj_z_eq_omega_smul e he]

theorem coordinateConj_linear_of_commute
    (e : W ≃* Multiplicative (Fin 3 → OmegaField))
    {z g : MulAut W}
    (he : ∀ w : W,
      Multiplicative.toAdd (e (z w)) = omega • Multiplicative.toAdd (e w))
    (hgz : g * z = z * g) :
    ∀ (c : OmegaField) (x : Fin 3 → OmegaField),
      coordinateConj e g (c • x) = c • coordinateConj e g x := by
  let gLin := coordinateConjLin e g
  let zLin := coordinateConjLin e z
  let gBin := coordinateConjGL e g
  let zBin := coordinateConjGL e z
  have hz_smul : ∀ x : Fin 3 → OmegaField,
      (zBin : (Fin 3 → OmegaField) →ₗ[ZMod 2] (Fin 3 → OmegaField)) x = omega • x := by
    intro x
    exact coordinateConjGL_z_apply e he x
  have hω : ∀ x : Fin 3 → OmegaField,
      omega • x = (zBin : (Fin 3 → OmegaField) →ₗ[ZMod 2] (Fin 3 → OmegaField)) x :=
    fun x => (hz_smul x).symm
  have hcommLin : gLin * zLin = zLin * gLin := by
    apply LinearEquiv.ext
    intro x
    simp only [gLin, zLin, LinearEquiv.mul_apply]
    rw [coordinateConjLin_apply, coordinateConjLin_apply,
      coordinateConjLin_apply, coordinateConjLin_apply,
      coordinateConj_z_eq_omega_smul e he x,
      coordinateConj_omega_of_commute e he hgz x,
      coordinateConj_z_eq_omega_smul e he (coordinateConj e g x)]
  have hcomm : gBin * zBin = zBin * gBin := by
    have h := congrArg (LinearMap.GeneralLinearGroup.ofLinearEquiv) hcommLin
    simpa [gBin, zBin, coordinateConjGL,
      LinearMap.GeneralLinearGroup.ofLinearEquiv_mul] using h
  intro c x
  simpa [gBin, coordinateConjGL_apply] using
    (commute_iff_omega_linear hω gBin).mp hcomm c x

theorem coordinateConj_semilinear_of_conj_sq
    (e : W ≃* Multiplicative (Fin 3 → OmegaField))
    {z g : MulAut W}
    (he : ∀ w : W,
      Multiplicative.toAdd (e (z w)) = omega • Multiplicative.toAdd (e w))
    (hgz : g * z * g⁻¹ = z ^ 2) :
    ∀ (c : OmegaField) (x : Fin 3 → OmegaField),
      coordinateConj e g (c • x) = frobeniusOmega c • coordinateConj e g x := by
  let gLin := coordinateConjLin e g
  let zLin := coordinateConjLin e z
  let gBin := coordinateConjGL e g
  let zBin := coordinateConjGL e z
  have hz_smul : ∀ x : Fin 3 → OmegaField,
      (zBin : (Fin 3 → OmegaField) →ₗ[ZMod 2] (Fin 3 → OmegaField)) x = omega • x := by
    intro x
    exact coordinateConjGL_z_apply e he x
  have hω : ∀ x : Fin 3 → OmegaField,
      omega • x = (zBin : (Fin 3 → OmegaField) →ₗ[ZMod 2] (Fin 3 → OmegaField)) x :=
    fun x => (hz_smul x).symm
  have hconjLin : gLin * zLin * gLin⁻¹ = zLin ^ 2 := by
    apply LinearEquiv.ext
    intro x
    simp only [gLin, zLin, LinearEquiv.coe_inv, LinearEquiv.mul_apply, pow_two]
    rw [coordinateConjLin_apply, coordinateConjLin_apply,
      coordinateConjLin_symm_apply, coordinateConjLin_apply, coordinateConjLin_apply,
      coordinateConj_z_eq_omega_smul e he ((coordinateConj e g).symm x),
      coordinateConj_omega_of_conj_sq e he hgz,
      coordinateConj_z_eq_omega_smul e he x,
      coordinateConj_z_eq_omega_smul e he (omega • x)]
    simp [smul_smul, pow_two]
  have hconj : gBin * zBin * gBin⁻¹ = zBin ^ 2 := by
    have h := congrArg (LinearMap.GeneralLinearGroup.ofLinearEquiv) hconjLin
    simpa [gBin, zBin, coordinateConjGL, pow_two,
      LinearMap.GeneralLinearGroup.ofLinearEquiv_mul,
      LinearMap.GeneralLinearGroup.ofLinearEquiv_inv] using h
  intro c x
  simpa [gBin, coordinateConjGL_apply, frobeniusOmega_apply] using
    (conj_eq_sq_iff_semilinear hω gBin).mp hconj c x

theorem exists_coordinate_semilinear_action_of_normalizes_three
    (hW : ∀ w : W, w ^ 2 = 1)
    (z : MulAut W) (hz : orderOf z = 3)
    (e : W ≃* Multiplicative (Fin 3 → OmegaField))
    (he : ∀ w : W,
      Multiplicative.toAdd (e (z w)) = omega • Multiplicative.toAdd (e w))
    (A : Subgroup (MulAut W))
    (hAN : A ≤ Subgroup.normalizer (Subgroup.zpowers z : Set (MulAut W))) :
    ∃ ρ : A →* coordinateSemilinearGroup 3 OmegaField,
      Function.Injective ρ ∧
      (∀ (g : A) (w : W),
        Multiplicative.toAdd (e ((g : MulAut W) w)) =
          coordinateSemilinearMap (ρ g) (Multiplicative.toAdd (e w))) ∧
      (SemidirectProduct.rightHom.comp ρ).ker =
        (Subgroup.centralizer ({z} : Set (MulAut W))).subgroupOf A := by
  classical
  have hWexp : ∀ w : W, w ^ 2 = 1 := hW
  have hdich : ∀ g : A,
      (g : MulAut W) * z * (g : MulAut W)⁻¹ = z ∨
        (g : MulAut W) * z * (g : MulAut W)⁻¹ = z ^ 2 :=
    fun g => conj_eq_or_eq_sq_of_mem_normalizer hz (hAN g.2)
  let σ : A → (OmegaField ≃+* OmegaField) := fun g =>
    if (g : MulAut W) * z * (g : MulAut W)⁻¹ = z then RingEquiv.refl _ else frobeniusOmega
  have hsem : ∀ g : A, ∀ (c : OmegaField) (x : Fin 3 → OmegaField),
      coordinateConj e (g : MulAut W) (c • x) =
        σ g c • coordinateConj e (g : MulAut W) x := by
    intro g
    by_cases h : (g : MulAut W) * z * (g : MulAut W)⁻¹ = z
    · have hgz : (g : MulAut W) * z = z * (g : MulAut W) := by
        have := congrArg (fun h : MulAut W => h * (g : MulAut W)) h
        simpa [mul_assoc] using this
      simpa [σ, h] using coordinateConj_linear_of_commute e he hgz
    · have hsq : (g : MulAut W) * z * (g : MulAut W)⁻¹ = z ^ 2 := by
        rcases hdich g with hz1 | hz2
        · exact absurd hz1 h
        · exact hz2
      simpa [σ, h, frobeniusOmega_apply] using coordinateConj_semilinear_of_conj_sq e he hsq
  let pair : A → coordinateSemilinearGroup 3 OmegaField := fun g =>
    Classical.choose (exists_pair_of_semilin (σ g) (coordinateConj e (g : MulAut W)) (hsem g))
  have pair_right : ∀ g : A, (pair g).right = σ g := fun g =>
    (Classical.choose_spec
      (exists_pair_of_semilin (σ g) (coordinateConj e (g : MulAut W)) (hsem g))).1
  have pair_map : ∀ (g : A) (x : Fin 3 → OmegaField),
      coordinateSemilinearMap (pair g) x = coordinateConj e (g : MulAut W) x := fun g =>
    (Classical.choose_spec
      (exists_pair_of_semilin (σ g) (coordinateConj e (g : MulAut W)) (hsem g))).2
  have pair_one : pair 1 = 1 := by
    apply coordinateSemilinearHom_injective (d := 3) (K := OmegaField) (by norm_num)
    apply congrArg Multiplicative.ofAdd
    ext x
    rw [pair_map, coordinateSemilinearMap_one]
    simp [coordinateConj]
  have pair_mul : ∀ g h : A, pair (g * h) = pair g * pair h := by
    intro g h
    apply coordinateSemilinearHom_injective (d := 3) (K := OmegaField) (by norm_num)
    apply congrArg Multiplicative.ofAdd
    ext x
    rw [pair_map, coordinateSemilinearMap_mul, pair_map, pair_map]
    simp [coordinateConj, AddEquiv.trans_apply]
  let ρ : A →* coordinateSemilinearGroup 3 OmegaField :=
    { toFun := pair
      map_one' := pair_one
      map_mul' := pair_mul }
  have hρmap : ∀ (g : A) (x : Fin 3 → OmegaField),
      coordinateSemilinearMap (ρ g) x = coordinateConj e (g : MulAut W) x := pair_map
  have hρinj : Function.Injective ρ := by
    intro g h hgh
    apply Subtype.ext
    ext w
    have h1 : coordinateSemilinearMap (ρ g) (coordinateAddEquiv e (Additive.ofMul w)) =
        coordinateSemilinearMap (ρ h) (coordinateAddEquiv e (Additive.ofMul w)) := by
      rw [hgh]
    rw [hρmap g, hρmap h, coordinateConj_ofMul, coordinateConj_ofMul] at h1
    exact Additive.ofMul.injective ((coordinateAddEquiv e).injective h1)
  have hact : ∀ (g : A) (w : W),
      Multiplicative.toAdd (e ((g : MulAut W) w)) =
        coordinateSemilinearMap (ρ g) (Multiplicative.toAdd (e w)) := by
    intro g w
    rw [← coordinateAddEquiv_ofMul e w, hρmap, coordinateConj_ofMul, coordinateAddEquiv_ofMul]
  have hker : (SemidirectProduct.rightHom.comp ρ).ker =
      (Subgroup.centralizer ({z} : Set (MulAut W))).subgroupOf A := by
    ext g
    constructor
    · intro hg
      rw [MonoidHom.mem_ker] at hg
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
      have hright : (ρ g).right = 1 := by simpa using hg
      have hlin : ∀ (c : OmegaField) (x : Fin 3 → OmegaField),
          coordinateSemilinearMap (ρ g) (c • x) =
            c • coordinateSemilinearMap (ρ g) x := by
        intro c x
        rw [coordinateSemilinearMap_smul, hright]
        simp
      ext w
      apply e.injective
      apply Multiplicative.toAdd.injective
      calc
        Multiplicative.toAdd (e ((g : MulAut W) (z w)))
            = coordinateSemilinearMap (ρ g) (Multiplicative.toAdd (e (z w))) := hact g (z w)
        _ = coordinateSemilinearMap (ρ g) (omega • Multiplicative.toAdd (e w)) := by rw [he w]
        _ = omega • coordinateSemilinearMap (ρ g) (Multiplicative.toAdd (e w)) := hlin omega _
        _ = omega • Multiplicative.toAdd (e ((g : MulAut W) w)) := by rw [hact g w]
        _ = Multiplicative.toAdd (e (z ((g : MulAut W) w))) :=
              (he ((g : MulAut W) w)).symm
    · intro hg
      rw [Subgroup.mem_subgroupOf] at hg
      have hgz : (g : MulAut W) * z = z * (g : MulAut W) :=
        Subgroup.mem_centralizer_singleton_iff.mp hg
      obtain ⟨q, hqright, hqmap⟩ :=
        exists_pair_of_semilin (RingEquiv.refl OmegaField)
          (coordinateConj e (g : MulAut W))
          (by
            intro c x
            simpa using coordinateConj_linear_of_commute e he hgz c x)
      have hmap_eq : coordinateSemilinearMap q = coordinateSemilinearMap (ρ g) := by
        ext x
        rw [hqmap, hρmap]
      have hright_eq := coordinateSemilinearMap_field_eq (d := 3) (K := OmegaField)
        (by norm_num) q (ρ g) hmap_eq
      rw [hqright] at hright_eq
      rw [MonoidHom.mem_ker]
      have hright : (ρ g).right = 1 := by
        rw [hright_eq.symm]
        rfl
      simpa using hright
  refine ⟨ρ, hρinj, hact, hker⟩

theorem exists_faithful_linear_kernel_action_of_normalizes_three
    (hW : ∀ w : W, w ^ 2 = 1)
    (z : MulAut W) (hz : orderOf z = 3)
    (e : W ≃* Multiplicative (Fin 3 → OmegaField))
    (he : ∀ w : W,
      Multiplicative.toAdd (e (z w)) = omega • Multiplicative.toAdd (e w))
    (A : Subgroup (MulAut W))
    (hAN : A ≤ Subgroup.normalizer (Subgroup.zpowers z : Set (MulAut W))) :
    ∃ (ρ : A →* coordinateSemilinearGroup 3 OmegaField)
      (tau : (SemidirectProduct.rightHom.comp ρ).ker →* GL (Fin 3) OmegaField),
      Function.Injective ρ ∧
      (∀ (g : A) (w : W),
        Multiplicative.toAdd (e ((g : MulAut W) w)) =
          coordinateSemilinearMap (ρ g) (Multiplicative.toAdd (e w))) ∧
      (SemidirectProduct.rightHom.comp ρ).ker =
        (Subgroup.centralizer ({z} : Set (MulAut W))).subgroupOf A ∧
      Function.Injective tau ∧
      (∀ c : (SemidirectProduct.rightHom.comp ρ).ker,
        ρ (c : A) = SemidirectProduct.inl
          (φ := glFieldAut (Fin 3) OmegaField) (tau c)) ∧
      (∀ (c : (SemidirectProduct.rightHom.comp ρ).ker) (w : W),
        Multiplicative.toAdd (e (((c : A) : MulAut W) w)) =
          (tau c : Matrix (Fin 3) (Fin 3) OmegaField).mulVec
            (Multiplicative.toAdd (e w))) := by
  classical
  obtain ⟨ρ, hρinj, hact, hker⟩ :=
    exists_coordinate_semilinear_action_of_normalizes_three hW z hz e he A hAN
  let χ : A →* (OmegaField ≃+* OmegaField) := SemidirectProduct.rightHom.comp ρ
  have hχ (c : χ.ker) : (ρ (c : A)).right = 1 := by
    have hc := MonoidHom.mem_ker.mp c.2
    simpa [χ, MonoidHom.comp_apply] using hc
  have hpair (c : χ.ker) : ρ (c : A) =
      SemidirectProduct.inl (φ := glFieldAut (Fin 3) OmegaField) ((ρ (c : A)).left) := by
    have h := SemidirectProduct.inl_left_mul_inr_right (ρ (c : A))
    rw [hχ c, map_one, mul_one] at h
    exact h.symm
  let tau : χ.ker →* GL (Fin 3) OmegaField :=
    { toFun := fun c => (ρ (c : A)).left
      map_one' := by
        change (ρ ((1 : χ.ker) : A)).left = 1
        simp
      map_mul' := by
        intro c d
        change (ρ (((c * d : χ.ker) : A))).left =
          (ρ (c : A)).left * (ρ (d : A)).left
        have hcd : ρ (((c * d : χ.ker) : A)) = ρ (c : A) * ρ (d : A) := map_mul ρ _ _
        rw [hcd, hpair c, hpair d, ← map_mul]
        simp }
  have htau_apply (c : χ.ker) : tau c = (ρ (c : A)).left := rfl
  have htau_pair (c : χ.ker) : ρ (c : A) =
      SemidirectProduct.inl (φ := glFieldAut (Fin 3) OmegaField) (tau c) := by
    rw [hpair c, htau_apply]
  have htau_inj : Function.Injective tau := by
    intro c d hcd
    apply Subtype.ext
    apply hρinj
    rw [htau_pair c, htau_pair d, hcd]
  have htau_act (c : χ.ker) (w : W) :
      Multiplicative.toAdd (e (((c : A) : MulAut W) w)) =
        (tau c : Matrix (Fin 3) (Fin 3) OmegaField).mulVec
          (Multiplicative.toAdd (e w)) := by
    have h := hact (c : A) w
    rw [hpair c, coordinateSemilinearMap_inl, matrixLinearEquiv_apply] at h
    rw [htau_apply c]
    exact h
  exact ⟨ρ, tau, hρinj, hact, hker, htau_inj, htau_pair, htau_act⟩

end CFSG.LinearAlgebra
