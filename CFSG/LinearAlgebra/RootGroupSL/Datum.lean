module

public import Mathlib.LinearAlgebra.SpecialLinearGroup

public section

namespace CFSG.LinearAlgebra.RootGroupSL

variable {k E X : Type} [Field k] [Field E] [Algebra k E] [AddCommGroup X] [Module k X]

abbrev DSpace (E X : Type) : Type := E × X × E

variable (X) in
@[expose] def shearE (φ : E →ₗ[k] E) : DSpace E X ≃ₗ[k] DSpace E X where
  toFun v := (v.1 + φ v.2.2, v.2.1, v.2.2)
  invFun v := (v.1 - φ v.2.2, v.2.1, v.2.2)
  map_add' u v := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, map_add] <;> abel
  map_smul' c v := by
    ext <;> simp [smul_add]
  left_inv v := by
    ext <;> simp
  right_inv v := by
    ext <;> simp

variable (k X) in
@[expose] def rootEquiv (t : E) : DSpace E X ≃ₗ[k] DSpace E X :=
  shearE X (LinearMap.mulLeft k t)

@[expose] def unipElt (φ : X →ₗ[k] E) (χ : E →ₗ[k] X) (ψ : E →ₗ[k] E) :
    DSpace E X ≃ₗ[k] DSpace E X where
  toFun v := (v.1 + φ v.2.1 + ψ v.2.2, v.2.1 + χ v.2.2, v.2.2)
  invFun v := (v.1 - φ (v.2.1 - χ v.2.2) - ψ v.2.2, v.2.1 - χ v.2.2, v.2.2)
  map_add' u v := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, map_add] <;> abel
  map_smul' c v := by
    ext <;> simp [smul_add]
  left_inv v := by
    ext <;> simp <;> abel
  right_inv v := by
    ext <;> simp <;> abel

private lemma shearE_add_aux (φ ψ : E →ₗ[k] E) :
    shearE X (φ + ψ) = shearE X φ * shearE X ψ := by
  ext v <;> simp [shearE, map_add] <;> abel
private lemma rootEquiv_add_aux (s t : E) :
    rootEquiv k X (s + t) = rootEquiv k X s * rootEquiv k X t := by
  simp only [rootEquiv]
  have h : LinearMap.mulLeft k (s + t) = LinearMap.mulLeft k s + LinearMap.mulLeft k t := by
    ext x; simp [LinearMap.mulLeft_apply, add_mul]
  rw [h, shearE_add_aux]
private lemma unipElt_mul_aux (φ φ' : X →ₗ[k] E) (χ χ' : E →ₗ[k] X) (ψ ψ' : E →ₗ[k] E) :
    unipElt φ χ ψ * unipElt φ' χ' ψ' =
      unipElt (φ + φ') (χ + χ') (ψ + ψ' + φ ∘ₗ χ') := by
  ext v <;> simp [unipElt, map_add] <;> abel

private def prodShear {A B : Type} [AddCommGroup A] [Module k A]
    [AddCommGroup B] [Module k B] (L : B →ₗ[k] A) : (A × B) ≃ₗ[k] (A × B) where
  toFun v := (v.1 + L v.2, v.2)
  invFun v := (v.1 - L v.2, v.2)
  map_add' u v := by ext <;> simp only [Prod.fst_add, Prod.snd_add, map_add] <;> abel
  map_smul' c v := by ext <;> simp [smul_add]
  left_inv v := by ext <;> simp
  right_inv v := by ext <;> simp

private lemma det_prodCongr {A B : Type} [AddCommGroup A] [Module k A] [Module.Finite k A]
    [AddCommGroup B] [Module k B] [Module.Finite k B]
    (e₁ : A ≃ₗ[k] A) (e₂ : B ≃ₗ[k] B) :
    LinearEquiv.det (e₁.prodCongr e₂) = LinearEquiv.det e₁ * LinearEquiv.det e₂ := by
  apply Units.ext
  simp only [LinearEquiv.coe_det, LinearEquiv.coe_prodCongr, Units.val_mul,
    LinearMap.det_prodMap]

private lemma det_prodShear {A B : Type} [AddCommGroup A] [Module k A] [Module.Finite k A]
    [AddCommGroup B] [Module k B] [Module.Finite k B] (L : B →ₗ[k] A) :
    LinearEquiv.det (prodShear L) = 1 := by
  classical
  let bA := Module.finBasis k A
  let bB := Module.finBasis k B
  have hmat : LinearMap.toMatrix (bA.prod bB) (bA.prod bB)
      (prodShear L : A × B →ₗ[k] A × B) =
      Matrix.fromBlocks (1 : Matrix _ _ k) (LinearMap.toMatrix bB bA L) 0 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [LinearMap.toMatrix_apply, prodShear, Module.Basis.prod, Matrix.one_apply,
        Finsupp.single_apply, eq_comm]
  apply Units.ext
  simp only [LinearEquiv.coe_det, Units.val_one]
  rw [← LinearMap.det_toMatrix (bA.prod bB), hmat, Matrix.det_fromBlocks_zero₂₁]
  simp

@[expose] def blockDiag (a : E ≃ₗ[k] E) (g : X ≃ₗ[k] X) (b : E ≃ₗ[k] E) :
    DSpace E X ≃ₗ[k] DSpace E X :=
  a.prodCongr (g.prodCongr b)

variable (k) in
@[expose] def mulLeftEquiv (s : Eˣ) : E ≃ₗ[k] E :=
  LinearEquiv.ofLinear (LinearMap.mulLeft k (s : E)) (LinearMap.mulLeft k ((s⁻¹ : Eˣ) : E))
    (by ext x; simp [LinearMap.comp_apply, LinearMap.mulLeft_apply, mul_assoc])
    (by ext x; simp [LinearMap.comp_apply, LinearMap.mulLeft_apply, mul_assoc])

variable (k E X) in
@[expose] def flagW : Submodule k (DSpace E X) :=
  LinearMap.ker (LinearMap.snd k E (X × E))

variable (k E X) in
@[expose] def flagK : Submodule k (DSpace E X) :=
  LinearMap.ker ((LinearMap.snd k X E).comp (LinearMap.snd k E (X × E)))

variable (k E X) in
@[expose] def rootGrp : Subgroup (DSpace E X ≃ₗ[k] DSpace E X) where
  carrier := {g | ∃ t : E, g = rootEquiv k X t}
  mul_mem' := by
    rintro g h ⟨s, rfl⟩ ⟨t, rfl⟩
    refine ⟨s + t, ?_⟩
    ext v <;> simp [rootEquiv, shearE, LinearMap.mulLeft_apply, add_mul] <;> abel
  one_mem' := ⟨0, by ext v <;> simp [rootEquiv, shearE]⟩
  inv_mem' := by
    rintro g ⟨t, rfl⟩
    refine ⟨-t, ?_⟩
    ext v <;> simp [rootEquiv, shearE, LinearMap.mulLeft_apply] <;> abel

variable (k E X) in
@[expose] def unipRad : Subgroup (DSpace E X ≃ₗ[k] DSpace E X) where
  carrier := {g | (∀ v ∈ flagW k E X, g v = v) ∧ (∀ v ∈ flagK k E X, g v - v ∈ flagW k E X) ∧
    ∀ v, g v - v ∈ flagK k E X}
  mul_mem' := by
    rintro g h ⟨hgW, hgK, hgM⟩ ⟨hhW, hhK, hhM⟩
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      rw [LinearEquiv.mul_apply, hhW v hv, hgW v hv]
    · intro v hv
      have h1 : h v - v ∈ flagW k E X := hhK v hv
      have h2 : g v - v ∈ flagW k E X := hgK v hv
      have h3 : g (h v - v) = h v - v := hgW _ h1
      have h4 : (g * h) v - v = (g v - v) + g (h v - v) := by
        rw [LinearEquiv.mul_apply, show h v = v + (h v - v) by abel, map_add]
        abel
      rw [h4, h3]
      exact add_mem h2 h1
    · intro v
      have h1 : h v - v ∈ flagK k E X := hhM v
      have h2 : g v - v ∈ flagK k E X := hgM v
      have h3 : g (h v - v) - (h v - v) ∈ flagK k E X := hgM (h v - v)
      have h4 : g (h v - v) ∈ flagK k E X := by
        have hh := add_mem h1 h3
        have heq : (h v - v) + (g (h v - v) - (h v - v)) = g (h v - v) := by abel
        rwa [heq] at hh
      have h5 : (g * h) v - v = (g v - v) + g (h v - v) := by
        rw [LinearEquiv.mul_apply, show h v = v + (h v - v) by abel, map_add]
        abel
      rw [h5]
      exact add_mem h2 h4
  one_mem' := ⟨by intro v _; rfl, by intro v _; simp, by intro v; simp⟩
  inv_mem' := by
    rintro g ⟨hgW, hgK, hgM⟩
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      have h := congrArg (fun w : DSpace E X => g.symm w) (hgW v hv)
      have h' : v = g.symm v := by simpa using h
      exact h'.symm
    · intro v hv
      have hvW : g v - v ∈ flagW k E X := hgK v hv
      have hw : g (g⁻¹ v - v) = -(g v - v) := by
        rw [map_sub]
        rw [show g (g⁻¹ v) = v by exact LinearEquiv.apply_symm_apply g v]
        abel
      have hwW : g (g⁻¹ v - v) ∈ flagW k E X := by
        rw [hw]; exact neg_mem hvW
      have hfix : g (g (g⁻¹ v - v)) = g (g⁻¹ v - v) := hgW _ hwW
      have heq : g (g⁻¹ v - v) = g⁻¹ v - v := by
        have h := congrArg (fun w : DSpace E X => g.symm w) hfix
        simpa using h
      rw [← heq]
      exact hwW
    · intro v
      have hu : v - g⁻¹ v ∈ flagK k E X := by
        simpa using hgM (g⁻¹ v)
      have heq : g⁻¹ v - v = -(v - g⁻¹ v) := by abel
      rw [heq]
      exact neg_mem hu

variable (k E X) in
@[expose] def rootSL : Subgroup (SpecialLinearGroup k (DSpace E X)) :=
  (rootGrp k E X).comap SpecialLinearGroup.toLinearEquiv

variable (k E X) in
@[expose] def QK : Subgroup (SpecialLinearGroup k (DSpace E X)) :=
  (unipRad k E X).comap SpecialLinearGroup.toLinearEquiv

theorem rootEquiv_add (s t : E) :
    rootEquiv k X (s + t) = rootEquiv k X s * rootEquiv k X t :=
  rootEquiv_add_aux s t

theorem shearE_injective : Function.Injective (shearE (k := k) (E := E) X) := by
  intro φ ψ h
  ext b
  have h' := congrArg (fun e : DSpace E X ≃ₗ[k] DSpace E X => (e (0, (0 : X), b)).1) h
  simpa [shearE] using h'

variable [Module.Finite k E] [Module.Finite k X] in
theorem det_shearE (φ : E →ₗ[k] E) : LinearEquiv.det (shearE X φ) = 1 := by
  rw [show shearE X φ = prodShear (φ ∘ₗ LinearMap.snd k X E) by
    ext v <;> simp [shearE, prodShear]]
  exact det_prodShear _

variable [Module.Finite k E] [Module.Finite k X] in
theorem det_unipElt (φ : X →ₗ[k] E) (χ : E →ₗ[k] X) (ψ : E →ₗ[k] E) :
    LinearEquiv.det (unipElt φ χ ψ) = 1 := by
  have hfac : unipElt φ χ ψ =
      unipElt φ 0 0 * unipElt 0 χ 0 * unipElt 0 0 (ψ - φ ∘ₗ χ) := by
    rw [unipElt_mul_aux, unipElt_mul_aux]
    ext v <;> simp [unipElt] <;> abel
  have hd1 : LinearEquiv.det (unipElt φ 0 0) = 1 := by
    rw [show unipElt φ 0 0 = prodShear (φ ∘ₗ LinearMap.fst k X E) by
      ext v <;> simp [unipElt, prodShear]]
    exact det_prodShear _
  have hd2 : LinearEquiv.det (unipElt 0 χ 0) = 1 := by
    rw [show unipElt (0 : X →ₗ[k] E) χ 0 = (1 : E ≃ₗ[k] E).prodCongr (prodShear χ) by
      ext v <;> simp [unipElt, prodShear]]
    rw [det_prodCongr, show LinearEquiv.det (1 : E ≃ₗ[k] E) = 1 by simp, one_mul]
    exact det_prodShear χ
  have hd3 : LinearEquiv.det (unipElt (0 : X →ₗ[k] E) (0 : E →ₗ[k] X) (ψ - φ ∘ₗ χ)) = 1 := by
    rw [show unipElt (0 : X →ₗ[k] E) (0 : E →ₗ[k] X) (ψ - φ ∘ₗ χ) =
        prodShear ((ψ - φ ∘ₗ χ) ∘ₗ LinearMap.snd k X E) by
      ext v <;> simp [unipElt, prodShear]]
    exact det_prodShear _
  rw [hfac, map_mul, map_mul, hd1, hd2, hd3, one_mul, one_mul]

variable [Module.Finite k E] [Module.Finite k X] in
theorem det_blockDiag (a : E ≃ₗ[k] E) (g : X ≃ₗ[k] X) (b : E ≃ₗ[k] E) :
    LinearEquiv.det (blockDiag a g b) =
      LinearEquiv.det a * LinearEquiv.det g * LinearEquiv.det b := by
  rw [blockDiag, det_prodCongr, det_prodCongr, mul_assoc]

theorem unipElt_mul (φ φ' : X →ₗ[k] E) (χ χ' : E →ₗ[k] X) (ψ ψ' : E →ₗ[k] E) :
    unipElt φ χ ψ * unipElt φ' χ' ψ' =
      unipElt (φ + φ') (χ + χ') (ψ + ψ' + φ ∘ₗ χ') :=
  unipElt_mul_aux φ φ' χ χ' ψ ψ'

theorem shearE_eq_unipElt (φ : E →ₗ[k] E) : shearE X φ = unipElt 0 0 φ := by
  ext v <;> simp [shearE, unipElt]

theorem blockDiag_mul_shearE_mul_inv (a : E ≃ₗ[k] E) (g : X ≃ₗ[k] X) (b : E ≃ₗ[k] E)
    (φ : E →ₗ[k] E) :
    blockDiag a g b * shearE X φ * (blockDiag a g b)⁻¹ =
      shearE X (a.toLinearMap ∘ₗ φ ∘ₗ b.symm.toLinearMap) := by
  ext v <;> simp [blockDiag, shearE, LinearMap.comp_apply]

theorem blockDiag_mul_unipElt_mul_inv (a : E ≃ₗ[k] E) (g : X ≃ₗ[k] X) (b : E ≃ₗ[k] E)
    (φ : X →ₗ[k] E) (χ : E →ₗ[k] X) (ψ : E →ₗ[k] E) :
    blockDiag a g b * unipElt φ χ ψ * (blockDiag a g b)⁻¹ =
      unipElt (a.toLinearMap ∘ₗ φ ∘ₗ g.symm.toLinearMap)
        (g.toLinearMap ∘ₗ χ ∘ₗ b.symm.toLinearMap)
        (a.toLinearMap ∘ₗ ψ ∘ₗ b.symm.toLinearMap) := by
  ext v <;> simp [blockDiag, unipElt, LinearMap.comp_apply]

theorem unipElt_mem_unipRad (φ : X →ₗ[k] E) (χ : E →ₗ[k] X) (ψ : E →ₗ[k] E) :
    unipElt φ χ ψ ∈ unipRad k E X := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    simp only [flagW, LinearMap.mem_ker, LinearMap.snd_apply] at hv
    ext <;> simp [unipElt, hv]
  · intro v hv
    simp only [flagK, LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.snd_apply] at hv
    simp only [flagW, LinearMap.mem_ker, LinearMap.snd_apply]
    simp [unipElt, hv, Prod.ext_iff]
  · intro v
    simp only [flagK, LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.snd_apply]
    simp [unipElt]

theorem exists_unipElt_of_mem_unipRad {g : DSpace E X ≃ₗ[k] DSpace E X}
    (hg : g ∈ unipRad k E X) :
    ∃ (φ : X →ₗ[k] E) (χ : E →ₗ[k] X) (ψ : E →ₗ[k] E), g = unipElt φ χ ψ := by
  obtain ⟨hgW, hgK, hgM⟩ := hg
  let eX : X →ₗ[k] DSpace E X :=
    LinearMap.prod (0 : X →ₗ[k] E) (LinearMap.prod LinearMap.id (0 : X →ₗ[k] E))
  let eE : E →ₗ[k] DSpace E X :=
    LinearMap.prod (0 : E →ₗ[k] E) (LinearMap.prod (0 : E →ₗ[k] X) LinearMap.id)
  let φ : X →ₗ[k] E := (LinearMap.fst k E (X × E)).comp (g.toLinearMap.comp eX)
  let ψ : E →ₗ[k] E := (LinearMap.fst k E (X × E)).comp (g.toLinearMap.comp eE)
  let χ : E →ₗ[k] X :=
    ((LinearMap.fst k X E).comp (LinearMap.snd k E (X × E))).comp (g.toLinearMap.comp eE)
  refine ⟨φ, χ, ψ, ?_⟩
  apply LinearEquiv.ext
  intro v
  obtain ⟨a, x, b⟩ := v
  have hW : g (a, 0, 0) = (a, 0, 0) := hgW _ (by simp [flagW])
  have hXmem : (0, x, 0) ∈ flagK k E X := by simp [flagK]
  have hXW : g (0, x, 0) - (0, x, 0) ∈ flagW k E X := hgK _ hXmem
  have hXK : g (0, x, 0) - (0, x, 0) ∈ flagK k E X := hgM _
  have hX2 : (g (0, x, 0)).2 = (x, 0) := by
    have h := hXW
    simp only [flagW, LinearMap.mem_ker, LinearMap.snd_apply] at h
    exact sub_eq_zero.mp (by simpa using h)
  have hX3 : (g (0, x, 0)).2.2 = 0 := by
    have h := hXK
    simp only [flagK, LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.snd_apply] at h
    exact sub_eq_zero.mp (by simpa using h)
  have hX1 : (g (0, x, 0)).1 = φ x := by simp [φ, eX]
  have hX : g (0, x, 0) = (φ x, x, 0) :=
    Prod.ext hX1 (Prod.ext (by rw [hX2]) hX3)
  have hE3 : (g (0, 0, b)).2.2 = b := by
    have h := hgM (0, 0, b)
    simp only [flagK, LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.snd_apply] at h
    exact sub_eq_zero.mp (by simpa using h)
  have hE1 : (g (0, 0, b)).1 = ψ b := by simp [ψ, eE]
  have hE2 : (g (0, 0, b)).2.1 = χ b := by simp [χ, eE]
  have hE : g (0, 0, b) = (ψ b, χ b, b) :=
    Prod.ext hE1 (Prod.ext hE2 hE3)
  rw [show (a, x, b) = (a, 0, 0) + ((0, x, 0) + (0, 0, b)) by ext <;> simp,
    map_add, map_add, hW, hX, hE]
  simp [unipElt] <;> abel

theorem mem_rootSL_iff {g : SpecialLinearGroup k (DSpace E X)} :
    g ∈ rootSL k E X ↔ ∃ t : E, (g : DSpace E X ≃ₗ[k] DSpace E X) = rootEquiv k X t :=
  Iff.rfl

theorem mem_QK_iff {g : SpecialLinearGroup k (DSpace E X)} :
    g ∈ QK k E X ↔ (g : DSpace E X ≃ₗ[k] DSpace E X) ∈ unipRad k E X :=
  Iff.rfl

theorem rootEquiv_mem_unipRad (t : E) : rootEquiv k X t ∈ unipRad k E X := by
  rw [rootEquiv, shearE_eq_unipElt]
  exact unipElt_mem_unipRad 0 0 (LinearMap.mulLeft k t)

variable (k X) [Module.Finite k E] [Module.Finite k X] in
@[expose] def rootElt (t : E) : SpecialLinearGroup k (DSpace E X) :=
  ⟨rootEquiv k X t, det_shearE _⟩

variable [Module.Finite k E] [Module.Finite k X] in
theorem rootElt_mem_rootSL (t : E) : rootElt k X t ∈ rootSL k E X :=
  ⟨t, rfl⟩

theorem rootSL_le_QK : rootSL k E X ≤ QK k E X := by
  rintro g ⟨t, ht⟩
  refine mem_QK_iff.mpr ?_
  change SpecialLinearGroup.toLinearEquiv g ∈ unipRad k E X
  rw [ht]
  exact rootEquiv_mem_unipRad t

theorem mulLeftEquiv_apply (s : Eˣ) (x : E) : mulLeftEquiv k s x = (s : E) * x := by
  rw [mulLeftEquiv, LinearEquiv.ofLinear_apply, LinearMap.mulLeft_apply]

theorem blockDiag_mul (a a' : E ≃ₗ[k] E) (g g' : X ≃ₗ[k] X) (b b' : E ≃ₗ[k] E) :
    blockDiag a g b * blockDiag a' g' b' = blockDiag (a * a') (g * g') (b * b') := by
  ext v <;> simp [blockDiag, LinearEquiv.mul_apply]

theorem blockDiag_one : blockDiag (1 : E ≃ₗ[k] E) (1 : X ≃ₗ[k] X) (1 : E ≃ₗ[k] E) = 1 := by
  ext v <;> simp [blockDiag]

theorem blockDiag_inv (a : E ≃ₗ[k] E) (g : X ≃ₗ[k] X) (b : E ≃ₗ[k] E) :
    (blockDiag a g b)⁻¹ = blockDiag a⁻¹ g⁻¹ b⁻¹ := by
  ext v <;> simp [blockDiag]

theorem unipElt_inj {φ φ' : X →ₗ[k] E} {χ χ' : E →ₗ[k] X} {ψ ψ' : E →ₗ[k] E} :
    unipElt φ χ ψ = unipElt φ' χ' ψ' ↔ φ = φ' ∧ χ = χ' ∧ ψ = ψ' := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · ext x
      have h' := congrArg (fun e : DSpace E X ≃ₗ[k] DSpace E X => (e (0, x, 0)).1) h
      simpa [unipElt] using h'
    · ext b
      have h' := congrArg (fun e : DSpace E X ≃ₗ[k] DSpace E X => (e (0, 0, b)).2.1) h
      simpa [unipElt] using h'
    · ext b
      have h' := congrArg (fun e : DSpace E X ≃ₗ[k] DSpace E X => (e (0, 0, b)).1) h
      simpa [unipElt] using h'
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem unipElt_zero : unipElt (0 : X →ₗ[k] E) (0 : E →ₗ[k] X) (0 : E →ₗ[k] E) = 1 := by
  ext v <;> simp [unipElt]

end CFSG.LinearAlgebra.RootGroupSL
