module

public import CFSG.FeitThompson.Representations.OddDiagonalGroupFixedMovingDualOrbits
public import CFSG.FeitThompson.Representations.FixedFreeKernelMovingCharacterPair
public import CFSG.FeitThompson.Representations.FreeCentralSectionInducedLayerIrreducible

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace DiagonalCore

open MulAction SemidirectProduct

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

def mulAutOfLinearEquiv {k E : Type*} [Semiring k] [AddCommGroup E] [Module k E] :
    (E ≃ₗ[k] E) →* MulAut (Multiplicative E) where
  toFun f := AddEquiv.toMultiplicative f.toAddEquiv
  map_one' := by ext; (rfl)
  map_mul' f g := by ext; (rfl)

@[simp] lemma mulAutOfLinearEquiv_apply {k E : Type*} [Semiring k] [AddCommGroup E] [Module k E]
    (f : E ≃ₗ[k] E) (v : E) :
    mulAutOfLinearEquiv f (Multiplicative.ofAdd v) = Multiplicative.ofAdd (f v) := (rfl)

section Model

variable {p q : ℕ} {E : Type*} [AddCommGroup E] [Module (ZMod p) E]
  {D : Subgroup (E ≃ₗ[ZMod p] E)}
  {U : Type*} [Group U] {σ : Multiplicative (ZMod q) →* MulAut U}

abbrev Cyc (q : ℕ) := Multiplicative (ZMod q)

noncomputable def toGL (r : U →* D) (b : Cyc q →* (E ≃ₗ[ZMod p] E))
    (hr : ∀ g : Cyc q, ((D.subtype).comp r).comp (σ g).toMonoidHom
      = (MulAut.conj (b g)).toMonoidHom.comp ((D.subtype).comp r)) :
    (U ⋊[σ] Cyc q) →* (E ≃ₗ[ZMod p] E) :=
  SemidirectProduct.lift ((D.subtype).comp r) b hr

noncomputable def semidirectAut (r : U →* D) (b : Cyc q →* (E ≃ₗ[ZMod p] E))
    (hr : ∀ g : Cyc q, ((D.subtype).comp r).comp (σ g).toMonoidHom
      = (MulAut.conj (b g)).toMonoidHom.comp ((D.subtype).comp r)) :
    (U ⋊[σ] Cyc q) →* MulAut (Multiplicative E) :=
  mulAutOfLinearEquiv.comp (toGL r b hr)

variable {r : U →* D} {b : Cyc q →* (E ≃ₗ[ZMod p] E)}
  {hr : ∀ g : Cyc q, ((D.subtype).comp r).comp (σ g).toMonoidHom
      = (MulAut.conj (b g)).toMonoidHom.comp ((D.subtype).comp r)}

noncomputable abbrev Amb (r : U →* D) (b : Cyc q →* (E ≃ₗ[ZMod p] E))
    (hr : ∀ g : Cyc q, ((D.subtype).comp r).comp (σ g).toMonoidHom
      = (MulAut.conj (b g)).toMonoidHom.comp ((D.subtype).comp r)) :=
  Multiplicative E ⋊[semidirectAut r b hr] (U ⋊[σ] Cyc q)

def sdpEquivProd {N G : Type*} [Group N] [Group G] (ψ : G →* MulAut N) : (N ⋊[ψ] G) ≃ N × G where
  toFun x := (x.left, x.right)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance instFintypeAmb [Fintype E] [Fintype U] [NeZero q] :
    Fintype (Amb r b hr) :=
  Fintype.ofEquiv (Multiplicative E × (U × Cyc q))
    ((sdpEquivProd (semidirectAut r b hr)).trans
      ((Equiv.refl _).prodCongr (sdpEquivProd σ))).symm

noncomputable def eSub (r : U →* D) (b : Cyc q →* (E ≃ₗ[ZMod p] E))
    (hr : ∀ g : Cyc q, ((D.subtype).comp r).comp (σ g).toMonoidHom
      = (MulAut.conj (b g)).toMonoidHom.comp ((D.subtype).comp r)) :
    Subgroup (Amb r b hr) :=
  (SemidirectProduct.inl : Multiplicative E →* Amb r b hr).range

noncomputable def subOf (r : U →* D) (b : Cyc q →* (E ≃ₗ[ZMod p] E))
    (hr : ∀ g : Cyc q, ((D.subtype).comp r).comp (σ g).toMonoidHom
      = (MulAut.conj (b g)).toMonoidHom.comp ((D.subtype).comp r)) (S : Subgroup U) :
    Subgroup (Amb r b hr) :=
  Subgroup.comap SemidirectProduct.rightHom
    (Subgroup.map (SemidirectProduct.inl : U →* U ⋊[σ] Cyc q) S)

lemma mem_subOf_iff {S : Subgroup U} {x : Amb r b hr} :
    x ∈ subOf r b hr S ↔ ∃ u ∈ S, SemidirectProduct.inl u = x.right := Iff.rfl

lemma eSub_le_subOf (S : Subgroup U) : eSub r b hr ≤ subOf r b hr S := by
  rintro _ ⟨v, rfl⟩
  exact ⟨1, S.one_mem, by simp⟩

lemma subOf_mono {S S' : Subgroup U} (h : S ≤ S') : subOf r b hr S ≤ subOf r b hr S' :=
  Subgroup.comap_mono (Subgroup.map_mono h)

noncomputable abbrev coreSub (r : U →* D) (b : Cyc q →* (E ≃ₗ[ZMod p] E))
    (hr : ∀ g : Cyc q, ((D.subtype).comp r).comp (σ g).toMonoidHom
      = (MulAut.conj (b g)).toMonoidHom.comp ((D.subtype).comp r)) :
    Subgroup (Amb r b hr) := subOf r b hr ⊤

instance : (coreSub r b hr).Normal := by
  have h : Subgroup.map (SemidirectProduct.inl : U →* U ⋊[σ] Cyc q) ⊤
      = (SemidirectProduct.inl : U →* U ⋊[σ] Cyc q).range := by
    ext x; simp [Subgroup.mem_map, MonoidHom.mem_range]
  rw [coreSub, subOf, h, SemidirectProduct.range_inl_eq_ker_rightHom]
  infer_instance

noncomputable abbrev kerSub (r : U →* D) (b : Cyc q →* (E ≃ₗ[ZMod p] E))
    (hr : ∀ g : Cyc q, ((D.subtype).comp r).comp (σ g).toMonoidHom
      = (MulAut.conj (b g)).toMonoidHom.comp ((D.subtype).comp r)) :
    Subgroup (Amb r b hr) := subOf r b hr r.ker

noncomputable abbrev tSub (r : U →* D) (b : Cyc q →* (E ≃ₗ[ZMod p] E))
    (hr : ∀ g : Cyc q, ((D.subtype).comp r).comp (σ g).toMonoidHom
      = (MulAut.conj (b g)).toMonoidHom.comp ((D.subtype).comp r)) :
    Subgroup (Amb r b hr) := kerSub r b hr

lemma tSub_le_coreSub : tSub r b hr ≤ coreSub r b hr := subOf_mono le_top

lemma toGL_inl (u : U) : toGL r b hr (SemidirectProduct.inl u) = (r u : E ≃ₗ[ZMod p] E) :=
  SemidirectProduct.lift_inl _ _ _ _

lemma toGL_inr (z : Cyc q) : toGL r b hr (SemidirectProduct.inr z) = b z :=
  SemidirectProduct.lift_inr _ _ _ _

lemma semidirectAut_apply (g : U ⋊[σ] Cyc q) (v : E) :
    semidirectAut r b hr g (Multiplicative.ofAdd v)
      = Multiplicative.ofAdd (toGL r b hr g v) := (rfl)

lemma mem_subOf_iff' {S : Subgroup U} {x : Amb r b hr} :
    x ∈ subOf r b hr S ↔ x.right.left ∈ S ∧ x.right.right = 1 := by
  rw [mem_subOf_iff]
  refine ⟨fun ⟨u, hu, hux⟩ => ⟨by rw [← hux]; exact hu, by rw [← hux]; rfl⟩, fun ⟨h1, h2⟩ => ?_⟩
  exact ⟨x.right.left, h1, SemidirectProduct.ext rfl h2.symm⟩

lemma mem_coreSub_iff {x : Amb r b hr} : x ∈ coreSub r b hr ↔ x.right.right = 1 := by
  rw [coreSub, mem_subOf_iff']
  simp

lemma mem_tSub_iff {x : Amb r b hr} :
    x ∈ tSub r b hr ↔ r x.right.left = 1 ∧ x.right.right = 1 := by
  rw [tSub, kerSub, mem_subOf_iff', MonoidHom.mem_ker]

lemma mem_eSub_iff {x : Amb r b hr} : x ∈ eSub r b hr ↔ x.right = 1 := by
  refine ⟨fun ⟨v, hv⟩ => by rw [← hv]; rfl, fun h => ⟨x.left, SemidirectProduct.ext rfl h.symm⟩⟩

lemma toGL_right_of_mem_tSub {x : Amb r b hr} (hx : x ∈ tSub r b hr) :
    toGL r b hr x.right = 1 := by
  obtain ⟨h1, h2⟩ := mem_tSub_iff.1 hx
  have hxr : x.right = SemidirectProduct.inl x.right.left :=
    SemidirectProduct.ext rfl (by rw [h2]; rfl)
  rw [hxr, toGL_inl, h1]
  rfl

lemma toGL_right_of_mem_coreSub {x : Amb r b hr} (hx : x ∈ coreSub r b hr) :
    toGL r b hr x.right = (r x.right.left : E ≃ₗ[ZMod p] E) := by
  have h2 : x.right.right = 1 := mem_coreSub_iff.1 hx
  have hxr : x.right = SemidirectProduct.inl x.right.left :=
    SemidirectProduct.ext rfl (by rw [h2]; rfl)
  conv_lhs => rw [hxr]
  rw [toGL_inl]

lemma semidirectAut_right_of_mem_tSub {x : Amb r b hr} (hx : x ∈ tSub r b hr) :
    semidirectAut r b hr x.right = 1 := by
  refine MulEquiv.ext fun y => ?_
  have h : semidirectAut r b hr x.right (Multiplicative.ofAdd (Multiplicative.toAdd y))
      = Multiplicative.ofAdd (toGL r b hr x.right (Multiplicative.toAdd y)) :=
    semidirectAut_apply _ _
  rw [toGL_right_of_mem_tSub hx] at h
  simpa using h

lemma left_conj_of_mem_tSub (g : Amb r b hr) {x : Amb r b hr} (hx : x ∈ tSub r b hr) :
    (g⁻¹ * x * g).left = semidirectAut r b hr g.right⁻¹ x.left := by
  have hx1 : semidirectAut r b hr x.right = 1 := semidirectAut_right_of_mem_tSub hx
  simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
    SemidirectProduct.inv_left, SemidirectProduct.inv_right, map_mul, hx1, mul_one, map_inv]
  rw [mul_comm _ (((semidirectAut r b hr) g.right)⁻¹ x.left), mul_assoc, inv_mul_cancel, mul_one]

lemma mem_map_inl_iff {N G : Type*} [Group N] [Group G] {φ : G →* MulAut N} {S : Subgroup N}
    {x : N ⋊[φ] G} :
    x ∈ Subgroup.map (SemidirectProduct.inl : N →* N ⋊[φ] G) S ↔ x.left ∈ S ∧ x.right = 1 := by
  refine ⟨fun ⟨s, hs, hsx⟩ => by rw [← hsx]; exact ⟨hs, rfl⟩, fun ⟨h1, h2⟩ => ?_⟩
  exact ⟨x.left, h1, SemidirectProduct.ext rfl h2.symm⟩

lemma left_conj_of_right_eq_one {N G : Type*} [Group N] [Group G] {φ : G →* MulAut N}
    (g : N ⋊[φ] G) {x : N ⋊[φ] G} (hx : x.right = 1) :
    (g * x * g⁻¹).left = g.left * φ g.right x.left * g.left⁻¹ := by
  simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right,
    SemidirectProduct.inv_left, hx, mul_one, map_inv, MulAut.apply_inv_self]

lemma map_inl_normal {N G : Type*} [Group N] [Group G] {φ : G →* MulAut N} {S : Subgroup N}
    (hS : S.Normal) (hφ : ∀ g : G, ∀ n ∈ S, φ g n ∈ S) :
    (Subgroup.map (SemidirectProduct.inl : N →* N ⋊[φ] G) S).Normal where
  conj_mem x hx g := by
    rw [mem_map_inl_iff] at hx ⊢
    obtain ⟨hx1, hx2⟩ := hx
    refine ⟨?_, by simp [SemidirectProduct.mul_right, hx2]⟩
    rw [left_conj_of_right_eq_one g hx2]
    exact hS.conj_mem _ (hφ _ _ hx1) _

lemma coe_r_sigma (hrr : ∀ g : Cyc q, ((D.subtype).comp r).comp (σ g).toMonoidHom
      = (MulAut.conj (b g)).toMonoidHom.comp ((D.subtype).comp r)) (z : Cyc q) (u : U) :
    ((r (σ z u) : E ≃ₗ[ZMod p] E)) = b z * (r u : E ≃ₗ[ZMod p] E) * (b z)⁻¹ := by
  have h := congrFun (congrArg (fun f : U →* (E ≃ₗ[ZMod p] E) => (f : U → _)) (hrr z)) u
  simpa using h

lemma sigma_mem_ker (hrr : ∀ g : Cyc q, ((D.subtype).comp r).comp (σ g).toMonoidHom
      = (MulAut.conj (b g)).toMonoidHom.comp ((D.subtype).comp r)) (z : Cyc q) {u : U}
    (hu : u ∈ r.ker) : σ z u ∈ r.ker := by
  rw [MonoidHom.mem_ker] at hu ⊢
  refine Subtype.ext ?_
  rw [coe_r_sigma hrr z u, hu]
  simp

lemma conj_b_mem_iff (hrr : ∀ g : Cyc q, ((D.subtype).comp r).comp (σ g).toMonoidHom
      = (MulAut.conj (b g)).toMonoidHom.comp ((D.subtype).comp r))
    (hrsurj : Function.Surjective r) (z : Cyc q) (d : E ≃ₗ[ZMod p] E) :
    b z * d * (b z)⁻¹ ∈ D ↔ d ∈ D := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := hrsurj ⟨b z * d * (b z)⁻¹, h⟩
    have h2 : ((r u : E ≃ₗ[ZMod p] E)) = b z * d * (b z)⁻¹ := by rw [hu]
    have h3 : ((r (σ z ((σ z).symm u)) : E ≃ₗ[ZMod p] E))
        = b z * (r ((σ z).symm u) : E ≃ₗ[ZMod p] E) * (b z)⁻¹ := coe_r_sigma hrr z _
    rw [MulEquiv.apply_symm_apply, h2] at h3
    have h4 : d = (r ((σ z).symm u) : E ≃ₗ[ZMod p] E) :=
      mul_right_cancel (mul_left_cancel (a := b z) h3)
    rw [h4]
    exact (r ((σ z).symm u)).2
  · intro h
    obtain ⟨u, hu⟩ := hrsurj ⟨d, h⟩
    have h2 : ((r u : E ≃ₗ[ZMod p] E)) = d := by rw [hu]
    have h3 := coe_r_sigma hrr z u
    rw [h2] at h3
    rw [← h3]
    exact (r (σ z u)).2

lemma ofAdd_eq_pow [NeZero q] (i : ZMod q) :
    (Multiplicative.ofAdd i : Cyc q) = (Multiplicative.ofAdd (1 : ZMod q)) ^ i.val := by
  rw [← ofAdd_nsmul]
  congr 1
  simp [ZMod.natCast_val]

lemma toGL_eq (g : U ⋊[σ] Cyc q) :
    toGL r b hr g = (r g.left : E ≃ₗ[ZMod p] E) * b g.right := by
  conv_lhs => rw [show g = SemidirectProduct.inl g.left * SemidirectProduct.inr g.right from
    SemidirectProduct.ext (by simp) (by simp)]
  rw [map_mul, toGL_inl, toGL_inr]

instance : (tSub r b hr).Normal := by
  have h : (Subgroup.map (SemidirectProduct.inl : U →* U ⋊[σ] Cyc q) r.ker).Normal :=
    map_inl_normal r.normal_ker fun z u hu => sigma_mem_ker hr z hu
  exact Subgroup.normal_comap _

noncomputable def ambToCyc (r : U →* D) (b : Cyc q →* (E ≃ₗ[ZMod p] E))
    (hr : ∀ g : Cyc q, ((D.subtype).comp r).comp (σ g).toMonoidHom
      = (MulAut.conj (b g)).toMonoidHom.comp ((D.subtype).comp r)) :
    Amb r b hr →* Cyc q :=
  (SemidirectProduct.rightHom : (U ⋊[σ] Cyc q) →* Cyc q).comp
    (SemidirectProduct.rightHom : Amb r b hr →* (U ⋊[σ] Cyc q))

@[simp] lemma ambToCyc_apply (x : Amb r b hr) : ambToCyc r b hr x = x.right.right := (rfl)

lemma ker_ambToCyc : (ambToCyc r b hr).ker = coreSub r b hr := by
  ext x
  rw [MonoidHom.mem_ker, ambToCyc_apply, mem_coreSub_iff]

lemma ambToCyc_surjective : Function.Surjective (ambToCyc r b hr) := fun z =>
  ⟨SemidirectProduct.inr (SemidirectProduct.inr z), by rw [ambToCyc_apply]; simp⟩

lemma index_coreSub [NeZero q] : (coreSub r b hr).index = q := by
  rw [← ker_ambToCyc, Subgroup.index_ker,
    show (ambToCyc r b hr).range = ⊤ from MonoidHom.range_eq_top.2 ambToCyc_surjective,
    Subgroup.card_top]
  exact Nat.card_zmod q

def coreToD (r : U →* D) (b : Cyc q →* (E ≃ₗ[ZMod p] E))
    (hr : ∀ g : Cyc q, ((D.subtype).comp r).comp (σ g).toMonoidHom
      = (MulAut.conj (b g)).toMonoidHom.comp ((D.subtype).comp r)) :
    (coreSub r b hr) →* D where
  toFun x := r (x : Amb r b hr).right.left
  map_one' := by simp
  map_mul' x y := by
    have hx : ((x : coreSub r b hr) : Amb r b hr).right.right = 1 := mem_coreSub_iff.1 x.2
    change r ((((x : Amb r b hr)) * ((y : Amb r b hr))).right.left) = _
    rw [SemidirectProduct.mul_right, SemidirectProduct.mul_left, hx, map_one]
    simp

@[simp] lemma coreToD_apply (x : coreSub r b hr) :
    coreToD r b hr x = r (x : Amb r b hr).right.left := (rfl)

lemma ker_coreToD : (coreToD r b hr).ker = (tSub r b hr).subgroupOf (coreSub r b hr) := by
  ext x
  rw [MonoidHom.mem_ker, coreToD_apply, Subgroup.mem_subgroupOf, mem_tSub_iff]
  exact ⟨fun h => ⟨h, mem_coreSub_iff.1 x.2⟩, fun h => h.1⟩

lemma range_coreToD (hrsurj : Function.Surjective r) : (coreToD r b hr).range = ⊤ := by
  rw [MonoidHom.range_eq_top]
  intro d
  obtain ⟨u, hu⟩ := hrsurj d
  refine ⟨⟨SemidirectProduct.inr (SemidirectProduct.inl u), ?_⟩, ?_⟩
  · rw [mem_coreSub_iff]; rfl
  · rw [coreToD_apply]; exact hu

lemma index_tSub_subgroupOf (hrsurj : Function.Surjective r) :
    ((tSub r b hr).subgroupOf (coreSub r b hr)).index = Nat.card D := by
  rw [← ker_coreToD, Subgroup.index_ker, range_coreToD hrsurj, Subgroup.card_top]

def tLeftHom (r : U →* D) (b : Cyc q →* (E ≃ₗ[ZMod p] E))
    (hr : ∀ g : Cyc q, ((D.subtype).comp r).comp (σ g).toMonoidHom
      = (MulAut.conj (b g)).toMonoidHom.comp ((D.subtype).comp r)) :
    ((tSub r b hr).subgroupOf (coreSub r b hr)) →* Multiplicative E where
  toFun x := ((x : coreSub r b hr) : Amb r b hr).left
  map_one' := rfl
  map_mul' x y := by
    have hx : ((x : coreSub r b hr) : Amb r b hr) ∈ tSub r b hr := (Subgroup.mem_subgroupOf).1 x.2
    change (((x : coreSub r b hr) : Amb r b hr) * ((y : coreSub r b hr) : Amb r b hr)).left = _
    rw [SemidirectProduct.mul_left, semidirectAut_right_of_mem_tSub hx]
    rfl

@[simp] lemma tLeftHom_apply (x : (tSub r b hr).subgroupOf (coreSub r b hr)) :
    tLeftHom r b hr x = ((x : coreSub r b hr) : Amb r b hr).left := (rfl)

noncomputable def tOfE (r : U →* D) (b : Cyc q →* (E ≃ₗ[ZMod p] E))
    (hr : ∀ g : Cyc q, ((D.subtype).comp r).comp (σ g).toMonoidHom
      = (MulAut.conj (b g)).toMonoidHom.comp ((D.subtype).comp r)) (v : Multiplicative E) :
    (tSub r b hr).subgroupOf (coreSub r b hr) :=
  ⟨⟨SemidirectProduct.inl v, eSub_le_subOf ⊤ ⟨v, rfl⟩⟩,
    (Subgroup.mem_subgroupOf).2 (eSub_le_subOf r.ker ⟨v, rfl⟩)⟩

@[simp] lemma tLeftHom_tOfE (v : Multiplicative E) : tLeftHom r b hr (tOfE r b hr v) = v := (rfl)

lemma tLeftHom_surjective : Function.Surjective (tLeftHom r b hr) :=
  fun v => ⟨tOfE r b hr v, tLeftHom_tOfE v⟩

end Model

theorem indClassFun_apply_mulEquiv {G : Type*} [Group G] {P : Subgroup G} [Fintype G]
    (Φ : G ≃* G) (hΦ : ∀ x : G, Φ x ∈ P ↔ x ∈ P) (θ : P → ℂ) (y : G) :
    indClassFun P θ (Φ y) = indClassFun P (fun x : P => θ ⟨Φ x, (hΦ x).2 x.2⟩) y :=
  congrFun (indClassFun_comp_mulEquiv Φ (K := P) (K' := P) (fun z => (hΦ z).symm)
    (θ := fun x : P => θ ⟨Φ x, (hΦ x).2 x.2⟩) (θ' := θ)
    (fun x y hxy => congrArg θ (Subtype.ext hxy))) y

section Characters

open NormalInduction (conjClassFun conjClassFun_apply)

variable {p q : ℕ} [Fact p.Prime] [NeZero q] {E : Type*} [AddCommGroup E] [Module (ZMod p) E]
  {D : Subgroup (E ≃ₗ[ZMod p] E)}
  {U : Type*} [Group U] {σ : Multiplicative (ZMod q) →* MulAut U}

lemma finite_linearEquiv [Finite E] : Finite (E ≃ₗ[ZMod p] E) :=
  Finite.of_injective (fun f : E ≃ₗ[ZMod p] E => (f : E → E)) fun _ _ h =>
    LinearEquiv.toLinearMap_injective (LinearMap.ext fun v => congrFun h v)

lemma smul_dual_ne_zero (f : E ≃ₗ[ZMod p] E) {ℓ : Module.Dual (ZMod p) E} (hℓ : ℓ ≠ 0) :
    f • ℓ ≠ 0 := by
  obtain ⟨v, hv⟩ : ∃ v, ℓ v ≠ 0 := by
    by_contra h
    push Not at h
    exact hℓ (LinearMap.ext h)
  intro hc
  have h2 : (f • ℓ) (f v) = ℓ v := by rw [smul_dual_apply, f.symm_apply_apply]
  rw [hc] at h2
  exact hv h2.symm

lemma sum_dualChar_eq_zero [Fintype E] {ℓ : Module.Dual (ZMod p) E} (hℓ : ℓ ≠ 0) :
    ∑ v : Multiplicative E, (FixedFreeImage.dualChar ℓ v : ℂ) = 0 := by
  refine sum_hom_units_eq_zero ((Units.coeHom ℂ).comp (FixedFreeImage.dualChar ℓ)) ?_
  obtain ⟨v, hv⟩ : ∃ v, ℓ v ≠ 0 := by
    by_contra h
    push Not at h
    exact hℓ (LinearMap.ext h)
  intro hc
  have h1 : FixedFreeImage.dualChar ℓ (Multiplicative.ofAdd v) = 1 := by
    refine Units.ext ?_
    have := congrFun (congrArg (fun f : Multiplicative E →* ℂ => (f : Multiplicative E → ℂ)) hc)
      (Multiplicative.ofAdd v)
    simpa using this
  exact hv ((FixedFreeImage.dualChar_eq_one_iff ℓ v).1 h1)

lemma inl_mem_eSub {r : U →* D} {b : Cyc q →* (E ≃ₗ[ZMod p] E)}
    {hr : ∀ g : Cyc q, ((D.subtype).comp r).comp (σ g).toMonoidHom
      = (MulAut.conj (b g)).toMonoidHom.comp ((D.subtype).comp r)} (v : Multiplicative E) :
    (SemidirectProduct.inl v : Amb r b hr) ∈ eSub r b hr := mem_eSub_iff.2 rfl

lemma dualChar_semidirectAut_inv {r : U →* D} {b : Cyc q →* (E ≃ₗ[ZMod p] E)}
    {hr : ∀ g : Cyc q, ((D.subtype).comp r).comp (σ g).toMonoidHom
      = (MulAut.conj (b g)).toMonoidHom.comp ((D.subtype).comp r)}
    (ℓ : Module.Dual (ZMod p) E) (g : U ⋊[σ] Cyc q) (w : Multiplicative E) :
    FixedFreeImage.dualChar ℓ (semidirectAut r b hr g⁻¹ w)
      = FixedFreeImage.dualChar (toGL r b hr g • ℓ) w := by
  have hw : w = Multiplicative.ofAdd (Multiplicative.toAdd w) := rfl
  rw [hw, semidirectAut_apply, FixedFreeImage.dualChar_apply, FixedFreeImage.dualChar_apply,
    smul_dual_apply]
  congr 2
  rw [map_inv]
  rfl

variable (r : U →* D) (b : Cyc q →* (E ≃ₗ[ZMod p] E))
  (hr : ∀ g : Cyc q, ((D.subtype).comp r).comp (σ g).toMonoidHom
      = (MulAut.conj (b g)).toMonoidHom.comp ((D.subtype).comp r))

noncomputable def psiHom (ℓ : Module.Dual (ZMod p) E) :
    ((tSub r b hr).subgroupOf (coreSub r b hr)) →* ℂˣ :=
  (FixedFreeImage.dualChar ℓ).comp (tLeftHom r b hr)

lemma psiHom_apply (ℓ : Module.Dual (ZMod p) E)
    (x : (tSub r b hr).subgroupOf (coreSub r b hr)) :
    psiHom r b hr ℓ x = FixedFreeImage.dualChar ℓ (tLeftHom r b hr x) := (rfl)

noncomputable def psiOf (ℓ : Module.Dual (ZMod p) E) :
    ((tSub r b hr).subgroupOf (coreSub r b hr)) → ℂ :=
  fun x => (psiHom r b hr ℓ x : ℂ)

lemma psiOf_apply (ℓ : Module.Dual (ZMod p) E)
    (x : (tSub r b hr).subgroupOf (coreSub r b hr)) :
    psiOf r b hr ℓ x
      = (FixedFreeImage.dualChar ℓ (((x : coreSub r b hr) : Amb r b hr).left) : ℂ) := by
  rw [psiOf, psiHom_apply, tLeftHom_apply]

lemma psiOf_mem_Irr (ℓ : Module.Dual (ZMod p) E) :
    psiOf r b hr ℓ ∈ Irr ((tSub r b hr).subgroupOf (coreSub r b hr)) :=
  monoidHom_mem_Irr ((Units.coeHom ℂ).comp (psiHom r b hr ℓ))

@[simp] lemma psiOf_one (ℓ : Module.Dual (ZMod p) E) : psiOf r b hr ℓ 1 = 1 := by
  rw [psiOf, map_one]
  simp

lemma psiOf_eq_one_of_left_eq_one (ℓ : Module.Dual (ZMod p) E)
    {x : (tSub r b hr).subgroupOf (coreSub r b hr)}
    (hx : ((x : coreSub r b hr) : Amb r b hr).left = 1) : psiOf r b hr ℓ x = 1 := by
  rw [psiOf_apply, hx]
  simp

lemma psiOf_injective : Function.Injective (psiOf r b hr (E := E) (D := D) (σ := σ)) := by
  intro ℓ₁ ℓ₂ h
  refine FixedFreeImage.dualChar_injective (MonoidHom.ext fun v => ?_)
  obtain ⟨x, hx⟩ := tLeftHom_surjective (r := r) (b := b) (hr := hr) v
  have h2 := congrFun h x
  rw [psiOf, psiOf, psiHom_apply, psiHom_apply, hx] at h2
  exact Units.ext h2

lemma conjClassFun_psiOf (ℓ : Module.Dual (ZMod p) E) (g : coreSub r b hr) :
    conjClassFun ((tSub r b hr).subgroupOf (coreSub r b hr)) g (psiOf r b hr ℓ)
      = psiOf r b hr (toGL r b hr (g : Amb r b hr).right • ℓ) := by
  funext x
  rw [conjClassFun_apply, psiOf_apply, psiOf_apply]
  have hmem : ((x : coreSub r b hr) : Amb r b hr) ∈ tSub r b hr := (Subgroup.mem_subgroupOf).1 x.2
  have hcoe : ((((MulAut.conjNormal g⁻¹) x : (tSub r b hr).subgroupOf (coreSub r b hr))
      : coreSub r b hr) : Amb r b hr)
      = (g : Amb r b hr)⁻¹ * ((x : coreSub r b hr) : Amb r b hr) * (g : Amb r b hr) := by
    push_cast [MulAut.conjNormal_apply]
    group
  rw [hcoe, left_conj_of_mem_tSub _ hmem, dualChar_semidirectAut_inv]

lemma inertiaGroup_psiOf [Fintype E] [Fintype U] {ℓ : Module.Dual (ZMod p) E}
    (hfree : ∀ d : D, (d : E ≃ₗ[ZMod p] E) • ℓ = ℓ → d = 1) :
    inertiaGroup ((tSub r b hr).subgroupOf (coreSub r b hr)) (psiOf r b hr ℓ)
      = (tSub r b hr).subgroupOf (coreSub r b hr) := by
  classical
  refine le_antisymm (fun g hg => ?_)
    (le_inertiaGroup _ (Irr_subset_classFun (psiOf_mem_Irr r b hr ℓ)))
  rw [mem_inertiaGroup, conjClassFun_psiOf] at hg
  have hfix : toGL r b hr (g : Amb r b hr).right • ℓ = ℓ := psiOf_injective r b hr hg
  rw [toGL_right_of_mem_coreSub g.2] at hfix
  rw [Subgroup.mem_subgroupOf, mem_tSub_iff]
  exact ⟨hfree _ hfix, mem_coreSub_iff.1 g.2⟩

noncomputable def coreOfE (v : Multiplicative E) : coreSub r b hr :=
  ⟨SemidirectProduct.inl v, eSub_le_subOf ⊤ (inl_mem_eSub v)⟩

@[simp] lemma coe_coreOfE (v : Multiplicative E) :
    ((coreOfE r b hr v : coreSub r b hr) : Amb r b hr) = SemidirectProduct.inl v := (rfl)

@[simp] lemma coreOfE_one : coreOfE r b hr 1 = 1 := by
  refine Subtype.ext ?_
  rw [coe_coreOfE, map_one]
  rfl

lemma coreOfE_mem_tSub_subgroupOf (v : Multiplicative E) :
    coreOfE r b hr v ∈ (tSub r b hr).subgroupOf (coreSub r b hr) :=
  (Subgroup.mem_subgroupOf).2 (eSub_le_subOf r.ker (inl_mem_eSub v))

@[simp] lemma coe_tOfE (v : Multiplicative E) :
    ((tOfE r b hr v : (tSub r b hr).subgroupOf (coreSub r b hr)) : coreSub r b hr)
      = coreOfE r b hr v := (rfl)

lemma coreOfE_mem_eSub (v : Multiplicative E) :
    ((coreOfE r b hr v : coreSub r b hr) : Amb r b hr) ∈ eSub r b hr := inl_mem_eSub v

lemma psiOf_conj_coreOfE (ℓ : Module.Dual (ZMod p) E) (t : coreSub r b hr)
    (v : Multiplicative E) :
    psiOf r b hr ℓ ⟨t⁻¹ * coreOfE r b hr v * t,
      Subgroup.Normal.conj_mem' inferInstance _ (coreOfE_mem_tSub_subgroupOf r b hr v) t⟩
      = (FixedFreeImage.dualChar (toGL r b hr (t : Amb r b hr).right • ℓ) v : ℂ) := by
  rw [psiOf_apply]
  have hcoe : (((t⁻¹ * coreOfE r b hr v * t : coreSub r b hr)) : Amb r b hr)
      = (t : Amb r b hr)⁻¹ * (SemidirectProduct.inl v) * (t : Amb r b hr) := by
    push_cast
    rw [coe_coreOfE]
  rw [hcoe]
  have hmem : (SemidirectProduct.inl v : Amb r b hr) ∈ tSub r b hr :=
    eSub_le_subOf r.ker (inl_mem_eSub v)
  rw [left_conj_of_mem_tSub _ hmem]
  have hl : (SemidirectProduct.inl v : Amb r b hr).left = v := rfl
  rw [hl, dualChar_semidirectAut_inv]

lemma conjNormal_mem_tSub_subgroupOf_iff (t : Amb r b hr) (x : coreSub r b hr) :
    (MulAut.conjNormal t⁻¹ x : coreSub r b hr) ∈ (tSub r b hr).subgroupOf (coreSub r b hr)
      ↔ x ∈ (tSub r b hr).subgroupOf (coreSub r b hr) := by
  have hN : (tSub r b hr).Normal := inferInstance
  have hcoe : (((MulAut.conjNormal t⁻¹ x : coreSub r b hr)) : Amb r b hr)
      = t⁻¹ * ((x : Amb r b hr)) * t := by
    push_cast [MulAut.conjNormal_apply]
    group
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hcoe]
  refine ⟨fun h => ?_, fun h => hN.conj_mem' _ h t⟩
  simpa [mul_assoc] using hN.conj_mem _ h t

variable [Fintype E] [Fintype U]

open scoped Classical in
noncomputable def alphaOf (ℓ : Module.Dual (ZMod p) E) : coreSub r b hr → ℂ :=
  indClassFun ((tSub r b hr).subgroupOf (coreSub r b hr)) (psiOf r b hr ℓ)

open scoped Classical in
lemma alphaOf_eq_indClassFun (ℓ : Module.Dual (ZMod p) E) :
    alphaOf r b hr ℓ
      = indClassFun ((tSub r b hr).subgroupOf (coreSub r b hr)) (psiOf r b hr ℓ) := (rfl)

lemma conjClassFun_alphaOf (ℓ : Module.Dual (ZMod p) E) (t : Amb r b hr) :
    conjClassFun (coreSub r b hr) t (alphaOf r b hr ℓ)
      = alphaOf r b hr (toGL r b hr t.right • ℓ) := by
  classical
  funext y
  rw [conjClassFun_apply]
  change alphaOf r b hr ℓ (MulAut.conjNormal t⁻¹ y) = _
  rw [alphaOf, alphaOf,
    indClassFun_apply_mulEquiv (MulAut.conjNormal t⁻¹)
      (conjNormal_mem_tSub_subgroupOf_iff r b hr t)]
  congr 1
  funext x
  rw [psiOf_apply, psiOf_apply]
  have hcoe : ((((MulAut.conjNormal t⁻¹) (x : coreSub r b hr) : coreSub r b hr)) : Amb r b hr)
      = t⁻¹ * (((x : coreSub r b hr)) : Amb r b hr) * t := by
    push_cast [MulAut.conjNormal_apply]
    group
  rw [hcoe]
  have hmem : (((x : coreSub r b hr)) : Amb r b hr) ∈ tSub r b hr :=
    (Subgroup.mem_subgroupOf).1 x.2
  rw [left_conj_of_mem_tSub _ hmem, dualChar_semidirectAut_inv]

lemma alphaOf_mem_Irr {ℓ : Module.Dual (ZMod p) E}
    (hfree : ∀ d : D, (d : E ≃ₗ[ZMod p] E) • ℓ = ℓ → d = 1) :
    alphaOf r b hr ℓ ∈ Irr (coreSub r b hr) := by
  classical
  exact indClassFun_mem_Irr_of_inertiaGroup_eq (psiOf_mem_Irr r b hr ℓ)
    (inertiaGroup_psiOf r b hr hfree)

lemma alphaOf_one (hrsurj : Function.Surjective r) (ℓ : Module.Dual (ZMod p) E) :
    alphaOf r b hr ℓ 1 = (Nat.card D : ℂ) := by
  classical
  rw [alphaOf_eq_indClassFun, indClassFun_one, psiOf_one, mul_one]
  have h := index_tSub_subgroupOf (r := r) (b := b) (hr := hr) hrsurj
  have h2 : ((tSub r b hr).subgroupOf (coreSub r b hr)).index
      * Nat.card ((tSub r b hr).subgroupOf (coreSub r b hr)) = Nat.card (coreSub r b hr) :=
    Subgroup.index_mul_card _
  rw [h] at h2
  have hne : (Nat.card ((tSub r b hr).subgroupOf (coreSub r b hr)) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 Nat.card_pos.ne'
  field_simp
  rw [← h2]
  push_cast
  ring

lemma alphaOf_eq_iff {ℓ ℓ' : Module.Dual (ZMod p) E} :
    alphaOf r b hr ℓ = alphaOf r b hr ℓ' ↔
      ∃ g : coreSub r b hr, toGL r b hr (g : Amb r b hr).right • ℓ' = ℓ := by
  classical
  rw [alphaOf_eq_indClassFun, alphaOf_eq_indClassFun,
    NormalInducedFamily.indClassFun_eq_iff_exists_conjClassFun _
      (psiOf_mem_Irr r b hr ℓ) (psiOf_mem_Irr r b hr ℓ')]
  refine ⟨fun ⟨g, hg⟩ => ⟨g, ?_⟩, fun ⟨g, hg⟩ => ⟨g, ?_⟩⟩
  · rw [conjClassFun_psiOf] at hg
    exact psiOf_injective r b hr hg
  · rw [conjClassFun_psiOf, hg]

lemma alphaOf_eq_iff_exists_mem_D (hrsurj : Function.Surjective r)
    {ℓ ℓ' : Module.Dual (ZMod p) E} :
    alphaOf r b hr ℓ = alphaOf r b hr ℓ' ↔ ∃ d : D, (d : E ≃ₗ[ZMod p] E) • ℓ' = ℓ := by
  rw [alphaOf_eq_iff]
  refine ⟨fun ⟨g, hg⟩ => ⟨r ((g : Amb r b hr).right.left), ?_⟩, fun ⟨d, hd⟩ => ?_⟩
  · rwa [toGL_right_of_mem_coreSub g.2] at hg
  · obtain ⟨u, hu⟩ := hrsurj d
    refine ⟨⟨SemidirectProduct.inr (SemidirectProduct.inl u), by rw [mem_coreSub_iff]; rfl⟩, ?_⟩
    rw [toGL_right_of_mem_coreSub (mem_coreSub_iff.2 rfl)]
    change ((r (SemidirectProduct.inl u : U ⋊[σ] Cyc q).left : E ≃ₗ[ZMod p] E)) • ℓ' = ℓ
    rw [show (SemidirectProduct.inl u : U ⋊[σ] Cyc q).left = u from rfl, hu]
    exact hd

open scoped Classical in
lemma alphaOf_coreOfE (ℓ : Module.Dual (ZMod p) E) (v : Multiplicative E) :
    alphaOf r b hr ℓ (coreOfE r b hr v)
      = (Nat.card ((tSub r b hr).subgroupOf (coreSub r b hr)) : ℂ)⁻¹
        * ∑ t : coreSub r b hr,
          (FixedFreeImage.dualChar (toGL r b hr (t : Amb r b hr).right • ℓ) v : ℂ) := by
  classical
  rw [alphaOf_eq_indClassFun, indClassFun_apply]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [dif_pos (Subgroup.Normal.conj_mem' inferInstance _ (coreOfE_mem_tSub_subgroupOf r b hr v) t)]
  exact psiOf_conj_coreOfE r b hr ℓ t v

lemma sum_alphaOf_coreOfE {ℓ : Module.Dual (ZMod p) E} (hℓ : ℓ ≠ 0) :
    ∑ v : Multiplicative E, alphaOf r b hr ℓ (coreOfE r b hr v) = 0 := by
  classical
  rw [Finset.sum_congr rfl fun v _ => alphaOf_coreOfE r b hr ℓ v, ← Finset.mul_sum,
    Finset.sum_comm,
    Finset.sum_congr rfl fun t (_ : t ∈ (Finset.univ : Finset (coreSub r b hr))) =>
      sum_dualChar_eq_zero (smul_dual_ne_zero (toGL r b hr (t : Amb r b hr).right) hℓ)]
  simp

lemma exists_mem_eSub_alphaOf_ne (hrsurj : Function.Surjective r)
    {ℓ : Module.Dual (ZMod p) E} (hℓ : ℓ ≠ 0) :
    ∃ x : coreSub r b hr, (x : Amb r b hr) ∈ eSub r b hr ∧
      alphaOf r b hr ℓ x ≠ alphaOf r b hr ℓ 1 := by
  classical
  have : Finite (E ≃ₗ[ZMod p] E) := finite_linearEquiv
  by_contra hcon
  push Not at hcon
  have hall : ∀ v : Multiplicative E,
      alphaOf r b hr ℓ (coreOfE r b hr v) = alphaOf r b hr ℓ 1 := fun v =>
    hcon _ (inl_mem_eSub v)
  have h0 := sum_alphaOf_coreOfE r b hr hℓ
  rw [Finset.sum_congr rfl fun v _ => hall v, Finset.sum_const, Finset.card_univ,
    alphaOf_one r b hr hrsurj, nsmul_eq_mul] at h0
  have hD : (Nat.card D : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hE : (Fintype.card (Multiplicative E) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  exact (mul_ne_zero hE hD) h0

lemma conjClassFun_inr_inr_alphaOf (ℓ : Module.Dual (ZMod p) E) (i : ZMod q) :
    conjClassFun (coreSub r b hr)
      (SemidirectProduct.inr (SemidirectProduct.inr (Multiplicative.ofAdd i)))
      (alphaOf r b hr ℓ)
      = alphaOf r b hr (b (Multiplicative.ofAdd i) • ℓ) := by
  rw [conjClassFun_alphaOf]
  congr 2
  rw [show (SemidirectProduct.inr (SemidirectProduct.inr (Multiplicative.ofAdd i)
      : U ⋊[σ] Cyc q) : Amb r b hr).right
      = SemidirectProduct.inr (Multiplicative.ofAdd i) from rfl, toGL_inr]

lemma conjClassFun_alphaOf_eq_inr_inr (hrsurj : Function.Surjective r)
    (ℓ : Module.Dual (ZMod p) E) (t : Amb r b hr) :
    conjClassFun (coreSub r b hr) t (alphaOf r b hr ℓ)
      = conjClassFun (coreSub r b hr) (SemidirectProduct.inr (SemidirectProduct.inr
          (Multiplicative.ofAdd (Multiplicative.toAdd t.right.right)))) (alphaOf r b hr ℓ) := by
  rw [conjClassFun_alphaOf, conjClassFun_alphaOf, toGL_eq,
    show (SemidirectProduct.inr (SemidirectProduct.inr
      (Multiplicative.ofAdd (Multiplicative.toAdd t.right.right)) : U ⋊[σ] Cyc q)
        : Amb r b hr).right
      = SemidirectProduct.inr (Multiplicative.ofAdd (Multiplicative.toAdd t.right.right)) from rfl,
    toGL_inr,
    show (Multiplicative.ofAdd (Multiplicative.toAdd t.right.right) : Cyc q) = t.right.right
      from rfl, mul_smul]
  exact (alphaOf_eq_iff_exists_mem_D r b hr hrsurj).2 ⟨r t.right.left, rfl⟩

lemma conjClassFun_alphaOf_eq_self (hrsurj : Function.Surjective r)
    {ℓ : Module.Dual (ZMod p) E} (hfix : ∀ z : Cyc q, b z • ℓ = ℓ) (t : Amb r b hr) :
    conjClassFun (coreSub r b hr) t (alphaOf r b hr ℓ) = alphaOf r b hr ℓ := by
  rw [conjClassFun_alphaOf, toGL_eq, mul_smul, hfix]
  exact (alphaOf_eq_iff_exists_mem_D r b hr hrsurj).2 ⟨r t.right.left, rfl⟩

lemma inertiaGroup_alphaOf_eq_coreSub (hrsurj : Function.Surjective r)
    {ℓ : Module.Dual (ZMod p) E}
    (hfree : ∀ d : D, (d : E ≃ₗ[ZMod p] E) • ℓ = ℓ → d = 1)
    (hinj : Function.Injective fun i : ZMod q => conjClassFun (coreSub r b hr)
      (SemidirectProduct.inr (SemidirectProduct.inr (Multiplicative.ofAdd i))) (alphaOf r b hr ℓ)) :
    inertiaGroup (coreSub r b hr) (alphaOf r b hr ℓ) = coreSub r b hr := by
  classical
  refine le_antisymm (fun t ht => ?_)
    (le_inertiaGroup _ (Irr_subset_classFun (alphaOf_mem_Irr r b hr hfree)))
  rw [mem_inertiaGroup] at ht
  rw [mem_coreSub_iff]
  have h0 : conjClassFun (coreSub r b hr)
      (SemidirectProduct.inr (SemidirectProduct.inr (Multiplicative.ofAdd (0 : ZMod q))))
      (alphaOf r b hr ℓ) = alphaOf r b hr ℓ := by
    rw [conjClassFun_inr_inr_alphaOf,
      show (Multiplicative.ofAdd (0 : ZMod q)) = 1 from rfl, map_one, one_smul]
  have hkey : (fun i : ZMod q => conjClassFun (coreSub r b hr)
      (SemidirectProduct.inr (SemidirectProduct.inr (Multiplicative.ofAdd i)))
      (alphaOf r b hr ℓ)) (Multiplicative.toAdd t.right.right)
      = (fun i : ZMod q => conjClassFun (coreSub r b hr)
      (SemidirectProduct.inr (SemidirectProduct.inr (Multiplicative.ofAdd i)))
      (alphaOf r b hr ℓ)) 0 := by
    show conjClassFun (coreSub r b hr) (SemidirectProduct.inr (SemidirectProduct.inr
        (Multiplicative.ofAdd (Multiplicative.toAdd t.right.right)))) (alphaOf r b hr ℓ)
      = conjClassFun (coreSub r b hr) (SemidirectProduct.inr (SemidirectProduct.inr
        (Multiplicative.ofAdd (0 : ZMod q)))) (alphaOf r b hr ℓ)
    rw [h0, ← conjClassFun_alphaOf_eq_inr_inr r b hr hrsurj, ht]
  have hzero := hinj hkey
  rw [show t.right.right = Multiplicative.ofAdd (Multiplicative.toAdd t.right.right) from rfl,
    hzero]
  rfl

open scoped Classical in
lemma indClassFun_coreSub_one (χ : coreSub r b hr → ℂ) :
    indClassFun (coreSub r b hr) χ 1 = (q : ℂ) * χ 1 := by
  classical
  rw [indClassFun_one]
  congr 1
  have h1 : (coreSub r b hr).index = q := index_coreSub
  have h2 : (coreSub r b hr).index * Nat.card (coreSub r b hr) = Nat.card (Amb r b hr) :=
    Subgroup.index_mul_card _
  rw [h1] at h2
  have hne : (Nat.card (coreSub r b hr) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  field_simp
  rw [← h2]
  push_cast
  ring

open scoped Classical in
lemma cfInner_self_indClassFun_of_invariant {χ : coreSub r b hr → ℂ}
    (hχ : χ ∈ Irr (coreSub r b hr))
    (hinv : ∀ t : Amb r b hr, conjClassFun (coreSub r b hr) t χ = χ) :
    cfInner (indClassFun (coreSub r b hr) χ) (indClassFun (coreSub r b hr) χ) = (q : ℂ) := by
  classical
  rw [cfInner_self_indClassFun _ hχ]
  congr 1
  have hI : inertiaGroup (coreSub r b hr) χ = ⊤ :=
    eq_top_iff.2 fun t _ => mem_inertiaGroup.2 (hinv t)
  rw [hI, Subgroup.relIndex_top_right, index_coreSub]

lemma b_smul_eq_self (e : Module.Basis (ZMod q) (ZMod p) E)
    (hb : b (Multiplicative.ofAdd 1) = shift e) {ℓ : Module.Dual (ZMod p) E}
    (hfix : shift e • ℓ = ℓ) (z : Cyc q) : b z • ℓ = ℓ := by
  have hpow : ∀ n : ℕ, (shift e ^ n : E ≃ₗ[ZMod p] E) • ℓ = ℓ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_smul, hfix, ih]
  rw [show z = Multiplicative.ofAdd (Multiplicative.toAdd z) from rfl, ofAdd_eq_pow, map_pow, hb]
  exact hpow _

end Characters

section MovingOrbit

open MulAction CoprimeFreeAction

variable {p q : ℕ} [Fact p.Prime] {E : Type*} [AddCommGroup E] [Module (ZMod p) E]
  (e : Module.Basis (ZMod q) (ZMod p) E) {D : Subgroup (E ≃ₗ[ZMod p] E)}
  (hD : D ≤ diagAutSubgroup e)
  (hconj : ∀ d : E ≃ₗ[ZMod p] E, shift e * d * (shift e)⁻¹ ∈ D ↔ d ∈ D)

lemma injective_orbit_of_minimalPeriod_eq [NeZero q] {x : fullSupportDual e hD}
    (hper : Function.minimalPeriod
      (CoprimeFreeAction.orbitQuotientPerm (shiftDualPerm_smul e hD hconj)) (Quotient.mk'' x) = q)
    {i j : ZMod q}
    (heq : ∃ d : D, (d : E ≃ₗ[ZMod p] E) • ((shift e ^ j.val) • (x : Module.Dual (ZMod p) E))
      = (shift e ^ i.val) • (x : Module.Dual (ZMod p) E)) : i = j := by
  set F := CoprimeFreeAction.orbitQuotientPerm (shiftDualPerm_smul e hD hconj) with hF
  obtain ⟨d, hd⟩ := heq
  have hmk : (F ^ i.val) (Quotient.mk'' x) = (F ^ j.val) (Quotient.mk'' x) := by
    rw [hF, CoprimeFreeAction.orbitQuotientPerm_pow_mk,
      CoprimeFreeAction.orbitQuotientPerm_pow_mk]
    refine Quotient.sound' ?_
    rw [orbitRel_apply, mem_orbit_iff]
    refine ⟨d, Subtype.ext ?_⟩
    rw [coe_smul_fullSupportDual, coe_shiftDualPerm_pow, coe_shiftDualPerm_pow]
    exact hd
  have hiter : ∀ n : ℕ, (F ^ n) (Quotient.mk'' x) = (⇑F)^[n] (Quotient.mk'' x) := fun n => by
    rw [Equiv.Perm.iterate_eq_pow]
  rw [hiter, hiter] at hmk
  exact ZMod.val_injective _ ((Function.iterate_eq_iterate_iff_of_lt_minimalPeriod (f := ⇑F)
    (x := Quotient.mk'' x) (by rw [hper]; exact ZMod.val_lt i)
    (by rw [hper]; exact ZMod.val_lt j)).1 hmk)

end MovingOrbit

section Pair

variable {p q : ℕ} [Fact p.Prime] [NeZero q] {E : Type*} [AddCommGroup E] [Module (ZMod p) E]
  {U : Type*} [Group U] {σ : Multiplicative (ZMod q) →* MulAut U}

open scoped Classical in
theorem exists_equal_degree_invariant_and_moving_pair
    (e : Module.Basis (ZMod q) (ZMod p) E) {D : Subgroup (E ≃ₗ[ZMod p] E)}
    (hD : D ≤ diagAutSubgroup e) (hp : Odd p) (hq : q.Prime)
    (hDodd : Odd (Nat.card D)) (hqD : ¬ q ∣ Nat.card D)
    (hcent : ∀ d : D, (d : E ≃ₗ[ZMod p] E) * shift e = shift e * d → d = 1)
    [Fintype E] [Fintype U] (hUodd : Odd (Nat.card U)) (hqU : ¬ q ∣ Nat.card U)
    {r : U →* D} (hrsurj : Function.Surjective r)
    {b : DiagonalCore.Cyc q →* (E ≃ₗ[ZMod p] E)} (hb : b (Multiplicative.ofAdd 1) = shift e)
    (hr : ∀ g : DiagonalCore.Cyc q, ((D.subtype).comp r).comp (σ g).toMonoidHom
      = (MulAut.conj (b g)).toMonoidHom.comp ((D.subtype).comp r)) :
    ∃ ψα ψβ :
        ((DiagonalCore.tSub r b hr).subgroupOf (DiagonalCore.coreSub r b hr)) → ℂ,
      ψα ∈ Irr _ ∧ ψβ ∈ Irr _ ∧ ψα 1 = 1 ∧ ψβ 1 = 1 ∧
      (∀ x : ((DiagonalCore.tSub r b hr).subgroupOf (DiagonalCore.coreSub r b hr)),
        ((x : DiagonalCore.coreSub r b hr) : DiagonalCore.Amb r b hr).left = 1 →
          ψα x = 1 ∧ ψβ x = 1) ∧
      (let α := indClassFun
          ((DiagonalCore.tSub r b hr).subgroupOf (DiagonalCore.coreSub r b hr)) ψα
       let β := indClassFun
          ((DiagonalCore.tSub r b hr).subgroupOf (DiagonalCore.coreSub r b hr)) ψβ
       α ∈ Irr (DiagonalCore.coreSub r b hr) ∧ β ∈ Irr (DiagonalCore.coreSub r b hr) ∧
       α 1 = (Nat.card D : ℂ) ∧ β 1 = (Nat.card D : ℂ) ∧
       (∃ x : DiagonalCore.coreSub r b hr,
         (x : DiagonalCore.Amb r b hr) ∈ DiagonalCore.eSub r b hr ∧ α x ≠ α 1) ∧
       (∃ x : DiagonalCore.coreSub r b hr,
         (x : DiagonalCore.Amb r b hr) ∈ DiagonalCore.eSub r b hr ∧ β x ≠ β 1) ∧
       (∀ t : DiagonalCore.Amb r b hr,
         NormalInduction.conjClassFun (DiagonalCore.coreSub r b hr) t α = α) ∧
       (Function.Injective fun i : ZMod q => NormalInduction.conjClassFun
         (DiagonalCore.coreSub r b hr)
         (SemidirectProduct.inr (SemidirectProduct.inr (Multiplicative.ofAdd i))) β) ∧
       indClassFun (DiagonalCore.coreSub r b hr) β ∈ Irr (DiagonalCore.Amb r b hr) ∧
       indClassFun (DiagonalCore.coreSub r b hr) β 1 = (q * Nat.card D : ℂ) ∧
       indClassFun (DiagonalCore.coreSub r b hr) α 1 = (q * Nat.card D : ℂ) ∧
       cfInner (indClassFun (DiagonalCore.coreSub r b hr) α)
         (indClassFun (DiagonalCore.coreSub r b hr) α) = (q : ℂ)) := by
  classical
  have hconj : ∀ d : E ≃ₗ[ZMod p] E, shift e * d * (shift e)⁻¹ ∈ D ↔ d ∈ D := by
    intro d
    rw [← hb]
    exact conj_b_mem_iff hr hrsurj _ d
  have hbi : ∀ k : ZMod q, b (Multiplicative.ofAdd k) = (shift e) ^ k.val := fun k => by
    rw [ofAdd_eq_pow, map_pow, hb]
  obtain ⟨⟨ℓ₀, hℓ₀⟩, -⟩ :=
    exists_fixed_and_moving_fullSupportDual e hD hconj hq hqD hcent hp hDodd
  obtain ⟨Q, hQ, hper⟩ :=
    exists_minimalPeriod_orbitQuotientPerm_eq e hD hconj hq hqD hcent hp hDodd
  induction Q using Quotient.inductionOn' with
  | h ℓ₁ =>
  have hfree : ∀ (x : fullSupportDual e hD) (d : D),
      (d : E ≃ₗ[ZMod p] E) • (x : Module.Dual (ZMod p) E) = x → d = 1 :=
    fun x d hdx => eq_one_of_smul_eq_self d x (Subtype.ext hdx)
  have hne0 : ∀ x : fullSupportDual e hD, (x : Module.Dual (ZMod p) E) ≠ 0 := by
    intro x hx
    have h := (mem_fullSupportDual (hD := hD)).1 x.2 0
    rw [hx] at h
    exact h rfl
  have hfix0 : shift e • (ℓ₀ : Module.Dual (ZMod p) E) = ℓ₀ := by
    rw [← coe_shiftDualPerm e hD ℓ₀, hℓ₀]
  have hfixQ : ∀ z : Cyc q, b z • (ℓ₀ : Module.Dual (ZMod p) E) = ℓ₀ :=
    b_smul_eq_self b e hb hfix0
  refine ⟨psiOf r b hr (ℓ₀ : Module.Dual (ZMod p) E),
    psiOf r b hr (ℓ₁ : Module.Dual (ZMod p) E),
    psiOf_mem_Irr r b hr _, psiOf_mem_Irr r b hr _, psiOf_one r b hr _, psiOf_one r b hr _,
    fun x hx => ⟨psiOf_eq_one_of_left_eq_one r b hr _ hx,
      psiOf_eq_one_of_left_eq_one r b hr _ hx⟩, ?_⟩
  intro α β
  rw [show α = alphaOf r b hr (ℓ₀ : Module.Dual (ZMod p) E) from
      (alphaOf_eq_indClassFun r b hr _).symm,
    show β = alphaOf r b hr (ℓ₁ : Module.Dual (ZMod p) E) from
      (alphaOf_eq_indClassFun r b hr _).symm]
  have hαIrr : alphaOf r b hr (ℓ₀ : Module.Dual (ZMod p) E) ∈ Irr (coreSub r b hr) :=
    alphaOf_mem_Irr r b hr (hfree ℓ₀)
  have hβIrr : alphaOf r b hr (ℓ₁ : Module.Dual (ZMod p) E) ∈ Irr (coreSub r b hr) :=
    alphaOf_mem_Irr r b hr (hfree ℓ₁)
  have hαinv : ∀ t : Amb r b hr,
      NormalInduction.conjClassFun (coreSub r b hr) t
          (alphaOf r b hr (ℓ₀ : Module.Dual (ZMod p) E))
        = alphaOf r b hr (ℓ₀ : Module.Dual (ZMod p) E) :=
    conjClassFun_alphaOf_eq_self r b hr hrsurj hfixQ
  have hβinj : Function.Injective fun i : ZMod q =>
      NormalInduction.conjClassFun (coreSub r b hr)
      (SemidirectProduct.inr (SemidirectProduct.inr (Multiplicative.ofAdd i)))
      (alphaOf r b hr (ℓ₁ : Module.Dual (ZMod p) E)) := by
    intro i j hij
    simp only [conjClassFun_inr_inr_alphaOf] at hij
    rw [alphaOf_eq_iff_exists_mem_D r b hr hrsurj] at hij
    obtain ⟨d, hd⟩ := hij
    refine injective_orbit_of_minimalPeriod_eq e hD hconj hper ⟨d, ?_⟩
    rw [← hbi, ← hbi]
    exact hd
  refine ⟨hαIrr, hβIrr, alphaOf_one r b hr hrsurj _, alphaOf_one r b hr hrsurj _,
    exists_mem_eSub_alphaOf_ne r b hr hrsurj (hne0 ℓ₀),
    exists_mem_eSub_alphaOf_ne r b hr hrsurj (hne0 ℓ₁), hαinv, hβinj, ?_, ?_, ?_, ?_⟩
  · exact indClassFun_mem_Irr_of_inertiaGroup_eq hβIrr
      (inertiaGroup_alphaOf_eq_coreSub r b hr hrsurj (hfree ℓ₁) hβinj)
  · rw [indClassFun_coreSub_one r b hr, alphaOf_one r b hr hrsurj]
  · rw [indClassFun_coreSub_one r b hr, alphaOf_one r b hr hrsurj]
  · exact cfInner_self_indClassFun_of_invariant r b hr hαIrr hαinv

end Pair

end DiagonalCore

end CFSG.FeitThompson
