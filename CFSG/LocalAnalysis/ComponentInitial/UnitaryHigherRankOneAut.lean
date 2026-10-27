module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRankOneTorus
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLargeTorus

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K]

section Params

variable (h : UnitaryFieldData p f K)

@[expose] noncomputable def uS (a b : K) (hab : h.norm a + h.trace b = 0) : rkOneUStar h :=
  ⟨rkOneU h a b hab, rkOneU_mem h hab⟩

@[expose] noncomputable def uA (x : rkOneUStar h) : K :=
  ((((rkOneUIso h).symm x : hypUnitriangular h 1 1) : hypSU h 1 1) : GL (HypIndex 1 1) K)
    (.inr (.inl 0)) (.inr (.inr 0))

@[expose] noncomputable def uB (x : rkOneUStar h) : K :=
  ((((rkOneUIso h).symm x : hypUnitriangular h 1 1) : hypSU h 1 1) : GL (HypIndex 1 1) K)
    (.inl 0) (.inr (.inr 0))

theorem rkOneUIso_symm_uS {a b : K} (hab : h.norm a + h.trace b = 0) :
    (rkOneUIso h).symm (uS h a b hab) = ⟨rkOneQElt h a b hab, rkOneQElt_mem h hab⟩ :=
  (rkOneUIso h).symm_apply_eq.mpr (rkOneUIso_rkOneQElt h hab).symm

theorem uA_uS {a b : K} (hab : h.norm a + h.trace b = 0) : uA h (uS h a b hab) = a := by
  rw [uA, rkOneUIso_symm_uS]
  exact rkOneQ_zf h a b

theorem uB_uS {a b : K} (hab : h.norm a + h.trace b = 0) : uB h (uS h a b hab) = b := by
  rw [uB, rkOneUIso_symm_uS]
  exact rkOneQ_ef h a b

theorem uAB_param (x : rkOneUStar h) : h.norm (uA h x) + h.trace (uB h x) = 0 := by
  obtain ⟨a, b, hab, hx⟩ := exists_eq_rkOneQElt h ((rkOneUIso h).symm x).2
  have hx' : (rkOneUIso h).symm x = ⟨rkOneQElt h a b hab, rkOneQElt_mem h hab⟩ := Subtype.ext hx
  rw [uA, uB, hx']
  change h.norm (rkOneQ h a b _ _) + h.trace (rkOneQ h a b _ _) = 0
  rw [rkOneQ_zf, rkOneQ_ef]
  exact hab

theorem uS_congr {a b a' b' : K} (hab : h.norm a + h.trace b = 0) (ha : a = a') (hb : b = b') :
    uS h a b hab = uS h a' b' (ha ▸ hb ▸ hab) := by
  subst ha hb
  rfl

theorem eq_uS (x : rkOneUStar h) : x = uS h (uA h x) (uB h x) (uAB_param h x) := by
  obtain ⟨a, b, hab, hx⟩ := exists_eq_rkOneQElt h ((rkOneUIso h).symm x).2
  have hx' : (rkOneUIso h).symm x = ⟨rkOneQElt h a b hab, rkOneQElt_mem h hab⟩ := Subtype.ext hx
  have ha : uA h x = a := by
    rw [uA, hx']
    exact rkOneQ_zf h a b
  have hb : uB h x = b := by
    rw [uB, hx']
    exact rkOneQ_ef h a b
  have hxe : x = uS h a b hab := by
    rw [← (rkOneUIso h).apply_symm_apply x, hx', rkOneUIso_rkOneQElt]
    rfl
  rw [hxe]
  exact uS_congr h hab (by rw [← hxe, ha]) (by rw [← hxe, hb])

theorem uS_mul {a b c d : K} (hab : h.norm a + h.trace b = 0)
    (hcd : h.norm c + h.trace d = 0) :
    uS h a b hab * uS h c d hcd = uS h (a + c) (b + d - h.bar a * c)
      ((unitary_heisenberg_identities h).2.1 a b c d hab hcd).2 :=
  Subtype.ext (rkOneU_mul h hab hcd)

theorem uS_injective {a b a' b' : K} {hab : h.norm a + h.trace b = 0}
    {hab' : h.norm a' + h.trace b' = 0} (he : uS h a b hab = uS h a' b' hab') :
    a = a' ∧ b = b' :=
  rkOneU_injective (congrArg Subtype.val he)

theorem uA_mul (x y : rkOneUStar h) : uA h (x * y) = uA h x + uA h y := by
  rw [eq_uS h x, eq_uS h y, uS_mul, uA_uS, uA_uS, uA_uS]

theorem uB_mul (x y : rkOneUStar h) :
    uB h (x * y) = uB h x + uB h y - h.bar (uA h x) * uA h y := by
  rw [eq_uS h x, eq_uS h y, uS_mul, uB_uS, uB_uS, uB_uS, uA_uS, uA_uS]

theorem uS_ext {x y : rkOneUStar h} (ha : uA h x = uA h y) (hb : uB h x = uB h y) : x = y := by
  rw [eq_uS h x, eq_uS h y]
  exact uS_congr h _ ha hb

theorem uS_zero_zero : uS h 0 0 (norm_zero_add_trace (zero_mem h.traceZero)) = 1 :=
  Subtype.ext (rkOneU_zero_zero h)

theorem uA_one : uA h (1 : rkOneUStar h) = 0 := by
  rw [← uS_zero_zero h, uA_uS]

theorem inv_param {a b : K} (hab : h.norm a + h.trace b = 0) :
    h.norm (-a) + h.trace (h.bar b) = 0 := by
  simp only [UnitaryFieldData.norm, UnitaryFieldData.trace, map_neg, h.bar_bar] at hab ⊢
  linear_combination hab

theorem uS_mul_uS_neg {a b : K} (hab : h.norm a + h.trace b = 0) :
    uS h a b hab * uS h (-a) (h.bar b) (inv_param h hab) = 1 := by
  rw [uS_mul, ← uS_zero_zero h]
  refine uS_congr h _ (add_neg_cancel a) ?_
  simp only [UnitaryFieldData.norm, UnitaryFieldData.trace] at hab
  linear_combination hab

end Params

section Tau

variable (h : UnitaryFieldData p f K)

theorem tau_param (c : K) {a b : K} (hab : h.norm a + h.trace b = 0) :
    h.norm (c * a) + h.trace (h.norm c * b) = 0 := by
  have he : h.norm (c * a) + h.trace (h.norm c * b) = h.norm c * (h.norm a + h.trace b) := by
    simp only [UnitaryFieldData.norm, UnitaryFieldData.trace, map_mul, h.bar_bar]
    ring
  rw [he, hab, mul_zero]

@[expose] noncomputable def rkOneTauFun (c : K) (x : rkOneUStar h) : rkOneUStar h :=
  uS h (c * uA h x) (h.norm c * uB h x) (tau_param h c (uAB_param h x))

theorem uA_rkOneTauFun (c : K) (x : rkOneUStar h) : uA h (rkOneTauFun h c x) = c * uA h x :=
  uA_uS h _

theorem uB_rkOneTauFun (c : K) (x : rkOneUStar h) :
    uB h (rkOneTauFun h c x) = h.norm c * uB h x :=
  uB_uS h _

theorem rkOneTauFun_mul (c : K) (x y : rkOneUStar h) :
    rkOneTauFun h c (x * y) = rkOneTauFun h c x * rkOneTauFun h c y := by
  apply uS_ext h
  · rw [uA_mul, uA_rkOneTauFun, uA_rkOneTauFun, uA_rkOneTauFun, uA_mul]
    ring
  · rw [uB_mul, uB_rkOneTauFun, uB_rkOneTauFun, uB_rkOneTauFun, uA_rkOneTauFun,
      uA_rkOneTauFun, uB_mul, UnitaryFieldData.norm, map_mul]
    ring

theorem rkOneTauFun_comp (c d : K) (x : rkOneUStar h) :
    rkOneTauFun h c (rkOneTauFun h d x) = rkOneTauFun h (c * d) x := by
  apply uS_ext h
  · rw [uA_rkOneTauFun, uA_rkOneTauFun, uA_rkOneTauFun]
    ring
  · rw [uB_rkOneTauFun, uB_rkOneTauFun, uB_rkOneTauFun, UnitaryFieldData.norm,
      UnitaryFieldData.norm, UnitaryFieldData.norm, map_mul]
    ring

theorem rkOneTauFun_one (x : rkOneUStar h) : rkOneTauFun h 1 x = x := by
  apply uS_ext h
  · rw [uA_rkOneTauFun, one_mul]
  · rw [uB_rkOneTauFun, UnitaryFieldData.norm, map_one, one_mul, one_mul]

@[expose] noncomputable def rkOneTau : Kˣ →* MulAut (rkOneUStar h) where
  toFun c :=
    { toFun := rkOneTauFun h c
      invFun := rkOneTauFun h (c⁻¹ : Kˣ)
      left_inv := fun x => by
        rw [rkOneTauFun_comp, ← Units.val_mul, inv_mul_cancel, Units.val_one, rkOneTauFun_one]
      right_inv := fun x => by
        rw [rkOneTauFun_comp, ← Units.val_mul, mul_inv_cancel, Units.val_one, rkOneTauFun_one]
      map_mul' := rkOneTauFun_mul h c }
  map_one' := MulEquiv.ext fun x => rkOneTauFun_one h x
  map_mul' c d := MulEquiv.ext fun x => by
    change rkOneTauFun h (c * d : Kˣ) x = rkOneTauFun h c (rkOneTauFun h d x)
    rw [rkOneTauFun_comp, Units.val_mul]

theorem rkOneTau_apply (c : Kˣ) (x : rkOneUStar h) : rkOneTau h c x = rkOneTauFun h c x :=
  rfl

end Tau

section Additive

variable (h : UnitaryFieldData p f K)

theorem rkOneAHom_eq (x : rkOneUStar h) : rkOneAHom h x = Multiplicative.ofAdd (uA h x) :=
  rfl

theorem uA_inv (x : rkOneUStar h) : uA h x⁻¹ = -uA h x := by
  have h1 := uA_mul h x x⁻¹
  rw [mul_inv_cancel] at h1
  have h0 : uA h (1 : rkOneUStar h) = 0 := by
    have := uA_mul h 1 1
    rw [mul_one] at this
    linear_combination -this
  linear_combination h0 - h1

theorem uS_commutator {a b c d : K} (hab : h.norm a + h.trace b = 0)
    (hcd : h.norm c + h.trace d = 0) :
    uS h a b hab * uS h c d hcd * (uS h a b hab)⁻¹ * (uS h c d hcd)⁻¹ =
      uS h 0 (h.bar c * a - h.bar a * c) (commutator_param_mem h a c) :=
  Subtype.ext (rkOneU_commutator h hab hcd)

theorem uA_commutator (x y : rkOneUStar h) : uA h (x * y * x⁻¹ * y⁻¹) = 0 := by
  rw [uA_mul, uA_mul, uA_mul, uA_inv, uA_inv]
  ring

theorem exists_uS_commutator {t : K} (ht : t ∈ h.traceZero) :
    ∃ (r b d : K) (hb : h.norm 1 + h.trace b = 0) (hd : h.norm r + h.trace d = 0),
      h.bar r - r = t ∧ uS h 1 b hb * uS h r d hd * (uS h 1 b hb)⁻¹ * (uS h r d hd)⁻¹ =
        uS h 0 t (norm_zero_add_trace ht) := by
  have ht' : t ∈ h.barSub.range := by rw [h.range_barSub]; exact ht
  obtain ⟨r, hr⟩ := ht'
  rw [UnitaryFieldData.barSub_apply] at hr
  obtain ⟨b, hb⟩ := exists_norm_add_trace_eq_zero h 1
  obtain ⟨d, hd⟩ := exists_norm_add_trace_eq_zero h r
  refine ⟨r, b, d, hb, hd, hr, ?_⟩
  rw [uS_commutator]
  exact uS_congr h _ rfl (by rw [map_one, mul_one, one_mul, hr])

theorem uA_eq_zero_iff_mem_commutator (x : rkOneUStar h) :
    uA h x = 0 ↔ x ∈ ⁅(⊤ : Subgroup (rkOneUStar h)), (⊤ : Subgroup (rkOneUStar h))⁆ := by
  have hCU : (⁅(⊤ : Subgroup (rkOneUStar h)), (⊤ : Subgroup (rkOneUStar h))⁆).map
      (rkOneUStar h).subtype = rkOneC h := by
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
      rkOneC_eq_commutator]
  have h1 : x ∈ ⁅(⊤ : Subgroup (rkOneUStar h)), (⊤ : Subgroup (rkOneUStar h))⁆ ↔
      (x : Equiv.Perm (hypIsotropicLines h 1 1)) ∈ rkOneC h := by
    rw [← hCU]
    exact (Subgroup.mem_map_iff_mem (rkOneUStar h).subtype_injective).symm
  rw [h1, ← Subgroup.mem_subgroupOf, ← ker_rkOneAHom, MonoidHom.mem_ker, rkOneAHom_eq]
  exact ⟨fun hx => by rw [hx]; rfl, fun hx => by simpa using hx⟩

theorem uA_map_eq_zero (ψ : MulAut (rkOneUStar h)) (x : rkOneUStar h) (hx : uA h x = 0) :
    uA h (ψ x) = 0 := by
  have hchar : (⁅(⊤ : Subgroup (rkOneUStar h)), (⊤ : Subgroup (rkOneUStar h))⁆).map
      ψ.toMonoidHom = ⁅(⊤ : Subgroup (rkOneUStar h)), (⊤ : Subgroup (rkOneUStar h))⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ ψ.surjective]
  rw [uA_eq_zero_iff_mem_commutator] at hx ⊢
  rw [← hchar]
  exact ⟨x, hx, rfl⟩

theorem addMap_add (ψ : MulAut (rkOneUStar h)) (b₀ : K → K)
    (hb₀ : ∀ a, h.norm a + h.trace (b₀ a) = 0)
    (hA : ∀ (x : rkOneUStar h) (a : K), uA h x = a →
      uA h (ψ x) = uA h (ψ (uS h a (b₀ a) (hb₀ a)))) (a a' : K) :
    uA h (ψ (uS h (a + a') (b₀ (a + a')) (hb₀ (a + a')))) =
      uA h (ψ (uS h a (b₀ a) (hb₀ a))) + uA h (ψ (uS h a' (b₀ a') (hb₀ a'))) := by
  have hXY : uA h (uS h a (b₀ a) (hb₀ a) * uS h a' (b₀ a') (hb₀ a')) = a + a' := by
    rw [uA_mul, uA_uS, uA_uS]
  rw [← hA _ (a + a') hXY, MulEquiv.map_mul, uA_mul]

theorem exists_addMap (ψ : MulAut (rkOneUStar h)) :
    ∃ A : K →+ K, ∀ x : rkOneUStar h, uA h (ψ x) = A (uA h x) := by
  choose b₀ hb₀ using exists_norm_add_trace_eq_zero h
  have hC : ∀ x : rkOneUStar h, uA h x = 0 → uA h (ψ x) = 0 := fun x hx =>
    uA_map_eq_zero h ψ x hx
  have hA : ∀ (x : rkOneUStar h) (a : K), uA h x = a →
      uA h (ψ x) = uA h (ψ (uS h a (b₀ a) (hb₀ a))) := by
    intro x a hxa
    have ht : h.norm 0 + h.trace (uB h x - b₀ a) = 0 := by
      rw [trace_sub]
      have h1 := uAB_param h x
      have h2 := hb₀ a
      rw [hxa] at h1
      simp only [UnitaryFieldData.norm] at h1 h2 ⊢
      linear_combination h1 - h2
    have hxy : x = uS h a (b₀ a) (hb₀ a) * uS h 0 _ ht := by
      rw [uS_mul]
      conv_lhs => rw [eq_uS h x]
      exact uS_congr h _ (by rw [hxa, add_zero]) (by rw [mul_zero]; ring)
    rw [hxy, MulEquiv.map_mul, uA_mul, hC _ (uA_uS h ht), add_zero]
  refine ⟨AddMonoidHom.mk' (fun a => uA h (ψ (uS h a (b₀ a) (hb₀ a))))
    (addMap_add h ψ b₀ hb₀ hA), fun x => hA x _ rfl⟩

end Additive

section Commutator

variable (h : UnitaryFieldData p f K)

theorem map_commutator_aut (ψ : MulAut (rkOneUStar h)) (x y : rkOneUStar h) :
    ψ (x * y * x⁻¹ * y⁻¹) = ψ x * ψ y * (ψ x)⁻¹ * (ψ y)⁻¹ := by
  simp only [map_mul, map_inv]

theorem uB_commutator (x y : rkOneUStar h) :
    uB h (x * y * x⁻¹ * y⁻¹) = h.bar (uA h y) * uA h x - h.bar (uA h x) * uA h y := by
  conv_lhs => rw [eq_uS h x, eq_uS h y, uS_commutator, uB_uS]

theorem map_uS_mul (ψ : MulAut (rkOneUStar h)) (x y : rkOneUStar h) :
    ψ (x * y) = ψ x * ψ y :=
  map_mul ψ x y

end Commutator

section Normalizing

variable (h : UnitaryFieldData p f K)

theorem aut_inv_apply_apply (ψ : MulAut (rkOneUStar h)) (x : rkOneUStar h) : ψ⁻¹ (ψ x) = x := by
  rw [MulAut.inv_apply, MulEquiv.symm_apply_apply]

theorem aut_apply_inv_apply (ψ : MulAut (rkOneUStar h)) (x : rkOneUStar h) : ψ (ψ⁻¹ x) = x := by
  rw [MulAut.inv_apply, MulEquiv.apply_symm_apply]

theorem addMap_inv_apply {ψ : MulAut (rkOneUStar h)} {A A' : K →+ K}
    (hA : ∀ x, uA h (ψ x) = A (uA h x)) (hA' : ∀ x, uA h (ψ⁻¹ x) = A' (uA h x)) (a : K) :
    A' (A a) = a := by
  obtain ⟨b, hb⟩ := exists_norm_add_trace_eq_zero h a
  have h1 := hA' (ψ (uS h a b hb))
  simp only [aut_inv_apply_apply, hA, uA_uS] at h1
  exact h1.symm

theorem exists_conj_tau {θ : MulAut (rkOneUStar h)}
    (hθ : θ ∈ Subgroup.normalizer (((rkOneM h).map (rkOneTau h) :
      Subgroup (MulAut (rkOneUStar h))) : Set (MulAut (rkOneUStar h)))) {k : Kˣ}
    (hk : k ∈ rkOneM h) : ∃ k' ∈ rkOneM h, ∀ x, θ (rkOneTau h k x) = rkOneTau h k' (θ x) := by
  obtain ⟨k', hk', he⟩ := (Subgroup.mem_normalizer_iff.mp hθ (rkOneTau h k)).mp ⟨k, hk, rfl⟩
  refine ⟨k', hk', fun x => ?_⟩
  have h1 := congrArg (fun g : MulAut (rkOneUStar h) => g (θ x)) he
  simp only [MulAut.mul_apply, aut_inv_apply_apply] at h1
  exact h1.symm

theorem addMap_tau {ψ : MulAut (rkOneUStar h)} {A : K →+ K}
    (hA : ∀ x, uA h (ψ x) = A (uA h x)) {k k' : Kˣ}
    (hkk : ∀ x, ψ (rkOneTau h k x) = rkOneTau h k' (ψ x)) (a : K) : A (k * a) = k' * A a := by
  obtain ⟨b, hb⟩ := exists_norm_add_trace_eq_zero h a
  have h1 := congrArg (uA h) (hkk (uS h a b hb))
  simp only [rkOneTau_apply, uA_rkOneTauFun, hA, uA_uS] at h1
  exact h1

@[expose] noncomputable def addEquivOf (A A' : K →+ K) (h1 : ∀ a, A' (A a) = a)
    (h2 : ∀ a, A (A' a) = a) : K ≃+ K :=
  { toFun := A
    invFun := A'
    left_inv := h1
    right_inv := h2
    map_add' := A.map_add }

theorem addEquivOf_mem_normalizer {θ : MulAut (rkOneUStar h)}
    (hθ : θ ∈ Subgroup.normalizer (((rkOneM h).map (rkOneTau h) :
      Subgroup (MulAut (rkOneUStar h))) : Set (MulAut (rkOneUStar h)))) {A A' : K →+ K}
    (hA : ∀ x, uA h (θ x) = A (uA h x)) (hA' : ∀ x, uA h (θ⁻¹ x) = A' (uA h x))
    (h1 : ∀ a, A' (A a) = a) (h2 : ∀ a, A (A' a) = a) :
    ((addEquivOf A A' h1 h2).toEquiv : Equiv.Perm K) ∈ Subgroup.normalizer
      (((rkOneM h).map (MulAction.toPermHom Kˣ K) : Subgroup (Equiv.Perm K)) :
        Set (Equiv.Perm K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨k', hk', hkk⟩ := exists_conj_tau h hθ hk
    refine ⟨k', hk', Equiv.ext fun z => ?_⟩
    change (k' : K) * z = A ((k : K) * A' z)
    rw [addMap_tau h hA hkk, h2]
  · rintro ⟨k, hk, hg⟩
    obtain ⟨k', hk', hkk⟩ := exists_conj_tau h (inv_mem hθ) hk
    refine ⟨k', hk', Equiv.ext fun z => ?_⟩
    have h3 := congrArg (fun π : Equiv.Perm K => π (A z)) hg
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.coe_inv] at h3
    change (k' : K) * z = g z
    have h4 : (addEquivOf A A' h1 h2).toEquiv.symm (A z) = z := h1 z
    rw [h4] at h3
    change (k : K) * A z = A (g z) at h3
    have h5 := congrArg A' h3
    rw [h1, addMap_tau h hA' hkk, h1] at h5
    exact h5

end Normalizing

section BParam

variable (h : UnitaryFieldData p f K)

theorem sigma_param (c : K) (σ : K ≃+* K) {a b : K} (hab : h.norm a + h.trace b = 0) :
    h.norm (c * σ a) + h.trace (h.norm c * σ b) = 0 := by
  have he : h.norm (σ a) + h.trace (σ b) = σ (h.norm a + h.trace b) := by
    simp only [UnitaryFieldData.norm, UnitaryFieldData.trace, map_add, map_mul,
      map_bar_comm h σ]
  have h1 := tau_param h c (a := σ a) (b := σ b) (by rw [he, hab, map_zero])
  exact h1

theorem uB_aut_center {θ : MulAut (rkOneUStar h)} {c : K} {σ : K ≃+* K}
    (hA : ∀ x, uA h (θ x) = c * σ (uA h x)) {t : K} (ht : t ∈ h.traceZero) :
    uB h (θ (uS h 0 t (norm_zero_add_trace ht))) = h.norm c * σ t := by
  obtain ⟨r, b, d, hb, hd, hrt, he⟩ := exists_uS_commutator h ht
  rw [← he, map_commutator_aut, uB_commutator]
  simp only [hA, uA_uS, map_one, mul_one, ← hrt, map_sub, map_bar_comm h σ, map_mul,
    UnitaryFieldData.norm]
  ring

theorem uB_aut_shift {θ : MulAut (rkOneUStar h)} {c : K} {σ : K ≃+* K}
    (hA : ∀ x, uA h (θ x) = c * σ (uA h x)) {a b t : K} (hab : h.norm a + h.trace b = 0)
    (ht : t ∈ h.traceZero) (hab' : h.norm a + h.trace (b + t) = 0) :
    uB h (θ (uS h a (b + t) hab')) = uB h (θ (uS h a b hab)) + h.norm c * σ t := by
  have hprod : uS h a b hab * uS h 0 t (norm_zero_add_trace ht) = uS h a (b + t) hab' := by
    rw [uS_mul]
    exact uS_congr h _ (add_zero a) (by rw [mul_zero, sub_zero])
  rw [← hprod, map_uS_mul, uB_mul]
  simp only [uB_aut_center h hA ht, hA, uA_uS, map_zero, mul_zero, sub_zero]

theorem uB_aut_sub_eq {θ : MulAut (rkOneUStar h)} {c : K} {σ : K ≃+* K}
    (hA : ∀ x, uA h (θ x) = c * σ (uA h x)) {a b b' : K} (hab : h.norm a + h.trace b = 0)
    (hab' : h.norm a + h.trace b' = 0) :
    uB h (θ (uS h a b' hab')) - h.norm c * σ b' = uB h (θ (uS h a b hab)) - h.norm c * σ b := by
  have ht : b' - b ∈ h.traceZero := by
    rw [UnitaryFieldData.mem_traceZero, trace_sub]
    linear_combination hab' - hab
  have he : b' = b + (b' - b) := by ring
  have hab'' : h.norm a + h.trace (b + (b' - b)) = 0 := by rw [← he]; exact hab'
  have h1 := uB_aut_shift h hA hab ht hab''
  rw [uS_congr h hab'' rfl he.symm] at h1
  rw [h1, map_sub]
  ring

end BParam

section Node

variable (h : UnitaryFieldData p f K)

theorem norm_map_sigma (σ : K ≃+* K) (x : K) : h.norm (σ x) = σ (h.norm x) := by
  rw [UnitaryFieldData.norm, UnitaryFieldData.norm, map_mul, map_bar_comm h σ]

@[expose] noncomputable def bOf (a : K) : K :=
  (exists_norm_add_trace_eq_zero h a).choose

theorem bOf_spec (a : K) : h.norm a + h.trace (bOf h a) = 0 :=
  (exists_norm_add_trace_eq_zero h a).choose_spec

@[expose] noncomputable def autDefect (θ : MulAut (rkOneUStar h)) (c : K) (σ : K ≃+* K)
    (a : K) : K :=
  uB h (θ (uS h a (bOf h a) (bOf_spec h a))) - h.norm c * σ (bOf h a)

theorem autDefect_eq {θ : MulAut (rkOneUStar h)} {c : K} {σ : K ≃+* K}
    (hA : ∀ x, uA h (θ x) = c * σ (uA h x)) {a b : K} (hab : h.norm a + h.trace b = 0) :
    uB h (θ (uS h a b hab)) = autDefect h θ c σ a + h.norm c * σ b := by
  have h1 := uB_aut_sub_eq h hA (bOf_spec h a) hab
  rw [autDefect]
  linear_combination h1

theorem autDefect_add {θ : MulAut (rkOneUStar h)} {c : K} {σ : K ≃+* K}
    (hA : ∀ x, uA h (θ x) = c * σ (uA h x)) (a a' : K) :
    autDefect h θ c σ (a + a') = autDefect h θ c σ a + autDefect h θ c σ a' := by
  have hp := ((unitary_heisenberg_identities h).2.1 a (bOf h a) a' (bOf h a') (bOf_spec h a)
    (bOf_spec h a')).2
  have h1 := autDefect_eq h hA hp
  have hxy := uS_mul h (bOf_spec h a) (bOf_spec h a')
  have h2 : uB h (θ (uS h a (bOf h a) (bOf_spec h a) * uS h a' (bOf h a') (bOf_spec h a'))) =
      uB h (θ (uS h a (bOf h a) (bOf_spec h a))) +
        uB h (θ (uS h a' (bOf h a') (bOf_spec h a'))) - h.bar (c * σ a) * (c * σ a') := by
    simp only [map_uS_mul, uB_mul, hA, uA_uS]
  simp only [hxy, autDefect_eq h hA] at h2
  simp only [map_sub, map_add, map_mul, map_bar_comm h σ, UnitaryFieldData.norm] at h2
  linear_combination h2

theorem autDefect_mul {θ : MulAut (rkOneUStar h)} {c : K} {σ : K ≃+* K}
    (hA : ∀ x, uA h (θ x) = c * σ (uA h x)) {k : Kˣ} (hkN : h.norm (k : K) = 1)
    (hk : ∀ x, θ (rkOneTau h k x) = rkOneTau h (Units.map (σ : K →* K) k) (θ x)) (a : K) :
    autDefect h θ c σ ((k : K) * a) = autDefect h θ c σ a := by
  have heq : rkOneTau h k (uS h a (bOf h a) (bOf_spec h a)) =
      uS h ((k : K) * a) (h.norm k * bOf h a) (tau_param h (k : K) (bOf_spec h a)) :=
    uS_ext h (by simp only [rkOneTau_apply, uA_rkOneTauFun, uA_uS])
      (by simp only [rkOneTau_apply, uB_rkOneTauFun, uB_uS])
  have h4 := congrArg (uB h) (hk (uS h a (bOf h a) (bOf_spec h a)))
  have hNσk : h.norm ((Units.map (σ : K →* K) k : Kˣ) : K) = 1 := by
    rw [Units.coe_map]
    change h.norm (σ (k : K)) = 1
    rw [norm_map_sigma h σ, hkN, map_one]
  simp only [heq, rkOneTau_apply, uB_rkOneTauFun, autDefect_eq h hA, hNσk, hkN, one_mul] at h4
  linear_combination h4

theorem autDefect_eq_zero {θ : MulAut (rkOneUStar h)} {c : K} {σ : K ≃+* K}
    (hA : ∀ x, uA h (θ x) = c * σ (uA h x)) {k : Kˣ} (hk1 : k ≠ 1)
    (hkN : h.norm (k : K) = 1)
    (hk : ∀ x, θ (rkOneTau h k x) = rkOneTau h (Units.map (σ : K →* K) k) (θ x)) (x : K) :
    autDefect h θ c σ x = 0 := by
  have hk1' : (k : K) - 1 ≠ 0 := fun h0 =>
    hk1 (Units.ext (by rw [Units.val_one]; linear_combination h0))
  have h0 : autDefect h θ c σ 0 = 0 := by
    have h1 := autDefect_add h hA 0 0
    rw [add_zero] at h1
    linear_combination -h1
  obtain ⟨y, hy⟩ : ∃ y : K, y = x / ((k : K) - 1) := ⟨_, rfl⟩
  have hx : x = (k : K) * y + -y := by
    rw [hy]
    field_simp
    ring
  have h1 := autDefect_add h hA ((k : K) * y) (-y)
  have h2 := autDefect_add h hA y (-y)
  rw [add_neg_cancel, h0] at h2
  rw [hx, h1, autDefect_mul h hA hkN hk]
  linear_combination -h2

theorem uB_aut_eq {θ : MulAut (rkOneUStar h)} {c : K} {σ : K ≃+* K}
    (hA : ∀ x, uA h (θ x) = c * σ (uA h x)) {k : Kˣ} (hk1 : k ≠ 1)
    (hkN : h.norm (k : K) = 1)
    (hk : ∀ x, θ (rkOneTau h k x) = rkOneTau h (Units.map (σ : K →* K) k) (θ x))
    {a b : K} (hab : h.norm a + h.trace b = 0) :
    uB h (θ (uS h a b hab)) = h.norm c * σ b := by
  rw [autDefect_eq h hA hab, autDefect_eq_zero h hA hk1 hkN hk, zero_add]

theorem unitary_rank_one_root_torus_automorphisms (h : UnitaryFieldData p f K) (hq : 2 < p ^ f)
    (θ : MulAut (rkOneUStar h))
    (hθ : θ ∈ Subgroup.normalizer (((rkOneM h).map (rkOneTau h) :
      Subgroup (MulAut (rkOneUStar h))) : Set (MulAut (rkOneUStar h)))) :
    ∃ (c : Kˣ) (σ : K ≃+* K), ∀ (a b : K) (hab : h.norm a + h.trace b = 0),
      θ (uS h a b hab) = uS h (c * σ a) (h.norm c * σ b) (sigma_param h c σ hab) := by
  obtain ⟨A, hA⟩ := exists_addMap h θ
  obtain ⟨A', hA'⟩ := exists_addMap h θ⁻¹
  have h1 : ∀ a, A' (A a) = a := addMap_inv_apply h hA hA'
  have hA'' : ∀ x, uA h (θ⁻¹⁻¹ x) = A (uA h x) := by simpa only [inv_inv] using hA
  have h2 : ∀ a, A (A' a) = a := addMap_inv_apply h hA' hA''
  have hnorm := addEquivOf_mem_normalizer h hθ hA hA' h1 h2
  obtain ⟨hMcard, k, hk, hk1⟩ := (unitary_rank_one_torus_action h).2.2.2.2.2 hq
  obtain ⟨c, σ, hcσ⟩ := unitary_large_torus_additive_normalizer h hMcard _ hnorm
  have hAcσ : ∀ x, uA h (θ x) = c * σ (uA h x) := fun x => by
    rw [hA]
    exact hcσ _
  obtain ⟨k', hk', hkk⟩ := exists_conj_tau h hθ hk.1
  have hkk' : (k' : K) = σ (k : K) := by
    have h3 := addMap_tau h hA hkk 1
    have h4 : A (k : K) = c * σ k := hcσ _
    have h5 : A 1 = c * σ 1 := hcσ _
    rw [mul_one, h4, h5, map_one, mul_one] at h3
    exact (mul_left_cancel₀ c.ne_zero (h3.trans (mul_comm _ _))).symm
  have hkσ : k' = Units.map (σ : K →* K) k := Units.ext (by rw [hkk', Units.coe_map]; rfl)
  rw [hkσ] at hkk
  have hkN : h.norm (k : K) = 1 := by
    have := (Subgroup.mem_inf.mp hk).2
    rw [MonoidHom.mem_ker] at this
    have h6 := congrArg (fun u : h.fixedFieldˣ => ((u : h.fixedField) : K)) this
    simpa [UnitaryFieldData.coe_normHom] using h6
  refine ⟨c, σ, fun a b hab => uS_ext h ?_ ?_⟩
  · rw [hAcσ, uA_uS, uA_uS]
  · rw [uB_aut_eq h hAcσ hk1 hkN hkk hab, uB_uS]

end Node

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
