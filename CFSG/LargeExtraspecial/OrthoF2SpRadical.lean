module

public import CFSG.LargeExtraspecial.OrthoF2Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module OrthoF2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {f : LinearMap.BilinForm (ZMod 2) V}

namespace OrthoF2

theorem isAlt_symm (hf : f.IsAlt) (x y : V) : f x y = f y x := by
  rw [← hf.neg_eq, zmod2_neg]

end OrthoF2

@[expose] noncomputable def spTransvection (f : LinearMap.BilinForm (ZMod 2) V) (hf : f.IsAlt)
    (a : V) : V ≃ₗ[ZMod 2] V :=
  LinearEquiv.ofInvolutive
    { toFun := fun x => x + f x a • a
      map_add' := fun x y => by
        simp only [map_add, LinearMap.add_apply, add_smul]
        abel
      map_smul' := fun c x => by
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add,
          mul_smul] }
    fun x => by
      change (x + f x a • a) + f (x + f x a • a) a • a = x
      rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hf.self_eq_zero,
        smul_zero, add_zero, add_assoc, vec_add_self, add_zero]

theorem spTransvection_apply (hf : f.IsAlt) (a x : V) :
    spTransvection f hf a x = x + f x a • a :=
  rfl

@[expose] def spPointRadical (f : LinearMap.BilinForm (ZMod 2) V) (a : V) :
    Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {t | t ∈ TauCeti.BilinForm.isometryGroup f ∧ t a = a ∧
    (∀ x, f a x = 0 → t x - x ∈ (ZMod 2) ∙ a) ∧ ∀ v, f a (t v - v) = 0}
  mul_mem' := by
    rintro s t ⟨hs, hsa, hs1, hs2⟩ ⟨ht, hta, ht1, ht2⟩
    refine ⟨mul_mem hs ht, by rw [LinearEquiv.mul_apply, hta, hsa], fun x hx => ?_, fun v => ?_⟩
    · have htx : f a (t x) = 0 := by
        rw [← hta, TauCeti.BilinForm.mem_isometryGroup_iff.mp ht, hx]
      have e : (s * t) x - x = (s (t x) - t x) + (t x - x) := by
        rw [LinearEquiv.mul_apply]
        abel
      rw [e]
      exact Submodule.add_mem _ (hs1 _ htx) (ht1 x hx)
    · have e : (s * t) v - v = (s (t v) - t v) + (t v - v) := by
        rw [LinearEquiv.mul_apply]
        abel
      rw [e, map_add, hs2, ht2, add_zero]
  one_mem' := ⟨one_mem _, rfl, fun x _ => by simp, fun v => by simp⟩
  inv_mem' := by
    rintro t ⟨ht, hta, ht1, ht2⟩
    have hinv : ∀ y, t⁻¹ y - y = -(t (t⁻¹ y) - t⁻¹ y) := fun y => by
      rw [apply_inv_apply]
      abel
    have hta' : t⁻¹ a = a := by
      conv_lhs => rw [← hta]
      exact CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply' t a
    refine ⟨inv_mem ht, hta', fun x hx => ?_, fun v => ?_⟩
    · have h : f a (t⁻¹ x) = 0 := by
        rw [← hta', TauCeti.BilinForm.mem_isometryGroup_iff.mp (inv_mem ht) a x]
        exact hx
      rw [hinv]
      exact neg_mem (ht1 _ h)
    · rw [hinv, map_neg, ht2, neg_zero]

theorem mem_spPointRadical {a : V} {t : V ≃ₗ[ZMod 2] V} :
    t ∈ spPointRadical f a ↔ t ∈ TauCeti.BilinForm.isometryGroup f ∧ t a = a ∧
      (∀ x, f a x = 0 → t x - x ∈ (ZMod 2) ∙ a) ∧ ∀ v, f a (t v - v) = 0 :=
  Iff.rfl

theorem spTransvection_mem_isometryGroup (hf : f.IsAlt) (a : V) :
    spTransvection f hf a ∈ TauCeti.BilinForm.isometryGroup f := by
  rw [TauCeti.BilinForm.mem_isometryGroup_iff]
  intro x y
  simp only [spTransvection_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, hf.self_eq_zero, mul_zero, add_zero, ← hf.neg_eq y a]
  ring

theorem spTransvection_mem_spPointRadical (hf : f.IsAlt) (a : V) :
    spTransvection f hf a ∈ spPointRadical f a := by
  refine ⟨spTransvection_mem_isometryGroup hf a, ?_, fun x hx => ?_, fun v => ?_⟩
  · rw [spTransvection_apply, hf.self_eq_zero, zero_smul, add_zero]
  · rw [spTransvection_apply, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)
  · rw [spTransvection_apply, add_sub_cancel_left, map_smul, hf.self_eq_zero, smul_zero]

theorem spTransvection_ne_one (hf : f.IsAlt) (hnd : f.Nondegenerate) {a : V} (ha : a ≠ 0) :
    spTransvection f hf a ≠ 1 := by
  intro h
  obtain ⟨y, hy⟩ : ∃ y, f y a ≠ 0 := by
    by_contra! h'
    exact ha (hnd.2 a h')
  have h2 := LinearEquiv.congr_fun h y
  rw [spTransvection_apply, LinearEquiv.coe_one, id, add_eq_left, smul_eq_zero] at h2
  rcases h2 with h2 | h2
  · exact hy h2
  · exact ha h2

theorem spPointRadical_apply_of_orthogonal {a b : V} (hb1 : f a b = 1) {t : V ≃ₗ[ZMod 2] V}
    (ht : t ∈ spPointRadical f a) {x : V} (hx : f a x = 0) : t x = x + f x (t b - b) • a := by
  obtain ⟨ht, -, ht1, ht2⟩ := ht
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (ht1 x hx)
  have htx : t x = x + c • a := by rw [hc]; abel
  set w := t b - b with hw
  have htb : t b = b + w := by rw [hw]; abel
  have hw2 : f a w = 0 := ht2 b
  have hiso := TauCeti.BilinForm.mem_isometryGroup_iff.mp ht x b
  rw [htx, htb] at hiso
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hb1,
    hw2, mul_one, mul_zero, add_zero] at hiso
  have hc' : c = f x w := by
    have h' : f x w + c = 0 := by linear_combination hiso
    exact (zmod2_eq_of_add_eq_zero h').symm
  rw [htx, hc']

theorem spPointRadical_ext {a b : V} (hb1 : f a b = 1) {s t : V ≃ₗ[ZMod 2] V}
    (hs : s ∈ spPointRadical f a) (ht : t ∈ spPointRadical f a) (h : s b = t b) : s = t := by
  refine LinearEquiv.ext fun v => ?_
  have hperp : f a (v - f a v • b) = 0 := by
    rw [map_sub, map_smul, hb1, smul_eq_mul, mul_one, sub_self]
  have hv : v = (v - f a v • b) + f a v • b := by abel
  rw [hv, map_add, map_add, map_smul, map_smul, spPointRadical_apply_of_orthogonal hb1 hs hperp,
    spPointRadical_apply_of_orthogonal hb1 ht hperp, h]

theorem isElementaryAbelian_spPointRadical (hf : f.IsAlt) (hnd : f.Nondegenerate) {a : V}
    (ha : a ≠ 0) : IsElementaryAbelian 2 (spPointRadical f a) := by
  obtain ⟨b, hb⟩ : ∃ b, f a b ≠ 0 := by
    by_contra! h
    exact ha (hnd.1 a h)
  have hb1 : f a b = 1 := zmod2_eq_one_of_ne_zero hb
  have hprod : ∀ s t : spPointRadical f a, (s : V ≃ₗ[ZMod 2] V) ((t : V ≃ₗ[ZMod 2] V) b) =
      b + ((s : V ≃ₗ[ZMod 2] V) b - b) + ((t : V ≃ₗ[ZMod 2] V) b - b) +
        f ((t : V ≃ₗ[ZMod 2] V) b - b) ((s : V ≃ₗ[ZMod 2] V) b - b) • a := by
    intro s t
    have hw : f a ((t : V ≃ₗ[ZMod 2] V) b - b) = 0 := t.2.2.2.2 b
    have e : (t : V ≃ₗ[ZMod 2] V) b = b + ((t : V ≃ₗ[ZMod 2] V) b - b) := by abel
    rw [e, map_add, spPointRadical_apply_of_orthogonal hb1 s.2 hw, ← e]
    abel
  have hcomm : ∀ s t : spPointRadical f a, s * t = t * s := by
    intro s t
    refine Subtype.ext (spPointRadical_ext hb1 (s * t).2 (t * s).2 ?_)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hprod,
      hprod, isAlt_symm hf ((t : V ≃ₗ[ZMod 2] V) b - b)]
    abel
  have hsq : ∀ t : spPointRadical f a, t ^ 2 = 1 := by
    intro t
    refine Subtype.ext (spPointRadical_ext hb1 (t ^ 2).2 (one_mem _) ?_)
    rw [pow_two, Subgroup.coe_mul, LinearEquiv.mul_apply, hprod, hf.self_eq_zero, zero_smul,
      add_zero, add_assoc, vec_add_self, add_zero, OneMemClass.coe_one, LinearEquiv.coe_one, id]
  exact { is_comm := ⟨hcomm⟩
          exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hsq }

theorem card_spPointRadical [FiniteDimensional (ZMod 2) V] (hf : f.IsAlt)
    (hnd : f.Nondegenerate) {a : V} (ha : a ≠ 0) :
    Nat.card (spPointRadical f a) = 2 ^ (finrank (ZMod 2) V - 1) := by
  obtain ⟨b, hb⟩ : ∃ b, f a b ≠ 0 := by
    by_contra! h
    exact ha (hnd.1 a h)
  have hb1 : f a b = 1 := zmod2_eq_one_of_ne_zero hb
  have hba : f b a = 1 := by rw [isAlt_symm hf, hb1]
  have hfaa : f a a = 0 := hf.self_eq_zero a
  let Γ : spPointRadical f a → LinearMap.ker (f a) := fun t =>
    ⟨(t : V ≃ₗ[ZMod 2] V) b - b, t.2.2.2.2 b⟩
  have hinj : Function.Injective Γ := by
    rintro ⟨s, hs⟩ ⟨t, ht⟩ hst
    exact Subtype.ext (spPointRadical_ext hb1 hs ht (sub_left_inj.mp (congrArg Subtype.val hst)))
  have hsurj : Function.Surjective Γ := by
    rintro ⟨w, hw⟩
    have hfaw : f a w = 0 := hw
    have hfwa : f w a = 0 := by rw [isAlt_symm hf, hfaw]
    have hfww : f w w = 0 := hf.self_eq_zero w
    set c := f b w with hc
    let T : V →ₗ[ZMod 2] V :=
      { toFun := fun v => v + (f v a • w + (f v w + c * f v a) • a)
        map_add' := fun x y => by
          simp only [map_add, LinearMap.add_apply, add_smul, mul_add]
          abel
        map_smul' := fun r x => by
          simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
          module }
    have hT : ∀ v, T v = v + (f v a • w + (f v w + c * f v a) • a) := fun v => rfl
    have hTa : ∀ v, f (T v) a = f v a := fun v => by
      simp only [hT, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hfwa, hfaa, mul_zero, add_zero]
    have hTw : ∀ v, f (T v) w = f v w := fun v => by
      simp only [hT, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hfww, hfaw, mul_zero, add_zero]
    have hTinv : Function.Involutive T := fun v => by
      rw [hT (T v), hTa, hTw, hT v, add_assoc, vec_add_self, add_zero]
    let t : V ≃ₗ[ZMod 2] V := LinearEquiv.ofInvolutive T hTinv
    have htv : ∀ v, t v = T v := fun v => rfl
    have ht : t ∈ spPointRadical f a := by
      refine ⟨TauCeti.BilinForm.mem_isometryGroup_iff.mpr fun x y => ?_, ?_, fun x hx => ?_,
        fun v => ?_⟩
      · rw [htv, htv]
        simp only [hT, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
          hfaa, hfww, hfwa, hfaw, mul_zero, add_zero, ← hf.neg_eq y w, ← hf.neg_eq y a]
        ring
      · rw [htv, hT, hfaa, hfaw]
        simp
      · have hxa : f x a = 0 := by rw [isAlt_symm hf, hx]
        rw [htv, hT, hxa, add_sub_cancel_left]
        simp only [zero_smul, mul_zero, add_zero, zero_add]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)
      · rw [htv, hT, add_sub_cancel_left, map_add, map_smul, map_smul, hfaw, hfaa]
        simp
    refine ⟨⟨t, ht⟩, Subtype.ext ?_⟩
    change t b - b = w
    rw [htv, hT, add_sub_cancel_left, hba, ← hc, one_smul, mul_one, vec_add_self, zero_smul,
      add_zero]
  rw [Nat.card_congr (Equiv.ofBijective Γ ⟨hinj, hsurj⟩),
    Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  congr 1
  have h := LinearMap.finrank_range_add_finrank_ker (f a)
  have hr : LinearMap.range (f a) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    exact ⟨c • b, by rw [map_smul, hb1, smul_eq_mul, mul_one]⟩
  rw [hr, finrank_top, finrank_self] at h
  omega

end CFSG.LargeExtraspecial
