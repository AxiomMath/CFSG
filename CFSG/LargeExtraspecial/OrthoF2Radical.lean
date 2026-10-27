module

public import CFSG.LargeExtraspecial.OrthoF2Eichler

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions OrthoF2
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_apply eichler_mul eichler_zero_right
  eichler_mem_orthogonalGroup)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

@[expose] def pointRadical (q : QuadraticForm (ZMod 2) V) (a : V) :
    Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {t | t ∈ orthogonalGroup q ∧ t a = a ∧
    (∀ x, polar q a x = 0 → t x - x ∈ (ZMod 2) ∙ a) ∧ ∀ v, polar q a (t v - v) = 0}
  mul_mem' := by
    rintro s t ⟨hs, hsa, hs1, hs2⟩ ⟨ht, hta, ht1, ht2⟩
    refine ⟨mul_mem hs ht, by rw [LinearEquiv.mul_apply, hta, hsa], fun x hx => ?_, fun v => ?_⟩
    · have htx : polar q a (t x) = 0 := by
        rw [← hta, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup ht, hx]
      have e : (s * t) x - x = (s (t x) - t x) + (t x - x) := by
        rw [LinearEquiv.mul_apply]
        abel
      rw [e]
      exact Submodule.add_mem _ (hs1 _ htx) (ht1 x hx)
    · have e : (s * t) v - v = (s (t v) - t v) + (t v - v) := by
        rw [LinearEquiv.mul_apply]
        abel
      rw [e, polar_add_right, hs2, ht2, add_zero]
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
    · have h : polar q a (t⁻¹ x) = 0 := by
        rw [← hta', TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (inv_mem ht) a x]
        exact hx
      rw [hinv]
      exact neg_mem (ht1 _ h)
    · rw [hinv, polar_neg_right, ht2, neg_zero]

theorem mem_pointRadical {a : V} {t : V ≃ₗ[ZMod 2] V} :
    t ∈ pointRadical q a ↔ t ∈ orthogonalGroup q ∧ t a = a ∧
      (∀ x, polar q a x = 0 → t x - x ∈ (ZMod 2) ∙ a) ∧ ∀ v, polar q a (t v - v) = 0 :=
  Iff.rfl

theorem eichler_mem_pointRadical {a u : V} (ha : q a = 0) (hau : polar q a u = 0) :
    eichler q a u ∈ pointRadical q a := by
  refine ⟨eichler_mem_orthogonalGroup q a u,
    CFSG.ClassicalGroups.Orthogonal.eichler_apply_self a u, fun x hx => ?_, fun v => ?_⟩
  · rw [eichler_apply_zmod2 ha hau, polar_comm q x a, hx]
    simp only [zero_smul, mul_zero, add_zero, add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)
  · rw [eichler_apply_zmod2 ha hau, add_assoc, add_sub_cancel_left, polar_add_right,
      polar_smul_right, polar_smul_right, hau, polar_self_eq_zero]
    simp

theorem mem_pointRadical_iff [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    {a : V} (ha0 : a ≠ 0) (ha : q a = 0) {t : V ≃ₗ[ZMod 2] V} :
    t ∈ pointRadical q a ↔ ∃ u, polar q a u = 0 ∧ t = eichler q a u := by
  constructor
  · rintro ⟨ht, -, ht1, ht2⟩
    obtain ⟨b, hb⟩ := CFSG.ClassicalGroups.Orthogonal.exists_polar_ne_zero hq ha0
    have hb1 : polar q a b = 1 := zmod2_eq_one_of_ne_zero hb
    set w := t b - b with hw
    have haw : polar q a w = 0 := ht2 b
    refine ⟨w, haw, ?_⟩
    have hperp : ∀ x, polar q a x = 0 → t x = x + polar q x w • a := by
      intro x hx
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (ht1 x hx)
      have htx : t x = x + c • a := by rw [hc]; abel
      have htb : t b = b + w := by rw [hw]; abel
      have h := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup ht x b
      rw [htx, htb, polar_add_left, polar_add_right, polar_add_right, polar_smul_left,
        polar_smul_left, hb1, haw, smul_eq_mul, smul_eq_mul, mul_one, mul_zero, add_zero] at h
      have hc' : c = polar q x w := by
        have h' : polar q x w + c = 0 := by linear_combination h
        exact (zmod2_eq_of_add_eq_zero h').symm
      rw [htx, hc']
    ext v
    set d := polar q a v with hd
    set x := v - d • b with hx
    have hxa : polar q a x = 0 := by
      rw [hx, polar_sub_right, polar_smul_right, hb1, smul_eq_mul, mul_one, sub_self]
    have hv : v = x + d • b := by rw [hx]; abel
    have hE : ∀ y, polar q a y = 0 → eichler q a w y = y + polar q y w • a := by
      intro y hy
      rw [eichler_apply_zmod2 ha haw, polar_comm q y a, hy]
      simp
    have hEb : eichler q a w b = t b := by
      have hqw : q w + polar q b w = 0 := by
        have h := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup ht b
        rw [show t b = b + w by rw [hw]; abel, map_add_eq] at h
        linear_combination h
      have hqw' : polar q b w + q w = 0 := by rw [add_comm]; exact hqw
      rw [eichler_apply_zmod2 ha haw, polar_comm q b a, hb1, one_smul, mul_one, hqw', zero_smul,
        add_zero, hw, add_sub_cancel]
    rw [hv, map_add, map_add, map_smul, map_smul, hperp x hxa, hE x hxa, hEb]
  · rintro ⟨u, hau, rfl⟩
    exact eichler_mem_pointRadical ha hau

theorem eichler_type_of_not_mem_span [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) {a u : V} (ha0 : a ≠ 0) (ha : q a = 0)
    (hau : polar q a u = 0) (hu : u ∉ (ZMod 2) ∙ a) :
    commSpace (eichler q a u) = Submodule.span (ZMod 2) {a, u} ∧
      (q u = 0 → IsTypeA q (eichler q a u) 2) ∧ (q u = 1 → IsTypeC q (eichler q a u) 2) := by
  have hli : LinearIndependent (ZMod 2) ![a, u] :=
    linearIndependent_pair_iff.mpr ⟨ha0, fun h => hu (h ▸ Submodule.zero_mem _),
      fun h => hu (h ▸ Submodule.mem_span_singleton_self a)⟩
  exact ⟨commSpace_eichler hq ha hau hli, fun h => (eichler_isTypeA hq ha hau hli h).1,
    fun h => (eichler_isTypeC hq ha0 ha hau h).1⟩

theorem pointRadical_apply_of_polar_eq_zero [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) {a : V} (ha0 : a ≠ 0) (ha : q a = 0)
    {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ pointRadical q a) :
    ∃ u, polar q a u = 0 ∧ t = eichler q a u ∧
      ∀ x, polar q a x = 0 → t x = x + polar q x u • a := by
  obtain ⟨u, hau, rfl⟩ := (mem_pointRadical_iff hq ha0 ha).mp ht
  refine ⟨u, hau, rfl, fun x hx => ?_⟩
  rw [eichler_apply_zmod2 ha hau, polar_comm q x a, hx]
  simp

theorem eichler_eq_one_iff [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    {a u : V} (ha0 : a ≠ 0) (ha : q a = 0) (hau : polar q a u = 0) :
    eichler q a u = 1 ↔ u ∈ (ZMod 2) ∙ a := by
  constructor
  · intro h1
    rw [← LinearMap.BilinForm.orthogonal_orthogonal hq (isRefl_polarBilin q) ((ZMod 2) ∙ a),
      LinearMap.BilinForm.mem_orthogonal_iff]
    intro x hx
    have hxa : polar q a x = 0 := mem_orthogonal_span_singleton_iff.mp hx
    have h := LinearEquiv.congr_fun h1 x
    rw [eichler_apply_zmod2 ha hau, polar_comm q x a, hxa, LinearEquiv.coe_one, id] at h
    simp only [zero_smul, mul_zero, add_zero, add_eq_left, smul_eq_zero, ha0, or_false] at h
    rw [polarBilin_apply_apply, h]
  · intro hmem
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hmem
    have := CFSG.ClassicalGroups.Orthogonal.eichler_add_smul_self (Q := q) ha 0 c
    rw [zero_add, eichler_zero_right] at this
    exact this

theorem isElementaryAbelian_pointRadical [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) {a : V} (ha0 : a ≠ 0) (ha : q a = 0) :
    IsElementaryAbelian 2 (pointRadical q a) := by
  have hcomm : ∀ s t : pointRadical q a, s * t = t * s := by
    rintro ⟨s, hs⟩ ⟨t, ht⟩
    obtain ⟨u, hau, rfl⟩ := (mem_pointRadical_iff hq ha0 ha).mp hs
    obtain ⟨u', hau', rfl⟩ := (mem_pointRadical_iff hq ha0 ha).mp ht
    refine Subtype.ext ?_
    change eichler q a u * eichler q a u' = eichler q a u' * eichler q a u
    rw [eichler_mul hau hau', eichler_mul hau' hau, add_comm]
  have hsq : ∀ t : pointRadical q a, t ^ 2 = 1 := by
    rintro ⟨t, ht⟩
    obtain ⟨u, hau, rfl⟩ := (mem_pointRadical_iff hq ha0 ha).mp ht
    refine Subtype.ext ?_
    change eichler q a u ^ 2 = 1
    rw [pow_two, eichler_mul_self hau]
  exact { is_comm := ⟨hcomm⟩
          exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hsq }

namespace OrthoF2

theorem mem_orthogonal_span_singleton_self (a : V) :
    a ∈ LinearMap.BilinForm.orthogonal q.polarBilin ((ZMod 2) ∙ a) :=
  mem_orthogonal_span_singleton_iff.mpr (polar_self_eq_zero q a)

end OrthoF2

theorem pointRadical_mulEquiv [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    {a : V} (ha0 : a ≠ 0) (ha : q a = 0) :
    ∃ e : Multiplicative (LinearMap.BilinForm.orthogonal q.polarBilin ((ZMod 2) ∙ a) ⧸
        ((ZMod 2) ∙ a).comap (LinearMap.BilinForm.orthogonal q.polarBilin ((ZMod 2) ∙ a)).subtype)
        ≃* pointRadical q a,
      ∀ u, (e (Multiplicative.ofAdd (Submodule.Quotient.mk u)) : V ≃ₗ[ZMod 2] V) =
        eichler q a u := by
  set P := LinearMap.BilinForm.orthogonal q.polarBilin ((ZMod 2) ∙ a) with hP
  set S := ((ZMod 2) ∙ a).comap P.subtype with hS
  have hmem : ∀ u : P, eichler q a u ∈ pointRadical q a := fun u =>
    eichler_mem_pointRadical ha (mem_orthogonal_span_singleton_iff.mp u.2)
  let φ : P →+ Additive (pointRadical q a) :=
    { toFun := fun u => Additive.ofMul ⟨eichler q a u, hmem u⟩
      map_zero' := by
        change Additive.ofMul _ = Additive.ofMul 1
        congr 1
        exact Subtype.ext (eichler_zero_right q a)
      map_add' := fun u u' => by
        change Additive.ofMul _ = Additive.ofMul (_ * _)
        congr 1
        exact Subtype.ext (eichler_mul (mem_orthogonal_span_singleton_iff.mp u.2)
          (mem_orthogonal_span_singleton_iff.mp u'.2)).symm }
  have hφ : ∀ u, ((Additive.toMul (φ u) : pointRadical q a) : V ≃ₗ[ZMod 2] V) = eichler q a u :=
    fun u => rfl
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨u, hau, hu⟩ := (mem_pointRadical_iff hq ha0 ha).mp (Additive.toMul y).2
    refine ⟨⟨u, mem_orthogonal_span_singleton_iff.mpr hau⟩, ?_⟩
    apply Additive.toMul.injective
    exact Subtype.ext (by rw [hφ]; exact hu.symm)
  have hker : φ.ker = S.toAddSubgroup := by
    ext u
    rw [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, hS, Submodule.mem_comap,
      Submodule.subtype_apply,
      ← eichler_eq_one_iff hq ha0 ha (mem_orthogonal_span_singleton_iff.mp u.2)]
    constructor
    · intro h
      have h' := congrArg (fun y => ((Additive.toMul y : pointRadical q a) : V ≃ₗ[ZMod 2] V)) h
      simpa [hφ] using h'
    · intro h
      apply Additive.toMul.injective
      exact Subtype.ext (by rw [hφ, h]; rfl)
  let e₁ : P ⧸ φ.ker ≃+ Additive (pointRadical q a) :=
    QuotientAddGroup.quotientKerEquivOfSurjective φ hsurj
  let e₂ : P ⧸ φ.ker ≃+ P ⧸ S.toAddSubgroup := QuotientAddGroup.quotientAddEquivOfEq hker
  let e₃ : (P ⧸ S) ≃+ Additive (pointRadical q a) := e₂.symm.trans e₁
  exact ⟨AddEquiv.toMultiplicativeLeft e₃, fun u => rfl⟩

theorem card_pointRadical [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    {a : V} (ha0 : a ≠ 0) (ha : q a = 0) :
    Nat.card (pointRadical q a) = 2 ^ (finrank (ZMod 2) V - 2) := by
  obtain ⟨e, -⟩ := pointRadical_mulEquiv hq ha0 ha
  set P := LinearMap.BilinForm.orthogonal q.polarBilin ((ZMod 2) ∙ a) with hP
  set S := ((ZMod 2) ∙ a).comap P.subtype with hS
  rw [← Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd,
    Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  congr 1
  have h1 := Submodule.finrank_quotient_add_finrank S
  have h2 : finrank (ZMod 2) P = finrank (ZMod 2) V - 1 := by
    rw [hP, LinearMap.BilinForm.finrank_orthogonal hq, finrank_span_singleton ha0]
  have h3 : finrank (ZMod 2) S = 1 := by
    rw [← Submodule.finrank_map_subtype_eq, hS, Submodule.map_comap_subtype,
      inf_eq_right.mpr ((Submodule.span_singleton_le_iff_mem a P).mpr
        (mem_orthogonal_span_singleton_self a)), finrank_span_singleton ha0]
  omega

end CFSG.LargeExtraspecial
