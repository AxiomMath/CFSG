module

public import CFSG.Blueprint.FischerDefs

public noncomputable section

namespace CFSG.Fischer

open Blueprint.Fischer

variable {X Y : Type} [Group X] [Group Y] {E : Set X}

section Basic

theorem Pair.finite (hP : Pair X E) : Finite X := hP.1

theorem Pair.closure_eq (hP : Pair X E) : Subgroup.closure E = ⊤ := hP.2.2.2.2

theorem Pair.isConj (hP : Pair X E) {e f : X} (he : e ∈ E) (hf : f ∈ E) : IsConj e f := by
  obtain ⟨e₀, rfl⟩ := hP.2.1
  exact he.symm.trans hf

theorem Pair.mem_of_isConj (hP : Pair X E) {e f : X} (he : e ∈ E) (h : IsConj e f) : f ∈ E := by
  obtain ⟨e₀, rfl⟩ := hP.2.1
  exact IsConj.trans he h

theorem Pair.conj_mem (hP : Pair X E) {e : X} (he : e ∈ E) (g : X) : g * e * g⁻¹ ∈ E :=
  Pair.mem_of_isConj hP he (isConj_iff.2 ⟨g, rfl⟩)

theorem Pair.nonempty (hP : Pair X E) : E.Nonempty := by
  obtain ⟨e₀, rfl⟩ := hP.2.1
  exact ⟨e₀, IsConj.refl e₀⟩

theorem Pair.orderOf_eq_two (hP : Pair X E) {e : X} (he : e ∈ E) : orderOf e = 2 :=
  hP.2.2.1 e he

theorem Pair.mul_self (hP : Pair X E) {e : X} (he : e ∈ E) : e * e = 1 := by
  rw [← sq, ← Pair.orderOf_eq_two hP he, pow_orderOf_eq_one]

theorem Pair.inv_eq (hP : Pair X E) {e : X} (he : e ∈ E) : e⁻¹ = e :=
  inv_eq_of_mul_eq_one_right (Pair.mul_self hP he)

theorem Pair.ne_one (hP : Pair X E) {e : X} (he : e ∈ E) : e ≠ 1 := by
  intro h
  have := Pair.orderOf_eq_two hP he
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem Pair.orderOf_mul_mem (hP : Pair X E) {e f : X} (he : e ∈ E) (hf : f ∈ E) :
    orderOf (e * f) ∈ ({1, 2, 3} : Set ℕ) :=
  hP.2.2.2.1 e he f hf

theorem Pair.mul_mul_mem (hP : Pair X E) {e f : X} (he : e ∈ E) (hf : f ∈ E) :
    e * f * e ∈ E := by
  have := Pair.conj_mem hP hf e
  rwa [Pair.inv_eq hP he] at this

theorem Pair.orderOf_mul_eq_three (hP : Pair X E) {e f : X} (he : e ∈ E) (hf : f ∈ E)
    (hef : e * f ≠ f * e) : orderOf (e * f) = 3 := by
  rcases Pair.orderOf_mul_mem hP he hf with h | h | h
  · rw [orderOf_eq_one_iff] at h
    have hfe : f = e := by rw [← Pair.inv_eq hP he]; exact eq_inv_of_mul_eq_one_right h
    exact absurd (by rw [hfe]) hef
  · exfalso
    apply hef
    have h2 : (e * f) * (e * f) = 1 := by rw [← sq, ← h, pow_orderOf_eq_one]
    rw [eq_inv_of_mul_eq_one_left h2, mul_inv_rev, Pair.inv_eq hP he, Pair.inv_eq hP hf]
  · exact h

theorem Pair.mul_mul_eq (hP : Pair X E) {e f : X} (he : e ∈ E) (hf : f ∈ E)
    (hef : e * f ≠ f * e) : e * f * e = f * e * f := by
  have h3 : (e * f) ^ 3 = 1 := by
    rw [← Pair.orderOf_mul_eq_three hP he hf hef, pow_orderOf_eq_one]
  have h : e * f * e * (f * e * f) = 1 := by
    rw [← h3]; simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [eq_inv_of_mul_eq_one_left h, mul_inv_rev, mul_inv_rev, Pair.inv_eq hP he,
    Pair.inv_eq hP hf, mul_assoc]

end Basic

section Action

theorem Pair.mem_center_iff (hP : Pair X E) {g : X} :
    g ∈ Subgroup.center X ↔ ∀ e ∈ E, e * g = g * e := by
  refine ⟨fun h e _ => Subgroup.mem_center_iff.1 h e, fun h => ?_⟩
  have hg : g ∈ Subgroup.centralizer (Subgroup.closure E : Set X) := by
    rw [Subgroup.centralizer_closure]
    exact Subgroup.mem_centralizer_iff.2 h
  rw [Pair.closure_eq hP] at hg
  exact Subgroup.mem_center_iff.2 fun y => Subgroup.mem_centralizer_iff.1 hg y trivial

theorem Pair.eq_one_of_forall_conj_eq (hP : Pair X E) (hZ : Subgroup.center X = ⊥) {g : X}
    (hg : ∀ e ∈ E, g * e * g⁻¹ = e) : g = 1 := by
  have h : g ∈ Subgroup.center X := (Pair.mem_center_iff hP).2 fun e he => by
    conv_lhs => rw [← hg e he]
    group
  rwa [hZ, Subgroup.mem_bot] at h

theorem Pair.eq_of_forall_conj_eq (hP : Pair X E) (hZ : Subgroup.center X = ⊥) {g h : X}
    (hgh : ∀ e ∈ E, g * e * g⁻¹ = h * e * h⁻¹) : g = h := by
  have : h⁻¹ * g = 1 := Pair.eq_one_of_forall_conj_eq hP hZ fun e he => by
    calc h⁻¹ * g * e * (h⁻¹ * g)⁻¹ = h⁻¹ * (g * e * g⁻¹) * h := by group
      _ = e := by rw [hgh e he]; group
  rw [← mul_left_cancel_iff (a := h⁻¹), this, inv_mul_cancel]

@[expose] def Pair.conjPerm (hP : Pair X E) : X →* Equiv.Perm E where
  toFun g :=
    { toFun := fun x => ⟨g * x * g⁻¹, Pair.conj_mem hP x.2 g⟩
      invFun := fun x => ⟨g⁻¹ * x * g, by simpa using Pair.conj_mem hP x.2 g⁻¹⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc]) }
  map_one' := Equiv.ext fun x => Subtype.ext (by simp)
  map_mul' g h := Equiv.ext fun x => Subtype.ext (by simp [mul_assoc])

@[simp]
theorem Pair.conjPerm_apply (hP : Pair X E) (g : X) (x : E) :
    (Pair.conjPerm hP g x : X) = g * x * g⁻¹ :=
  rfl

theorem Pair.conjPerm_injective (hP : Pair X E) (hZ : Subgroup.center X = ⊥) :
    Function.Injective (Pair.conjPerm hP) := fun g h hgh =>
  Pair.eq_of_forall_conj_eq hP hZ fun e he => by
    simpa using congrArg Subtype.val (Equiv.ext_iff.1 hgh ⟨e, he⟩)

end Action

section Star

theorem mem_localGroup {e f : X} (hf : f ∈ LocalClass E e) : f ∈ LocalGroup E e :=
  Subgroup.subset_closure hf

theorem commute_of_mem_localGroup {e x y : X} (hx : ∀ g ∈ LocalClass E e, g * x = x * g)
    (hy : y ∈ LocalGroup E e) : y * x = x * y := by
  have hx' : x ∈ Subgroup.centralizer (Subgroup.closure (LocalClass E e) : Set X) := by
    rw [Subgroup.centralizer_closure]
    exact Subgroup.mem_centralizer_iff.2 hx
  exact Subgroup.mem_centralizer_iff.1 hx' y hy

@[expose] def starImage (E : Set X) (e : X) (f : LocalClass E e) : LocalQuotient E e :=
  QuotientGroup.mk (⟨f, mem_localGroup f.2⟩ : LocalGroup E e)

theorem starImage_conj {e : X} (f g : LocalClass E e) (h : (f : X) * g * f ∈ LocalClass E e) :
    starImage E e ⟨_, h⟩ = starImage E e f * starImage E e g * starImage E e f := rfl

theorem range_starImage (e : X) : Set.range (starImage E e) = LocalImages E e := by
  ext q
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨⟨f, mem_localGroup f.2⟩, f.2, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨⟨f, hf⟩, rfl⟩

theorem starImage_eq_one_iff {e : X} (f : LocalClass E e) :
    starImage E e f = 1 ↔ ∀ g ∈ LocalClass E e, g * f = f * g := by
  rw [starImage, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
  constructor
  · intro h g hg
    simpa using congrArg Subtype.val (h ⟨g, mem_localGroup hg⟩)
  · intro h y
    exact Subtype.ext (commute_of_mem_localGroup h y.2)

theorem starImage_eq_starImage_iff {e : X} (f g : LocalClass E e) :
    starImage E e f = starImage E e g ↔
      ∀ y ∈ LocalGroup E e, y * ((f : X)⁻¹ * g) = ((f : X)⁻¹ * g) * y := by
  rw [starImage, starImage, QuotientGroup.eq, Subgroup.mem_center_iff]
  constructor
  · intro h y hy
    simpa using congrArg Subtype.val (h ⟨y, hy⟩)
  · intro h y
    exact Subtype.ext (by simpa using h y y.2)

theorem commute_of_involutions {f g : X} (hf : f * f = 1) (hg : g * g = 1)
    (h3 : (g * f) ^ 3 = 1) (hc : f * ((f * g)⁻¹ * (g * f)) = (f * g)⁻¹ * (g * f) * f) :
    f * g = g * f := by
  have hfi : f⁻¹ = f := inv_eq_of_mul_eq_one_right hf
  have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  have hsq : g * f * (g * f) = f * g := by
    have h : g * f * (g * f) * (g * f) = 1 := by
      rw [← h3]; simp only [pow_succ, pow_zero, one_mul]
    rw [eq_inv_of_mul_eq_one_left h, mul_inv_rev, hfi, hgi]
  rw [mul_inv_rev, hfi, hgi, hsq] at hc
  have hg' : g = f * g * f := by rw [← hc, ← mul_assoc, hf, one_mul]
  calc f * g = f * (f * g * f) := by rw [← hg']
    _ = g * f := by simp only [← mul_assoc, hf, one_mul]

theorem Pair.starImage_commute_iff (hP : Pair X E) {e : X} (f g : LocalClass E e) :
    Commute (starImage E e f) (starImage E e g) ↔ Commute (f : X) g := by
  constructor
  · intro h
    by_contra hfg
    have hfE : (f : X) ∈ E := f.2.1
    have hgE : (g : X) ∈ E := g.2.1
    have hgf : (g : X) * f ≠ f * g := fun h' => hfg h'.symm
    have h3 : ((g : X) * f) ^ 3 = 1 := by
      rw [← Pair.orderOf_mul_eq_three hP hgE hfE hgf, pow_orderOf_eq_one]
    have hq : starImage E e f * starImage E e g = starImage E e g * starImage E e f := h
    simp only [starImage, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      Subgroup.mem_center_iff] at hq
    have hc := congrArg Subtype.val (hq ⟨f, mem_localGroup f.2⟩)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hc
    exact hfg (commute_of_involutions (Pair.mul_self hP hfE) (Pair.mul_self hP hgE) h3 hc)
  · intro h
    have h' : Commute (⟨f, mem_localGroup f.2⟩ : LocalGroup E e) ⟨g, mem_localGroup g.2⟩ :=
      Subtype.ext h
    exact h'.map (QuotientGroup.mk' _)

theorem Pair.starImage_injective_iff (hP : Pair X E) {e : X} :
    Function.Injective (starImage E e) ↔
      {f | f ∈ LocalClass E e ∧ ∀ g ∈ LocalClass E e, g * f = f * g}.Subsingleton := by
  constructor
  · rintro hinj f₁ ⟨hf₁, h₁⟩ f₂ ⟨hf₂, h₂⟩
    have h := hinj (a₁ := ⟨f₁, hf₁⟩) (a₂ := ⟨f₂, hf₂⟩)
      (by rw [(starImage_eq_one_iff _).2 h₁, (starImage_eq_one_iff _).2 h₂])
    exact congrArg Subtype.val h
  · intro hsub f₁ f₂ h12
    by_contra hne
    have hne' : (f₁ : X) ≠ f₂ := fun h => hne (Subtype.ext h)
    have hE1 : (f₁ : X) ∈ E := f₁.2.1
    have hE2 : (f₂ : X) ∈ E := f₂.2.1
    rw [starImage_eq_starImage_iff] at h12
    have hi1 := Pair.inv_eq hP hE1
    rw [hi1] at h12
    have hz2 : (f₁ : X) * (f₁ * f₂) = f₁ * f₂ * f₁ := h12 f₁ (mem_localGroup f₁.2)
    have hc12 : (f₁ : X) * f₂ = f₂ * f₁ := by
      have h := hz2
      rw [← mul_assoc, Pair.mul_self hP hE1, one_mul] at h
      calc (f₁ : X) * f₂ = f₁ * (f₁ * f₂ * f₁) := by rw [← h]
        _ = f₂ * f₁ := by simp only [← mul_assoc, Pair.mul_self hP hE1, one_mul]
    have hzo : orderOf ((f₁ : X) * f₂) = 2 := by
      apply orderOf_eq_prime
      · calc ((f₁ : X) * f₂) ^ 2 = f₁ * (f₂ * f₁) * f₂ := by simp only [sq, mul_assoc]
          _ = (f₁ * f₁) * (f₂ * f₂) := by rw [← hc12]; group
          _ = 1 := by rw [Pair.mul_self hP hE1, Pair.mul_self hP hE2, one_mul]
      · intro h
        apply hne'
        rw [← hi1]
        exact (eq_inv_of_mul_eq_one_right h).symm
    obtain ⟨g, hg, hgf⟩ : ∃ g ∈ LocalClass E e, g * f₁ ≠ f₁ * g := by
      by_contra! hall
      apply hne'
      refine hsub ⟨f₁.2, hall⟩ ⟨f₂.2, fun g hg => ?_⟩
      have hzg : g * (f₁ * f₂) = f₁ * f₂ * g := h12 g (mem_localGroup hg)
      calc g * (f₂ : X) = g * f₁ * (f₁ * f₂) := by
            rw [mul_assoc g, ← mul_assoc (f₁ : X), Pair.mul_self hP hE1, one_mul]
        _ = f₁ * (g * (f₁ * f₂)) := by rw [hall g hg, mul_assoc]
        _ = f₂ * g := by
            rw [hzg, ← mul_assoc, ← mul_assoc, Pair.mul_self hP hE1, one_mul]
    have h3 : orderOf (g * f₁) = 3 := Pair.orderOf_mul_eq_three hP hg.1 hE1 hgf
    have hcom : Commute (g * f₁) ((f₁ : X) * f₂) :=
      h12 (g * f₁) (mul_mem (mem_localGroup hg) (mem_localGroup f₁.2))
    have h6 := hcom.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [h3, hzo]; norm_num)
    rw [h3, hzo, show g * (f₁ : X) * (f₁ * f₂) = g * f₂ by
      rw [mul_assoc g, ← mul_assoc (f₁ : X), Pair.mul_self hP hE1, one_mul]] at h6
    have hmem := Pair.orderOf_mul_mem hP hg.1 hE2
    rw [h6] at hmem
    simp at hmem

theorem Pair.starImage_injective (hP : Pair X E) {e : X}
    (h : ∀ f ∈ LocalClass E e, ∃ g ∈ LocalClass E e, g * f ≠ f * g) :
    Function.Injective (starImage E e) := by
  rw [Pair.starImage_injective_iff hP]
  rintro f ⟨hf, hf'⟩
  obtain ⟨g, hg, hgf⟩ := h f hf
  exact absurd (hf' g hg) hgf

theorem Pair.starImage_injective_of_one_notMem (hP : Pair X E) {e : X}
    (h : (1 : LocalQuotient E e) ∉ LocalImages E e) : Function.Injective (starImage E e) := by
  refine Pair.starImage_injective hP fun f hf => ?_
  by_contra! hall
  exact h (range_starImage (E := E) e ▸ ⟨⟨f, hf⟩, (starImage_eq_one_iff _).2 hall⟩)

end Star

section Map

variable {F : Set Y} {e : X} {f : Y}

theorem image_symm_image {A B : Type*} [Mul A] [Mul B] (φ : A ≃* B) (S : Set A) :
    φ.symm '' (φ '' S) = S :=
  φ.toEquiv.symm_image_image S

theorem image_setOf_isConj (φ : X ≃* Y) (x₀ : X) :
    φ '' {x | IsConj x₀ x} = {y | IsConj (φ x₀) y} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact MonoidHom.map_isConj φ.toMonoidHom hx
  · intro hy
    refine ⟨φ.symm y, ?_, φ.apply_symm_apply y⟩
    simpa using MonoidHom.map_isConj φ.symm.toMonoidHom hy

theorem map_closure_image (φ : X ≃* Y) (S : Set X) :
    (Subgroup.closure S).map (φ : X →* Y) = Subgroup.closure (φ '' S) :=
  MonoidHom.map_closure (φ : X →* Y) S

theorem pair_map (hP : Pair X E) (φ : X ≃* Y) : Pair Y (φ '' E) := by
  obtain ⟨hfin, ⟨x₀, rfl⟩, h2, h3, hgen⟩ := hP
  refine ⟨Finite.of_equiv X φ.toEquiv, ⟨φ x₀, image_setOf_isConj φ x₀⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.orderOf_eq]
    exact h2 x hx
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, MulEquiv.orderOf_eq]
    exact h3 x hx y hy
  · rw [← map_closure_image, hgen, Subgroup.map_equiv_top]

theorem pair_congr (φ : X ≃* Y) (hE : φ '' E = F) : Pair X E ↔ Pair Y F := by
  subst hE
  refine ⟨fun h => pair_map h φ, fun h => ?_⟩
  simpa only [image_symm_image] using pair_map h φ.symm

theorem localClass_map (φ : X ≃* Y) (E : Set X) (e : X) :
    LocalClass (φ '' E) (φ e) = φ '' LocalClass E e := by
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hne, hc⟩
    refine ⟨x, ⟨hx, fun h => hne (by rw [h]), φ.injective ?_⟩, rfl⟩
    simpa only [map_mul] using hc
  · rintro ⟨x, ⟨hx, hne, hc⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, fun h => hne (φ.injective h), by rw [← map_mul, ← map_mul, hc]⟩

theorem localClass_congr (φ : X ≃* Y) (hE : φ '' E = F) (he : φ e = f) :
    LocalClass F f = φ '' LocalClass E e := by
  subst hE he
  exact localClass_map φ E e

theorem localGroup_congr (φ : X ≃* Y) (hE : φ '' E = F) (he : φ e = f) :
    (LocalGroup E e).map (φ : X →* Y) = LocalGroup F f := by
  rw [LocalGroup, LocalGroup, map_closure_image, localClass_congr φ hE he]

theorem localGroup_map (φ : X ≃* Y) (E : Set X) (e : X) :
    LocalGroup (φ '' E) (φ e) = (LocalGroup E e).map (φ : X →* Y) :=
  (localGroup_congr φ rfl rfl).symm

@[expose] def localGroupCongr (φ : X ≃* Y) (hE : φ '' E = F) (he : φ e = f) :
    LocalGroup E e ≃* LocalGroup F f :=
  (φ.subgroupMap (LocalGroup E e)).trans (MulEquiv.subgroupCongr (localGroup_congr φ hE he))

@[simp]
theorem localGroupCongr_apply (φ : X ≃* Y) (hE : φ '' E = F) (he : φ e = f)
    (x : LocalGroup E e) : (localGroupCongr φ hE he x : Y) = φ x :=
  rfl

def quotientCenterCongr {A B : Type*} [Group A] [Group B] (ψ : A ≃* B) :
    A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B :=
  QuotientGroup.congr _ _ ψ (Subgroup.map_center_eq ψ)

@[simp]
theorem quotientCenterCongr_mk {A B : Type*} [Group A] [Group B] (ψ : A ≃* B) (a : A) :
    quotientCenterCongr ψ (QuotientGroup.mk a) = QuotientGroup.mk (ψ a) :=
  QuotientGroup.congr_mk _ _ _ _ a

def localQuotientCongr (φ : X ≃* Y) (hE : φ '' E = F) (he : φ e = f) :
    LocalQuotient E e ≃* LocalQuotient F f :=
  quotientCenterCongr (localGroupCongr φ hE he)

theorem localQuotientCongr_mk (φ : X ≃* Y) (hE : φ '' E = F) (he : φ e = f)
    (x : LocalGroup E e) :
    localQuotientCongr φ hE he (QuotientGroup.mk x) =
      QuotientGroup.mk (localGroupCongr φ hE he x) :=
  quotientCenterCongr_mk _ x

theorem localQuotientCongr_image (φ : X ≃* Y) (hE : φ '' E = F) (he : φ e = f) :
    localQuotientCongr φ hE he '' LocalImages E e = LocalImages F f := by
  ext q
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨localGroupCongr φ hE he x, ?_, (localQuotientCongr_mk φ hE he x).symm⟩
    rw [localGroupCongr_apply, localClass_congr φ hE he]
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    rw [localClass_congr φ hE he] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    have hxL : x ∈ LocalGroup E e := mem_localGroup hx
    refine ⟨QuotientGroup.mk ⟨x, hxL⟩, ⟨⟨x, hxL⟩, hx, rfl⟩, ?_⟩
    rw [localQuotientCongr_mk]
    congr 1
    exact Subtype.ext (by rw [localGroupCongr_apply]; exact hxy)

def localQuotientEquiv (φ : X ≃* Y) (E : Set X) (e : X) :
    LocalQuotient E e ≃* LocalQuotient (φ '' E) (φ e) :=
  localQuotientCongr φ rfl rfl

theorem localQuotientEquiv_image (φ : X ≃* Y) (E : Set X) (e : X) :
    localQuotientEquiv φ E e '' LocalImages E e = LocalImages (φ '' E) (φ e) :=
  localQuotientCongr_image φ rfl rfl

end Map

section Types

variable {F : Set Y}

theorem exists_psu_iso_congr {A B : Type*} [Group A] [Group B] (ψ : A ≃* B) {S : Set A}
    {T : Set B} (hST : ψ '' S = T) {H : Matrix (Fin 6) (Fin 6) K} :
    (∃ iso : A ≃* PSU H, iso '' S = Transvections H) ↔
      ∃ iso : B ≃* PSU H, iso '' T = Transvections H := by
  subst hST
  constructor
  · rintro ⟨iso, h⟩
    refine ⟨ψ.symm.trans iso, ?_⟩
    rw [MulEquiv.coe_trans, Set.image_comp, image_symm_image, h]
  · rintro ⟨iso, h⟩
    refine ⟨ψ.trans iso, ?_⟩
    rw [MulEquiv.coe_trans, Set.image_comp, h]

theorem F22_congr (φ : X ≃* Y) (hE : φ '' E = F) : F22 X E ↔ F22 Y F := by
  subst hE
  constructor
  · rintro ⟨hP, e, he, H, hH, hiso⟩
    exact ⟨pair_map hP φ, φ e, ⟨e, he, rfl⟩, H, hH,
      (exists_psu_iso_congr _ (localQuotientEquiv_image φ E e)).1 hiso⟩
  · rintro ⟨hP, _, ⟨e, he, rfl⟩, H, hH, hiso⟩
    exact ⟨(pair_congr φ rfl).2 hP, e, he, H, hH,
      (exists_psu_iso_congr _ (localQuotientEquiv_image φ E e)).2 hiso⟩

theorem F23_congr (φ : X ≃* Y) (hE : φ '' E = F) : F23 X E ↔ F23 Y F := by
  subst hE
  constructor
  · rintro ⟨hP, e, he, h⟩
    exact ⟨pair_map hP φ, φ e, ⟨e, he, rfl⟩,
      (F22_congr _ (localQuotientEquiv_image φ E e)).1 h⟩
  · rintro ⟨hP, _, ⟨e, he, rfl⟩, h⟩
    exact ⟨(pair_congr φ rfl).2 hP, e, he, (F22_congr _ (localQuotientEquiv_image φ E e)).2 h⟩

theorem F24_congr (φ : X ≃* Y) (hE : φ '' E = F) : F24 X E ↔ F24 Y F := by
  subst hE
  constructor
  · rintro ⟨hP, e, he, h⟩
    exact ⟨pair_map hP φ, φ e, ⟨e, he, rfl⟩,
      (F23_congr _ (localQuotientEquiv_image φ E e)).1 h⟩
  · rintro ⟨hP, _, ⟨e, he, rfl⟩, h⟩
    exact ⟨(pair_congr φ rfl).2 hP, e, he, (F23_congr _ (localQuotientEquiv_image φ E e)).2 h⟩

theorem hasType_congr (k : Fin 3) (φ : X ≃* Y) (hE : φ '' E = F) :
    HasType k X E ↔ HasType k Y F := by
  obtain ⟨_ | _ | n, hk⟩ := k
  · exact F22_congr φ hE
  · exact F23_congr φ hE
  · exact F24_congr φ hE

theorem F22_map (h : F22 X E) (φ : X ≃* Y) : F22 Y (φ '' E) := (F22_congr φ rfl).1 h

theorem F23_map (h : F23 X E) (φ : X ≃* Y) : F23 Y (φ '' E) := (F23_congr φ rfl).1 h

theorem F24_map (h : F24 X E) (φ : X ≃* Y) : F24 Y (φ '' E) := (F24_congr φ rfl).1 h

theorem hasType_map {k : Fin 3} (h : HasType k X E) (φ : X ≃* Y) : HasType k Y (φ '' E) :=
  (hasType_congr k φ rfl).1 h

end Types

section Forall

theorem Pair.exists_mulEquiv (hP : Pair X E) {e e' : X} (he : e ∈ E) (he' : e' ∈ E) :
    ∃ φ : X ≃* X, φ '' E = E ∧ φ e = e' := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (Pair.isConj hP he he')
  refine ⟨MulAut.conj c, ?_, by rw [MulAut.conj_apply, hc]⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [MulAut.conj_apply]
    exact Pair.conj_mem hP hy c
  · intro hx
    refine ⟨c⁻¹ * x * c, ?_, ?_⟩
    · simpa using Pair.conj_mem hP hx c⁻¹
    · rw [MulAut.conj_apply]
      group

theorem F22_iff_forall : F22 X E ↔ Pair X E ∧ ∀ e ∈ E, ∃ H : Matrix (Fin 6) (Fin 6) K,
    IsNondegenerateHermitian H ∧
      ∃ iso : LocalQuotient E e ≃* PSU H, iso '' LocalImages E e = Transvections H := by
  constructor
  · rintro ⟨hP, e₀, he₀, H, hH, hiso⟩
    refine ⟨hP, fun e he => ?_⟩
    obtain ⟨φ, hφE, hφe⟩ := Pair.exists_mulEquiv hP he₀ he
    exact ⟨H, hH, (exists_psu_iso_congr _ (localQuotientCongr_image φ hφE hφe)).1 hiso⟩
  · rintro ⟨hP, h⟩
    obtain ⟨e₀, he₀⟩ := Pair.nonempty hP
    exact ⟨hP, e₀, he₀, h e₀ he₀⟩

theorem F23_iff_forall :
    F23 X E ↔ Pair X E ∧ ∀ e ∈ E, F22 (LocalQuotient E e) (LocalImages E e) := by
  constructor
  · rintro ⟨hP, e₀, he₀, h⟩
    refine ⟨hP, fun e he => ?_⟩
    obtain ⟨φ, hφE, hφe⟩ := Pair.exists_mulEquiv hP he₀ he
    exact (F22_congr _ (localQuotientCongr_image φ hφE hφe)).1 h
  · rintro ⟨hP, h⟩
    obtain ⟨e₀, he₀⟩ := Pair.nonempty hP
    exact ⟨hP, e₀, he₀, h e₀ he₀⟩

theorem F24_iff_forall :
    F24 X E ↔ Pair X E ∧ ∀ e ∈ E, F23 (LocalQuotient E e) (LocalImages E e) := by
  constructor
  · rintro ⟨hP, e₀, he₀, h⟩
    refine ⟨hP, fun e he => ?_⟩
    obtain ⟨φ, hφE, hφe⟩ := Pair.exists_mulEquiv hP he₀ he
    exact (F23_congr _ (localQuotientCongr_image φ hφE hφe)).1 h
  · rintro ⟨hP, h⟩
    obtain ⟨e₀, he₀⟩ := Pair.nonempty hP
    exact ⟨hP, e₀, he₀, h e₀ he₀⟩

theorem F22_local (h : F22 X E) {e : X} (he : e ∈ E) :
    ∃ H : Matrix (Fin 6) (Fin 6) K, IsNondegenerateHermitian H ∧
      ∃ iso : LocalQuotient E e ≃* PSU H, iso '' LocalImages E e = Transvections H :=
  (F22_iff_forall.1 h).2 e he

theorem F23_local (h : F23 X E) {e : X} (he : e ∈ E) :
    F22 (LocalQuotient E e) (LocalImages E e) :=
  (F23_iff_forall.1 h).2 e he

theorem F24_local (h : F24 X E) {e : X} (he : e ∈ E) :
    F23 (LocalQuotient E e) (LocalImages E e) :=
  (F24_iff_forall.1 h).2 e he

end Forall

section Centralizer

theorem centralizer_image_eq_map (φ : X ≃* Y) (S : Set X) :
    Subgroup.centralizer (φ '' S) = (Subgroup.centralizer S).map (φ : X →* Y) := by
  ext y
  change _ ↔ y ∈ (Subgroup.centralizer S).map φ.toMonoidHom
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h x hx
    apply φ.injective
    simpa using h (φ x) ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    simpa using congrArg φ (h x hx)

theorem centralizer_singleton_eq_map (φ : X ≃* Y) (d : X) :
    Subgroup.centralizer ({φ d} : Set Y) =
      (Subgroup.centralizer ({d} : Set X)).map (φ : X →* Y) := by
  rw [← centralizer_image_eq_map, Set.image_singleton]

@[expose] def centralizerEquiv (φ : X ≃* Y) (d : X) :
    Subgroup.centralizer ({d} : Set X) ≃* Subgroup.centralizer ({φ d} : Set Y) :=
  (φ.subgroupMap _).trans (MulEquiv.subgroupCongr (centralizer_singleton_eq_map φ d).symm)

@[simp]
theorem centralizerEquiv_apply (φ : X ≃* Y) (d : X) (x : Subgroup.centralizer ({d} : Set X)) :
    (centralizerEquiv φ d x : Y) = φ x :=
  rfl

def centralizerQuotientEquiv (φ : X ≃* Y) (d : X) :
    Subgroup.centralizer ({d} : Set X) ⧸ Subgroup.center (Subgroup.centralizer ({d} : Set X)) ≃*
      Subgroup.centralizer ({φ d} : Set Y) ⧸
        Subgroup.center (Subgroup.centralizer ({φ d} : Set Y)) :=
  quotientCenterCongr (centralizerEquiv φ d)

theorem map_commutator_mulEquiv {A B : Type*} [Group A] [Group B] (ψ : A ≃* B) :
    (_root_.commutator A).map (ψ : A →* B) = _root_.commutator B := by
  rw [commutator_def, commutator_def, Subgroup.map_commutator, Subgroup.map_equiv_top]

theorem commutator_eq_top_congr {A B : Type*} [Group A] [Group B] (ψ : A ≃* B) :
    _root_.commutator A = ⊤ ↔ _root_.commutator B = ⊤ := by
  rw [← map_commutator_mulEquiv ψ]
  constructor
  · intro h
    rw [h, Subgroup.map_equiv_top]
  · intro h
    have := congrArg (Subgroup.map (ψ.symm : B →* A)) h
    rwa [Subgroup.map_map, Subgroup.map_equiv_top, show (ψ.symm : B →* A).comp (ψ : A →* B) =
      MonoidHom.id A from MonoidHom.ext fun a => ψ.symm_apply_apply a, Subgroup.map_id] at this

theorem card_center_congr {A B : Type*} [Group A] [Group B] (ψ : A ≃* B) :
    Nat.card (Subgroup.center A) = Nat.card (Subgroup.center B) :=
  Nat.card_congr (Subgroup.centerCongr ψ).toEquiv

theorem map_subtype_center_centralizer (φ : X ≃* Y) (d : X) :
    (Subgroup.center (Subgroup.centralizer ({φ d} : Set Y))).map
        (Subgroup.centralizer ({φ d} : Set Y)).subtype =
      ((Subgroup.center (Subgroup.centralizer ({d} : Set X))).map
        (Subgroup.centralizer ({d} : Set X)).subtype).map (φ : X →* Y) := by
  rw [← Subgroup.map_center_eq (centralizerEquiv φ d), Subgroup.map_map, Subgroup.map_map]
  rfl

theorem map_subtype_center_centralizer_eq_zpowers (φ : X ≃* Y) {d : X}
    (h : (Subgroup.center (Subgroup.centralizer ({d} : Set X))).map
      (Subgroup.centralizer ({d} : Set X)).subtype = Subgroup.zpowers d) :
    (Subgroup.center (Subgroup.centralizer ({φ d} : Set Y))).map
      (Subgroup.centralizer ({φ d} : Set Y)).subtype = Subgroup.zpowers (φ d) := by
  rw [map_subtype_center_centralizer, h, MonoidHom.map_zpowers]
  rfl

theorem centralizer_eq_zpowers_sup_map (φ : X ≃* Y) {d : X} {T : Type*} [Mul T]
    (h : ∃ L : Subgroup X, Nonempty (L ≃* T) ∧
      Subgroup.centralizer ({d} : Set X) = Subgroup.zpowers d ⊔ L ∧
      Subgroup.zpowers d ⊓ L = ⊥ ∧ Subgroup.zpowers d ≤ Subgroup.centralizer (L : Set X)) :
    ∃ L : Subgroup Y, Nonempty (L ≃* T) ∧
      Subgroup.centralizer ({φ d} : Set Y) = Subgroup.zpowers (φ d) ⊔ L ∧
      Subgroup.zpowers (φ d) ⊓ L = ⊥ ∧
        Subgroup.zpowers (φ d) ≤ Subgroup.centralizer (L : Set Y) := by
  obtain ⟨L, ⟨iso⟩, hC, hinf, hle⟩ := h
  have hz : Subgroup.zpowers (φ d) = (Subgroup.zpowers d).map (φ : X →* Y) :=
    (MonoidHom.map_zpowers (φ : X →* Y) d).symm
  refine ⟨L.map (φ : X →* Y), ⟨(φ.subgroupMap L).symm.trans iso⟩, ?_, ?_, ?_⟩
  · rw [centralizer_singleton_eq_map, hC, Subgroup.map_sup, hz]
  · rw [hz, ← Subgroup.map_inf_eq _ _ _ φ.injective, hinf, Subgroup.map_bot]
  · rw [Subgroup.coe_map, MonoidHom.coe_ofClass, centralizer_image_eq_map, hz]
    exact Subgroup.map_mono hle

end Centralizer

section LocalStructure

@[expose] def LocalStructureAt (k : Fin 3) {G : Type} [Group G] (d : G) : Prop :=
  let C := Subgroup.centralizer ({d} : Set G)
  (k.val = 0 → _root_.commutator C = ⊤ ∧
      (Subgroup.center C).map C.subtype = Subgroup.zpowers d ∧ Nat.card (Subgroup.center C) = 2 ∧
      ∃ H : Matrix (Fin 6) (Fin 6) K, IsNondegenerateHermitian H ∧
        Nonempty ((C ⧸ Subgroup.center C) ≃* PSU H)) ∧
    (k.val = 1 → _root_.commutator C = ⊤ ∧
      (Subgroup.center C).map C.subtype = Subgroup.zpowers d ∧ Nat.card (Subgroup.center C) = 2 ∧
      Nonempty ((C ⧸ Subgroup.center C) ≃* Blueprint.NativeSporadic.Fi22)) ∧
    (k.val = 2 → ∃ L : Subgroup G, Nonempty (L ≃* Blueprint.NativeSporadic.Fi23) ∧
      C = Subgroup.zpowers d ⊔ L ∧ Subgroup.zpowers d ⊓ L = ⊥ ∧
      Subgroup.zpowers d ≤ Subgroup.centralizer (L : Set G))

theorem localStructure_iff (k : Fin 3) (D : Set (Carrier k)) :
    LocalStructure k D ↔ ∀ d ∈ D, LocalStructureAt k d :=
  Iff.rfl

theorem LocalStructureAt.map {k : Fin 3} {d : X} (h : LocalStructureAt k d) (φ : X ≃* Y) :
    LocalStructureAt k (φ d) := by
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨fun hk => ?_, fun hk => ?_, fun hk => centralizer_eq_zpowers_sup_map φ (h2 hk)⟩
  · obtain ⟨hc, hz, hcard, H, hH, ⟨iso⟩⟩ := h0 hk
    exact ⟨(commutator_eq_top_congr (centralizerEquiv φ d)).1 hc,
      map_subtype_center_centralizer_eq_zpowers φ hz,
      (card_center_congr (centralizerEquiv φ d)).symm.trans hcard, H, hH,
      ⟨(centralizerQuotientEquiv φ d).symm.trans iso⟩⟩
  · obtain ⟨hc, hz, hcard, ⟨iso⟩⟩ := h1 hk
    exact ⟨(commutator_eq_top_congr (centralizerEquiv φ d)).1 hc,
      map_subtype_center_centralizer_eq_zpowers φ hz,
      (card_center_congr (centralizerEquiv φ d)).symm.trans hcard,
      ⟨(centralizerQuotientEquiv φ d).symm.trans iso⟩⟩

theorem localStructureAt_congr {k : Fin 3} (φ : X ≃* Y) (d : X) :
    LocalStructureAt k (φ d) ↔ LocalStructureAt k d :=
  ⟨fun h => by simpa using h.map φ.symm, fun h => h.map φ⟩

theorem localStructure_of_mulEquiv {k : Fin 3} {D : Set Y} (φ : Y ≃* Carrier k)
    (h : ∀ d ∈ D, LocalStructureAt k d) : LocalStructure k (φ '' D) := by
  rintro _ ⟨d, hd, rfl⟩
  exact (h d hd).map φ

theorem localStructure_map {k : Fin 3} {D : Set (Carrier k)} (h : LocalStructure k D)
    (φ : Carrier k ≃* Carrier k) : LocalStructure k (φ '' D) :=
  localStructure_of_mulEquiv φ h

end LocalStructure

end CFSG.Fischer
