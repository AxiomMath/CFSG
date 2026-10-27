module

public import CFSG.Fischer.Classification.Orthogonal3.Model
public import CFSG.Fischer.Pairs

public section

namespace CFSG.Fischer.Classification

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Blueprint.Fischer CFSG.Fischer F3 Module

variable {m n : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}

theorem localClass_D3 (hf : IsF3Form f) (hm : 4 ≤ m) {v : Fin m → ZMod 3} (hv : f v v = 1) :
    LocalClass (D3 f) (reflBar f v) = {q | ∃ w, f w w = 1 ∧ f w v = 0 ∧ reflBar f w = q} := by
  ext q
  constructor
  · rintro ⟨hq, hne, hc⟩
    obtain ⟨w, hw, rfl⟩ := mem_D3_iff.1 hq
    refine ⟨w, hw, ?_, rfl⟩
    rcases (reflBar_commute_iff hf hm hw hv).1 hc with h | h | h
    · exact h
    · exact absurd (by rw [h]) hne
    · exact absurd (by rw [h, reflBar_neg]) hne
  · rintro ⟨w, hw, hwv, rfl⟩
    refine ⟨reflBar_mem_D3 hw, fun h => ?_, (reflBar_commute_iff hf hm hw hv).2 (Or.inl hwv)⟩
    rcases (reflBar_eq_reflBar_iff hf hm hw hv).1 h with h | h
    · rw [h, hw] at hwv
      exact one_ne_zero hwv
    · rw [h, LinearMap.BilinForm.neg_right, hw] at hwv
      exact one_ne_zero (neg_eq_zero.1 hwv)

theorem reflBar_mem_localClass (hf : IsF3Form f) (hm : 4 ≤ m) {v w : Fin m → ZMod 3}
    (hv : f v v = 1) (hw : f w w = 1) (hwv : f w v = 0) :
    reflBar f w ∈ LocalClass (D3 f) (reflBar f v) := by
  rw [localClass_D3 hf hm hv]
  exact ⟨w, hw, hwv, rfl⟩

theorem exists_not_commute_localClass (hf : IsF3Form f) (hm : 5 ≤ m) {v : Fin m → ZMod 3}
    (hv : f v v = 1) : ∀ q ∈ LocalClass (D3 f) (reflBar f v),
      ∃ q' ∈ LocalClass (D3 f) (reflBar f v), q' * q ≠ q * q' := by
  intro q hq
  rw [localClass_D3 hf (by omega) hv] at hq
  obtain ⟨w, hw, hwv, rfl⟩ := hq
  obtain ⟨z, hz0, hzz, hzw, hzv⟩ := exists_isotropic_perp_two hf hm hw hv hwv
  have hwz : f w z = 0 := by rw [hf.symm]; exact hzw
  have hn : f (w + z) (w + z) = 1 := by rw [norm_add hf, hw, hwz, hzz]; ring
  have hp : f (w + z) w = 1 := by rw [LinearMap.BilinForm.add_left, hw, hzw, add_zero]
  refine ⟨reflBar f (w + z), reflBar_mem_localClass hf (by omega) hv hn
    (by rw [LinearMap.BilinForm.add_left, hwv, hzv, add_zero]), fun h => ?_⟩
  rcases (reflBar_commute_iff hf (by omega) hn hw).1 h with h1 | h1 | h1
  · rw [hp] at h1
    exact one_ne_zero h1
  · exact hz0 (by simpa using h1)
  · have hz : z = w := by linear_combination (norm := module) h1 - three_eq_zero • w
    rw [hz, hw] at hzw
    exact one_ne_zero hzw

namespace F3

variable (f) in
@[expose] def reflSetPerp (v : Fin m → ZMod 3) : Set (GL (Fin m) (ZMod 3)) :=
  {g | ∃ w, f w w = 1 ∧ f w v = 0 ∧ refl f w = g}

variable (f) in
abbrev reflGroupPerp (v : Fin m → ZMod 3) : Subgroup (GL (Fin m) (ZMod 3)) :=
  Subgroup.closure (reflSetPerp f v)

variable (f) in
@[expose] def stabSub (v : Fin m → ZMod 3) : Subgroup (GL (Fin m) (ZMod 3)) where
  carrier := {g | ∀ x, f (act g x) v = f x v}
  mul_mem' {a b} ha hb x := by rw [act_mul, ha, hb]
  one_mem' x := by rw [act_one]
  inv_mem' {a} ha x := by rw [← ha (act a⁻¹ x), act_act_inv]

theorem reflGroupPerp_le_reflGroup (v : Fin m → ZMod 3) : reflGroupPerp f v ≤ reflGroup f :=
  Subgroup.closure_mono fun _ ⟨_, hw, _, hg⟩ => hg ▸ refl_mem_reflSet hw

theorem reflGroupPerp_le_stabSub (v : Fin m → ZMod 3) : reflGroupPerp f v ≤ stabSub f v := by
  rw [reflGroupPerp, Subgroup.closure_le]
  rintro _ ⟨w, hw, hwv, rfl⟩ x
  rw [act_refl hw, LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hwv, mul_zero,
    add_zero]

@[expose] def fixSub (v : Fin m → ZMod 3) : Subgroup (GL (Fin m) (ZMod 3)) where
  carrier := {g | act g v = v}
  mul_mem' {a b} ha hb := by
    change act (a * b) v = v
    rw [act_mul, show act b v = v from hb, show act a v = v from ha]
  one_mem' := act_one v
  inv_mem' {a} ha := by
    change act a⁻¹ v = v
    conv_lhs => rw [← (show act a v = v from ha)]
    exact act_inv_act a v

theorem act_eq_of_mem_reflGroupPerp (hf : IsF3Form f) {v : Fin m → ZMod 3}
    {g : GL (Fin m) (ZMod 3)} (hg : g ∈ reflGroupPerp f v) : act g v = v := by
  have : reflGroupPerp f v ≤ fixSub v := by
    rw [reflGroupPerp, Subgroup.closure_le]
    rintro _ ⟨w, hw, hwv, rfl⟩
    exact act_refl_of_perp hw (by rw [hf.symm]; exact hwv)
  exact this hg

variable (f) in
abbrev perpOne (v : Fin m → ZMod 3) : Submodule (ZMod 3) (Fin m → ZMod 3) :=
  LinearMap.ker (f.flip v)

theorem mem_perpOne {v x : Fin m → ZMod 3} : x ∈ perpOne f v ↔ f x v = 0 :=
  LinearMap.mem_ker

theorem finrank_perpOne {v : Fin m → ZMod 3} (hv : f v v = 1) :
    finrank (ZMod 3) (perpOne f v) = m - 1 := by
  have hr : LinearMap.range (f.flip v) = ⊤ :=
    LinearMap.range_eq_top.2 fun c => ⟨c • v, by
      show f (c • v) v = c
      rw [LinearMap.BilinForm.smul_left, hv, mul_one]⟩
  have h := LinearMap.finrank_range_add_finrank_ker (f.flip v)
  rw [hr, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h
  show finrank (ZMod 3) (LinearMap.ker (f.flip v)) = m - 1
  omega

@[expose] noncomputable def restrPerp {v : Fin m → ZMod 3} (g : stabSub f v) :
    perpOne f v →ₗ[ZMod 3] perpOne f v :=
  (Matrix.toLin' ((g : GL (Fin m) (ZMod 3)) : Matrix (Fin m) (Fin m) (ZMod 3))).restrict
    fun x hx => by
      rw [mem_perpOne, Matrix.toLin'_apply, ← act_def, g.2 x]
      exact mem_perpOne.1 hx

theorem coe_restrPerp {v : Fin m → ZMod 3} (g : stabSub f v) (x : perpOne f v) :
    (restrPerp g x : Fin m → ZMod 3) = act g x :=
  rfl

@[expose] noncomputable def restrHom {v : Fin m → ZMod 3}
    (e : perpOne f v ≃ₗ[ZMod 3] (Fin n → ZMod 3)) :
    stabSub f v →* Matrix (Fin n) (Fin n) (ZMod 3) where
  toFun g := LinearMap.toMatrix' (e.toLinearMap ∘ₗ restrPerp g ∘ₗ e.symm.toLinearMap)
  map_one' := by
    rw [← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun y => ?_
    have : restrPerp (1 : stabSub f v) (e.symm y) = e.symm y :=
      Subtype.ext (by rw [coe_restrPerp]; exact act_one _)
    simp [this]
  map_mul' g h := by
    rw [← LinearMap.toMatrix'_comp]
    congr 1
    refine LinearMap.ext fun y => ?_
    have : restrPerp (g * h) (e.symm y) = restrPerp g (restrPerp h (e.symm y)) :=
      Subtype.ext (by rw [coe_restrPerp, coe_restrPerp, coe_restrPerp]; exact act_mul _ _ _)
    simp [this]

@[expose] noncomputable def restrGL {v : Fin m → ZMod 3}
    (e : perpOne f v ≃ₗ[ZMod 3] (Fin n → ZMod 3)) :
    stabSub f v →* GL (Fin n) (ZMod 3) :=
  (restrHom e).toHomUnits

theorem act_restrGL {v : Fin m → ZMod 3} (e : perpOne f v ≃ₗ[ZMod 3] (Fin n → ZMod 3))
    (g : stabSub f v) (y : Fin n → ZMod 3) :
    act (restrGL e g) y = e (restrPerp g (e.symm y)) := by
  rw [act, restrGL, MonoidHom.coe_toHomUnits]
  exact LinearMap.toMatrix'_mulVec _ _

theorem coe_restrPerp_symm {v : Fin m → ZMod 3} (e : perpOne f v ≃ₗ[ZMod 3] (Fin n → ZMod 3))
    (g : stabSub f v) (y : Fin n → ZMod 3) :
    ((e.symm (act (restrGL e g) y) : perpOne f v) : Fin m → ZMod 3) = act g (e.symm y) := by
  rw [act_restrGL, LinearEquiv.symm_apply_apply, coe_restrPerp]

end F3

variable (f) in
@[expose] noncomputable def perpToR3 (v : Fin m → ZMod 3) : F3.reflGroupPerp f v →* R3 f :=
  (QuotientGroup.mk' _).comp (Subgroup.inclusion (F3.reflGroupPerp_le_reflGroup v))

@[expose] noncomputable def perpToGL {v : Fin m → ZMod 3}
    (e : F3.perpOne f v ≃ₗ[ZMod 3] (Fin n → ZMod 3)) :
    F3.reflGroupPerp f v →* GL (Fin n) (ZMod 3) :=
  (F3.restrGL e).comp (Subgroup.inclusion (F3.reflGroupPerp_le_stabSub v))

theorem refl_mem_reflGroupPerp {v w : Fin m → ZMod 3} (hw : f w w = 1) (hwv : f w v = 0) :
    F3.refl f w ∈ F3.reflGroupPerp f v :=
  Subgroup.subset_closure ⟨w, hw, hwv, rfl⟩

theorem perpToR3_refl {v w : Fin m → ZMod 3} (h : F3.refl f w ∈ F3.reflGroupPerp f v) :
    perpToR3 f v ⟨F3.refl f w, h⟩ = reflBar f w :=
  rfl

theorem perpToR3_injective (hf : IsF3Form f) (hm : 4 ≤ m) {v : Fin m → ZMod 3}
    (hv : f v v = 1) : Function.Injective (perpToR3 f v) := by
  refine (injective_iff_map_eq_one _).2 fun g hg => ?_
  rw [perpToR3, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hg
  have hfix := F3.act_eq_of_mem_reflGroupPerp hf g.2
  rcases F3.coe_eq_of_mem_center hf hm hg with h | h <;>
    rw [Subgroup.coe_inclusion] at h
  · exact Subtype.ext h
  · exfalso
    rw [h, act_neg_one] at hfix
    exact ne_zero_of_norm_one hv (eq_zero_of_eq_neg hfix.symm)

theorem image_perpToR3 (hf : IsF3Form f) (hm : 4 ≤ m) {v : Fin m → ZMod 3} (hv : f v v = 1) :
    perpToR3 f v '' (Subtype.val ⁻¹' F3.reflSetPerp f v) = LocalClass (D3 f) (reflBar f v) := by
  rw [localClass_D3 hf hm hv]
  ext q
  constructor
  · rintro ⟨g, ⟨w, hw, hwv, hg⟩, rfl⟩
    refine ⟨w, hw, hwv, ?_⟩
    obtain ⟨g, hg'⟩ := g
    subst hg
    rfl
  · rintro ⟨w, hw, hwv, rfl⟩
    exact ⟨⟨F3.refl f w, refl_mem_reflGroupPerp hw hwv⟩, ⟨w, hw, hwv, rfl⟩, rfl⟩

theorem range_perpToR3 (hf : IsF3Form f) (hm : 4 ≤ m) {v : Fin m → ZMod 3} (hv : f v v = 1) :
    (perpToR3 f v).range = LocalGroup (D3 f) (reflBar f v) := by
  rw [MonoidHom.range_eq_map, ← Subgroup.closure_closure_coe_preimage (k := F3.reflSetPerp f v),
    MonoidHom.map_closure, image_perpToR3 hf hm hv]
  rfl

section Restrict

variable {v : Fin m → ZMod 3} (e : F3.perpOne f v ≃ₗ[ZMod 3] (Fin n → ZMod 3))
  {f' : LinearMap.BilinForm (ZMod 3) (Fin n → ZMod 3)}

theorem coe_perpToGL_symm (g : F3.reflGroupPerp f v) (y : Fin n → ZMod 3) :
    ((e.symm (act (perpToGL e g) y) : F3.perpOne f v) : Fin m → ZMod 3) =
      act (g : GL (Fin m) (ZMod 3)) (e.symm y) :=
  F3.coe_restrPerp_symm e _ y

theorem act_perpToGL (g : F3.reflGroupPerp f v) (x : F3.perpOne f v) :
    act (perpToGL e g) (e x) = e ⟨act (g : GL (Fin m) (ZMod 3)) x, F3.mem_perpOne.2 (by
      rw [F3.reflGroupPerp_le_stabSub v g.2 x]; exact F3.mem_perpOne.1 x.2)⟩ := by
  rw [← e.symm_apply_eq]
  apply Subtype.ext
  rw [coe_perpToGL_symm, e.symm_apply_apply]

theorem perpToGL_refl (hf' : ∀ a b : F3.perpOne f v, f' (e a) (e b) = f a b) {w : Fin m → ZMod 3}
    (hw : f w w = 1) (hwv : f w v = 0) :
    perpToGL e ⟨F3.refl f w, refl_mem_reflGroupPerp hw hwv⟩ =
      F3.refl f' (e ⟨w, F3.mem_perpOne.2 hwv⟩) := by
  have hw' : f' (e ⟨w, F3.mem_perpOne.2 hwv⟩) (e ⟨w, F3.mem_perpOne.2 hwv⟩) = 1 := by
    rw [hf']; exact hw
  refine F3.gl_ext fun y => ?_
  apply e.symm.injective
  apply Subtype.ext
  rw [coe_perpToGL_symm, act_refl hw, act_refl hw', LinearEquiv.map_add, LinearEquiv.map_smul,
    e.symm_apply_apply, Submodule.coe_add, Submodule.coe_smul]
  have := hf' (e.symm y) ⟨w, F3.mem_perpOne.2 hwv⟩
  rw [e.apply_symm_apply] at this
  rw [this]

theorem perpToGL_injective (hf : IsF3Form f) (hv : f v v = 1) :
    Function.Injective (perpToGL e) := by
  refine (injective_iff_map_eq_one _).2 fun g hg => ?_
  have hW : ∀ x : F3.perpOne f v, act (g : GL (Fin m) (ZMod 3)) x = x := fun x => by
    have := coe_perpToGL_symm e g (e x)
    rw [hg, act_one, e.symm_apply_apply] at this
    exact this.symm
  have hfix := F3.act_eq_of_mem_reflGroupPerp hf g.2
  apply Subtype.ext
  refine F3.gl_ext fun x => ?_
  have hx : x - f x v • v ∈ F3.perpOne f v := F3.mem_perpOne.2 (by
    rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hv, mul_one, sub_self])
  have := hW ⟨_, hx⟩
  simp only at this
  rw [act_sub, act_smul, hfix] at this
  rw [Subgroup.coe_one, act_one]
  linear_combination (norm := module) this

theorem image_perpToGL (hf' : ∀ a b : F3.perpOne f v, f' (e a) (e b) = f a b) :
    perpToGL e '' (Subtype.val ⁻¹' F3.reflSetPerp f v) = F3.reflSet f' := by
  ext h
  constructor
  · rintro ⟨g, ⟨w, hw, hwv, hg⟩, rfl⟩
    obtain ⟨g, hg'⟩ := g
    subst hg
    rw [perpToGL_refl e hf' hw hwv]
    exact refl_mem_reflSet (by rw [hf']; exact hw)
  · intro hh
    obtain ⟨w', hw', rfl⟩ := mem_reflSet_iff.1 hh
    set x := e.symm w'
    have hx : f (x : Fin m → ZMod 3) x = 1 := by
      rw [← hf', LinearEquiv.apply_symm_apply]; exact hw'
    have hxv : f (x : Fin m → ZMod 3) v = 0 := F3.mem_perpOne.1 x.2
    refine ⟨⟨F3.refl f x, refl_mem_reflGroupPerp hx hxv⟩, ⟨x, hx, hxv, rfl⟩, ?_⟩
    rw [perpToGL_refl e hf' hx hxv]
    simp [x]

theorem range_perpToGL (hf' : ∀ a b : F3.perpOne f v, f' (e a) (e b) = f a b) :
    (perpToGL e).range = F3.reflGroup f' := by
  rw [MonoidHom.range_eq_map, ← Subgroup.closure_closure_coe_preimage (k := F3.reflSetPerp f v),
    MonoidHom.map_closure, image_perpToGL e hf']

end Restrict

section Equiv

variable (hf : IsF3Form f) (hm : 4 ≤ m) {v : Fin m → ZMod 3} (hv : f v v = 1)
  (e : F3.perpOne f v ≃ₗ[ZMod 3] (Fin n → ZMod 3))
  {f' : LinearMap.BilinForm (ZMod 3) (Fin n → ZMod 3)}
  (hf' : ∀ a b : F3.perpOne f v, f' (e a) (e b) = f a b)

@[expose] noncomputable def localGroupEquivR3 :
    LocalGroup (D3 f) (reflBar f v) ≃* F3.reflGroup f' :=
  (MulEquiv.subgroupCongr (range_perpToR3 hf hm hv).symm).trans
    ((MonoidHom.ofInjective (perpToR3_injective hf hm hv)).symm.trans
      ((MonoidHom.ofInjective (perpToGL_injective e hf hv)).trans
        (MulEquiv.subgroupCongr (range_perpToGL e hf'))))

include hf hm hv in
theorem mem_localGroup_perpToR3 (g : F3.reflGroupPerp f v) :
    perpToR3 f v g ∈ LocalGroup (D3 f) (reflBar f v) := by
  rw [← range_perpToR3 hf hm hv]
  exact ⟨g, rfl⟩

theorem localGroupEquivR3_apply (g : F3.reflGroupPerp f v) :
    (localGroupEquivR3 hf hm hv e hf' ⟨perpToR3 f v g, mem_localGroup_perpToR3 hf hm hv g⟩ :
      GL (Fin n) (ZMod 3)) = perpToGL e g := by
  have h1 : (MonoidHom.ofInjective (perpToR3_injective hf hm hv)).symm
      ⟨perpToR3 f v g, ⟨g, rfl⟩⟩ = g := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext (MonoidHom.ofInjective_apply _).symm
  simp only [localGroupEquivR3, MulEquiv.trans_apply]
  erw [h1]
  rfl

theorem mem_localClass_iff (x : LocalGroup (D3 f) (reflBar f v)) :
    (x : R3 f) ∈ LocalClass (D3 f) (reflBar f v) ↔
      ((localGroupEquivR3 hf hm hv e hf' x : F3.reflGroup f') : GL (Fin n) (ZMod 3)) ∈
        F3.reflSet f' := by
  obtain ⟨x, hx⟩ := x
  have hx' := hx
  rw [← range_perpToR3 hf hm hv] at hx'
  obtain ⟨g, rfl⟩ := hx'
  rw [localGroupEquivR3_apply]
  show perpToR3 f v g ∈ LocalClass (D3 f) (reflBar f v) ↔ _
  constructor
  · intro h
    rw [← image_perpToR3 hf hm hv] at h
    obtain ⟨g', hg', hgg'⟩ := h
    rw [← image_perpToGL e hf']
    exact ⟨g', hg', by rw [perpToR3_injective hf hm hv hgg']⟩
  · intro h
    rw [← image_perpToGL e hf'] at h
    obtain ⟨g', hg', hgg'⟩ := h
    rw [← perpToGL_injective e hf hv hgg', ← image_perpToR3 hf hm hv]
    exact ⟨g', hg', rfl⟩

@[expose] noncomputable def localQuotientEquivR3 : LocalQuotient (D3 f) (reflBar f v) ≃* R3 f' :=
  quotientCenterCongr (localGroupEquivR3 hf hm hv e hf')

theorem localQuotientEquivR3_mk (x : LocalGroup (D3 f) (reflBar f v)) :
    localQuotientEquivR3 hf hm hv e hf' (QuotientGroup.mk x) =
      QuotientGroup.mk (localGroupEquivR3 hf hm hv e hf' x) :=
  quotientCenterCongr_mk _ x

theorem localQuotientEquivR3_image :
    localQuotientEquivR3 hf hm hv e hf' '' LocalImages (D3 f) (reflBar f v) = D3 f' := by
  ext q
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [localQuotientEquivR3_mk]
    exact ⟨_, (mem_localClass_iff hf hm hv e hf' x).1 hx, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    set x := (localGroupEquivR3 hf hm hv e hf').symm h
    have hxh : localGroupEquivR3 hf hm hv e hf' x = h := MulEquiv.apply_symm_apply _ h
    refine ⟨QuotientGroup.mk x, ⟨x, (mem_localClass_iff hf hm hv e hf' x).2 (by rw [hxh]; exact hh),
      rfl⟩, ?_⟩
    rw [localQuotientEquivR3_mk, hxh]

theorem localQuotientEquivR3_starImage {w : Fin m → ZMod 3} (hw : f w w = 1) (hwv : f w v = 0) :
    localQuotientEquivR3 hf hm hv e hf'
        (starImage (D3 f) (reflBar f v) ⟨reflBar f w, reflBar_mem_localClass hf hm hv hw hwv⟩) =
      reflBar f' (e ⟨w, F3.mem_perpOne.2 hwv⟩) := by
  rw [starImage, localQuotientEquivR3_mk]
  show QuotientGroup.mk _ = QuotientGroup.mk (reflElt f' (e ⟨w, F3.mem_perpOne.2 hwv⟩))
  congr 1
  apply Subtype.ext
  have h := localGroupEquivR3_apply hf hm hv e hf' ⟨F3.refl f w, refl_mem_reflGroupPerp hw hwv⟩
  rw [perpToGL_refl e hf' hw hwv] at h
  exact h

end Equiv

section RestrictForm

variable {v : Fin m → ZMod 3}

variable (f) in
@[expose] noncomputable def restrictForm (e : F3.perpOne f v ≃ₗ[ZMod 3] (Fin n → ZMod 3)) :
    LinearMap.BilinForm (ZMod 3) (Fin n → ZMod 3) :=
  LinearMap.BilinForm.congr e (f.restrict (F3.perpOne f v))

theorem restrictForm_apply (e : F3.perpOne f v ≃ₗ[ZMod 3] (Fin n → ZMod 3))
    (a b : F3.perpOne f v) : restrictForm f e (e a) (e b) = f a b := by
  rw [restrictForm, LinearMap.BilinForm.congr_apply, e.symm_apply_apply, e.symm_apply_apply]
  rfl

theorem isF3Form_restrictForm (hf : IsF3Form f) (hv : f v v = 1)
    (e : F3.perpOne f v ≃ₗ[ZMod 3] (Fin n → ZMod 3)) : IsF3Form (restrictForm f e) := by
  have happ : ∀ x y, restrictForm f e x y = f (e.symm x) (e.symm y) := fun x y => by
    rw [← restrictForm_apply e, e.apply_symm_apply, e.apply_symm_apply]
  refine ⟨fun x y => by rw [happ, happ, hf.symm], fun x hx => ?_⟩
  have hs : ∀ z, f (e.symm x) z = 0 := fun z => by
    have hz : z - f z v • v ∈ F3.perpOne f v := F3.mem_perpOne.2 (by
      rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hv, mul_one, sub_self])
    have h1 := hx (e ⟨_, hz⟩)
    rw [happ, e.symm_apply_apply] at h1
    have h2 : f (e.symm x) v = 0 := F3.mem_perpOne.1 (e.symm x).2
    rw [show z = (z - f z v • v) + f z v • v by abel, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_right, h2, mul_zero, add_zero]
    exact h1
  have : ((e.symm x : F3.perpOne f v) : Fin m → ZMod 3) = 0 := hf.nondeg _ hs
  rw [← e.apply_symm_apply x, show e.symm x = 0 from Subtype.ext this, map_zero]

theorem exists_localQuotient_equiv (hf : IsF3Form f) (hm : 4 ≤ m) (hv : f v v = 1) :
    ∃ f' : LinearMap.BilinForm (ZMod 3) (Fin (m - 1) → ZMod 3), IsF3Form f' ∧
      (∃ e : F3.perpOne f v ≃ₗ[ZMod 3] (Fin (m - 1) → ZMod 3),
        ∀ a b : F3.perpOne f v, f' (e a) (e b) = f a b) ∧
      ∃ Φ : LocalQuotient (D3 f) (reflBar f v) ≃* R3 f',
        Φ '' LocalImages (D3 f) (reflBar f v) = D3 f' := by
  let e : F3.perpOne f v ≃ₗ[ZMod 3] (Fin (m - 1) → ZMod 3) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [F3.finrank_perpOne hv, Module.finrank_fin_fun])
  exact ⟨restrictForm f e, isF3Form_restrictForm hf hv e, ⟨e, restrictForm_apply e⟩,
    localQuotientEquivR3 hf hm hv e (restrictForm_apply e),
    localQuotientEquivR3_image hf hm hv e (restrictForm_apply e)⟩

end RestrictForm

section Extend

variable {f' : LinearMap.BilinForm (ZMod 3) (Fin n → ZMod 3)}

variable (f') in
@[expose] noncomputable def extendForm : LinearMap.BilinForm (ZMod 3) (Fin (n + 1) → ZMod 3) :=
  (LinearMap.mul (ZMod 3) (ZMod 3)).compl₁₂ (LinearMap.proj 0) (LinearMap.proj 0) +
    f'.compl₁₂ (LinearMap.funLeft (ZMod 3) (ZMod 3) Fin.succ)
      (LinearMap.funLeft (ZMod 3) (ZMod 3) Fin.succ)

theorem extendForm_apply (x y : Fin (n + 1) → ZMod 3) :
    extendForm f' x y = x 0 * y 0 + f' (Fin.tail x) (Fin.tail y) :=
  rfl

theorem tail_single_zero : Fin.tail (Pi.single 0 1 : Fin (n + 1) → ZMod 3) = 0 := by
  ext i
  simp [Fin.tail, Fin.succ_ne_zero]

theorem extendForm_single : extendForm f' (Pi.single 0 1) (Pi.single 0 1) = 1 := by
  rw [extendForm_apply, tail_single_zero]
  simp

theorem isF3Form_extendForm (hf' : IsF3Form f') : IsF3Form (extendForm f') := by
  refine ⟨fun x y => by rw [extendForm_apply, extendForm_apply, mul_comm, hf'.symm],
    fun x hx => ?_⟩
  have h0 : x 0 = 0 := by
    have := hx (Pi.single 0 1)
    rwa [extendForm_apply, tail_single_zero, map_zero, Pi.single_eq_same, mul_one,
      add_zero] at this
  have ht : Fin.tail x = 0 := hf'.nondeg _ fun y => by
    have := hx (Fin.cons 0 y)
    rwa [extendForm_apply, Fin.tail_cons, Fin.cons_zero, mul_zero, zero_add] at this
  rw [← Fin.cons_self_tail x, h0, ht]
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem mem_perpOne_extendForm {x : Fin (n + 1) → ZMod 3} :
    x ∈ F3.perpOne (extendForm f') (Pi.single 0 1) ↔ x 0 = 0 := by
  rw [F3.mem_perpOne, extendForm_apply, tail_single_zero, map_zero, Pi.single_eq_same,
    mul_one, add_zero]

variable (f') in
@[expose] noncomputable def tailEquiv :
    F3.perpOne (extendForm f') (Pi.single 0 1) ≃ₗ[ZMod 3] (Fin n → ZMod 3) where
  toFun x := Fin.tail (x : Fin (n + 1) → ZMod 3)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun y := ⟨Fin.cons 0 y, mem_perpOne_extendForm.2 (Fin.cons_zero _ _)⟩
  left_inv x := Subtype.ext (by
    have h := Fin.cons_self_tail (x : Fin (n + 1) → ZMod 3)
    rw [mem_perpOne_extendForm.1 x.2] at h
    exact h)
  right_inv y := Fin.tail_cons _ _

theorem tailEquiv_coe (a : F3.perpOne (extendForm f') (Pi.single 0 1)) :
    tailEquiv f' a = Fin.tail (a : Fin (n + 1) → ZMod 3) :=
  rfl

theorem tailEquiv_apply (a b : F3.perpOne (extendForm f') (Pi.single 0 1)) :
    f' (tailEquiv f' a) (tailEquiv f' b) = extendForm f' a b := by
  rw [extendForm_apply, mem_perpOne_extendForm.1 a.2, zero_mul, zero_add, tailEquiv_coe,
    tailEquiv_coe]

@[expose] noncomputable def localQuotientExtendEquiv (hf' : IsF3Form f') (hn : 3 ≤ n) :
    LocalQuotient (D3 (extendForm f')) (reflBar (extendForm f') (Pi.single 0 1)) ≃* R3 f' :=
  localQuotientEquivR3 (isF3Form_extendForm hf') (by omega) extendForm_single (tailEquiv f')
    tailEquiv_apply

theorem localQuotientExtendEquiv_image (hf' : IsF3Form f') (hn : 3 ≤ n) :
    localQuotientExtendEquiv hf' hn ''
      LocalImages (D3 (extendForm f')) (reflBar (extendForm f') (Pi.single 0 1)) = D3 f' :=
  localQuotientEquivR3_image _ _ _ _ _

end Extend

end CFSG.Fischer.Classification
