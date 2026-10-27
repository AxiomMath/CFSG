module

public import CFSG.Fischer.Classification.Orthogonal3.Forms
public import CFSG.Open.FischerThreeTranspositionMilestoneDefs

public section

namespace CFSG.Fischer.Classification

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Open Matrix

variable {m : ℕ}

namespace F3

variable {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}

@[expose] def act (g : GL (Fin m) (ZMod 3)) (x : Fin m → ZMod 3) : Fin m → ZMod 3 :=
  (g : Matrix (Fin m) (Fin m) (ZMod 3)) *ᵥ x

theorem act_def (g : GL (Fin m) (ZMod 3)) (x : Fin m → ZMod 3) :
    act g x = (g : Matrix (Fin m) (Fin m) (ZMod 3)) *ᵥ x :=
  rfl

@[simp]
theorem act_mul (g h : GL (Fin m) (ZMod 3)) (x : Fin m → ZMod 3) :
    act (g * h) x = act g (act h x) := by
  rw [act, act, act, Units.val_mul, Matrix.mulVec_mulVec]

@[simp]
theorem act_one (x : Fin m → ZMod 3) : act 1 x = x := by
  rw [act, Units.val_one, Matrix.one_mulVec]

@[simp]
theorem act_inv_act (g : GL (Fin m) (ZMod 3)) (x : Fin m → ZMod 3) : act g⁻¹ (act g x) = x := by
  rw [← act_mul, inv_mul_cancel, act_one]

@[simp]
theorem act_act_inv (g : GL (Fin m) (ZMod 3)) (x : Fin m → ZMod 3) : act g (act g⁻¹ x) = x := by
  rw [← act_mul, mul_inv_cancel, act_one]

@[simp]
theorem act_add (g : GL (Fin m) (ZMod 3)) (x y : Fin m → ZMod 3) :
    act g (x + y) = act g x + act g y :=
  Matrix.mulVec_add _ _ _

@[simp]
theorem act_smul (g : GL (Fin m) (ZMod 3)) (c : ZMod 3) (x : Fin m → ZMod 3) :
    act g (c • x) = c • act g x :=
  Matrix.mulVec_smul _ _ _

@[simp]
theorem act_neg (g : GL (Fin m) (ZMod 3)) (x : Fin m → ZMod 3) : act g (-x) = -act g x :=
  Matrix.mulVec_neg _ _

@[simp]
theorem act_sub (g : GL (Fin m) (ZMod 3)) (x y : Fin m → ZMod 3) :
    act g (x - y) = act g x - act g y :=
  Matrix.mulVec_sub _ _ _

@[simp]
theorem act_zero (g : GL (Fin m) (ZMod 3)) : act g 0 = 0 :=
  Matrix.mulVec_zero _

@[simp]
theorem act_neg_one (x : Fin m → ZMod 3) : act (-1) x = -x := by
  rw [act, Units.val_neg, Units.val_one, Matrix.neg_mulVec, Matrix.one_mulVec]

theorem act_injective (g : GL (Fin m) (ZMod 3)) : Function.Injective (act g) := fun x y h => by
  rw [← act_inv_act g x, h, act_inv_act]

theorem gl_ext {g h : GL (Fin m) (ZMod 3)} (H : ∀ x, act g x = act h x) : g = h :=
  Units.ext (Matrix.ext_of_mulVec_single fun _ => H _)

variable (f) in
@[expose] noncomputable def reflLin (v : Fin m → ZMod 3) :
    (Fin m → ZMod 3) →ₗ[ZMod 3] Fin m → ZMod 3 :=
  LinearMap.id + (f.flip v).smulRight v

theorem reflLin_apply (v x : Fin m → ZMod 3) : reflLin f v x = x + f x v • v :=
  rfl

variable (f) in
@[expose] noncomputable def reflMat (v : Fin m → ZMod 3) : Matrix (Fin m) (Fin m) (ZMod 3) :=
  LinearMap.toMatrix' (reflLin f v)

theorem reflMat_mulVec (v x : Fin m → ZMod 3) : reflMat f v *ᵥ x = x + f x v • v := by
  rw [reflMat, LinearMap.toMatrix'_mulVec, reflLin_apply]

theorem reflMat_mul_self {v : Fin m → ZMod 3} (hv : f v v = 1) : reflMat f v * reflMat f v = 1 := by
  refine Matrix.ext_of_mulVec_single fun i => ?_
  rw [← Matrix.mulVec_mulVec, reflMat_mulVec, reflMat_mulVec, Matrix.one_mulVec,
    LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hv]
  linear_combination (norm := module) three_eq_zero • (f (Pi.single i 1) v • v)

variable (f) in
@[expose] noncomputable def refl (v : Fin m → ZMod 3) : GL (Fin m) (ZMod 3) :=
  if h : f v v = 1 then ⟨reflMat f v, reflMat f v, reflMat_mul_self h, reflMat_mul_self h⟩
  else 1

theorem act_refl {v : Fin m → ZMod 3} (hv : f v v = 1) (x : Fin m → ZMod 3) :
    act (refl f v) x = x + f x v • v := by
  rw [act, refl, dite_eq_left_of_eq_true (eq_true hv)]
  exact reflMat_mulVec v x

theorem refl_of_ne {v : Fin m → ZMod 3} (hv : f v v ≠ 1) : refl f v = 1 :=
  dite_eq_right_of_eq_false (eq_false hv)

theorem act_refl_self {v : Fin m → ZMod 3} (hv : f v v = 1) : act (refl f v) v = -v := by
  rw [act_refl hv, hv]
  linear_combination (norm := module) three_eq_zero • v

theorem act_refl_of_perp {v x : Fin m → ZMod 3} (hv : f v v = 1) (hx : f x v = 0) :
    act (refl f v) x = x := by
  rw [act_refl hv, hx, zero_smul, add_zero]

theorem ne_zero_of_norm_one {v : Fin m → ZMod 3} (hv : f v v = 1) : v ≠ 0 := by
  intro h
  rw [h] at hv
  simp at hv

@[simp]
theorem refl_mul_self (v : Fin m → ZMod 3) : refl f v * refl f v = 1 := by
  by_cases hv : f v v = 1
  · exact Units.ext (by
      rw [Units.val_mul, refl, dite_eq_left_of_eq_true (eq_true hv)]
      exact reflMat_mul_self hv)
  · rw [refl_of_ne hv, one_mul]

@[simp]
theorem refl_inv (v : Fin m → ZMod 3) : (refl f v)⁻¹ = refl f v :=
  inv_eq_of_mul_eq_one_right (refl_mul_self v)

theorem refl_smul {c : ZMod 3} (hc : c ≠ 0) (v : Fin m → ZMod 3) : refl f (c • v) = refl f v := by
  have hcc := mul_self_of_ne_zero hc
  have hn : f (c • v) (c • v) = f v v := by rw [norm_smul, hcc, one_mul]
  by_cases hv : f v v = 1
  · refine gl_ext fun x => ?_
    rw [act_refl (hn.trans hv), act_refl hv, LinearMap.BilinForm.smul_right, smul_smul,
      mul_comm c, mul_assoc, hcc, mul_one]
  · rw [refl_of_ne hv, refl_of_ne (hn ▸ hv)]

theorem refl_neg (v : Fin m → ZMod 3) : refl f (-v) = refl f v := by
  rw [← neg_one_smul (ZMod 3) v, refl_smul (by decide)]

theorem refl_eq_refl_iff {v w : Fin m → ZMod 3} (hv : f v v = 1) (hw : f w w = 1) :
    refl f v = refl f w ↔ w = v ∨ w = -v := by
  constructor
  · intro h
    have h1 : act (refl f v) v = act (refl f w) v := by rw [h]
    rw [act_refl_self hv, act_refl hw] at h1
    have h2 : v = f v w • w := by linear_combination (norm := module) h1 + three_eq_zero • v
    have hc : f v w * f v w = 1 := by
      have := hv
      rw [h2, norm_smul, hw, mul_one] at this
      exact this
    have hc' : f v w = 1 ∨ f v w = -1 := by
      revert hc; generalize f v w = c; revert c; decide
    rcases hc' with hc' | hc'
    · left; rw [h2, hc', one_smul]
    · right; rw [h2, hc', neg_one_smul, neg_neg]
  · rintro (rfl | rfl)
    · rfl
    · exact (refl_neg v).symm

variable (f) in
@[expose] def IsIsom (g : GL (Fin m) (ZMod 3)) : Prop :=
  ∀ x y, f (act g x) (act g y) = f x y

theorem isIsom_one : IsIsom f 1 := fun x y => by rw [act_one, act_one]

theorem IsIsom.mul {g h : GL (Fin m) (ZMod 3)} (hg : IsIsom f g) (hh : IsIsom f h) :
    IsIsom f (g * h) := fun x y => by rw [act_mul, act_mul, hg, hh]

theorem IsIsom.inv {g : GL (Fin m) (ZMod 3)} (hg : IsIsom f g) : IsIsom f g⁻¹ := fun x y => by
  rw [← hg, act_act_inv, act_act_inv]

theorem IsIsom.norm {g : GL (Fin m) (ZMod 3)} (hg : IsIsom f g) (x : Fin m → ZMod 3) :
    f (act g x) (act g x) = f x x :=
  hg x x

theorem IsIsom.inv_left {g : GL (Fin m) (ZMod 3)} (hg : IsIsom f g) (x y : Fin m → ZMod 3) :
    f (act g⁻¹ x) y = f x (act g y) := by
  rw [← hg, act_act_inv]

theorem isIsom_refl (hf : IsF3Form f) (v : Fin m → ZMod 3) : IsIsom f (refl f v) := by
  by_cases hv : f v v = 1
  · intro x y
    rw [act_refl hv, act_refl hv]
    simp only [LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hv, hf.symm v y]
    linear_combination f x v * f y v * three_eq_zero
  · rw [refl_of_ne hv]
    exact isIsom_one

variable (f) in
@[expose] def isomGroup : Subgroup (GL (Fin m) (ZMod 3)) where
  carrier := {g | IsIsom f g}
  mul_mem' ha hb := IsIsom.mul ha hb
  one_mem' := isIsom_one
  inv_mem' ha := IsIsom.inv ha

theorem mem_isomGroup {g : GL (Fin m) (ZMod 3)} : g ∈ isomGroup f ↔ IsIsom f g :=
  Iff.rfl

theorem conj_refl {g : GL (Fin m) (ZMod 3)} (hg : IsIsom f g) (v : Fin m → ZMod 3) :
    g * refl f v * g⁻¹ = refl f (act g v) := by
  by_cases hv : f v v = 1
  · refine gl_ext fun x => ?_
    rw [act_mul, act_mul, act_refl hv, act_refl (by rw [hg.norm, hv]), act_add, act_act_inv,
      act_smul, hg.inv_left]
  · rw [refl_of_ne hv, refl_of_ne (by rwa [hg.norm]), mul_one, mul_inv_cancel]

theorem refl_commute_iff (hf : IsF3Form f) {v w : Fin m → ZMod 3} (hv : f v v = 1)
    (hw : f w w = 1) :
    refl f v * refl f w = refl f w * refl f v ↔ f v w = 0 ∨ w = v ∨ w = -v := by
  constructor
  · intro h
    have h1 : refl f v * refl f w * (refl f v)⁻¹ = refl f w := by
      rw [h, mul_assoc, mul_inv_cancel, mul_one]
    rw [conj_refl (isIsom_refl hf v), refl_eq_refl_iff (by rw [(isIsom_refl hf v).norm, hw]) hw,
      act_refl hv] at h1
    rcases h1 with h1 | h1
    · left
      have : f w v • v = 0 := by linear_combination (norm := module) (-1 : ZMod 3) • h1
      rw [hf.symm]
      exact (smul_eq_zero.1 this).resolve_right (ne_zero_of_norm_one hv)
    · right
      have h2 : w = f w v • v := by
        linear_combination (norm := module) (-1 : ZMod 3) • h1 + three_eq_zero • w
      have hc : f w v * f w v = 1 := by
        have := hw
        rw [h2, norm_smul, hv, mul_one] at this
        exact this
      have hc' : f w v = 1 ∨ f w v = -1 := by
        revert hc; generalize f w v = c; revert c; decide
      rcases hc' with hc' | hc'
      · left; rw [h2, hc', one_smul]
      · right; rw [h2, hc', neg_one_smul]
  · rintro (h | rfl | rfl)
    · refine gl_ext fun x => ?_
      have hwv : f w v = 0 := by rw [hf.symm]; exact h
      simp only [act_mul, act_refl hv, act_refl hw, LinearMap.BilinForm.add_left,
        LinearMap.BilinForm.smul_left, h, hwv, mul_zero, add_zero]
      abel
    · rfl
    · rw [refl_neg]

theorem refl_braid (hf : IsF3Form f) {v w : Fin m → ZMod 3} (hv : f v v = 1) (hw : f w w = 1)
    (hvw : f v w ≠ 0) :
    refl f v * refl f w * refl f v = refl f w * refl f v * refl f w := by
  have e1 : refl f v * refl f w * refl f v = refl f (w + f w v • v) := by
    rw [← act_refl hv, ← conj_refl (isIsom_refl hf v), refl_inv]
  have e2 : refl f w * refl f v * refl f w = refl f (v + f v w • w) := by
    rw [← act_refl hw, ← conj_refl (isIsom_refl hf w), refl_inv]
  rw [e1, e2, ← refl_smul (f := f) hvw (w + f w v • v), smul_add, smul_smul, hf.symm w v,
    mul_self_of_ne_zero hvw, one_smul, add_comm]

theorem refl_mul_refl_pow_three (hf : IsF3Form f) {v w : Fin m → ZMod 3} (hv : f v v = 1)
    (hw : f w w = 1) (hvw : f v w ≠ 0) : (refl f v * refl f w) ^ 3 = 1 := by
  have hb := refl_braid hf hv hw hvw
  calc (refl f v * refl f w) ^ 3
      = (refl f v * refl f w * refl f v) * (refl f w * refl f v * refl f w) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = (refl f w * refl f v * refl f w) * (refl f w * refl f v * refl f w) := by rw [hb]
    _ = 1 := by
      simp only [mul_assoc, refl_mul_self, ← mul_assoc (refl f w) (refl f w), one_mul]
      rw [← mul_assoc (refl f v) (refl f v), refl_mul_self, one_mul, refl_mul_self]

theorem refl_mul_refl_pow_two (hf : IsF3Form f) {v w : Fin m → ZMod 3} (hv : f v v = 1)
    (hw : f w w = 1) (hvw : f v w = 0) : (refl f v * refl f w) ^ 2 = 1 := by
  have hc := (refl_commute_iff hf hv hw).2 (Or.inl hvw)
  calc (refl f v * refl f w) ^ 2 = refl f v * (refl f w * refl f v) * refl f w := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := by rw [← hc, ← mul_assoc, refl_mul_self, one_mul, refl_mul_self]

theorem refl_ne_neg_refl (hm : 3 ≤ m) (v w : Fin m → ZMod 3) : refl f w ≠ -refl f v := by
  intro h
  obtain ⟨y, hy0, hy⟩ := exists_ne_zero_perp (f := f) (k := 2) (by omega) ![v, w]
  have hyv : f y v = 0 := by simpa using hy 0
  have hyw : f y w = 0 := by simpa using hy 1
  have h1 : act (refl f w) y = y := by
    by_cases hw : f w w = 1
    · exact act_refl_of_perp hw hyw
    · rw [refl_of_ne hw, act_one]
  have h2 : act (refl f v) y = y := by
    by_cases hv : f v v = 1
    · exact act_refl_of_perp hv hyv
    · rw [refl_of_ne hv, act_one]
  have h3 : act (-refl f v) y = -act (refl f v) y := by
    rw [act, Units.val_neg, Matrix.neg_mulVec]; rfl
  rw [h, h3, h2] at h1
  exact hy0 (eq_zero_of_eq_neg h1.symm)

variable (f) in
abbrev reflSet : Set (GL (Fin m) (ZMod 3)) :=
  fischerTransvections (fun x y => f x y) fun v => f v v = 1

variable (f) in
abbrev reflGroup : Subgroup (GL (Fin m) (ZMod 3)) :=
  Subgroup.closure (reflSet f)

theorem refl_mem_reflSet {v : Fin m → ZMod 3} (hv : f v v = 1) : refl f v ∈ reflSet f :=
  ⟨v, hv, act_refl hv⟩

theorem mem_reflSet_iff {g : GL (Fin m) (ZMod 3)} :
    g ∈ reflSet f ↔ ∃ v, f v v = 1 ∧ refl f v = g := by
  constructor
  · rintro ⟨v, hv, hg⟩
    exact ⟨v, hv, gl_ext fun x => by rw [act_refl hv]; exact (hg x).symm⟩
  · rintro ⟨v, hv, rfl⟩
    exact refl_mem_reflSet hv

theorem refl_mem_reflGroup (v : Fin m → ZMod 3) : refl f v ∈ reflGroup f := by
  by_cases hv : f v v = 1
  · exact Subgroup.subset_closure (refl_mem_reflSet hv)
  · rw [refl_of_ne hv]
    exact Subgroup.one_mem _

theorem reflGroup_le_isomGroup (hf : IsF3Form f) : reflGroup f ≤ isomGroup f := by
  rw [Subgroup.closure_le]
  intro g hg
  obtain ⟨v, -, rfl⟩ := mem_reflSet_iff.1 hg
  exact isIsom_refl hf v

theorem isIsom_of_mem (hf : IsF3Form f) {g : GL (Fin m) (ZMod 3)} (hg : g ∈ reflGroup f) :
    IsIsom f g :=
  reflGroup_le_isomGroup hf hg

theorem conj_refl_add (hf : IsF3Form f) {v w : Fin m → ZMod 3} (hv : f v v = 1)
    (hw : f w w = 1) (hvw : f v w ≠ 0) :
    refl f (v + f v w • w) * refl f v * (refl f (v + f v w • w))⁻¹ = refl f w := by
  rw [conj_refl (isIsom_refl hf _), act_refl (norm_add_pair hf hv hw)]
  have : v + f v (v + f v w • w) • (v + f v w • w) = (-f v w) • w := by
    rw [LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, hv,
      mul_self_of_ne_zero hvw]
    linear_combination (norm := module) three_eq_zero • (v + f v w • w)
  rw [this, refl_smul (neg_ne_zero.2 hvw)]

theorem exists_conj_refl (hf : IsF3Form f) (hm : 4 ≤ m) {v w : Fin m → ZMod 3}
    (hv : f v v = 1) (hw : f w w = 1) : ∃ g ∈ reflGroup f, g * refl f v * g⁻¹ = refl f w := by
  by_cases hvw : f v w = 0
  · obtain ⟨x, hx, hxv, hxw⟩ := exists_norm_one_ne_zero_ne_zero hf hm hv hw hvw
    have h1 := conj_refl_add hf hv hx (by rwa [hf.symm])
    have h2 := conj_refl_add hf hx hw hxw
    refine ⟨refl f (x + f x w • w) * refl f (v + f v x • x),
      mul_mem (refl_mem_reflGroup _) (refl_mem_reflGroup _), ?_⟩
    calc refl f (x + f x w • w) * refl f (v + f v x • x) * refl f v *
          (refl f (x + f x w • w) * refl f (v + f v x • x))⁻¹
        = refl f (x + f x w • w) *
            (refl f (v + f v x • x) * refl f v * (refl f (v + f v x • x))⁻¹) *
              (refl f (x + f x w • w))⁻¹ := by group
      _ = refl f w := by rw [h1, h2]
  · exact ⟨_, refl_mem_reflGroup _, conj_refl_add hf hv hw hvw⟩

theorem eq_one_or_eq_neg_one (hf : IsF3Form f) (hm : 4 ≤ m) {g : GL (Fin m) (ZMod 3)}
    (hg : IsIsom f g) (h : ∀ v, f v v = 1 → act g v = v ∨ act g v = -v) : g = 1 ∨ g = -1 := by
  have mixed : ∀ v w, f v v = 1 → f w w = 1 → f v w ≠ 0 → act g v = v → act g w = -w →
      False := by
    intro v w hv hw hvw h1 h2
    rcases h _ (norm_add_pair hf hv hw) with h3 | h3 <;>
      rw [act_add, act_smul, h1, h2] at h3
    · have : f v w • w = -(f v w • w) := by
        linear_combination (norm := module) (-1 : ZMod 3) • h3
      exact ne_zero_of_norm_one hw ((smul_eq_zero.1 (eq_zero_of_eq_neg this)).resolve_left hvw)
    · have : v = -v := by linear_combination (norm := module) h3
      exact ne_zero_of_norm_one hv (eq_zero_of_eq_neg this)
  have agree₁ : ∀ v w, f v v = 1 → f w w = 1 → f v w ≠ 0 → (act g v = v ↔ act g w = w) := by
    intro v w hv hw hvw
    constructor
    · intro h1
      rcases h w hw with h2 | h2
      · exact h2
      · exact (mixed v w hv hw hvw h1 h2).elim
    · intro h2
      rcases h v hv with h1 | h1
      · exact h1
      · exact (mixed w v hw hv (by rwa [hf.symm]) h2 h1).elim
  have agree : ∀ v w, f v v = 1 → f w w = 1 → (act g v = v ↔ act g w = w) := by
    intro v w hv hw
    by_cases hvw : f v w = 0
    · obtain ⟨x, hx, hxv, hxw⟩ := exists_norm_one_ne_zero_ne_zero hf hm hv hw hvw
      exact (agree₁ v x hv hx (by rwa [hf.symm])).trans (agree₁ x w hx hw hxw)
    · exact agree₁ v w hv hw hvw
  have key : ∀ ε : ZMod 3, ε * ε = 1 → (∀ v, f v v = 1 → act g v = ε • v) →
      ∀ x, act g x = ε • x := by
    intro ε hε hv x
    have : act g x - ε • x = 0 := eq_zero_of_forall_norm_one hf (by omega) fun w hw => by
      have hw' : w = ε • act g w := by rw [hv w hw, smul_smul, hε, one_smul]
      have h1 : f (act g x) w = ε * f x w := by
        calc f (act g x) w = f (act g x) (ε • act g w) := by rw [← hw']
          _ = ε * f x w := by rw [LinearMap.BilinForm.smul_right, hg]
      rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, h1, sub_self]
    exact sub_eq_zero.1 this
  obtain ⟨v₀, hv₀⟩ := exists_norm_eq hf (by omega) (one_ne_zero (α := ZMod 3))
  by_cases h0 : act g v₀ = v₀
  · left
    have hall : ∀ v, f v v = 1 → act g v = (1 : ZMod 3) • v := fun v hv => by
      rw [one_smul]; exact (agree v₀ v hv₀ hv).1 h0
    exact gl_ext fun x => by rw [key 1 (by decide) hall x, one_smul, act_one]
  · right
    have hall : ∀ v, f v v = 1 → act g v = (-1 : ZMod 3) • v := fun v hv => by
      rw [neg_one_smul]
      rcases h v hv with h1 | h1
      · exact absurd ((agree v₀ v hv₀ hv).2 h1) h0
      · exact h1
    exact gl_ext fun x => by rw [key (-1) (by decide) hall x, neg_one_smul, act_neg_one]

theorem act_eq_or_of_commute {g : GL (Fin m) (ZMod 3)} (hg : IsIsom f g) {v : Fin m → ZMod 3}
    (hv : f v v = 1) (hc : refl f v * g = g * refl f v) : act g v = v ∨ act g v = -v := by
  have h1 : g * refl f v * g⁻¹ = refl f v := by rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
  rw [conj_refl hg, refl_eq_refl_iff (by rw [hg.norm, hv]) hv] at h1
  rcases h1 with h1 | h1
  · exact Or.inl h1.symm
  · right
    have := congrArg Neg.neg h1
    rw [neg_neg] at this
    exact this.symm

theorem coe_eq_of_mem_center (hf : IsF3Form f) (hm : 4 ≤ m) {g : reflGroup f}
    (hg : g ∈ Subgroup.center (reflGroup f)) :
    (g : GL (Fin m) (ZMod 3)) = 1 ∨ (g : GL (Fin m) (ZMod 3)) = -1 := by
  have hiso := isIsom_of_mem hf g.2
  refine eq_one_or_eq_neg_one hf hm hiso fun v hv => act_eq_or_of_commute hiso hv ?_
  exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hg ⟨refl f v, refl_mem_reflGroup v⟩)

end F3

end CFSG.Fischer.Classification
