module

public import CFSG.Fischer.Classification.Orthogonal3.Refl
public import CFSG.Fischer.Classification.Defs

public section

namespace CFSG.Fischer.Classification

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Blueprint.Fischer CFSG.Open CFSG.Fischer F3

variable {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}

variable (f) in
abbrev R3 : Type :=
  F3.reflGroup f ⧸ Subgroup.center (F3.reflGroup f)

variable (f) in
@[expose] def D3 : Set (R3 f) :=
  {q | ∃ h : F3.reflGroup f, (h : GL (Fin m) (ZMod 3)) ∈ F3.reflSet f ∧ q = QuotientGroup.mk h}

variable (f) in
@[expose] noncomputable def reflElt (v : Fin m → ZMod 3) : F3.reflGroup f :=
  ⟨F3.refl f v, F3.refl_mem_reflGroup v⟩

variable (f) in
@[expose] noncomputable def reflBar (v : Fin m → ZMod 3) : R3 f :=
  QuotientGroup.mk (reflElt f v)

@[simp]
theorem coe_reflElt (v : Fin m → ZMod 3) : (reflElt f v : GL (Fin m) (ZMod 3)) = F3.refl f v :=
  rfl

theorem reflBar_def (v : Fin m → ZMod 3) : reflBar f v = QuotientGroup.mk (reflElt f v) :=
  rfl

theorem fischerCentralQuotientModel_iff {G : Type*} [Group G] (D : Set G) :
    fischerCentralQuotientModel D
        (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
        (fischerTransvections (fun x y => f x y) fun v => f v v = 1) ↔
      ∃ φ : G ≃* R3 f, ∀ g, g ∈ D ↔ φ g ∈ D3 f :=
  Iff.rfl

theorem mem_D3_iff {q : R3 f} : q ∈ D3 f ↔ ∃ v, f v v = 1 ∧ reflBar f v = q := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨v, hv, hvh⟩ := mem_reflSet_iff.1 hh
    exact ⟨v, hv, congrArg _ (Subtype.ext hvh)⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨reflElt f v, refl_mem_reflSet hv, rfl⟩

theorem reflBar_mem_D3 {v : Fin m → ZMod 3} (hv : f v v = 1) : reflBar f v ∈ D3 f :=
  mem_D3_iff.2 ⟨v, hv, rfl⟩

theorem reflBar_smul {c : ZMod 3} (hc : c ≠ 0) (v : Fin m → ZMod 3) :
    reflBar f (c • v) = reflBar f v := by
  rw [reflBar, reflBar]
  exact congrArg _ (Subtype.ext (refl_smul hc v))

theorem reflBar_neg (v : Fin m → ZMod 3) : reflBar f (-v) = reflBar f v := by
  rw [reflBar, reflBar]
  exact congrArg _ (Subtype.ext (refl_neg v))

theorem commute_of_mul_eq_one {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (h : b * a * b * a = 1) : a * b = b * a := by
  calc a * b = a * b * (b * a * b * a) := by rw [h, mul_one]
    _ = a * (b * b) * a * (b * a) := by group
    _ = b * a := by rw [hb, mul_one, ha, one_mul]

@[simp]
theorem reflBar_mul_self (v : Fin m → ZMod 3) : reflBar f v * reflBar f v = 1 := by
  rw [reflBar, ← QuotientGroup.mk_mul,
    show reflElt f v * reflElt f v = 1 from Subtype.ext (refl_mul_self v), QuotientGroup.mk_one]

theorem mk_conj_reflBar (hf : IsF3Form f) (g : F3.reflGroup f) (v : Fin m → ZMod 3) :
    (QuotientGroup.mk g : R3 f) * reflBar f v * (QuotientGroup.mk g)⁻¹ =
      reflBar f (act (g : GL (Fin m) (ZMod 3)) v) := by
  rw [reflBar, reflBar, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (conj_refl (isIsom_of_mem hf g.2) v)

theorem reflBar_conj (hf : IsF3Form f) (v w : Fin m → ZMod 3) :
    reflBar f v * reflBar f w * reflBar f v = reflBar f (act (F3.refl f v) w) := by
  have := mk_conj_reflBar hf (reflElt f v) w
  rwa [← reflBar_def, show (reflBar f v)⁻¹ = reflBar f v from
    inv_eq_of_mul_eq_one_right (reflBar_mul_self v)] at this

theorem reflBar_eq_reflBar_iff (hf : IsF3Form f) (hm : 4 ≤ m) {v w : Fin m → ZMod 3}
    (hv : f v v = 1) (hw : f w w = 1) : reflBar f v = reflBar f w ↔ w = v ∨ w = -v := by
  constructor
  · intro h
    rw [reflBar, reflBar, QuotientGroup.eq] at h
    have hcoe : (((reflElt f v)⁻¹ * reflElt f w : F3.reflGroup f) : GL (Fin m) (ZMod 3)) =
        F3.refl f v * F3.refl f w := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_reflElt, coe_reflElt, refl_inv]
    rcases coe_eq_of_mem_center hf hm h with h1 | h1 <;> rw [hcoe] at h1
    · rw [mul_eq_one_iff_eq_inv, refl_inv] at h1
      exact (refl_eq_refl_iff hv hw).1 h1
    · exfalso
      apply refl_ne_neg_refl (f := f) (by omega) v w
      calc F3.refl f w = F3.refl f v * (F3.refl f v * F3.refl f w) := by
            rw [← mul_assoc, refl_mul_self, one_mul]
        _ = -F3.refl f v := by rw [h1, mul_neg_one]
  · rintro (rfl | rfl)
    · rfl
    · exact (reflBar_neg v).symm

theorem reflBar_commute_iff (hf : IsF3Form f) (hm : 4 ≤ m) {v w : Fin m → ZMod 3}
    (hv : f v v = 1) (hw : f w w = 1) :
    reflBar f v * reflBar f w = reflBar f w * reflBar f v ↔ f v w = 0 ∨ w = v ∨ w = -v := by
  rw [← refl_commute_iff hf hv hw]
  constructor
  · intro h
    rw [reflBar, reflBar, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h
    have hcoe : (((reflElt f v * reflElt f w)⁻¹ * (reflElt f w * reflElt f v) :
        F3.reflGroup f) : GL (Fin m) (ZMod 3)) =
          F3.refl f w * F3.refl f v * F3.refl f w * F3.refl f v := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_mul, coe_reflElt,
        coe_reflElt, mul_inv_rev, refl_inv, refl_inv, mul_assoc, mul_assoc, mul_assoc]
    rcases coe_eq_of_mem_center hf hm h with h1 | h1 <;> rw [hcoe] at h1
    · exact commute_of_mul_eq_one (refl_mul_self v) (refl_mul_self w) h1
    · exfalso
      apply refl_ne_neg_refl (f := f) (by omega) v (act (F3.refl f w) v)
      rw [← conj_refl (isIsom_refl hf w), refl_inv]
      calc F3.refl f w * F3.refl f v * F3.refl f w
          = F3.refl f w * F3.refl f v * F3.refl f w * F3.refl f v * F3.refl f v := by
            rw [mul_assoc _ (F3.refl f v) (F3.refl f v), refl_mul_self, mul_one]
        _ = -F3.refl f v := by rw [h1, neg_one_mul]
  · intro h
    rw [reflBar, reflBar, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg _ (Subtype.ext h)

theorem reflBar_ne_one (hf : IsF3Form f) (hm : 4 ≤ m) {v : Fin m → ZMod 3} (hv : f v v = 1) :
    reflBar f v ≠ 1 := by
  intro h
  obtain ⟨z, hz0, hzz, hzv⟩ := exists_isotropic_perp hf hm hv
  have hvz : f v z = 0 := by rw [hf.symm]; exact hzv
  have hw : f (v + z) (v + z) = 1 := by rw [norm_add hf, hv, hvz, hzz]; ring
  have hc : reflBar f v * reflBar f (v + z) = reflBar f (v + z) * reflBar f v := by
    rw [h, one_mul, mul_one]
  rcases (reflBar_commute_iff hf hm hv hw).1 hc with h1 | h1 | h1
  · rw [LinearMap.BilinForm.add_right, hv, hvz, add_zero] at h1
    exact one_ne_zero h1
  · exact hz0 (by simpa using h1)
  · apply one_ne_zero (α := ZMod 3)
    have hz : z = v := by linear_combination (norm := module) h1 - three_eq_zero • v
    calc (1 : ZMod 3) = f v v := hv.symm
      _ = f z v := by rw [hz]
      _ = 0 := hzv

theorem orderOf_reflBar (hf : IsF3Form f) (hm : 4 ≤ m) {v : Fin m → ZMod 3} (hv : f v v = 1) :
    orderOf (reflBar f v) = 2 :=
  orderOf_eq_prime (by rw [sq, reflBar_mul_self]) (reflBar_ne_one hf hm hv)

theorem reflBar_mul_pow_three (hf : IsF3Form f) {v w : Fin m → ZMod 3} (hv : f v v = 1)
    (hw : f w w = 1) (hvw : f v w ≠ 0) : (reflBar f v * reflBar f w) ^ 3 = 1 := by
  rw [reflBar, reflBar, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow,
    show (reflElt f v * reflElt f w) ^ 3 = 1 from Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_mul, coe_reflElt, coe_reflElt,
        refl_mul_refl_pow_three hf hv hw hvw, Subgroup.coe_one]), QuotientGroup.mk_one]

theorem reflBar_mul_pow_two (hf : IsF3Form f) {v w : Fin m → ZMod 3} (hv : f v v = 1)
    (hw : f w w = 1) (hvw : f v w = 0) : (reflBar f v * reflBar f w) ^ 2 = 1 := by
  rw [reflBar, reflBar, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow,
    show (reflElt f v * reflElt f w) ^ 2 = 1 from Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_mul, coe_reflElt, coe_reflElt,
        refl_mul_refl_pow_two hf hv hw hvw, Subgroup.coe_one]), QuotientGroup.mk_one]

theorem D3_eq_image : D3 f = QuotientGroup.mk '' (Subtype.val ⁻¹' F3.reflSet f) := by
  ext q
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩

theorem pair_R3 (hf : IsF3Form f) (hm : 4 ≤ m) : Pair (R3 f) (D3 f) := by
  obtain ⟨v₀, hv₀⟩ := exists_norm_eq hf (by omega) (one_ne_zero (α := ZMod 3))
  refine ⟨inferInstance, ⟨reflBar f v₀, ?_⟩, ?_, ?_, ?_⟩
  · ext q
    constructor
    · intro hq
      obtain ⟨w, hw, rfl⟩ := mem_D3_iff.1 hq
      obtain ⟨g, hg, hgc⟩ := exists_conj_refl hf hm hv₀ hw
      refine isConj_iff.2 ⟨QuotientGroup.mk ⟨g, hg⟩, ?_⟩
      rw [mk_conj_reflBar hf, reflBar, reflBar]
      rw [conj_refl (isIsom_of_mem hf hg)] at hgc
      exact congrArg _ (Subtype.ext hgc)
    · intro hq
      obtain ⟨c, rfl⟩ := isConj_iff.1 hq
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
      rw [mk_conj_reflBar hf]
      exact reflBar_mem_D3 (by rw [(isIsom_of_mem hf g.2).norm, hv₀])
  · intro e he
    obtain ⟨v, hv, rfl⟩ := mem_D3_iff.1 he
    exact orderOf_reflBar hf hm hv
  · intro e he e' he'
    obtain ⟨v, hv, rfl⟩ := mem_D3_iff.1 he
    obtain ⟨w, hw, rfl⟩ := mem_D3_iff.1 he'
    by_cases hvw : f v w = 0
    · rcases (Nat.dvd_prime Nat.prime_two).1
          (orderOf_dvd_of_pow_eq_one (reflBar_mul_pow_two hf hv hw hvw)) with h | h <;>
        simp [h]
    · rcases (Nat.dvd_prime Nat.prime_three).1
          (orderOf_dvd_of_pow_eq_one (reflBar_mul_pow_three hf hv hw hvw)) with h | h <;>
        simp [h]
  · rw [D3_eq_image, ← QuotientGroup.coe_mk', ← MonoidHom.map_closure,
      Subgroup.closure_closure_coe_preimage]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

theorem center_R3_eq_bot (hf : IsF3Form f) (hm : 4 ≤ m) : Subgroup.center (R3 f) = ⊥ := by
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
  have hiso := isIsom_of_mem hf g.2
  have hpm : (g : GL (Fin m) (ZMod 3)) = 1 ∨ (g : GL (Fin m) (ZMod 3)) = -1 := by
    refine eq_one_or_eq_neg_one hf hm hiso fun v hv => ?_
    have hc := Subgroup.mem_center_iff.1 hq (reflBar f v)
    have h1 : (QuotientGroup.mk g : R3 f) * reflBar f v * (QuotientGroup.mk g)⁻¹ =
        reflBar f v := by
      rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
    rw [mk_conj_reflBar hf, reflBar_eq_reflBar_iff hf hm (by rw [hiso.norm, hv]) hv] at h1
    rcases h1 with h1 | h1
    · exact Or.inl h1.symm
    · right
      have := congrArg Neg.neg h1
      rw [neg_neg] at this
      exact this.symm
  rw [Subgroup.mem_center_iff]
  intro h
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  rcases hpm with h1 | h1 <;> rw [h1]
  · rw [mul_one, one_mul]
  · rw [mul_neg_one, neg_one_mul]

theorem classicalConclusion_of_mulEquiv {G : Type} [Group G] {D : Set G} (hf : IsF3Form f)
    (hm : 5 ≤ m) (φ : G ≃* R3 f) (hφ : ∀ g, g ∈ D ↔ φ g ∈ D3 f) : ClassicalConclusion G D :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨m, hm, f, hf.symm, hf.nondeg, φ, hφ⟩)))

end CFSG.Fischer.Classification
