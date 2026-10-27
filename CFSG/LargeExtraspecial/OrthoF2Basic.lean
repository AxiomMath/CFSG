module

public import CFSG.LargeExtraspecial.Types
public import CFSG.ClassicalGroups.Orthogonal.Derived

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open TauCeti.QuadraticMap (orthogonalGroup)

namespace OrthoF2

theorem zmod2_eq_zero_or_eq_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem zmod2_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 :=
  (zmod2_eq_zero_or_eq_one a).resolve_left h

theorem zmod2_mul_self (a : ZMod 2) : a * a = a := by
  revert a
  decide

theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  revert a
  decide

theorem zmod2_neg (a : ZMod 2) : -a = a := by
  revert a
  decide

theorem zmod2_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  revert a b
  decide

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem vec_add_self (v : V) : v + v = 0 :=
  add_self_vec (ZMod 2) v

theorem vec_neg (v : V) : -v = v :=
  neg_vec_eq (ZMod 2) v

theorem vec_sub (u v : V) : u - v = u + v :=
  sub_eq_add_vec (ZMod 2) u v

theorem map_smul_zmod2 (q : QuadraticForm (ZMod 2) V) (c : ZMod 2) (x : V) :
    q (c • x) = c * q x := by
  rw [QuadraticMap.map_smul, smul_eq_mul, zmod2_mul_self]

theorem mem_span_singleton_iff {x v : V} :
    v ∈ (ZMod 2) ∙ x ↔ v = 0 ∨ v = x := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
    · exact Or.inl (zero_smul _ _)
    · exact Or.inr (one_smul _ _)
  · rintro (rfl | rfl)
    · exact ⟨0, zero_smul _ _⟩
    · exact ⟨1, one_smul _ _⟩

theorem eq_one_of_forall_apply_eq {t : V ≃ₗ[ZMod 2] V} (h : ∀ v, t v = v) : t = 1 :=
  LinearEquiv.ext h

theorem apply_inv_apply (t : V ≃ₗ[ZMod 2] V) (v : V) : t (t⁻¹ v) = v :=
  CFSG.ClassicalGroups.Orthogonal.LinearEquiv.apply_inv_apply' t v

theorem isRefl_polarBilin {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    (Q : QuadraticForm K W) : (polarBilin Q).IsRefl := fun x y h => by
  rw [polarBilin_apply_apply] at h ⊢
  rwa [polar_comm]

end OrthoF2

open OrthoF2

theorem fixSpace_eq_orthogonal_commSpace_of_mem {K : Type*} [Field K] {W : Type*}
    [AddCommGroup W] [Module K W] {Q : QuadraticForm K W} (hQ : Q.polarBilin.Nondegenerate)
    {t : W ≃ₗ[K] W} (ht : t ∈ orthogonalGroup Q) :
    fixSpace t = LinearMap.BilinForm.orthogonal Q.polarBilin (commSpace t) := by
  ext v
  rw [LinearMap.BilinForm.mem_orthogonal_iff, mem_fixSpace]
  constructor
  · intro hv n hn
    obtain ⟨y, rfl⟩ := mem_commSpace.mp hn
    have h := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup ht y v
    rw [hv] at h
    rw [polarBilin_apply_apply, QuadraticMap.polar_sub_left, h, sub_self]
  · intro hv
    refine sub_eq_zero.mp (hQ.1 _ fun y => ?_)
    have hty : t (t⁻¹ y) = y := CFSG.ClassicalGroups.Orthogonal.LinearEquiv.apply_inv_apply' t y
    have key := hv (t (t⁻¹ y) - t⁻¹ y) (sub_mem_commSpace t _)
    rw [polarBilin_apply_apply, hty] at key
    have h1 : polar Q (t v) y = polar Q v (t⁻¹ y) := by
      conv_lhs => rw [← hty]
      exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup ht v (t⁻¹ y)
    rw [polarBilin_apply_apply, QuadraticMap.polar_sub_left, h1]
    rw [QuadraticMap.polar_sub_left, polar_comm Q y v, polar_comm Q (t⁻¹ y) v] at key
    linear_combination -key

theorem commSpace_eq_orthogonal_fixSpace_of_mem {K : Type*} [Field K] {W : Type*}
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] {Q : QuadraticForm K W}
    (hQ : Q.polarBilin.Nondegenerate) {t : W ≃ₗ[K] W} (ht : t ∈ orthogonalGroup Q) :
    commSpace t = LinearMap.BilinForm.orthogonal Q.polarBilin (fixSpace t) := by
  rw [fixSpace_eq_orthogonal_commSpace_of_mem hQ ht,
    LinearMap.BilinForm.orthogonal_orthogonal hQ (isRefl_polarBilin Q)]

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

theorem eq_one_or_eq_transvection_of_finrank_fixSpace [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ orthogonalGroup q)
    (hfix : finrank (ZMod 2) V - 1 ≤ finrank (ZMod 2) (fixSpace t)) :
    t = 1 ∨ ∃ c : V, q c = 1 ∧ (∀ v, t v = v + polar q v c • c) ∧
      commSpace t = (ZMod 2) ∙ c ∧ t = CFSG.ClassicalGroups.Orthogonal.reflect q c := by
  by_cases h1 : t = 1
  · exact Or.inl h1
  right
  have hdim := finrank_commSpace_add_finrank_fixSpace t
  have hone := one_le_finrank_commSpace h1
  have hfin1 : finrank (ZMod 2) (commSpace t) = 1 := by omega
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, t v₀ ≠ v₀ := by
    by_contra! h
    exact h1 (eq_one_of_forall_apply_eq h)
  set c := t v₀ - v₀ with hc
  have hc0 : c ≠ 0 := sub_ne_zero.mpr hv₀
  have hspan : commSpace t = (ZMod 2) ∙ c := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_singleton_le_iff_mem]
      exact sub_mem_commSpace t v₀
    · rw [finrank_span_singleton hc0, hfin1]
  have hfixc : fixSpace t = LinearMap.BilinForm.orthogonal q.polarBilin ((ZMod 2) ∙ c) := by
    rw [fixSpace_eq_orthogonal_commSpace_of_mem hq ht, hspan]
  have hmemfix : ∀ v, v ∈ fixSpace t ↔ polar q v c = 0 := by
    intro v
    rw [hfixc, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h
      have := h c (Submodule.mem_span_singleton_self c)
      rwa [polarBilin_apply_apply, polar_comm] at this
    · intro h n hn
      obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hn
      rw [polarBilin_apply_apply, polar_smul_left, polar_comm, h, smul_zero]
  have hformula : ∀ v, t v = v + polar q v c • c := by
    intro v
    have hmem : t v - v ∈ (ZMod 2) ∙ c := hspan ▸ sub_mem_commSpace t v
    rcases zmod2_eq_zero_or_eq_one (polar q v c) with h | h
    · rw [mem_fixSpace.mp ((hmemfix v).mpr h), h, zero_smul, add_zero]
    · have hv : t v ≠ v := fun h' => by
        have := (hmemfix v).mp (mem_fixSpace.mpr h')
        rw [h] at this
        exact one_ne_zero this
      rcases mem_span_singleton_iff.mp hmem with h0 | h0
      · exact absurd (sub_eq_zero.mp h0) hv
      · rw [h, one_smul, ← h0]
        abel
  have hqc : q c = 1 := by
    obtain ⟨y, hy⟩ := CFSG.ClassicalGroups.Orthogonal.exists_polar_ne_zero hq hc0
    have hy1 : polar q y c = 1 := by
      rw [polar_comm]
      exact zmod2_eq_one_of_ne_zero hy
    have h2 := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup ht y
    rw [hformula y, hy1, one_smul, map_add_eq, hy1] at h2
    have h3 : q c + 1 = 0 := by linear_combination h2
    rw [eq_neg_of_add_eq_zero_left h3]
    rfl
  refine ⟨c, hqc, hformula, hspan, ?_⟩
  ext v
  rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply (by rw [hqc]; exact one_ne_zero), hqc,
    div_one, hformula, polar_comm, vec_sub]

theorem eq_one_of_fix_orthogonal_of_map_eq_zero [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) {a : V} (ha : q a = 0) {t : V ≃ₗ[ZMod 2] V}
    (ht : t ∈ orthogonalGroup q) (hfix : ∀ x, polar q a x = 0 → t x = x) : t = 1 := by
  by_cases ha0 : a = 0
  · subst ha0
    exact eq_one_of_forall_apply_eq fun x => hfix x (polar_zero_left q x)
  have hle : LinearMap.BilinForm.orthogonal q.polarBilin ((ZMod 2) ∙ a) ≤ fixSpace t := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx
    have := hx a (Submodule.mem_span_singleton_self a)
    rw [polarBilin_apply_apply] at this
    exact mem_fixSpace.mpr (hfix x this)
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hq, finrank_span_singleton ha0] at h1
  rcases eq_one_or_eq_transvection_of_finrank_fixSpace hq ht h1 with h | ⟨c, hqc, hform, -, -⟩
  · exact h
  · exfalso
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero] at hqc
      exact zero_ne_one hqc
    have hcperp : ∀ x, polar q a x = 0 → polar q x c = 0 := by
      intro x hx
      have h2 := hform x
      rw [hfix x hx, left_eq_add, smul_eq_zero] at h2
      exact h2.resolve_right hc0
    have hcmem : c ∈ (ZMod 2) ∙ a := by
      rw [← LinearMap.BilinForm.orthogonal_orthogonal hq (isRefl_polarBilin q)
        ((ZMod 2) ∙ a), LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at hn
      have := hn a (Submodule.mem_span_singleton_self a)
      rw [polarBilin_apply_apply] at this ⊢
      exact hcperp n this
    rcases mem_span_singleton_iff.mp hcmem with h | h
    · exact hc0 h
    · rw [h, ha] at hqc
      exact zero_ne_one hqc

theorem map_add_of_mem_commSpace {x : V ≃ₗ[ZMod 2] V} (hx : x ∈ orthogonalGroup q)
    (hxx : x * x = 1) {u v : V} (hu : u ∈ commSpace x) (hv : v ∈ commSpace x) :
    q (u + v) = q u + q v := by
  rw [map_add_eq, polar_commSpace_eq_zero hx hxx hu hv, add_zero]

theorem commSpace_dichotomy [FiniteDimensional (ZMod 2) V] {x : V ≃ₗ[ZMod 2] V}
    (hx : x ∈ orthogonalGroup q) (hxx : x * x = 1) :
    (∀ v ∈ commSpace x, q v = 0) ∨
      ∃ H : Submodule (ZMod 2) V, H ≤ commSpace x ∧
        finrank (ZMod 2) H + 1 = finrank (ZMod 2) (commSpace x) ∧
        ∀ v ∈ commSpace x, (q v = 0 ↔ v ∈ H) := by
  by_cases h0 : ∀ v ∈ commSpace x, q v = 0
  · exact Or.inl h0
  right
  push Not at h0
  obtain ⟨v₀, hv₀, hqv₀⟩ := h0
  let φ : commSpace x →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun v => q v
      map_add' := fun u v => map_add_of_mem_commSpace hx hxx u.2 v.2
      map_smul' := fun c v => by
        simp only [SetLike.val_smul, RingHom.id_apply, smul_eq_mul]
        exact map_smul_zmod2 q c v }
  have hφ : ∀ v : commSpace x, φ v = q v := fun v => rfl
  have hsurj : LinearMap.range φ = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
    · exact ⟨0, map_zero φ⟩
    · exact ⟨⟨v₀, hv₀⟩, by rw [hφ]; exact zmod2_eq_one_of_ne_zero hqv₀⟩
  refine ⟨(LinearMap.ker φ).map (commSpace x).subtype, Submodule.map_subtype_le _ _, ?_, ?_⟩
  · have h := LinearMap.finrank_range_add_finrank_ker φ
    rw [hsurj, finrank_top, finrank_self] at h
    rw [Submodule.finrank_map_subtype_eq]
    omega
  · intro v hv
    constructor
    · intro hqv
      exact ⟨⟨v, hv⟩, (show φ ⟨v, hv⟩ = 0 from hqv), rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact (show φ w = 0 from hw)

theorem eq_transvection_of_anisotropic_commSpace [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) {x : V ≃ₗ[ZMod 2] V} (hx : x ∈ orthogonalGroup q)
    (hxx : x * x = 1) (hx1 : x ≠ 1) (hanis : ∀ v ∈ commSpace x, q v = 0 → v = 0) :
    finrank (ZMod 2) (commSpace x) = 1 ∧ ∃ c : V, q c = 1 ∧ (∀ v, x v = v + polar q v c • c) ∧
      commSpace x = (ZMod 2) ∙ c ∧ x = CFSG.ClassicalGroups.Orthogonal.reflect q c := by
  have hone := one_le_finrank_commSpace hx1
  have hfin : finrank (ZMod 2) (commSpace x) = 1 := by
    rcases commSpace_dichotomy hx hxx with h | ⟨H, hH, hdim, hiff⟩
    · have hbot : commSpace x = ⊥ := by
        rw [eq_bot_iff]
        intro v hv
        exact (Submodule.mem_bot _).mpr (hanis v hv (h v hv))
      rw [hbot, finrank_bot] at hone
      omega
    · have hHbot : H = ⊥ := by
        rw [eq_bot_iff]
        intro v hv
        exact (Submodule.mem_bot _).mpr (hanis v (hH hv) ((hiff v (hH hv)).mpr hv))
      rw [hHbot, finrank_bot] at hdim
      omega
  refine ⟨hfin, ?_⟩
  have hdim := finrank_commSpace_add_finrank_fixSpace x
  rcases eq_one_or_eq_transvection_of_finrank_fixSpace hq hx (by omega) with h | h
  · exact absurd h hx1
  · exact h

theorem existsUnique_singular_of_isTypeC [FiniteDimensional (ZMod 2) V] {x : V ≃ₗ[ZMod 2] V}
    (hx : IsTypeC q x 2) : ∃! v : V, v ∈ commSpace x ∧ v ≠ 0 ∧ q v = 0 := by
  obtain ⟨hxO, -, hxx, hdim2, -, w, hw, hqw⟩ := hx
  have hxO' : x ∈ orthogonalGroup q := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hxO
  rcases commSpace_dichotomy hxO' hxx with h | ⟨H, hH, hdim, hiff⟩
  · exact absurd (h w hw) hqw
  have hH1 : finrank (ZMod 2) H = 1 := by omega
  obtain ⟨h, hh0, hhspan⟩ := finrank_eq_one_iff'.mp hH1
  have hmemH : ∀ v, v ∈ H ↔ v = 0 ∨ v = (h : V) := by
    intro v
    constructor
    · intro hv
      obtain ⟨c, hc⟩ := hhspan ⟨v, hv⟩
      have hc' : c • (h : V) = v := congrArg Subtype.val hc
      rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
      · rw [zero_smul] at hc'
        exact Or.inl hc'.symm
      · rw [one_smul] at hc'
        exact Or.inr hc'.symm
    · rintro (rfl | rfl)
      · exact H.zero_mem
      · exact h.2
  have hh0' : (h : V) ≠ 0 := fun h' => hh0 (Subtype.ext h')
  refine ⟨h, ⟨hH h.2, hh0', (hiff h (hH h.2)).mpr h.2⟩, ?_⟩
  rintro v ⟨hv, hv0, hqv⟩
  rcases (hmemH v).mp ((hiff v hv).mp hqv) with h' | h'
  · exact absurd h' hv0
  · exact h'

end CFSG.LargeExtraspecial
