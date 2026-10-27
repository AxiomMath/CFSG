module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.ShapeData
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLForm

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open Module CFSG.ComponentClassification.OutcomeLocal CFSG.LocalAnalysis.ComponentInitial

section Alt

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {f : LinearMap.BilinForm (ZMod 2) V}

theorem eq_form_of_tv_mem_bilin (hcomm : ∀ u v, f u v = f v u)
    (hnd : ∀ u, (∀ v, f u v = 0) → u = 0) {φ : Dual (ZMod 2) V} {a : V} (h : φ a = 0)
    (hφ : φ ≠ 0) (ha : a ≠ 0) (halt : f a a = 0) (hmem : tv φ a h ∈ bilinIsometryGroup f) :
    φ = f a := by
  obtain ⟨y, hy⟩ := exists_apply_eq_one hφ
  have key : ∀ x, f x a = φ x * f a y := by
    intro x
    have h1 := hmem x y
    simp only [tv_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, hy, halt, mul_zero, add_zero, one_mul] at h1
    generalize f x y = γ at h1
    generalize f x a = α at h1 ⊢
    generalize f a y = β at h1 ⊢
    generalize φ x = p at h1 ⊢
    revert α β γ p
    decide
  rcases zmod2_eq_zero_or_one (f a y) with h0 | h1
  · exfalso
    apply ha
    refine hnd a fun v => ?_
    rw [hcomm, key v, h0, mul_zero]
  · refine LinearMap.ext fun x => ?_
    rw [hcomm a x, key x, h1, mul_one]

theorem mem_bilinIsometryGroup_of_mem_normalizer (halt : ∀ v, f v v = 0)
    (hcomm : ∀ u v, f u v = f v u) (hnd : ∀ u, (∀ v, f u v = 0) → u = 0)
    {g : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (hg : g ∈ Subgroup.normalizer (bilinIsometryGroup f : Set _)) : g ∈ bilinIsometryGroup f := by
  have key : ∀ a : V, a ≠ 0 → ∀ y, f ((g : V →ₗ[ZMod 2] V) a) ((g : V →ₗ[ZMod 2] V) y) = f a y := by
    intro a ha y
    have hgg : ∀ v : V, ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
        ((g : V →ₗ[ZMod 2] V) v) = v := fun v => by
      change ((g⁻¹ * g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v = v
      rw [inv_mul_cancel]; rfl
    have hgg' : ∀ v : V, (g : V →ₗ[ZMod 2] V)
        (((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v) = v := fun v => by
      change ((g * g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v = v
      rw [mul_inv_cancel]; rfl
    have h' : ((f a) ∘ₗ ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V))
        ((g : V →ₗ[ZMod 2] V) a) = 0 := by
      rw [LinearMap.comp_apply, hgg]; exact halt a
    have hmem := tv_mem_bilinIsometryGroup hcomm (halt a)
    have hconj := (Subgroup.mem_normalizer_iff.mp hg _).mp hmem
    rw [conj_tv g (f a) a (halt a) h'] at hconj
    have hga : (g : V →ₗ[ZMod 2] V) a ≠ 0 := by
      intro h0
      apply ha
      have := congrArg ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) h0
      rwa [hgg, map_zero] at this
    have hfa : f a ≠ 0 := by
      intro h0
      exact ha (hnd a fun v => by rw [h0]; rfl)
    have hφ : ((f a) ∘ₗ ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)) ≠ 0 := by
      intro h0
      apply hfa
      refine LinearMap.ext fun v => ?_
      have := LinearMap.congr_fun h0 ((g : V →ₗ[ZMod 2] V) v)
      rw [LinearMap.comp_apply, hgg] at this
      exact this
    have heq := eq_form_of_tv_mem_bilin hcomm hnd h' hφ hga (halt _) hconj
    have := LinearMap.congr_fun heq ((g : V →ₗ[ZMod 2] V) y)
    rw [LinearMap.comp_apply, hgg] at this
    exact this.symm
  intro x y
  by_cases hx : x = 0
  · subst hx
    simp
  · exact key x hx y

end Alt

section Orth

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem eq_polar_of_tv_mem_orthGL (Q : QuadraticForm (ZMod 2) V)
    (hnd : ∀ u, (∀ v, QuadraticMap.polar Q u v = 0) → u = 0)
    {φ : Dual (ZMod 2) V} {a : V} (h : φ a = 0) (hφ : φ ≠ 0) (ha : a ≠ 0)
    (hmem : tv φ a h ∈ orthGL Q) : Q a = 1 ∧ ∀ x, φ x = QuadraticMap.polar Q a x := by
  have hQ : ∀ x, Q (((tv φ a h : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) x) = Q x := by
    intro x
    have := (TauCeti.QuadraticMap.mem_orthogonalGroup_iff (Q := Q)
      (f := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V (tv φ a h))).mp hmem x
    simpa [LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv] using this
  have hpol : ∀ x, QuadraticMap.polar Q a x = QuadraticMap.polar Q x a := fun x =>
    QuadraticMap.polar_comm Q a x
  obtain ⟨y, hy⟩ := exists_apply_eq_one hφ
  have hone : ∀ x, φ x = 1 → QuadraticMap.polar Q x a = Q a := by
    intro x hx
    have h1 := hQ x
    rw [tv_apply, QuadraticMap.map_add (⇑Q) x (φ x • a), QuadraticMap.map_smul,
      QuadraticMap.polar_smul_right, hx] at h1
    simp only [smul_eq_mul, one_mul, mul_one] at h1
    generalize QuadraticMap.polar Q x a = α at h1 ⊢
    generalize Q a = β at h1 ⊢
    generalize Q x = γ at h1
    revert α β γ
    decide
  have key : ∀ x, QuadraticMap.polar Q x a = φ x * Q a := by
    intro x
    rcases zmod2_eq_zero_or_one (φ x) with h0 | h1
    · rw [h0, zero_mul]
      have h2 := hone y hy
      have h3 : φ (x + y) = 1 := by rw [map_add, h0, hy, zero_add]
      have h4 := hone _ h3
      rw [QuadraticMap.polar_add_left Q x y a, h2] at h4
      generalize QuadraticMap.polar Q x a = α at h4 ⊢
      generalize Q a = β at h4
      revert α β
      decide
    · rw [h1, one_mul]; exact hone x h1
  have hQa : Q a = 1 := by
    rcases zmod2_eq_zero_or_one (Q a) with h0 | h1
    · exfalso
      apply ha
      refine hnd a fun v => ?_
      rw [hpol, key v, h0, mul_zero]
    · exact h1
  refine ⟨hQa, fun x => ?_⟩
  rw [hpol, key x, hQa, mul_one]

theorem tv_mem_orthGL (Q : QuadraticForm (ZMod 2) V) {a : V} (ha : Q a = 1)
    (h : QuadraticMap.polarBilin Q a a = 0) : tv (QuadraticMap.polarBilin Q a) a h ∈ orthGL Q := by
  rw [orthGL, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro x
  rw [LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv, tv_apply]
  rw [QuadraticMap.map_add (⇑Q) x _, QuadraticMap.map_smul, QuadraticMap.polar_smul_right, ha]
  simp only [smul_eq_mul, QuadraticMap.polarBilin_apply_apply, mul_one]
  rw [QuadraticMap.polar_comm Q x a]
  generalize QuadraticMap.polar Q a x = α
  generalize Q x = γ
  revert α γ
  decide

omit [AddCommGroup V] [Module (ZMod 2) V] in
theorem iff_of_injective_of_imp [Finite V] {P : V → Prop} (g : V → V) (hg : Function.Injective g)
    (h : ∀ v, P v → P (g v)) : ∀ v, P (g v) → P v := by
  classical
  let e : {v // P v} → {v // P v} := fun v => ⟨g v, h v v.2⟩
  have he : Function.Injective e := fun a b hab => Subtype.ext (hg (congrArg Subtype.val hab))
  have hs : Function.Surjective e := Finite.surjective_of_injective he
  intro v hv
  obtain ⟨w, hw⟩ := hs ⟨g v, hv⟩
  have : g w = g v := congrArg Subtype.val hw
  have := hg this
  rw [← this]
  exact w.2

theorem mem_orthGL_of_mem_normalizer [Finite V] (Q : QuadraticForm (ZMod 2) V)
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    {g : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (hg : g ∈ Subgroup.normalizer (orthGL Q : Set _)) : g ∈ orthGL Q := by
  have hnd' : ∀ u, (∀ v, QuadraticMap.polar Q u v = 0) → u = 0 := fun u hu => hnd.1 u hu
  have hgg : ∀ v : V, ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
      ((g : V →ₗ[ZMod 2] V) v) = v := fun v => by
    change ((g⁻¹ * g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v = v
    rw [inv_mul_cancel]; rfl
  have hinj : Function.Injective (g : V →ₗ[ZMod 2] V) := fun x y hxy => by
    have := congrArg ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) hxy
    rwa [hgg, hgg] at this
  have hone : ∀ v, Q v = 1 → Q ((g : V →ₗ[ZMod 2] V) v) = 1 := by
    intro a ha
    have hQ0 : Q 0 = 0 := QuadraticMap.map_zero Q
    have ha0 : a ≠ 0 := fun h0 => by rw [h0, hQ0] at ha; exact zero_ne_one ha
    have halt : QuadraticMap.polarBilin Q a a = 0 := by
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, ha]
      decide
    have h' : ((QuadraticMap.polarBilin Q a) ∘ₗ
        ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V))
        ((g : V →ₗ[ZMod 2] V) a) = 0 := by
      rw [LinearMap.comp_apply, hgg]; exact halt
    have hmem := tv_mem_orthGL Q ha halt
    have hconj := (Subgroup.mem_normalizer_iff.mp hg _).mp hmem
    rw [conj_tv g _ a halt h'] at hconj
    have hga : (g : V →ₗ[ZMod 2] V) a ≠ 0 := by
      intro h0
      apply ha0
      have := congrArg ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) h0
      rwa [hgg, map_zero] at this
    have hfa : QuadraticMap.polarBilin Q a ≠ 0 := by
      intro h0
      exact ha0 (hnd' a fun v => by
        rw [← QuadraticMap.polarBilin_apply_apply, h0]; rfl)
    have hφ : ((QuadraticMap.polarBilin Q a) ∘ₗ
        ((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)) ≠ 0 := by
      intro h0
      apply hfa
      refine LinearMap.ext fun v => ?_
      have := LinearMap.congr_fun h0 ((g : V →ₗ[ZMod 2] V) v)
      rw [LinearMap.comp_apply, hgg] at this
      exact this
    exact (eq_polar_of_tv_mem_orthGL Q hnd' h' hφ hga hconj).1
  have hboth := iff_of_injective_of_imp (P := fun v => Q v = 1) (g : V → V) hinj hone
  rw [orthGL, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro x
  rw [LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv]
  rcases zmod2_eq_zero_or_one (Q x) with h0 | h1
  · rw [h0]
    rcases zmod2_eq_zero_or_one (Q ((g : V →ₗ[ZMod 2] V) x)) with h0' | h1'
    · exact h0'
    · exact absurd (hboth x h1') (by rw [h0]; exact zero_ne_one)
  · rw [h1]; exact hone x h1

end Orth

end CFSG.HardMathSupport.Cooperstein.StructureLie
