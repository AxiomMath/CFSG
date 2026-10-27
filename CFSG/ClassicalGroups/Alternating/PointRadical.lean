module

public import CFSG.ClassicalGroups.Alternating.Generation
public import CFSG.ClassicalGroups.Alternating.SteinbergBQTransvectionConjugation

public section

namespace CFSG.ClassicalGroups.Alternating

open LinearMap (BilinForm)
open CFSG.LocalAnalysis.ComponentInitial

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {B : BilinForm K V}

@[expose] noncomputable def siegel (B : BilinForm K V) (hB : B.IsAlt) (v w : V) (c : K) :
    LinearMap.GeneralLinearGroup K V :=
  symplecticTransvection B hB (v + w) 1 * symplecticTransvection B hB w (-1) *
    symplecticTransvection B hB v (c - 1)

private theorem gl_ext' {g h : LinearMap.GeneralLinearGroup K V}
    (H : ∀ x, (g : V →ₗ[K] V) x = (h : V →ₗ[K] V) x) : g = h :=
  Units.ext (LinearMap.ext H)

private theorem flip_eq_zero (hB : B.IsAlt) {v w : V} (h : B v w = 0) : B w v = 0 := by
  rw [← hB.neg_eq v w, h, neg_zero]

theorem siegel_apply (hB : B.IsAlt) {v w : V} (hvw : B v w = 0) (c : K) (x : V) :
    (siegel B hB v w c : V →ₗ[K] V) x = x + B x v • w + B x w • v + (c * B x v) • v := by
  have hwv := flip_eq_zero hB hvw
  simp only [siegel, Units.val_mul, Module.End.mul_apply, symplecticTransvection_apply, map_add,
    map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hB.self_eq_zero, hvw, hwv]
  module

theorem siegel_mem_bilinIsometryGroup (hB : B.IsAlt) (v w : V) (c : K) :
    siegel B hB v w c ∈ bilinIsometryGroup B :=
  mul_mem (mul_mem (symplecticTransvection_mem_bilinIsometryGroup hB _ _)
    (symplecticTransvection_mem_bilinIsometryGroup hB _ _))
    (symplecticTransvection_mem_bilinIsometryGroup hB _ _)

theorem siegel_mul (hB : B.IsAlt) {v w w' : V} (hw : B v w = 0) (hw' : B v w' = 0) (c c' : K) :
    siegel B hB v w c * siegel B hB v w' c' = siegel B hB v (w + w') (c + c' + B w' w) := by
  have hww' : B v (w + w') = 0 := by rw [map_add, hw, hw', add_zero]
  have hwv := flip_eq_zero hB hw
  have hw'v := flip_eq_zero hB hw'
  refine gl_ext' fun x => ?_
  rw [Units.val_mul, Module.End.mul_apply, siegel_apply hB hw', siegel_apply hB hw,
    siegel_apply hB hww']
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hB.self_eq_zero, hw, hwv, hw'v]
  module

theorem siegel_zero (hB : B.IsAlt) (v : V) : siegel B hB v 0 0 = 1 :=
  gl_ext' fun x => by
    rw [siegel_apply hB (map_zero (B v))]
    simp

theorem siegel_inv (hB : B.IsAlt) {v w : V} (hw : B v w = 0) (c : K) :
    (siegel B hB v w c)⁻¹ = siegel B hB v (-w) (-c) := by
  have hnw : B v (-w) = 0 := by rw [map_neg, hw, neg_zero]
  refine inv_eq_of_mul_eq_one_right ?_
  rw [siegel_mul hB hw hnw]
  simp [hB.self_eq_zero, siegel_zero]

theorem siegel_form_apply_self (h2 : (2 : K) = 0) (hB : B.IsAlt) {u w : V} (huw : B u w = 0)
    (c : K) (y : V) : B y ((siegel B hB u w c : V →ₗ[K] V) y) = c * B y u ^ 2 := by
  rw [siegel_apply hB huw]
  simp only [map_add, map_smul, smul_eq_mul, hB.self_eq_zero]
  linear_combination (B y u * B y w) * h2

@[expose] def pointRadical (B : BilinForm K V) (hB : B.IsAlt) (v : V) :
    Subgroup (LinearMap.GeneralLinearGroup K V) where
  carrier := {g | ∃ w c, B v w = 0 ∧ siegel B hB v w c = g}
  one_mem' := ⟨0, 0, map_zero (B v), siegel_zero hB v⟩
  mul_mem' := by
    rintro _ _ ⟨w, c, hw, rfl⟩ ⟨w', c', hw', rfl⟩
    exact ⟨w + w', c + c' + B w' w, by rw [map_add, hw, hw', add_zero],
      (siegel_mul hB hw hw' c c').symm⟩
  inv_mem' := by
    rintro _ ⟨w, c, hw, rfl⟩
    exact ⟨-w, -c, by rw [map_neg, hw, neg_zero], (siegel_inv hB hw c).symm⟩

theorem mem_pointRadical {hB : B.IsAlt} {v : V} {g : LinearMap.GeneralLinearGroup K V} :
    g ∈ pointRadical B hB v ↔ ∃ w c, B v w = 0 ∧ siegel B hB v w c = g :=
  Iff.rfl

theorem siegel_mem_pointRadical (hB : B.IsAlt) {v w : V} (hw : B v w = 0) (c : K) :
    siegel B hB v w c ∈ pointRadical B hB v :=
  ⟨w, c, hw, rfl⟩

theorem pointRadical_le_bilinIsometryGroup (hB : B.IsAlt) (v : V) :
    pointRadical B hB v ≤ bilinIsometryGroup B := by
  rintro _ ⟨w, c, -, rfl⟩
  exact siegel_mem_bilinIsometryGroup hB v w c

theorem symplecticTransvection_mem_pointRadical (hB : B.IsAlt) (v : V) (c : K) :
    symplecticTransvection B hB v c ∈ pointRadical B hB v := by
  refine ⟨0, c, map_zero (B v), gl_ext' fun x => ?_⟩
  rw [siegel_apply hB (map_zero (B v)), symplecticTransvection_apply]
  simp

theorem siegel_conj (hB : B.IsAlt) {g : LinearMap.GeneralLinearGroup K V}
    (hg : g ∈ bilinIsometryGroup B) (v w : V) (c : K) :
    g * siegel B hB v w c * g⁻¹ = siegel B hB ((g : V →ₗ[K] V) v) ((g : V →ₗ[K] V) w) c := by
  have hg' := mem_bilinIsometryGroup.mp hg
  have key : g * siegel B hB v w c * g⁻¹ =
      (g * symplecticTransvection B hB (v + w) 1 * g⁻¹) *
        (g * symplecticTransvection B hB w (-1) * g⁻¹) *
          (g * symplecticTransvection B hB v (c - 1) * g⁻¹) := by
    simp only [siegel]
    group
  rw [key, SteinbergBQ.symplecticTransvection_conj hB hg',
    SteinbergBQ.symplecticTransvection_conj hB hg', SteinbergBQ.symplecticTransvection_conj hB hg',
    map_add]
  rfl

theorem conj_mem_pointRadical (hB : B.IsAlt) {g : LinearMap.GeneralLinearGroup K V}
    (hg : g ∈ bilinIsometryGroup B) {v : V} {x : LinearMap.GeneralLinearGroup K V}
    (hx : x ∈ pointRadical B hB v) : g * x * g⁻¹ ∈ pointRadical B hB ((g : V →ₗ[K] V) v) := by
  obtain ⟨w, c, hw, rfl⟩ := hx
  rw [siegel_conj hB hg]
  exact siegel_mem_pointRadical hB (by rw [mem_bilinIsometryGroup.mp hg, hw]) c

theorem siegel_smul_left (hB : B.IsAlt) {v w : V} (hw : B v w = 0) (s c : K) :
    siegel B hB (s • v) w c = siegel B hB v (s • w) (s ^ 2 * c) := by
  have h1 : B (s • v) w = 0 := by rw [map_smul, LinearMap.smul_apply, hw, smul_zero]
  have h2 : B v (s • w) = 0 := by rw [map_smul, hw, smul_zero]
  refine gl_ext' fun x => ?_
  rw [siegel_apply hB h1, siegel_apply hB h2]
  simp only [map_smul, smul_eq_mul]
  module

private theorem pointRadical_le_smul (hB : B.IsAlt) {v : V} {s : K} (hs : s ≠ 0) :
    pointRadical B hB v ≤ pointRadical B hB (s • v) := by
  rintro _ ⟨w, c, hw, rfl⟩
  have hw' : B v (s⁻¹ • w) = 0 := by rw [map_smul, hw, smul_zero]
  refine ⟨s⁻¹ • w, s⁻¹ ^ 2 * c, ?_, ?_⟩
  · simp [hw]
  · rw [siegel_smul_left hB hw', smul_smul, mul_inv_cancel₀ hs, one_smul, ← mul_assoc, ← mul_pow,
      mul_inv_cancel₀ hs, one_pow, one_mul]

theorem pointRadical_smul (hB : B.IsAlt) {v : V} {s : K} (hs : s ≠ 0) :
    pointRadical B hB (s • v) = pointRadical B hB v := by
  refine le_antisymm ?_ (pointRadical_le_smul hB hs)
  have := pointRadical_le_smul hB (v := s • v) (inv_ne_zero hs)
  rwa [smul_smul, inv_mul_cancel₀ hs, one_smul] at this

theorem exists_mem_pointRadical_apply_eq (hB : B.IsAlt) {v u u' : V} (h : B u v = B u' v)
    (ht : B u v ≠ 0) : ∃ s ∈ pointRadical B hB v, (s : V →ₗ[K] V) u = u' := by
  have hw : B v ((B u v)⁻¹ • (u' - u)) = 0 := by
    rw [map_smul, map_sub, ← hB.neg_eq u v, ← hB.neg_eq u' v, ← h, sub_self, smul_zero]
  refine ⟨siegel B hB v ((B u v)⁻¹ • (u' - u)) (-(B u ((B u v)⁻¹ • (u' - u))) * (B u v)⁻¹),
    siegel_mem_pointRadical hB hw _, ?_⟩
  rw [siegel_apply hB hw, smul_smul, mul_inv_cancel₀ ht, one_smul, inv_mul_cancel_right₀ ht,
    neg_smul]
  abel

private theorem gl_inv_apply_apply' (g : LinearMap.GeneralLinearGroup K V) (x : V) :
    ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) ((g : V →ₗ[K] V) x) = x := by
  rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Module.End.one_apply]

theorem eq_one_of_mem_pointRadical_of_apply_eq (hB : B.IsAlt) {u v : V} (huv : B u v ≠ 0)
    {g : LinearMap.GeneralLinearGroup K V} (hg : g ∈ pointRadical B hB v)
    (hgu : (g : V →ₗ[K] V) u = u) : g = 1 := by
  obtain ⟨w, c, hw, rfl⟩ := hg
  have hfix := hgu
  rw [siegel_apply hB hw, add_assoc, add_assoc, add_eq_left] at hfix
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact huv (map_zero (B u))
  have hpw : B u v • w = -((B u w + c * B u v) • v) := by
    rw [add_smul]
    exact eq_neg_of_add_eq_zero_left hfix
  have hwv : w = (-((B u v)⁻¹ * (B u w + c * B u v))) • v := by
    calc w = (B u v)⁻¹ • (B u v • w) := by rw [smul_smul, inv_mul_cancel₀ huv, one_smul]
      _ = _ := by rw [hpw, smul_neg, smul_smul, neg_smul]
  obtain ⟨t, rfl⟩ : ∃ t : K, w = t • v := ⟨_, hwv⟩
  have hcoef : (B u v * t + t * B u v + c * B u v) • v = 0 := by
    simp only [map_smul, smul_eq_mul] at hfix
    rw [← hfix]
    module
  have h2tc : c = -(2 * t) := by
    have h1 := (smul_eq_zero.mp hcoef).resolve_right hv0
    have h3 : (2 * t + c) * B u v = 0 := by linear_combination h1
    linear_combination (mul_eq_zero.mp h3).resolve_right huv
  refine gl_ext' fun x => ?_
  rw [siegel_apply hB hw, h2tc, Units.val_one, Module.End.one_apply]
  simp only [map_smul, smul_eq_mul]
  module

theorem pointRadical_inf_eq_bot (hB : B.IsAlt) {u v : V} (huv : B u v ≠ 0) :
    pointRadical B hB v ⊓ pointRadical B hB u = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hgv, w', c', hw', hg⟩
  rw [Subgroup.mem_bot]
  refine eq_one_of_mem_pointRadical_of_apply_eq hB huv hgv ?_
  rw [← hg, siegel_apply hB hw', hB.self_eq_zero, hw']
  simp

theorem pointRadical_sup_eq_bilinIsometryGroup [FiniteDimensional K V] (hB : B.IsAlt)
    (hBn : B.Nondegenerate) {u v : V} (huv : B u v ≠ 0) :
    pointRadical B hB v ⊔ pointRadical B hB u = bilinIsometryGroup B := by
  have hX : pointRadical B hB v ⊔ pointRadical B hB u ≤ bilinIsometryGroup B :=
    sup_le (pointRadical_le_bilinIsometryGroup hB v) (pointRadical_le_bilinIsometryGroup hB u)
  refine le_antisymm hX ?_
  set X := pointRadical B hB v ⊔ pointRadical B hB u
  have key : ∀ a b : V, pointRadical B hB a ≤ X → pointRadical B hB b ≤ X → B b a ≠ 0 →
      ∀ d : V, B d a ≠ 0 → pointRadical B hB d ≤ X := by
    intro a b ha hb hba d hda
    have hs : B b a / B d a ≠ 0 := div_ne_zero hba hda
    have hd' : B b a = B ((B b a / B d a) • d) a := by
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hda]
    obtain ⟨g, hg, hgb⟩ := exists_mem_pointRadical_apply_eq hB hd' hba
    rw [← pointRadical_smul hB hs]
    intro y hy
    have hgO := pointRadical_le_bilinIsometryGroup hB a hg
    have h1 := conj_mem_pointRadical hB (inv_mem hgO) hy
    rw [← hgb, inv_inv, gl_inv_apply_apply'] at h1
    have hgX : g ∈ X := ha hg
    have hy' : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
    rw [hy']
    exact mul_mem (mul_mem hgX (hb h1)) (inv_mem hgX)
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact huv (map_zero (B u))
  have hvu : B v u ≠ 0 := by
    rw [← hB.neg_eq u v]
    exact neg_ne_zero.mpr huv
  have hLv : pointRadical B hB v ≤ X := le_sup_left
  have hLu : pointRadical B hB u ≤ X := le_sup_right
  have hall : ∀ a : V, pointRadical B hB a ≤ X := by
    intro a
    by_cases ha0 : a = 0
    · subst ha0
      rintro _ ⟨w, c, -, rfl⟩
      have h1 : siegel B hB 0 w c = 1 := gl_ext' fun x => by
        rw [siegel_apply hB (by simp)]
        simp
      rw [h1]
      exact one_mem _
    by_cases hav : B a v ≠ 0
    · exact key v u hLv hLu huv a hav
    by_cases hau : B a u ≠ 0
    · exact key u v hLu hLv hvu a hau
    obtain ⟨w, hvw, haw⟩ := alternating_common_nonorthogonal_vector hB hBn hv0 ha0
    have hwv : B w v ≠ 0 := by
      rw [← hB.neg_eq v w]
      exact neg_ne_zero.mpr hvw
    exact key w v (key v u hLv hLu huv w hwv) hLv hvw a haw
  rw [alternating_transvection_generation hB hBn, Subgroup.closure_le]
  rintro _ ⟨a, c, rfl⟩
  exact hall a (symplecticTransvection_mem_pointRadical hB a c)

theorem pointRadical_sup_zpowers_siegel [FiniteDimensional K V] (h2 : (2 : K) = 0)
    (hB : B.IsAlt) (hBn : B.Nondegenerate) {u v w : V} (huv : B u v ≠ 0) (huw : B u w = 0)
    {c : K} (hc : c ≠ 0) :
    pointRadical B hB v ⊔ Subgroup.zpowers (siegel B hB u w c) = bilinIsometryGroup B := by
  set x := siegel B hB u w c with hx
  have hxO : x ∈ bilinIsometryGroup B := siegel_mem_bilinIsometryGroup hB u w c
  refine le_antisymm (sup_le (pointRadical_le_bilinIsometryGroup hB v)
    (Subgroup.zpowers_le.mpr hxO)) ?_
  have hxv : B ((x : V →ₗ[K] V) v) v ≠ 0 := by
    have hval : B ((x : V →ₗ[K] V) v) v = -(c * B u v ^ 2) := by
      rw [hx, siegel_apply hB huw]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hB.self_eq_zero]
      rw [← hB.neg_eq u v, ← hB.neg_eq v w]
      linear_combination (B u v * B v w) * h2
    rw [hval]
    exact neg_ne_zero.mpr (mul_ne_zero hc (pow_ne_zero 2 huv))
  rw [← pointRadical_sup_eq_bilinIsometryGroup hB hBn hxv]
  refine sup_le le_sup_left fun y hy => ?_
  have h1 := conj_mem_pointRadical hB (inv_mem hxO) hy
  rw [inv_inv, gl_inv_apply_apply'] at h1
  have hxX : x ∈ pointRadical B hB v ⊔ Subgroup.zpowers x :=
    le_sup_right (a := pointRadical B hB v) (b := Subgroup.zpowers x) (Subgroup.mem_zpowers x)
  have hy' : y = x * (x⁻¹ * y * x) * x⁻¹ := by group
  rw [hy']
  exact mul_mem (mul_mem hxX (le_sup_left (b := Subgroup.zpowers x) h1)) (inv_mem hxX)

theorem apply_self_of_mem_pointRadical (hB : B.IsAlt) {v : V} {g : LinearMap.GeneralLinearGroup K V}
    (hg : g ∈ pointRadical B hB v) : (g : V →ₗ[K] V) v = v := by
  obtain ⟨w, c, hw, rfl⟩ := hg
  rw [siegel_apply hB hw, hB.self_eq_zero, hw]
  simp

theorem exists_mem_pointRadical_mul_eq (hB : B.IsAlt) {u v : V} (huv : B u v ≠ 0)
    {g : LinearMap.GeneralLinearGroup K V} (hg : g ∈ bilinIsometryGroup B)
    (hgv : (g : V →ₗ[K] V) v = v) :
    ∃ s ∈ pointRadical B hB v, ∃ h ∈ bilinIsometryGroup B, (h : V →ₗ[K] V) u = u ∧
      (h : V →ₗ[K] V) v = v ∧ g = s * h := by
  have hg' := mem_bilinIsometryGroup.mp hg
  have hgu : B u v = B ((g : V →ₗ[K] V) u) v := by rw [← hg' u v, hgv]
  obtain ⟨s, hs, hsu⟩ := exists_mem_pointRadical_apply_eq hB hgu huv
  have hsO := pointRadical_le_bilinIsometryGroup hB v hs
  have hsv := apply_self_of_mem_pointRadical hB hs
  refine ⟨s, hs, s⁻¹ * g, mul_mem (inv_mem hsO) hg, ?_, ?_, by group⟩
  · rw [Units.val_mul, Module.End.mul_apply, ← hsu, gl_inv_apply_apply']
  · rw [Units.val_mul, Module.End.mul_apply, hgv]
    conv_lhs => rw [← hsv]
    rw [gl_inv_apply_apply']

end CFSG.ClassicalGroups.Alternating
