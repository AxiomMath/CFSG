module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryRigidity
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailRootData

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin Module Submodule
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction (Points pointMk)

variable {K : Type*} [Field K] {A : Type*} [AddCommGroup A] [Module K A] {r : ℕ}

section Pairing

theorem polarOrtho_span_singleton_iff_polar {V : Type*} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {a b : V} :
    PolarOrtho Q (K ∙ a) (K ∙ b) ↔ polar Q a b = 0 := by
  refine ⟨fun h => h a (mem_span_singleton_self a) b (mem_span_singleton_self b),
    fun h x hx y hy => ?_⟩
  obtain ⟨s, rfl⟩ := mem_span_singleton.1 hx
  obtain ⟨t, rfl⟩ := mem_span_singleton.1 hy
  rw [polar_smul_left, polar_smul_right, h, smul_zero, smul_zero]

theorem polar_fintype_sum_left {ι : Type*} [Fintype ι] (Q : QuadraticForm K A) (w : ι → A)
    (v : A) : polar Q (∑ i, w i) v = ∑ i, polar Q (w i) v := by
  have := map_sum ((polarBilin Q).flip v) w Finset.univ
  simpa only [LinearMap.flip_apply, polarBilin_apply_apply] using this

theorem polar_fintype_sum_right {ι : Type*} [Fintype ι] (Q : QuadraticForm K A) (v : A)
    (w : ι → A) : polar Q v (∑ i, w i) = ∑ i, polar Q v (w i) := by
  have := map_sum (polarBilin Q v) w Finset.univ
  simpa only [polarBilin_apply_apply] using this

theorem polar_splitScale (c : K) (u v : Fin r ⊕ Fin r → K) :
    polar (quadPlus r K) (splitScale r K c u) (splitScale r K c v) =
      c * polar (quadPlus r K) u v := by
  rw [polar_quadPlus, polar_quadPlus, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [splitScale_inl, splitScale_inl, splitScale_inr, splitScale_inr]
  ring

end Pairing

section Identity

variable [FiniteDimensional K A] {q₁ q₂ : QuadraticForm K A} {c : K} {F : A → A}
  (φ : Points (quadTail r q₁) ≃ Points (quadTail r q₂))
  (hφ : ∀ L M : Points (quadTail r q₁),
    PolarOrtho (quadTail r q₁) L.val M.val ↔ PolarOrtho (quadTail r q₂) (φ L).val (φ M).val)
  (hφF : ∀ (v : (Fin r ⊕ Fin r → K) × A) (hv0 : v ≠ 0) (hv : quadTail r q₁ v = 0),
    (φ (pointMk (Q := quadTail r q₁) v hv0 hv)).val = K ∙ (splitScale r K c v.1, F v.2))
include hφ hφF

omit [FiniteDimensional K A] in
theorem polar_map_eq (hr : 2 ≤ r) (a b : A) : polar q₂ (F a) (F b) = c * polar q₁ a b := by
  set i₀ : Fin r := ⟨0, by omega⟩
  set i₁ : Fin r := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := Fin.ne_of_val_ne (by simp [i₀, i₁])
  set C := -polar q₁ a b with hC
  set u : Fin r ⊕ Fin r → K := Pi.single (Sum.inl i₀) 1 - q₁ a • Pi.single (Sum.inr i₀) 1
    with hu
  set v : Fin r ⊕ Fin r → K := C • Pi.single (Sum.inr i₀) 1 + Pi.single (Sum.inl i₁) 1 -
    q₁ b • Pi.single (Sum.inr i₁) 1 with hv
  have hQu : quadPlus r K u = -q₁ a := by
    rw [quadPlus_apply, Finset.sum_eq_single i₀]
    · simp [hu]
    · intro k _ hk
      simp [hu, hk]
    · simp
  have hQv : quadPlus r K v = -q₁ b := by
    rw [quadPlus_apply, Finset.sum_eq_single i₁]
    · simp [hv, h01]
    · intro k _ hk
      simp [hv, hk]
    · simp
  have huv : polar (quadPlus r K) u v = C := by
    rw [polar_quadPlus, Finset.sum_eq_single i₀]
    · simp [hu, hv, h01]
    · intro k _ hk
      simp [hu, hv, hk]
    · simp
  have hx : quadTail r q₁ (u, a) = 0 := by rw [quadTail_apply, hQu]; ring
  have hy : quadTail r q₁ (v, b) = 0 := by rw [quadTail_apply, hQv]; ring
  have hx0 : ((u, a) : (Fin r ⊕ Fin r → K) × A) ≠ 0 := fun h => by
    have := congrFun (congrArg Prod.fst h) (Sum.inl i₀)
    simp [hu] at this
  have hy0 : ((v, b) : (Fin r ⊕ Fin r → K) × A) ≠ 0 := fun h => by
    have := congrFun (congrArg Prod.fst h) (Sum.inl i₁)
    simp [hv] at this
  have horth : polar (quadTail r q₁) (u, a) (v, b) = 0 := by
    rw [polar_quadTail]
    dsimp only
    rw [huv, hC, neg_add_cancel]
  have h := (hφ (pointMk (Q := quadTail r q₁) (u, a) hx0 hx)
    (pointMk (Q := quadTail r q₁) (v, b) hy0 hy)).1
    (polarOrtho_span_singleton_iff_polar.2 horth)
  rw [hφF, hφF, polarOrtho_span_singleton_iff_polar, polar_quadTail] at h
  dsimp only at h
  rw [polar_splitScale, huv, hC] at h
  linear_combination h

end Identity

theorem orthogonal_geometry_tail_linear_rigidity {K : Type*} [Field K] {A : Type*}
    [AddCommGroup A] [Module K A] [FiniteDimensional K A] {r : ℕ} (hr : 2 ≤ r)
    {q₁ q₂ : QuadraticForm K A} (hreg₁ : (polarBilin q₁).Nondegenerate)
    (hreg₂ : (polarBilin q₂).Nondegenerate) {c : K} (hc : c ≠ 0) {F : A → A}
    (hFq : ∀ a, q₂ (F a) = c * q₁ a)
    (φ : Points (quadTail r q₁) ≃ Points (quadTail r q₂))
    (hφ : ∀ L M : Points (quadTail r q₁),
      PolarOrtho (quadTail r q₁) L.val M.val ↔ PolarOrtho (quadTail r q₂) (φ L).val (φ M).val)
    (hφF : ∀ (v : (Fin r ⊕ Fin r → K) × A) (hv0 : v ≠ 0) (hv : quadTail r q₁ v = 0),
      (φ (pointMk (Q := quadTail r q₁) v hv0 hv)).val = K ∙ (splitScale r K c v.1, F v.2)) :
    ∃ f : A ≃ₗ[K] A, ⇑f = F ∧ (∀ a b, polar q₂ (F a) (F b) = c * polar q₁ a b) ∧
      ∃ g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A),
        (∀ v, g v = (splitScale r K c v.1, F v.2)) ∧
        ∀ v, quadTail r q₂ (g v) = c * quadTail r q₁ v := by
  have hpol : ∀ a b, polar q₂ (F a) (F b) = c * polar q₁ a b := polar_map_eq φ hφ hφF hr
  set e := Module.finBasis K A
  have hli : LinearIndependent K (F ∘ e) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hz : ∀ j, polar q₁ (∑ k, g k • e k) (e j) = 0 := fun j => by
      have h := congrArg (fun w => polar q₂ w (F (e j))) hg
      simp only [Function.comp_apply, polar_zero_left] at h
      rw [polar_fintype_sum_left] at h
      simp only [polar_smul_left_eq, hpol] at h
      rw [polar_fintype_sum_left]
      simp only [polar_smul_left_eq]
      have : c * ∑ k, g k * polar q₁ (e k) (e j) = 0 := by
        rw [Finset.mul_sum]
        rw [← h]
        exact Finset.sum_congr rfl fun k _ => by ring
      exact (mul_eq_zero.1 this).resolve_left hc
    have h0 : ∑ k, g k • e k = 0 := eq_zero_of_polar_eq_zero hreg₁ fun z => by
      rw [← e.sum_repr z, polar_fintype_sum_right]
      exact Finset.sum_eq_zero fun j _ => by rw [polar_smul_right_eq, hz j, mul_zero]
    exact (Fintype.linearIndependent_iff.1 e.linearIndependent) g h0 i
  have hspan : span K (Set.range (F ∘ e)) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin])
  have hzero : ∀ d : A, (∀ z, polar q₂ d (F z) = 0) → d = 0 := fun d hd =>
    eq_zero_of_polar_eq_zero hreg₂ fun w => by
      have hle : span K (Set.range (F ∘ e)) ≤ LinearMap.ker (polarBilin q₂ d) := by
        rw [span_le]
        rintro _ ⟨j, rfl⟩
        exact hd (e j)
      have hw : w ∈ LinearMap.ker (polarBilin q₂ d) := hle (by rw [hspan]; trivial)
      simpa using hw
  have hadd : ∀ a b, F (a + b) = F a + F b := fun a b => by
    rw [← sub_eq_zero, sub_add_eq_sub_sub]
    refine hzero _ fun z => ?_
    rw [polar_sub_left, polar_sub_left, hpol, hpol, hpol, polar_add_left]
    ring
  have hsmul : ∀ (t : K) a, F (t • a) = t • F a := fun t a => by
    rw [← sub_eq_zero]
    refine hzero _ fun z => ?_
    rw [polar_sub_left, polar_smul_left_eq, hpol, hpol, polar_smul_left_eq]
    ring
  set fl : A →ₗ[K] A := { toFun := F, map_add' := hadd, map_smul' := hsmul } with hfl
  have hinj : Function.Injective fl := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    refine eq_zero_of_polar_eq_zero hreg₁ fun z => ?_
    have h := hpol a z
    rw [show F a = fl a from rfl, ha, polar_zero_left] at h
    exact ((mul_eq_zero.1 h.symm).resolve_left hc)
  set f := LinearEquiv.ofBijective fl ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
  have hDD : ∀ (s t : K), s * t = 1 → ∀ w : Fin r ⊕ Fin r → K,
      splitScale r K s (splitScale r K t w) = w := fun s t hst w => funext fun x => by
    rcases x with i | i
    · simp
    · simp only [splitScale_inr]
      rw [← mul_assoc, hst, one_mul]
  set D : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K) :=
    LinearEquiv.ofLinearMap (splitScale r K c) (splitScale r K c⁻¹)
      (LinearMap.ext fun w => hDD c c⁻¹ (mul_inv_cancel₀ hc) w)
      (LinearMap.ext fun w => hDD c⁻¹ c (inv_mul_cancel₀ hc) w)
  refine ⟨f, rfl, hpol, D.prodCongr f, fun v => rfl, fun v => ?_⟩
  change quadTail r q₂ (splitScale r K c v.1, F v.2) = c * quadTail r q₁ v
  rw [quadTail_apply, quadTail_apply, quadPlus_splitScale, hFq]
  ring

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
