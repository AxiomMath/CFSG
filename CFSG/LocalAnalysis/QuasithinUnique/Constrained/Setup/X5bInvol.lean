module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrderSupport
public import CFSG.LocalAnalysis.ComponentInitial.FourGroupOddUnitary
public import CFSG.LinearAlgebra.LinearGroups.UnitaryBasics

public section

namespace CFSG.QuasithinUnique.Setup.X5

open CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial

section Frame

variable {f : ℕ} {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem exists_frame (h : UnitaryFieldData 2 f K) [FiniteDimensional K V]
    (hdim : Module.finrank K V = 3) {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) {v : V} (hv0 : v ≠ 0) (hv : B v v = 0) :
    ∃ b u : V, B v b = 1 ∧ B b b = 0 ∧ B v u = 0 ∧ B b u = 0 ∧ B u u = 1 ∧
      ∀ x, x = (B b x) • v + (B v x) • b + (B u x) • u := by
  have hsymm : ∀ x y, B y x = h.bar (B x y) := fun x y => (hB.eq x y).symm
  obtain ⟨⟨b, hab, hbb⟩, hsplit⟩ := hermitian_hyperbolic_splitting h hB hBl hv0 hv
  obtain ⟨-, -, -, hWsep, hWdim⟩ := hsplit b hab hbb
  obtain ⟨e, he⟩ := h.exists_orthonormal_basis (hB.domRestrict _) hWsep
  have hpos : 0 < Module.finrank K ((Submodule.span K {v, b}).orthogonalBilin B) := by omega
  set u : V := (e ⟨0, hpos⟩ : V) with hu
  have huu : B u u = 1 := by
    have := he ⟨0, hpos⟩ ⟨0, hpos⟩
    rw [LinearMap.domRestrict₁₂_apply] at this
    simpa using this
  have hvu : B v u = 0 := (Submodule.mem_orthogonalBilin.mp (e ⟨0, hpos⟩).2) v
    (Submodule.subset_span (by simp))
  have hbu : B b u = 0 := (Submodule.mem_orthogonalBilin.mp (e ⟨0, hpos⟩).2) b
    (Submodule.subset_span (by simp))
  have hbv : B b v = 1 := by rw [hsymm, hab, map_one]
  have huv : B u v = 0 := by rw [hsymm, hvu, map_zero]
  have hub : B u b = 0 := by rw [hsymm, hbu, map_zero]
  have hli : LinearIndependent K ![v, b, u] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at hg
    have h1 := congrArg (B b) hg
    have h2 := congrArg (B v) hg
    have h3 := congrArg (B u) hg
    simp only [map_add, map_smul, smul_eq_mul, hbv, hbb, hbu, hab, hv, hvu, huv, hub, huu,
      map_zero] at h1 h2 h3
    intro i
    fin_cases i
    · simpa using h1
    · simpa using h2
    · simpa using h3
  have hspan : Submodule.span K (Set.range ![v, b, u]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp [hdim])
  refine ⟨b, u, hab, hbb, hvu, hbu, huu, fun x => ?_⟩
  set d : V := x - ((B b x) • v + (B v x) • b + (B u x) • u) with hd
  have hdv : B v d = 0 := by
    simp only [hd, map_sub, map_add, map_smul, smul_eq_mul, hv, hab, hvu]
    ring
  have hdb : B b d = 0 := by
    simp only [hd, map_sub, map_add, map_smul, smul_eq_mul, hbv, hbb, hbu]
    ring
  have hdu : B u d = 0 := by
    simp only [hd, map_sub, map_add, map_smul, smul_eq_mul, huv, hub, huu]
    ring
  have hall : ∀ y ∈ Submodule.span K (Set.range ![v, b, u]), B y d = 0 := by
    intro y hy
    refine Submodule.span_induction (fun z hz => ?_) (by simp) (fun y₁ y₂ _ _ h₁ h₂ => ?_)
      (fun c y₁ _ h₁ => ?_) hy
    · obtain ⟨i, rfl⟩ := hz
      fin_cases i
      · simpa using hdv
      · simpa using hdb
      · simpa using hdu
    · rw [map_add, LinearMap.add_apply, h₁, h₂, add_zero]
    · rw [map_smulₛₗ, LinearMap.smul_apply, h₁, smul_zero]
  have hd0 : d = 0 := by
    apply hBl
    intro y
    rw [hsymm, hall y (by rw [hspan]; exact Submodule.mem_top), map_zero]
  have : x - ((B b x) • v + (B v x) • b + (B u x) • u) = 0 := hd0
  exact sub_eq_zero.mp this

end Frame

section Involutions

variable {f : ℕ} {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem add_self_eq_zero_of_charTwo (h : UnitaryFieldData 2 f K) (x : V) : x + x = 0 := by
  have : CharP K 2 := h.charP
  rw [← two_smul K x, show (2 : K) = 0 from CharP.cast_eq_zero K 2, zero_smul]

theorem involution_form (h : UnitaryFieldData 2 f K) [FiniteDimensional K V]
    (hdim : Module.finrank K V = 3) {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) {t : LinearMap.GeneralLinearGroup K V}
    (ht : t ∈ sesqSpecialUnitaryGroup B) (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    ∃ v : V, v ≠ 0 ∧ B v v = 0 ∧ ∃ c : K, c ≠ 0 ∧ h.bar c = c ∧
      ∀ x, (t : V →ₗ[K] V) x = x + (c * B v x) • v := by
  have hsymm : ∀ x y, B y x = h.bar (B x y) := fun x y => (hB.eq x y).symm
  have hiso : ∀ x y, B ((t : V →ₗ[K] V) x) ((t : V →ₗ[K] V) y) = B x y :=
    mem_sesqUnitaryGroup.mp (sesqSpecialUnitaryGroup_le B ht)
  have hTT : ∀ x, (t : V →ₗ[K] V) ((t : V →ₗ[K] V) x) = x := fun x => by
    have := congrArg (fun u : LinearMap.GeneralLinearGroup K V => (u : V →ₗ[K] V) x) ht2
    simpa [Module.End.mul_apply] using this
  set N : V →ₗ[K] V := (t : V →ₗ[K] V) - LinearMap.id with hN
  have hNapp : ∀ x, N x = (t : V →ₗ[K] V) x - x := fun x => by simp [hN]
  have hNN : ∀ x, N (N x) = 0 := by
    intro x
    rw [hNapp, hNapp, map_sub, hTT]
    have h1 := add_self_eq_zero_of_charTwo (V := V) h x
    have h2 := add_self_eq_zero_of_charTwo (V := V) h ((t : V →ₗ[K] V) x)
    calc x - (t : V →ₗ[K] V) x - ((t : V →ₗ[K] V) x - x) = (x + x) - ((t : V →ₗ[K] V) x +
        (t : V →ₗ[K] V) x) := by abel
      _ = 0 := by rw [h1, h2, sub_zero]
  have hN0 : N ≠ 0 := by
    intro h0
    apply ht1
    apply Units.ext
    apply LinearMap.ext
    intro x
    have := LinearMap.congr_fun h0 x
    rw [hNapp] at this
    simpa [sub_eq_zero] using this
  have hrk : LinearMap.range N ≤ LinearMap.ker N := by
    rintro _ ⟨x, rfl⟩
    exact LinearMap.mem_ker.mpr (hNN x)
  have hrn := LinearMap.finrank_range_add_finrank_ker N
  have hle := Submodule.finrank_mono hrk
  have hr0 : Module.finrank K (LinearMap.range N) ≠ 0 := by
    intro h0
    apply hN0
    rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0
    exact h0
  have hr1 : Module.finrank K (LinearMap.range N) = 1 := by omega
  have hk2 : Module.finrank K (LinearMap.ker N) = 2 := by omega
  obtain ⟨⟨v, hvr⟩, hv0', hvspan⟩ := finrank_eq_one_iff'.mp hr1
  have hv0 : v ≠ 0 := fun h0 => hv0' (Subtype.ext h0)
  obtain ⟨x₀, hx₀⟩ := hvr
  have hker_le : LinearMap.ker N ≤ LinearMap.ker (B v) := by
    intro y hy
    have hty : (t : V →ₗ[K] V) y = y := by
      have := LinearMap.mem_ker.mp hy
      rw [hNapp, sub_eq_zero] at this
      exact this
    rw [LinearMap.mem_ker, ← hx₀, hNapp, map_sub, LinearMap.sub_apply]
    have := hiso x₀ y
    rw [hty] at this
    rw [this, sub_self]
  have hBv_ne : B v ≠ 0 := fun h0 => hv0 (hBl v fun y => by rw [h0]; rfl)
  obtain ⟨x₁, hx₁⟩ : ∃ x₁, B v x₁ = 1 := by
    by_contra hcon
    push Not at hcon
    apply hBv_ne
    ext y
    by_contra hy
    obtain ⟨x, hx⟩ : ∃ x, B v x ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hBv_ne (LinearMap.ext hall)
    exact hcon ((B v x)⁻¹ • x) (by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hx])
  have hBvrange : LinearMap.range (B v) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    exact ⟨c • x₁, by rw [map_smul, hx₁, smul_eq_mul, mul_one]⟩
  have hker2 : Module.finrank K (LinearMap.ker (B v)) = 2 := by
    have := LinearMap.finrank_range_add_finrank_ker (B v)
    rw [hBvrange, finrank_top, Module.finrank_self] at this
    omega
  have hker : LinearMap.ker N = LinearMap.ker (B v) :=
    Submodule.eq_of_le_of_finrank_eq hker_le (by rw [hk2, hker2])
  have hvv : B v v = 0 := by
    have : v ∈ LinearMap.ker N := hrk ⟨x₀, hx₀⟩
    rw [hker] at this
    exact this
  obtain ⟨c₀, hc₀⟩ := hvspan ⟨N x₁, ⟨x₁, rfl⟩⟩
  have hc₀' : N x₁ = c₀ • v := (congrArg Subtype.val hc₀).symm
  have hform : ∀ x, N x = (c₀ * B v x) • v := by
    intro x
    have hmem : x - (B v x) • x₁ ∈ LinearMap.ker (B v) := by
      rw [LinearMap.mem_ker, map_sub, map_smul, hx₁, smul_eq_mul, mul_one, sub_self]
    rw [← hker, LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] at hmem
    rw [hmem, hc₀', smul_smul, mul_comm]
  have hc0 : c₀ ≠ 0 := by
    intro h0
    apply hN0
    ext x
    rw [hform, h0]
    simp
  have hbar : h.bar c₀ = c₀ := by
    have h1 := hiso x₁ x₁
    have hT : (t : V →ₗ[K] V) x₁ = x₁ + c₀ • v := by
      have := hform x₁
      rw [hNapp, hx₁, mul_one] at this
      exact sub_eq_iff_eq_add'.mp this
    rw [hT] at h1
    have hx1v : B x₁ v = 1 := by rw [hsymm, hx₁, map_one]
    simp only [map_add, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, hvv, hx₁, hx1v, mul_zero, add_zero, mul_one] at h1
    have h2 : c₀ + h.bar c₀ = 0 := by linear_combination h1
    have : CharP K 2 := h.charP
    have h3 : h.bar c₀ = -c₀ := by linear_combination h2
    rw [h3, CharTwo.neg_eq]
  refine ⟨v, hv0, hvv, c₀, hc0, hbar, fun x => ?_⟩
  have := hform x
  rw [hNapp] at this
  exact sub_eq_iff_eq_add'.mp this

end Involutions

section Transitivity

variable {f : ℕ} {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem scaling_isometry (h : UnitaryFieldData 2 f K) {B : V →ₛₗ[h.bar] V →ₗ[K] K}
    (hB : B.IsSymm) {u : V} (huu : B u u = 1) {μ : K} (hμ : h.bar μ * μ = 1) (x y : V) :
    B (x + ((μ - 1) * B u x) • u) (y + ((μ - 1) * B u y) • u) = B x y := by
  have hsymm : ∀ x y, B y x = h.bar (B x y) := fun x y => (hB.eq x y).symm
  simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, huu,
    map_mul, map_sub, map_one, hsymm u x, RingHom.id_apply]
  linear_combination (h.bar (B u x) * B u y) * hμ

theorem exists_mem_special_unitary_apply_eq (h : UnitaryFieldData 2 f K) [FiniteDimensional K V]
    (hdim : Module.finrank K V = 3) {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) {v w : V} (hv0 : v ≠ 0) (hv : B v v = 0) (hw0 : w ≠ 0)
    (hw : B w w = 0) :
    ∃ g ∈ sesqSpecialUnitaryGroup B, ((g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) v = w := by
  have hsymm : ∀ x y, B y x = h.bar (B x y) := fun x y => (hB.eq x y).symm
  obtain ⟨b, u, hvb, hbb, hvu, hbu, huu, hexp⟩ := exists_frame h hdim hB hBl hv0 hv
  obtain ⟨b', u', hwb', hb'b', hwu', hb'u', hu'u', -⟩ := exists_frame h hdim hB hBl hw0 hw
  have hbv : B b v = 1 := by rw [hsymm, hvb, map_one]
  have huv : B u v = 0 := by rw [hsymm, hvu, map_zero]
  have hb'w : B b' w = 1 := by rw [hsymm, hwb', map_one]
  have hu'w : B u' w = 0 := by rw [hsymm, hwu', map_zero]
  have hu'b' : B u' b' = 0 := by rw [hsymm, hb'u', map_zero]
  let φ₀ : V →ₗ[K] V := (B b).smulRight w + (B v).smulRight b' + (B u).smulRight u'
  have hφ₀ : ∀ x, φ₀ x = (B b x) • w + (B v x) • b' + (B u x) • u' := fun x => rfl
  have hBxy : ∀ x y, B x y = h.bar (B b x) * B v y + h.bar (B v x) * B b y +
      h.bar (B u x) * B u y := by
    intro x y
    conv_lhs => rw [hexp x]
    simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
  have hiso₀ : ∀ x y, B (φ₀ x) (φ₀ y) = B x y := by
    intro x y
    rw [hφ₀, hφ₀, hBxy x y]
    simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hw,
      hwb', hwu', hb'w, hb'b', hb'u', hu'w, hu'b', hu'u', RingHom.id_apply]
    ring
  have hφ₀v : φ₀ v = w := by
    rw [hφ₀, hbv, hv, huv]
    simp
  obtain ⟨e, he⟩ := h.exists_orthonormal_basis hB hBl
  have hnorm := norm_det_of_isometry h e (mem_orthonormalFrames.mpr he) hiso₀
  set d := LinearMap.det φ₀ with hd
  have hd0 : d ≠ 0 := by
    intro h0
    rw [h0] at hnorm
    simp [UnitaryFieldData.norm] at hnorm
  have hμ : h.bar d⁻¹ * d⁻¹ = 1 := by
    have : d * h.bar d = 1 := hnorm
    rw [map_inv₀, ← mul_inv, mul_comm (h.bar d) d, this, inv_one]
  let τ : V →ₗ[K] V := LinearMap.transvection (((d⁻¹ - 1)) • B u') u'
  have hτ : ∀ x, τ x = x + ((d⁻¹ - 1) * B u' x) • u' := fun x => by
    simp [τ, LinearMap.transvection.apply]
  have hisoτ : ∀ x y, B (τ x) (τ y) = B x y := fun x y => by
    rw [hτ, hτ]
    exact scaling_isometry h hB hu'u' hμ x y
  have hdetτ : LinearMap.det τ = d⁻¹ := by
    rw [LinearMap.transvection.det]
    simp [hu'u']
  have hiso : ∀ x y, B ((τ ∘ₗ φ₀) x) ((τ ∘ₗ φ₀) y) = B x y := fun x y => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hisoτ, hiso₀]
  refine ⟨((isometryUnit hBl hiso : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup K V),
    mem_sesqSpecialUnitaryGroup.mpr ⟨(isometryUnit hBl hiso).2, ?_⟩, ?_⟩
  · rw [coe_isometryUnit, LinearMap.det_comp, hdetτ, ← hd, inv_mul_cancel₀ hd0]
  · rw [coe_isometryUnit, LinearMap.comp_apply, hφ₀v, hτ, hu'w, mul_zero, zero_smul, add_zero]

end Transitivity

section Conjugacy

variable {f : ℕ} {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem exists_norm_eq (h : UnitaryFieldData 2 f K) {y : K} (hy : h.bar y = y) :
    ∃ μ : K, h.norm μ = y := by
  obtain ⟨μ, hμ⟩ := h.normHom_surjective ⟨y, h.mem_fixedField.mpr hy⟩
  exact ⟨μ, congrArg Subtype.val hμ⟩

theorem coe_mul_eq_one {σ : K →+* K} {B : V →ₛₗ[σ] V →ₗ[K] K}
    {s : sesqSpecialUnitaryGroup B} (hs : s * s = 1) :
    (s : LinearMap.GeneralLinearGroup K V) * s = 1 := by
  have := congrArg Subtype.val hs
  simpa using this

theorem involutions_isConj (h : UnitaryFieldData 2 f K) [FiniteDimensional K V]
    (hdim : Module.finrank K V = 3) {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) {s t : sesqSpecialUnitaryGroup B} (hs2 : s * s = 1) (hs1 : s ≠ 1)
    (ht2 : t * t = 1) (ht1 : t ≠ 1) : IsConj s t := by
  have hsymm : ∀ x y, B y x = h.bar (B x y) := fun x y => (hB.eq x y).symm
  obtain ⟨v, hv0, hvv, c, hc0, hcbar, hs⟩ := involution_form h hdim hB hBl s.2 (coe_mul_eq_one hs2)
    (fun h0 => hs1 (Subtype.ext h0))
  obtain ⟨w, hw0, hww, d, hd0, hdbar, ht⟩ := involution_form h hdim hB hBl t.2 (coe_mul_eq_one ht2)
    (fun h0 => ht1 (Subtype.ext h0))
  obtain ⟨μ, hμ⟩ := exists_norm_eq h (y := d / c) (by rw [map_div₀, hdbar, hcbar])
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0] at hμ
    have h1 : d / c = 0 := by rw [← hμ]; simp [UnitaryFieldData.norm]
    rcases div_eq_zero_iff.mp h1 with h2 | h2
    · exact hd0 h2
    · exact hc0 h2
  have hw'0 : μ • w ≠ 0 := smul_ne_zero hμ0 hw0
  have hw' : B (μ • w) (μ • w) = 0 := by
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hww, RingHom.id_apply, mul_zero]
  obtain ⟨g, hg, hgv⟩ := exists_mem_special_unitary_apply_eq h hdim hB hBl hv0 hvv hw'0 hw'
  refine isConj_iff.mpr ⟨⟨g, hg⟩, Subtype.ext (Units.ext (LinearMap.ext fun x => ?_))⟩
  have hgiso := mem_sesqUnitaryGroup.mp (sesqSpecialUnitaryGroup_le B hg)
  have hBv : B v (((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x) =
      h.bar μ * B w x := by
    have := hgiso v (((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x)
    rw [generalLinearGroup_apply_inv_apply, hgv, map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul] at this
    exact this.symm
  change ((g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)
      (((s : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)
        (((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x)) =
    ((t : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x
  rw [hs, ht, map_add, map_smul, hgv, hBv, generalLinearGroup_apply_inv_apply]
  have hμd : c * (μ * h.bar μ) = d := by
    have : μ * h.bar μ = d / c := hμ
    rw [this]; field_simp
  rw [smul_smul]
  congr 2
  linear_combination (B w x) * hμd

end Conjugacy

section Commuting

variable {f : ℕ} {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def IsElemAbelianTwo {G : Type*} [Group G] (E : Subgroup G) : Prop :=
  (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ ∀ a ∈ E, a ^ 2 = 1

theorem exists_pairing_eq_one {σ : K →+* K} {B : V →ₛₗ[σ] V →ₗ[K] K} (hBl : B.SeparatingLeft)
    {v : V} (hv0 : v ≠ 0) : ∃ x, B v x = 1 := by
  obtain ⟨x, hx⟩ : ∃ x, B v x ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hv0 (hBl v hall)
  exact ⟨(B v x)⁻¹ • x, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hx]⟩

theorem frame_expand {σ : K →+* K} {B : V →ₛₗ[σ] V →ₗ[K] K} {v b u : V}
    (hexp : ∀ x, x = (B b x) • v + (B v x) • b + (B u x) • u) (x y : V) :
    B x y = σ (B b x) * B v y + σ (B v x) * B b y + σ (B u x) * B u y := by
  have := congrArg (fun z => B z y) (hexp x)
  simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at this
  exact this

theorem exists_smul_of_orth_isotropic (h : UnitaryFieldData 2 f K) [FiniteDimensional K V]
    (hdim : Module.finrank K V = 3) {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) {v w : V} (hv0 : v ≠ 0) (hv : B v v = 0) (hvw : B v w = 0)
    (hww : B w w = 0) : ∃ α : K, w = α • v := by
  obtain ⟨b, u, hvb, hbb, hvu, hbu, huu, hexp⟩ := exists_frame h hdim hB hBl hv0 hv
  have hB1 := frame_expand hexp w w
  rw [hww, hvw] at hB1
  simp only [map_zero, mul_zero, zero_mul, zero_add, add_zero] at hB1
  have hu0 : B u w = 0 := by
    have : h.bar (B u w) * B u w = 0 := hB1.symm
    rcases mul_eq_zero.mp this with h1 | h1
    · exact (map_eq_zero h.bar).mp h1
    · exact h1
  refine ⟨B b w, ?_⟩
  calc w = (B b w) • v + (B v w) • b + (B u w) • u := hexp w
    _ = (B b w) • v := by rw [hvw, hu0]; simp

theorem exists_smul_of_commute (h : UnitaryFieldData 2 f K) [FiniteDimensional K V]
    (hdim : Module.finrank K V = 3) {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) {v w : V} (hv0 : v ≠ 0) (hvv : B v v = 0)
    (hww : B w w = 0) {c d : K} (hc : c ≠ 0) (hd : d ≠ 0) {s t : V →ₗ[K] V}
    (hs : ∀ x, s x = x + (c * B v x) • v) (ht : ∀ x, t x = x + (d * B w x) • w)
    (hcomm : ∀ x, s (t x) = t (s x)) : ∃ α : K, w = α • v := by
  have hsymm : ∀ x y, B y x = h.bar (B x y) := fun x y => (hB.eq x y).symm
  obtain ⟨x₁, hx₁⟩ := exists_pairing_eq_one hBl hv0
  have h1 := hcomm x₁
  rw [hs, ht, hs, ht] at h1
  simp only [map_add, map_smul, smul_eq_mul, hx₁, mul_one] at h1
  by_cases hwv : B w v = 0
  · exact exists_smul_of_orth_isotropic h hdim hB hBl hv0 hvv (by rw [hsymm, hwv, map_zero]) hww
  · have h2 : (c * d * B w x₁ * B v w) • v = (c * d * B w v) • w := by
      linear_combination (norm := module) h1
    have hne : c * d * B w v ≠ 0 := mul_ne_zero (mul_ne_zero hc hd) hwv
    refine ⟨(c * d * B w v)⁻¹ * (c * d * B w x₁ * B v w), ?_⟩
    rw [← smul_smul, h2, smul_smul, inv_mul_cancel₀ hne, one_smul]

end Commuting

section Rank

variable {f : ℕ} {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem elemAbelian_elements_form (h : UnitaryFieldData 2 f K) [FiniteDimensional K V]
    (hdim : Module.finrank K V = 3) {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) (E : Subgroup (sesqSpecialUnitaryGroup B)) (hE : IsElemAbelianTwo E)
    {t₀ : sesqSpecialUnitaryGroup B} (ht₀E : t₀ ∈ E) (ht₀1 : t₀ ≠ 1) :
    ∃ v : V, v ≠ 0 ∧ B v v = 0 ∧ ∀ t : E, ∃ c : h.fixedField, ∀ x,
      (((t : sesqSpecialUnitaryGroup B) : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x =
        x + ((c : K) * B v x) • v := by
  have ht₀2 : t₀ * t₀ = 1 := by simpa [sq] using hE.2 t₀ ht₀E
  obtain ⟨v, hv0, hvv, c₀, hc₀0, hc₀bar, hs₀⟩ := involution_form h hdim hB hBl t₀.2
    (coe_mul_eq_one ht₀2) (fun h0 => ht₀1 (Subtype.ext h0))
  refine ⟨v, hv0, hvv, ?_⟩
  rintro ⟨t, htE⟩
  by_cases ht1 : t = 1
  · exact ⟨0, fun x => by subst ht1; simp⟩
  · have ht2 : t * t = 1 := by simpa [sq] using hE.2 t htE
    obtain ⟨w, hw0, hww, d, hd0, hdbar, ht⟩ := involution_form h hdim hB hBl t.2
      (coe_mul_eq_one ht2) (fun h0 => ht1 (Subtype.ext h0))
    have hcomm := hE.1 t₀ ht₀E t htE
    obtain ⟨α, hα⟩ := exists_smul_of_commute h hdim hB hBl hv0 hvv hww hc₀0 hd0 hs₀ ht (fun x => by
      have := congrArg (fun g : sesqSpecialUnitaryGroup B =>
        ((g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x) hcomm
      simpa [Module.End.mul_apply] using this)
    refine ⟨⟨d * h.norm α, ?_⟩, fun x => ?_⟩
    · rw [UnitaryFieldData.mem_fixedField]
      simp only [UnitaryFieldData.norm, map_mul, h.bar_bar, hdbar]
      ring
    · show ((t : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x = _
      rw [ht, hα]
      simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_smul, UnitaryFieldData.norm]
      congr 2
      ring

theorem card_elemAbelian_le (h : UnitaryFieldData 2 f K) [FiniteDimensional K V]
    (hdim : Module.finrank K V = 3) {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) (E : Subgroup (sesqSpecialUnitaryGroup B)) (hE : IsElemAbelianTwo E) :
    Nat.card E ≤ 2 ^ f := by
  have : Finite K := h.finite
  by_cases hE1 : ∀ t ∈ E, t = 1
  · rw [(Subgroup.eq_bot_iff_forall E).mpr hE1, Subgroup.card_bot]
    exact Nat.one_le_two_pow
  · push Not at hE1
    obtain ⟨t₀, ht₀E, ht₀1⟩ := hE1
    obtain ⟨v, hv0, hvv, key⟩ := elemAbelian_elements_form h hdim hB hBl E hE ht₀E ht₀1
    choose φ hφ using key
    have hinj : Function.Injective φ := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      apply LinearMap.ext
      intro x
      rw [hφ a x, hφ b x, hab]
    calc Nat.card E ≤ Nat.card h.fixedField := Nat.card_le_card_of_injective φ hinj
      _ = 2 ^ f := h.card_fixedField

theorem finite_generalLinearGroup [Finite V] : Finite (LinearMap.GeneralLinearGroup K V) := by
  have h1 : Finite (V →ₗ[K] V) :=
    Finite.of_injective (fun f : V →ₗ[K] V => (f : V → V)) DFunLike.coe_injective
  exact inferInstanceAs (Finite (V →ₗ[K] V)ˣ)

theorem finite_sesqSpecialUnitaryGroup [Finite K] [FiniteDimensional K V] {σ : K →+* K}
    (B : V →ₛₗ[σ] V →ₗ[K] K) : Finite (sesqSpecialUnitaryGroup B) := by
  have : Finite V := Module.finite_of_finite K
  have : Finite (LinearMap.GeneralLinearGroup K V) := finite_generalLinearGroup
  infer_instance

end Rank

section Quotient

variable {f : ℕ} {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

open CFSG.LocalAnalysis.ComponentInitial.FourGroupOddUnitary in
theorem scalar_pow_three {σ : K →+* K} [FiniteDimensional K V] (hdim : Module.finrank K V = 3)
    {B : V →ₛₗ[σ] V →ₗ[K] K} {z : sesqSpecialUnitaryGroup B} (hz : z ∈ unitaryScalars B) :
    z ^ 3 = 1 := by
  obtain ⟨c, hc⟩ := (mem_unitaryScalars B).mp hz
  have hdet : LinearMap.det ((z : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) = 1 :=
    (mem_sesqSpecialUnitaryGroup.mp z.2).2
  rw [hc, LinearMap.det_smul, LinearMap.det_id, mul_one, hdim] at hdet
  apply Subtype.ext
  apply Units.ext
  apply LinearMap.ext
  intro x
  have hz1 : ∀ y, ((z : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) y = (c : K) • y := fun y => by
    rw [hc]; rfl
  show ((z : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) (((z : LinearMap.GeneralLinearGroup K V) :
    V →ₗ[K] V) (((z : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x)) = x
  have hc3 : (c : K) * c * c = 1 := by rw [← hdet]; ring
  rw [hz1, hz1, hz1, smul_smul, smul_smul, hc3, one_smul]

open CFSG.LocalAnalysis.ComponentInitial.FourGroupOddUnitary in
theorem scalar_central {σ : K →+* K} {B : V →ₛₗ[σ] V →ₗ[K] K} {z : sesqSpecialUnitaryGroup B}
    (hz : z ∈ unitaryScalars B) (g : sesqSpecialUnitaryGroup B) : g * z = z * g := by
  obtain ⟨c, hc⟩ := (mem_unitaryScalars B).mp hz
  apply Subtype.ext
  apply Units.ext
  apply LinearMap.ext
  intro x
  have hz1 : ∀ y, ((z : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) y = (c : K) • y := fun y => by
    rw [hc]; rfl
  show ((g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)
    (((z : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x) =
    ((z : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V)
      (((g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x)
  rw [hz1, hz1, map_smul]

end Quotient

section GenericQuotient

variable {G Q : Type*} [Group G] [Group Q]

theorem exists_lift_involution {π : G →* Q} (hπ : Function.Surjective π)
    (hC3 : ∀ z ∈ π.ker, z ^ 3 = 1) {q : Q} (hq2 : q * q = 1) :
    ∃ a : G, a * a = 1 ∧ π a = q := by
  obtain ⟨x, rfl⟩ := hπ q
  have hx2 : x * x ∈ π.ker := by rw [MonoidHom.mem_ker, map_mul]; exact hq2
  have h3 : (x * x) ^ 3 = 1 := hC3 _ hx2
  refine ⟨x ^ 3, ?_, ?_⟩
  · calc x ^ 3 * x ^ 3 = (x * x) ^ 3 := by rw [← pow_add, ← sq, ← pow_mul]
      _ = 1 := h3
  · rw [map_pow]
    rw [pow_succ, sq, hq2, one_mul]

theorem card_le_of_central_exponent_three [Finite G] {π : G →* Q} (hπ : Function.Surjective π)
    (hC3 : ∀ z ∈ π.ker, z ^ 3 = 1) (hCc : ∀ z ∈ π.ker, ∀ g : G, g * z = z * g) {n : ℕ}
    (hbound : ∀ E : Subgroup G, IsElemAbelianTwo E → Nat.card E ≤ n) (Ebar : Subgroup Q)
    (hEbar : IsElemAbelianTwo Ebar) : Nat.card Ebar ≤ n := by
  set Epre : Subgroup G := Ebar.comap π with hEpre
  have hsq : ∀ x ∈ Epre, x * x ∈ π.ker := fun x hx => by
    rw [MonoidHom.mem_ker, map_mul]
    have := hEbar.2 (π x) hx
    simpa [sq] using this
  have hcomm : ∀ x ∈ Epre, ∀ y ∈ Epre, x * y = y * x := by
    intro x hx y hy
    obtain ⟨z, hz⟩ : ∃ z, z = x * y * x⁻¹ * y⁻¹ := ⟨_, rfl⟩
    have hzC : z ∈ π.ker := by
      rw [MonoidHom.mem_ker, hz]
      simp only [map_mul, map_inv]
      have := hEbar.1 (π x) hx (π y) hy
      rw [this]
      group
    have hz3 := hC3 z hzC
    have hxy : x * y = z * (y * x) := by rw [hz]; group
    have hzx : x * z = z * x := hCc z hzC x
    have hx2c := hCc (x * x) (hsq x hx) y
    have e : (z * z) * (y * (x * x)) = y * (x * x) := by
      calc (z * z) * (y * (x * x)) = x * x * y := by
            calc (z * z) * (y * (x * x)) = z * (z * (y * x) * x) := by group
              _ = z * (x * y * x) := by rw [← hxy]
              _ = z * (x * (y * x)) := by group
              _ = x * (z * (y * x)) := by rw [← mul_assoc, ← hzx, mul_assoc]
              _ = x * (x * y) := by rw [← hxy]
              _ = x * x * y := by group
        _ = y * (x * x) := hx2c.symm
    have hzz : z * z = 1 := by
      exact (mul_left_inj (y * (x * x))).mp (e.trans (one_mul _).symm)
    have hz1 : z = 1 := by
      calc z = z ^ 3 * (z * z)⁻¹ := by group
        _ = 1 := by rw [hz3, hzz]; simp
    rw [hxy, hz1, one_mul]
  let E' : Subgroup G :=
    { carrier := {x | x ∈ Epre ∧ x * x = 1}
      one_mem' := ⟨Epre.one_mem, mul_one 1⟩
      mul_mem' := by
        rintro x y ⟨hx, hx2⟩ ⟨hy, hy2⟩
        refine ⟨Epre.mul_mem hx hy, ?_⟩
        calc x * y * (x * y) = x * (y * x) * y := by group
          _ = x * (x * y) * y := by rw [hcomm y hy x hx]
          _ = (x * x) * (y * y) := by group
          _ = 1 := by rw [hx2, hy2, mul_one]
      inv_mem' := by
        rintro x ⟨hx, hx2⟩
        refine ⟨Epre.inv_mem hx, ?_⟩
        calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
          _ = 1 := by rw [hx2, inv_one] }
  have hE' : IsElemAbelianTwo E' := by
    refine ⟨fun a ha b hb => hcomm a ha.1 b hb.1, fun a ha => ?_⟩
    rw [sq]; exact ha.2
  have hsurj : Function.Surjective (fun a : E' => (⟨π a, a.2.1⟩ : Ebar)) := by
    rintro ⟨q, hq⟩
    obtain ⟨x, rfl⟩ := hπ q
    have hxEpre : x ∈ Epre := hq
    have hq2 : π x * π x = 1 := by
      have := hEbar.2 (π x) hq
      simpa [sq] using this
    refine ⟨⟨x ^ 3, Epre.pow_mem hxEpre 3, ?_⟩, Subtype.ext ?_⟩
    · calc x ^ 3 * x ^ 3 = (x * x) ^ 3 := by rw [← pow_add, ← sq, ← pow_mul]
        _ = 1 := hC3 _ (hsq x hxEpre)
    · show π (x ^ 3) = π x
      rw [map_pow]
      rw [pow_succ, sq, hq2, one_mul]
  have : Finite E' := inferInstance
  calc Nat.card Ebar ≤ Nat.card E' := Nat.card_le_card_of_surjective _ hsurj
    _ ≤ n := hbound E' hE'

end GenericQuotient

section QuotientUnitary

variable {f : ℕ} {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

open CFSG.LocalAnalysis.ComponentInitial.FourGroupOddUnitary in
theorem quotient_involutions_isConj (h : UnitaryFieldData 2 f K) [FiniteDimensional K V]
    (hdim : Module.finrank K V = 3) {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) {Q : Type*} [Group Q] {π : sesqSpecialUnitaryGroup B →* Q}
    (hπ : Function.Surjective π) (hker : π.ker ≤ unitaryScalars B) {q₁ q₂ : Q}
    (h1 : q₁ * q₁ = 1) (h1' : q₁ ≠ 1) (h2 : q₂ * q₂ = 1) (h2' : q₂ ≠ 1) : IsConj q₁ q₂ := by
  have hC3 : ∀ z ∈ π.ker, z ^ 3 = 1 := fun z hz => scalar_pow_three hdim (hker hz)
  obtain ⟨a₁, ha₁, rfl⟩ := exists_lift_involution hπ hC3 h1
  obtain ⟨a₂, ha₂, rfl⟩ := exists_lift_involution hπ hC3 h2
  have ha₁' : a₁ ≠ 1 := fun h0 => h1' (by rw [h0, map_one])
  have ha₂' : a₂ ≠ 1 := fun h0 => h2' (by rw [h0, map_one])
  obtain ⟨g, hg⟩ := isConj_iff.mp (involutions_isConj h hdim hB hBl ha₁ ha₁' ha₂ ha₂')
  exact isConj_iff.mpr ⟨π g, by rw [← hg, map_mul, map_mul, map_inv]⟩

open CFSG.LocalAnalysis.ComponentInitial.FourGroupOddUnitary in
theorem quotient_card_elemAbelian_le (h : UnitaryFieldData 2 f K) [FiniteDimensional K V]
    (hdim : Module.finrank K V = 3) {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) {Q : Type*} [Group Q] {π : sesqSpecialUnitaryGroup B →* Q}
    (hπ : Function.Surjective π) (hker : π.ker ≤ unitaryScalars B) (E : Subgroup Q)
    (hE : IsElemAbelianTwo E) : Nat.card E ≤ 2 ^ f := by
  have : Finite K := h.finite
  have := finite_sesqSpecialUnitaryGroup B
  exact card_le_of_central_exponent_three hπ (fun z hz => scalar_pow_three hdim (hker hz))
    (fun z hz g => scalar_central (hker hz) g)
    (fun E hE => card_elemAbelian_le h hdim hB hBl E hE) E hE

end QuotientUnitary

end CFSG.QuasithinUnique.Setup.X5
