module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryBasics
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrderSupport

public section

namespace CFSG.LinearGroups

open CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

section Eichler

variable {σ : K →+* K}

@[expose] def eichlerMap (B : V →ₛₗ[σ] V →ₗ[K] K) (e y : V) (c : K) : V →ₗ[K] V :=
  LinearMap.id + (B e).smulRight (y + c • e) - (B y).smulRight e

theorem eichlerMap_apply (B : V →ₛₗ[σ] V →ₗ[K] K) (e y : V) (c : K) (x : V) :
    eichlerMap B e y c x = x + B e x • (y + c • e) - B y x • e := by
  simp [eichlerMap]

theorem eichlerMap_zero (B : V →ₛₗ[σ] V →ₗ[K] K) (e : V) (d : K) :
    eichlerMap B e 0 d = hermTransvection B e d := by
  ext x
  simp only [eichlerMap_apply, hermTransvection_apply, map_zero, LinearMap.zero_apply, zero_smul,
    sub_zero, zero_add, smul_smul]
  rw [mul_comm]

theorem eichlerMap_comp {B : V →ₛₗ[σ] V →ₗ[K] K} {e y y' : V} (he : B e e = 0)
    (hey' : B e y' = 0) (hye : B y e = 0) (c c' : K) :
    eichlerMap B e y c ∘ₗ eichlerMap B e y' c' = eichlerMap B e (y + y') (c + c' - B y y') := by
  ext x
  simp only [LinearMap.comp_apply, eichlerMap_apply, map_add, map_sub, map_smul,
    LinearMap.add_apply, he, hey', hye]
  module

theorem eichlerMap_isometry {B : V →ₛₗ[σ] V →ₗ[K] K} (hB : B.IsSymm) {e y : V} (he : B e e = 0)
    (hey : B e y = 0) {c : K} (hc : c + σ c + B y y = 0) (x x' : V) :
    B (eichlerMap B e y c x) (eichlerMap B e y c x') = B x x' := by
  have hxe : ∀ z, B z e = σ (B e z) := fun z => (hB.eq e z).symm
  have hxy : ∀ z, B z y = σ (B y z) := fun z => (hB.eq y z).symm
  have hye : B y e = 0 := by rw [hxe, hey, map_zero]
  simp only [eichlerMap_apply, map_add, map_sub, map_smulₛₗ, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, he, hey, hye, hxe x, hxy x,
    mul_zero, add_zero, sub_zero]
  linear_combination σ (B e x) * B e x' * hc

theorem det_eichlerMap [FiniteDimensional K V] {B : V →ₛₗ[σ] V →ₗ[K] K} {e y : V}
    (he : B e e = 0) (hey : B e y = 0) (hye : B y e = 0) (c : K) :
    LinearMap.det (eichlerMap B e y c) = 1 := by
  have hcomp : eichlerMap B e y c =
      LinearMap.transvection (B e) (y + c • e) ∘ₗ LinearMap.transvection (-B y) e := by
    ext x
    simp only [eichlerMap_apply, LinearMap.comp_apply, LinearMap.transvection.apply, map_add,
      map_neg, map_smul, LinearMap.neg_apply, he, neg_smul]
    module
  rw [hcomp, LinearMap.det_comp, LinearMap.transvection.det, LinearMap.transvection.det]
  simp [he, hey, hye]

end Eichler

section Frames

variable {σ : K →+* K}

theorem linearIndependent_of_mem_orthonormalFrames {B : V →ₛₗ[σ] V →ₗ[K] K} {r : ℕ}
    {v : Fin r → V} (hv : v ∈ orthonormalFrames B r) : LinearIndependent K v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have := congrArg (B (v j)) hg
  simpa [map_sum, map_smul, mem_orthonormalFrames.mp hv] using this

@[expose] noncomputable def frameBasis [FiniteDimensional K V] {B : V →ₛₗ[σ] V →ₗ[K] K} {r : ℕ}
    {v : Fin r → V} (hv : v ∈ orthonormalFrames B r) (hr : r = Module.finrank K V) :
    Module.Basis (Fin r) K V :=
  Module.Basis.mk (linearIndependent_of_mem_orthonormalFrames hv)
    (Submodule.eq_top_of_finrank_eq (by
      rw [finrank_span_eq_card (linearIndependent_of_mem_orthonormalFrames hv), Fintype.card_fin,
        hr])).ge

theorem coe_frameBasis [FiniteDimensional K V] {B : V →ₛₗ[σ] V →ₗ[K] K} {r : ℕ}
    {v : Fin r → V} (hv : v ∈ orthonormalFrames B r) (hr : r = Module.finrank K V) :
    ⇑(frameBasis hv hr) = v :=
  Module.Basis.coe_mk _ _

theorem span_pair_nondegenerate {B : V →ₛₗ[σ] V →ₗ[K] K} {u₁ u₂ : V}
    (hG : B u₁ u₁ * B u₂ u₂ - B u₁ u₂ * B u₂ u₁ ≠ 0) :
    Module.finrank K (Submodule.span K {u₁, u₂}) = 2 ∧
      (B.domRestrict₁₂ (Submodule.span K {u₁, u₂})
        (Submodule.span K {u₁, u₂})).SeparatingLeft := by
  have key : ∀ s t : K, B (s • u₁ + t • u₂) u₁ = 0 → B (s • u₁ + t • u₂) u₂ = 0 →
      s = 0 ∧ t = 0 := by
    intro s t h1 h2
    simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul] at h1 h2
    have hs : σ s * (B u₁ u₁ * B u₂ u₂ - B u₁ u₂ * B u₂ u₁) = 0 := by
      linear_combination B u₂ u₂ * h1 - B u₂ u₁ * h2
    have ht : σ t * (B u₁ u₁ * B u₂ u₂ - B u₁ u₂ * B u₂ u₁) = 0 := by
      linear_combination B u₁ u₁ * h2 - B u₁ u₂ * h1
    exact ⟨(map_eq_zero σ).mp ((mul_eq_zero.mp hs).resolve_right hG),
      (map_eq_zero σ).mp ((mul_eq_zero.mp ht).resolve_right hG)⟩
  have hli : LinearIndependent K ![u₁, u₂] := LinearIndependent.pair_iff.mpr fun s t hst =>
    key s t (by rw [hst, map_zero, LinearMap.zero_apply])
      (by rw [hst, map_zero, LinearMap.zero_apply])
  have hrange : Set.range ![u₁, u₂] = {u₁, u₂} := by
    ext x
    simp [eq_comm, or_comm]
  refine ⟨by rw [← hrange, finrank_span_eq_card hli, Fintype.card_fin], ?_⟩
  rintro ⟨z, hz⟩ hz0
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hz
  have h1 := hz0 ⟨u₁, Submodule.subset_span (by simp)⟩
  have h2 := hz0 ⟨u₂, Submodule.subset_span (by simp)⟩
  rw [LinearMap.domRestrict₁₂_apply] at h1 h2
  obtain ⟨rfl, rfl⟩ := key s t h1 h2
  exact Subtype.ext (by simp)

end Frames

@[expose] def unitaryTransvections (h : UnitaryFieldData p f K) (B : V →ₛₗ[h.bar] V →ₗ[K] K) :
    Set (LinearMap.GeneralLinearGroup K V) :=
  {T | ∃ (a : V) (ha : B a a = 0), ∃ c ∈ h.traceZero, T = hermTransvectionGL B ha c}

theorem hermTransvectionGL_mem_unitaryTransvections (h : UnitaryFieldData p f K)
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} {a : V} (ha : B a a = 0) {c : K} (hc : c ∈ h.traceZero) :
    hermTransvectionGL B ha c ∈ unitaryTransvections h B :=
  ⟨a, ha, c, hc, rfl⟩

theorem exists_isotropic_of_finrank_two (h : UnitaryFieldData p f K) [FiniteDimensional K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hn : Module.finrank K V = 2) : ∃ a : V, a ≠ 0 ∧ B a a = 0 := by
  have hc := (unitary_hermitian_vector_count h hB hBl hn (by norm_num)).2.2
  obtain ⟨q, hq⟩ : ∃ q : ℤ, q = ((p ^ f : ℕ) : ℤ) := ⟨_, rfl⟩
  rw [← hq] at hc
  have hq1 : 1 < q := by
    rw [hq]
    exact_mod_cast h.one_lt_pow
  have hpos : (0 : ℤ) < Nat.card {v : V // v ≠ 0 ∧ B v v = 0} := by
    rw [hc]
    apply mul_pos
    · nlinarith
    · norm_num
      linarith
  obtain ⟨⟨a, ha0, ha⟩⟩ := (Nat.card_pos_iff.mp (by exact_mod_cast hpos)).1
  exact ⟨a, ha0, ha⟩

theorem exists_isometry_det_eq_fix (h : UnitaryFieldData p f K) {B : V →ₛₗ[h.bar] V →ₗ[K] K}
    {r : ℕ} (e : Module.Basis (Fin (r + 1)) K V) (he : ⇑e ∈ orthonormalFrames B (r + 1)) {c : K}
    (hc : h.norm c = 1) :
    ∃ φ : V →ₗ[K] V, (∀ x y, B (φ x) (φ y) = B x y) ∧ LinearMap.det φ = c ∧
      ∀ i : Fin r, φ (e i.succ) = e i.succ := by
  classical
  obtain ⟨d, hd⟩ : ∃ d : Fin (r + 1) → K, d = Function.update (1 : Fin (r + 1) → K) 0 c :=
    ⟨_, rfl⟩
  have hdn : ∀ i, d i * h.bar (d i) = 1 := by
    intro i
    by_cases hi : i = 0
    · rw [hd, hi, Function.update_self]
      exact hc
    · rw [hd, Function.update_of_ne hi, Pi.one_apply, map_one, one_mul]
  obtain ⟨φ, hφ⟩ : ∃ φ : V →ₗ[K] V, φ = Matrix.toLin e e (Matrix.diagonal d) := ⟨_, rfl⟩
  have hφe : ∀ i, φ (e i) = d i • e i := fun i => by
    rw [hφ, Matrix.toLin_self]
    simp [Matrix.diagonal_apply]
  refine ⟨φ, isometry_of_mem_orthonormalFrames e he (mem_orthonormalFrames.mpr fun i j => ?_), ?_,
    fun i => ?_⟩
  · simp only [hφe, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, mem_orthonormalFrames.mp he,
      RingHom.id_apply]
    split_ifs with hij
    · subst hij
      linear_combination hdn i
    · simp only [mul_zero]
  · rw [hφ, LinearMap.det_toLin, Matrix.det_diagonal, Fin.prod_univ_succ, hd,
      Function.update_self]
    simp [Fin.succ_ne_zero]
  · rw [hφe, hd, Function.update_of_ne (Fin.succ_ne_zero i), Pi.one_apply, one_smul]

theorem exists_norm_one_perp_of_isotropic (h : UnitaryFieldData p f K) [FiniteDimensional K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hn : 3 ≤ Module.finrank K V) {a : V} (ha0 : a ≠ 0) (ha : B a a = 0) :
    ∃ w : V, B w w = 1 ∧ B a w = 0 := by
  obtain ⟨⟨b, hab, hbb⟩, hsplit⟩ := hermitian_hyperbolic_splitting h hB hBl ha0 ha
  obtain ⟨-, -, -, hWsep, hWdim⟩ := hsplit b hab hbb
  obtain ⟨e, he⟩ := h.exists_orthonormal_basis (hB.domRestrict _) hWsep
  have hpos : 0 < Module.finrank K ((Submodule.span K {a, b}).orthogonalBilin B) := by omega
  refine ⟨(e ⟨0, hpos⟩ : V), ?_, ?_⟩
  · have := he ⟨0, hpos⟩ ⟨0, hpos⟩
    rw [LinearMap.domRestrict₁₂_apply] at this
    simpa using this
  · exact (Submodule.mem_orthogonalBilin.mp (e ⟨0, hpos⟩).2) a (Submodule.subset_span (by simp))

theorem unitary_transvection_commutator (h : UnitaryFieldData p f K) [FiniteDimensional K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hn : 3 ≤ Module.finrank K V) {a : V} (ha : B a a = 0) {t : K} (ht : t ∈ h.traceZero) :
    ∃ g₁ ∈ sesqSpecialUnitaryGroup B, ∃ g₂ ∈ sesqSpecialUnitaryGroup B,
      hermTransvectionGL B ha t = g₁ * g₂ * g₁⁻¹ * g₂⁻¹ := by
  by_cases ha0 : a = 0
  · subst ha0
    refine ⟨1, one_mem _, 1, one_mem _, ?_⟩
    rw [mul_one, inv_one, mul_one, mul_one]
    refine Units.ext ?_
    rw [coe_hermTransvectionGL, Units.val_one]
    ext x
    simp [hermTransvection_apply]
  obtain ⟨w, hww, haw⟩ := exists_norm_one_perp_of_isotropic h hB hBl hn ha0 ha
  have hwa : B w a = 0 := by rw [← hB.eq a w, haw, map_zero]
  obtain ⟨r, hr⟩ : ∃ r : K, h.bar r - r = t := by
    have : t ∈ h.barSub.range := by rw [h.range_barSub]; exact ht
    obtain ⟨r, hr⟩ := this
    exact ⟨r, by rw [← hr, UnitaryFieldData.barSub_apply]⟩
  obtain ⟨c, hc⟩ := h.traceLin_surjective (-1)
  have hc' : c + h.bar c + B w w = 0 := by
    have := congrArg Subtype.val hc
    simp only [UnitaryFieldData.coe_traceLin, UnitaryFieldData.trace] at this
    rw [hww, this]
    simp
  obtain ⟨d, hd⟩ := h.traceLin_surjective (-⟨h.norm r, h.norm_mem_fixedField r⟩)
  have hrw : B (r • w) (r • w) = h.norm r := by
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hww, mul_one,
      UnitaryFieldData.norm, RingHom.id_apply]
  have hd' : d + h.bar d + B (r • w) (r • w) = 0 := by
    have := congrArg Subtype.val hd
    simp only [UnitaryFieldData.coe_traceLin, UnitaryFieldData.trace] at this
    rw [hrw, this]
    simp
  have har : B a (r • w) = 0 := by rw [map_smul, haw, smul_zero]
  have hra : B (r • w) a = 0 := by rw [map_smulₛₗ, LinearMap.smul_apply, hwa, smul_zero]
  have hE₁ := eichlerMap_isometry hB ha haw hc'
  have hE₂ := eichlerMap_isometry hB ha har hd'
  have hg₁ : ((isometryUnit hBl hE₁ : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup K V) ∈
      sesqSpecialUnitaryGroup B := by
    rw [mem_sesqSpecialUnitaryGroup, coe_isometryUnit]
    exact ⟨(isometryUnit hBl hE₁).2, det_eichlerMap ha haw hwa c⟩
  have hg₂ : ((isometryUnit hBl hE₂ : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup K V) ∈
      sesqSpecialUnitaryGroup B := by
    rw [mem_sesqSpecialUnitaryGroup, coe_isometryUnit]
    exact ⟨(isometryUnit hBl hE₂).2, det_eichlerMap ha har hra d⟩
  refine ⟨_, hg₁, _, hg₂, ?_⟩
  have hrel : ((isometryUnit hBl hE₁ : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup K V) *
        (isometryUnit hBl hE₂ : sesqUnitaryGroup B) =
      hermTransvectionGL B ha t * ((isometryUnit hBl hE₂ : sesqUnitaryGroup B) *
        (isometryUnit hBl hE₁ : sesqUnitaryGroup B)) := by
    refine Units.ext ?_
    simp only [Units.val_mul, coe_hermTransvectionGL, coe_isometryUnit, Module.End.mul_eq_comp]
    rw [eichlerMap_comp ha har hwa, eichlerMap_comp ha haw hra, ← eichlerMap_zero,
      eichlerMap_comp ha (by rw [map_add, har, haw, add_zero]) (by simp)]
    congr 1
    · abel
    · simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hww, mul_one, map_zero,
        LinearMap.zero_apply, sub_zero, ← hr]
      ring
  rw [hrel]
  group

section SUTwo

theorem hyperbolic_entries (h : UnitaryFieldData p f K) {α β γ δ : K}
    (e1 : h.bar α * γ + h.bar γ * α = 0) (e2 : h.bar β * δ + h.bar δ * β = 0)
    (e3 : h.bar α * δ + h.bar γ * β = 1) (e4 : α * δ - β * γ = 1) :
    h.bar α = α ∧ h.bar δ = δ ∧ γ + h.bar γ = 0 ∧ β + h.bar β = 0 := by
  have e3' : α * h.bar δ + γ * h.bar β = 1 := by
    have := congrArg h.bar e3
    simpa only [map_add, map_mul, h.bar_bar, map_one] using this
  have hα : h.bar α = α := by linear_combination (-h.bar α) * e4 + α * e3 - β * e1
  have hδ : h.bar δ = δ := by linear_combination (-h.bar δ) * e4 + δ * e3' - γ * e2
  have hγα : α * (γ + h.bar γ) = 0 := by linear_combination e1 - γ * hα
  have hγβ : β * (γ + h.bar γ) = 0 := by linear_combination e3 - e4 - δ * hα
  have hβδ : δ * (β + h.bar β) = 0 := by linear_combination e2 - β * hδ
  have hβγ : γ * (β + h.bar β) = 0 := by linear_combination e3' - e4 - α * hδ
  refine ⟨hα, hδ, ?_, ?_⟩
  · by_cases hα0 : α = 0
    · have hβ0 : β ≠ 0 := by
        rintro rfl
        rw [hα0] at e4
        simp at e4
      exact (mul_eq_zero.mp hγβ).resolve_left hβ0
    · exact (mul_eq_zero.mp hγα).resolve_left hα0
  · by_cases hδ0 : δ = 0
    · have hγ0 : γ ≠ 0 := by
        rintro rfl
        rw [hδ0] at e4
        simp at e4
      exact (mul_eq_zero.mp hβγ).resolve_left hγ0
    · exact (mul_eq_zero.mp hβδ).resolve_left hδ0

theorem eq_hermTransvection_comp {σ : K →+* K} {B : V →ₛₗ[σ] V →ₗ[K] K} (hB : B.IsSymm)
    {a b : V} (ha : B a a = 0) (hb : B b b = 0) (hab : B a b = 1)
    (hspan : Submodule.span K {a, b} = ⊤) {g : V →ₗ[K] V} {α β γ δ : K}
    (hga : g a = α • a + γ • b) (hgb : g b = β • a + δ • b) (e4 : α * δ - β * γ = 1)
    (hγ : γ ≠ 0) {s t : K} (hs : s * γ = α - 1) (ht : t * γ = δ - 1) :
    g = hermTransvection B a s ∘ₗ hermTransvection B b γ ∘ₗ hermTransvection B a t := by
  have hba : B b a = 1 := by rw [← hB.eq a b, hab, map_one]
  have hcb : 1 + γ * t = δ := by linear_combination ht
  have hca : t + s * (1 + γ * t) = β := by
    apply mul_right_cancel₀ hγ
    linear_combination ht + hs + (t * γ) * hs + (α - 1) * ht + e4
  refine LinearMap.ext_on hspan ?_
  rintro z (rfl | rfl)
  · rw [hga, show α = 1 + s * γ by linear_combination -hs]
    simp only [LinearMap.comp_apply, hermTransvection_apply, map_add, map_smul, ha, hab, hba,
      mul_zero, zero_smul, add_zero, mul_one]
    module
  · rw [hgb, ← hca, ← hcb]
    simp only [LinearMap.comp_apply, hermTransvection_apply, map_add, map_smul, ha, hab, hba, hb,
      mul_zero, zero_smul, add_zero, mul_one]
    module

theorem mem_closure_unitaryTransvections_of_finrank_two (h : UnitaryFieldData p f K)
    [FiniteDimensional K V] {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hn : Module.finrank K V = 2) {g : LinearMap.GeneralLinearGroup K V}
    (hg : g ∈ sesqSpecialUnitaryGroup B) : g ∈ Submonoid.closure (unitaryTransvections h B) := by
  obtain ⟨a, ha0, ha⟩ := exists_isotropic_of_finrank_two h hB hBl hn
  obtain ⟨⟨b, hab, hb⟩, hsplit⟩ := hermitian_hyperbolic_splitting h hB hBl ha0 ha
  have hba : B b a = 1 := by rw [← hB.eq a b, hab, map_one]
  have hspan : Submodule.span K {a, b} = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [(hsplit b hab hb).1, hn])
  have hcoord : ∀ z : V, z = B b z • a + B a z • b := by
    intro z
    have hd : ∀ y : V, B y (z - (B b z • a + B a z • b)) = 0 := by
      intro y
      have hy : y ∈ Submodule.span K {a, b} := hspan ▸ Submodule.mem_top
      obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hy
      simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, map_sub,
        smul_eq_mul, ha, hab, hba, hb, RingHom.id_apply]
      ring
    exact sub_eq_zero.mp (hBl _ fun y => by rw [← hB.eq y, hd y, map_zero])
  have hli : LinearIndependent K ![a, b] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (B a) hst
    have h2 := congrArg (B b) hst
    simp only [map_add, map_smul, smul_eq_mul, ha, hab, hba, hb, map_zero] at h1 h2
    exact ⟨by linear_combination h2, by linear_combination h1⟩
  have hrange : Set.range ![a, b] = {a, b} := by
    ext x
    simp [eq_comm, or_comm]
  let e : Module.Basis (Fin 2) K V := Module.Basis.mk hli (by rw [hrange, hspan])
  have he0 : e 0 = a := by simp [e]
  have he1 : e 1 = b := by simp [e]
  have key : ∀ g' : LinearMap.GeneralLinearGroup K V, g' ∈ sesqSpecialUnitaryGroup B →
      B a ((g' : V →ₗ[K] V) a) ≠ 0 → g' ∈ Submonoid.closure (unitaryTransvections h B) := by
    intro g' hg' hγ
    obtain ⟨hU, hdet⟩ := mem_sesqSpecialUnitaryGroup.mp hg'
    obtain ⟨φ, hφ⟩ : ∃ φ : V →ₗ[K] V, φ = (g' : V →ₗ[K] V) := ⟨_, rfl⟩
    rw [← hφ] at hdet hγ
    have hU' : ∀ x y, B (φ x) (φ y) = B x y := by rw [hφ]; exact mem_sesqUnitaryGroup.mp hU
    obtain ⟨α, hα⟩ : ∃ α, α = B b (φ a) := ⟨_, rfl⟩
    obtain ⟨γ, hγ'⟩ : ∃ γ, γ = B a (φ a) := ⟨_, rfl⟩
    obtain ⟨β, hβ⟩ : ∃ β, β = B b (φ b) := ⟨_, rfl⟩
    obtain ⟨δ, hδ⟩ : ∃ δ, δ = B a (φ b) := ⟨_, rfl⟩
    have hga : φ a = α • a + γ • b := by rw [hα, hγ']; exact hcoord _
    have hgb : φ b = β • a + δ • b := by rw [hβ, hδ]; exact hcoord _
    rw [← hγ'] at hγ
    have e1 : h.bar α * γ + h.bar γ * α = 0 := by
      have := hU' a a
      rw [hga, ha] at this
      simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, ha,
        hab, hba, hb] at this
      linear_combination this
    have e2 : h.bar β * δ + h.bar δ * β = 0 := by
      have := hU' b b
      rw [hgb, hb] at this
      simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, ha,
        hab, hba, hb] at this
      linear_combination this
    have e3 : h.bar α * δ + h.bar γ * β = 1 := by
      have := hU' a b
      rw [hga, hgb, hab] at this
      simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, ha,
        hab, hba, hb] at this
      linear_combination this
    have e4 : α * δ - β * γ = 1 := by
      have hM : φ = Matrix.toLin e e !![α, β; γ, δ] := by
        refine e.ext fun j => ?_
        rw [Matrix.toLin_self, Fin.sum_univ_two]
        fin_cases j
        · simp [he0, he1, hga]
        · simp [he0, he1, hgb]
      rw [hM, LinearMap.det_toLin, Matrix.det_fin_two_of] at hdet
      exact hdet
    obtain ⟨hαF, hδF, hγE, hβE⟩ := hyperbolic_entries h e1 e2 e3 e4
    have hγbar : h.bar γ = -γ := by linear_combination hγE
    have hsE : (α - 1) / γ ∈ h.traceZero := by
      rw [UnitaryFieldData.mem_traceZero, UnitaryFieldData.trace, map_div₀, map_sub, map_one, hαF,
        hγbar, div_neg, add_neg_cancel]
    have htE : (δ - 1) / γ ∈ h.traceZero := by
      rw [UnitaryFieldData.mem_traceZero, UnitaryFieldData.trace, map_div₀, map_sub, map_one, hδF,
        hγbar, div_neg, add_neg_cancel]
    have hγT : γ ∈ h.traceZero := by
      rw [UnitaryFieldData.mem_traceZero, UnitaryFieldData.trace]
      exact hγE
    have hdec := eq_hermTransvection_comp hB ha hb hab hspan hga hgb e4 hγ
      (div_mul_cancel₀ (α - 1) hγ) (div_mul_cancel₀ (δ - 1) hγ)
    have hg'eq : g' = hermTransvectionGL B ha ((α - 1) / γ) * hermTransvectionGL B hb γ *
        hermTransvectionGL B ha ((δ - 1) / γ) := by
      refine Units.ext ?_
      rw [Units.val_mul, Units.val_mul, coe_hermTransvectionGL, coe_hermTransvectionGL,
        coe_hermTransvectionGL, Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← hφ, hdec]
      rfl
    rw [hg'eq]
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _
      (Submonoid.subset_closure (hermTransvectionGL_mem_unitaryTransvections h ha hsE))
      (Submonoid.subset_closure (hermTransvectionGL_mem_unitaryTransvections h hb hγT)))
      (Submonoid.subset_closure (hermTransvectionGL_mem_unitaryTransvections h ha htE))
  by_cases hγ : B a ((g : V →ₗ[K] V) a) = 0
  · obtain ⟨c, hc, hc0⟩ := h.exists_mem_traceZero_ne_zero
    have hT := (hermitian_unitary_transvection h hB hb).2.1 c hc
    have hα0 : B b ((g : V →ₗ[K] V) a) ≠ 0 := by
      intro hα0
      have hga0 : (g : V →ₗ[K] V) a = 0 := by rw [hcoord ((g : V →ₗ[K] V) a), hα0, hγ]; simp
      have := generalLinearGroup_apply_inv_apply g⁻¹ a
      rw [inv_inv, hga0, map_zero] at this
      exact ha0 this.symm
    have hg' : hermTransvectionGL B hb c * g ∈ Submonoid.closure (unitaryTransvections h B) := by
      refine key _ (Subgroup.mul_mem _ hT hg) ?_
      rw [Units.val_mul, Module.End.mul_apply, coe_hermTransvectionGL, hermTransvection_apply,
        map_add, map_smul, hγ, hab, smul_eq_mul, mul_one, zero_add]
      exact mul_ne_zero hc0 hα0
    have hgeq : g = hermTransvectionGL B hb (-c) * (hermTransvectionGL B hb c * g) := by
      rw [← hermTransvectionGL_inv, inv_mul_cancel_left]
    rw [hgeq]
    exact Submonoid.mul_mem _ (Submonoid.subset_closure
      (hermTransvectionGL_mem_unitaryTransvections h hb (neg_mem hc))) hg'
  · exact key g hg hγ

end SUTwo

theorem exists_norm_one_perp_of_norm_one (h : UnitaryFieldData p f K) [FiniteDimensional K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hn : 2 ≤ Module.finrank K V) {x : V} (hx : B x x = 1) : ∃ u : V, B u u = 1 ∧ B x u = 0 := by
  obtain ⟨hsep, hdim⟩ := separatingLeft_ker_of_norm_one h hB hBl hx
  obtain ⟨e, he⟩ := h.exists_orthonormal_basis (hB.domRestrict _) hsep
  have hpos : 0 < Module.finrank K (LinearMap.ker (B x)) := by omega
  refine ⟨(e ⟨0, hpos⟩ : V), ?_, LinearMap.mem_ker.mp (e ⟨0, hpos⟩).2⟩
  have := he ⟨0, hpos⟩ ⟨0, hpos⟩
  rw [LinearMap.domRestrict₁₂_apply] at this
  simpa using this

theorem hermitian_norm_one_plane_transitivity (h : UnitaryFieldData p f K) [FiniteDimensional K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hn : Module.finrank K V = 2) {x y : V} (hx : B x x = 1) (hy : B y y = 1) :
    ∃ g ∈ Submonoid.closure (unitaryTransvections h B), (g : V →ₗ[K] V) x = y := by
  obtain ⟨u, hu, hxu⟩ := exists_norm_one_perp_of_norm_one h hB hBl hn.ge hx
  obtain ⟨v, hv, hyv⟩ := exists_norm_one_perp_of_norm_one h hB hBl hn.ge hy
  have hux : B u x = 0 := by rw [← hB.eq x u, hxu, map_zero]
  have hvy : B v y = 0 := by rw [← hB.eq y v, hyv, map_zero]
  have hf₁ : ![u, x] ∈ orthonormalFrames B 2 := mem_orthonormalFrames.mpr fun i j => by
    fin_cases i <;> fin_cases j <;> simp [hu, hx, hux, hxu]
  have hf₂ : ![v, y] ∈ orthonormalFrames B 2 := mem_orthonormalFrames.mpr fun i j => by
    fin_cases i <;> fin_cases j <;> simp [hv, hy, hvy, hyv]
  let e := frameBasis hf₁ hn.symm
  have he : ⇑e ∈ orthonormalFrames B 2 := by rw [coe_frameBasis]; exact hf₁
  have he1 : e 1 = x := by simp [e, coe_frameBasis]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : V →ₗ[K] V, ψ = e.constr K ![v, y] := ⟨_, rfl⟩
  have hψe : ∀ i, ψ (e i) = ![v, y] i := fun i => by rw [hψ, Module.Basis.constr_basis]
  have hψiso := isometry_of_mem_orthonormalFrames e he (φ := ψ)
    (by simp only [hψe]; exact hf₂)
  have hψx : ψ x = y := by rw [← he1, hψe]; rfl
  have hN := norm_det_of_isometry h e he hψiso
  have hδ0 : LinearMap.det ψ ≠ 0 := by
    intro h0
    rw [h0, UnitaryFieldData.norm, zero_mul] at hN
    exact zero_ne_one hN
  have hNinv : h.norm (LinearMap.det ψ)⁻¹ = 1 := by
    rw [UnitaryFieldData.norm, map_inv₀, ← mul_inv, ← UnitaryFieldData.norm, hN, inv_one]
  obtain ⟨k, hkiso, hkdet, hkfix⟩ := exists_isometry_det_eq_fix h (r := 1) e he hNinv
  have hkx : k x = x := by rw [← he1]; exact hkfix 0
  have hgiso : ∀ a b, B ((ψ ∘ₗ k) a) ((ψ ∘ₗ k) b) = B a b := fun a b => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hψiso, hkiso]
  refine ⟨isometryUnit hBl hgiso, mem_closure_unitaryTransvections_of_finrank_two h hB hBl hn ?_,
    ?_⟩
  · rw [mem_sesqSpecialUnitaryGroup, coe_isometryUnit, LinearMap.det_comp, hkdet,
      mul_inv_cancel₀ hδ0]
    exact ⟨(isometryUnit hBl hgiso).2, rfl⟩
  · rw [coe_isometryUnit, LinearMap.comp_apply, hkx, hψx]

theorem exists_ne_zero_norm_ne_one (h : UnitaryFieldData p f K) (hq : 2 < p ^ f) :
    ∃ s : K, s ≠ 0 ∧ h.norm s ≠ 1 := by
  by_contra! hcon
  have := h.finite
  have hle : Nat.card Kˣ ≤ Nat.card {t : K // h.norm t = 1} :=
    Nat.card_le_card_of_injective (fun u => ⟨u, hcon u u.ne_zero⟩)
      fun u v huv => Units.ext (congrArg Subtype.val huv)
  rw [card_norm_eq_one h, Nat.card_units, h.card_eq_sq, Nat.sub_le_iff_le_add] at hle
  nlinarith

theorem hermitian_norm_one_connectivity (h : UnitaryFieldData p f K) [FiniteDimensional K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hn : 4 ≤ Module.finrank K V ∨ (Module.finrank K V = 3 ∧ 2 < p ^ f)) {x y : V}
    (hx : B x x = 1) (hy : B y y = 1) :
    ∃ z : V, B z z = 1 ∧
      (∃ P : Submodule K V, Module.finrank K P = 2 ∧ (B.domRestrict₁₂ P P).SeparatingLeft ∧
        x ∈ P ∧ z ∈ P) ∧
      ∃ P : Submodule K V, Module.finrank K P = 2 ∧ (B.domRestrict₁₂ P P).SeparatingLeft ∧
        z ∈ P ∧ y ∈ P := by
  have hn2 : 2 ≤ Module.finrank K V := by omega
  have horth : ∀ u v : V, B u u = 1 → B v v = 1 → B u v = 0 →
      ∃ P : Submodule K V, Module.finrank K P = 2 ∧ (B.domRestrict₁₂ P P).SeparatingLeft ∧
        u ∈ P ∧ v ∈ P := by
    intro u v hu hv huv
    obtain ⟨h1, h2⟩ := span_pair_nondegenerate (B := B) (u₁ := u) (u₂ := v)
      (by rw [hu, hv, huv]; simp)
    exact ⟨_, h1, h2, Submodule.subset_span (by simp), Submodule.subset_span (by simp)⟩
  by_cases hd : B x x * B y y - B x y * B y x = 0
  swap
  · obtain ⟨h1, h2⟩ := span_pair_nondegenerate hd
    exact ⟨y, hy, ⟨_, h1, h2, Submodule.subset_span (by simp), Submodule.subset_span (by simp)⟩,
      ⟨_, h1, h2, Submodule.subset_span (by simp), Submodule.subset_span (by simp)⟩⟩
  obtain ⟨w, hw⟩ : ∃ w : V, w = y - B x y • x := ⟨_, rfl⟩
  have hy' : y = w + B x y • x := by rw [hw, sub_add_cancel]
  have hyx : B y x = h.bar (B x y) := (hB.eq x y).symm
  have hxw : B x w = 0 := by rw [hw, map_sub, map_smul, hx, smul_eq_mul, mul_one, sub_self]
  have hww : B w w = 0 := by
    rw [hw]
    simp only [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hx,
      hy, hyx]
    rw [hx, hy, hyx] at hd
    linear_combination hd
  by_cases hw0 : w = 0
  · obtain ⟨u, hu, hxu⟩ := exists_norm_one_perp_of_norm_one h hB hBl hn2 hx
    obtain ⟨P, hP2, hPs, hxP, -⟩ := horth x u hx hu hxu
    have hyP : y ∈ P := by
      rw [hy', hw0, zero_add]
      exact P.smul_mem _ hxP
    exact ⟨y, hy, ⟨P, hP2, hPs, hxP, hyP⟩, ⟨P, hP2, hPs, hyP, hyP⟩⟩
  obtain ⟨hWsep, hWdim⟩ := separatingLeft_ker_of_norm_one h hB hBl hx
  have hw'0 : (⟨w, hxw⟩ : LinearMap.ker (B x)) ≠ 0 := fun h0 => hw0 (congrArg Subtype.val h0)
  have hw'w' : B.domRestrict₁₂ (LinearMap.ker (B x)) (LinearMap.ker (B x)) ⟨w, hxw⟩
      ⟨w, hxw⟩ = 0 := by
    rw [LinearMap.domRestrict₁₂_apply]
    exact hww
  rcases hn with hn4 | ⟨hn3, hq⟩
  · obtain ⟨z', hz', hwz'⟩ := exists_norm_one_perp_of_isotropic h (hB.domRestrict _) hWsep
      (by omega) hw'0 hw'w'
    rw [LinearMap.domRestrict₁₂_apply] at hz' hwz'
    have hxz : B x z' = 0 := LinearMap.mem_ker.mp z'.2
    have hyz : B y z' = 0 := by
      rw [hy', map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, hwz', hxz,
        smul_zero, add_zero]
    have hzy : B z' y = 0 := by rw [← hB.eq y, hyz, map_zero]
    exact ⟨z', hz', horth x z' hx hz' hxz, horth z' y hz' hy hzy⟩
  · obtain ⟨⟨v', hwv', hv'⟩, -⟩ := hermitian_hyperbolic_splitting h (hB.domRestrict _) hWsep hw'0
      hw'w'
    rw [LinearMap.domRestrict₁₂_apply] at hwv' hv'
    have hxv : B x v' = 0 := LinearMap.mem_ker.mp v'.2
    have hvw : B v' w = 1 := by
      rw [← hB.eq, hwv', map_one]
    obtain ⟨s, hs0, hs1⟩ := exists_ne_zero_norm_ne_one h hq
    obtain ⟨t₀, ht₀⟩ := h.traceLin_surjective 1
    have ht₀' : t₀ + h.bar t₀ = 1 := by
      simpa [UnitaryFieldData.trace] using congrArg Subtype.val ht₀
    obtain ⟨r, hr⟩ : ∃ r : K, r = h.bar (t₀ / s) := ⟨_, rfl⟩
    have hrs : h.bar r * s = t₀ := by rw [hr, h.bar_bar, div_mul_cancel₀ _ hs0]
    have hrs' : r * h.bar s = h.bar t₀ := by
      rw [← hrs, map_mul, h.bar_bar]
    obtain ⟨z, hz⟩ : ∃ z : V, z = r • w + s • (v' : V) := ⟨_, rfl⟩
    have hzz : B z z = 1 := by
      rw [hz]
      simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hww, hwv', hvw, hv']
      linear_combination hrs + hrs' + ht₀'
    have hxz : B x z = 0 := by
      rw [hz, map_add, map_smul, map_smul, hxw, hxv, smul_zero, smul_zero, add_zero]
    have hyz : B y z = s := by
      rw [hy', hz]
      simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hww, hwv', hxw, hxv, RingHom.id_apply]
      ring
    have hzy : B z y = h.bar s := by rw [← hB.eq y, hyz]
    obtain ⟨h1, h2⟩ := span_pair_nondegenerate (B := B) (u₁ := z) (u₂ := y) (by
      rw [hzz, hy, hzy, hyz, one_mul]
      intro h0
      apply hs1
      rw [UnitaryFieldData.norm, mul_comm]
      linear_combination -h0)
    exact ⟨z, hzz, horth x z hx hzz hxz,
      ⟨_, h1, h2, Submodule.subset_span (by simp), Submodule.subset_span (by simp)⟩⟩

end CFSG.LinearGroups
