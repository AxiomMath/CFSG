module

public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryTrace
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryHermitian
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal

public section

namespace CFSG.LinearGroups

open CFSG.LocalAnalysis.ComponentInitial Matrix

variable {p f : ℕ} {K : Type*} [Field K]

section Heisenberg

@[expose] noncomputable def heisenbergMatrix (h : UnitaryFieldData p f K) (a b : K) :
    Matrix (Fin 3) (Fin 3) K :=
  !![1, -h.bar a, b; 0, 1, a; 0, 0, 1]

theorem heisenbergMatrix_mul (h : UnitaryFieldData p f K) (a b c d : K) :
    heisenbergMatrix h a b * heisenbergMatrix h c d =
      heisenbergMatrix h (a + c) (b + d - h.bar a * c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heisenbergMatrix, Matrix.mul_apply, Fin.sum_univ_three, map_add] <;> ring

theorem heisenbergMatrix_zero_zero (h : UnitaryFieldData p f K) :
    heisenbergMatrix h 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heisenbergMatrix]

theorem heisenbergMatrix_inv (h : UnitaryFieldData p f K) (a b : K) :
    (heisenbergMatrix h a b)⁻¹ = heisenbergMatrix h (-a) (-b - h.bar a * a) := by
  apply Matrix.inv_eq_right_inv
  rw [heisenbergMatrix_mul, ← heisenbergMatrix_zero_zero h]
  congr 1 <;> ring

theorem unitary_heisenberg_commutator (h : UnitaryFieldData p f K) :
    (∀ a b c d : K, h.norm a + h.trace b = 0 → h.norm c + h.trace d = 0 →
      heisenbergMatrix h a b * heisenbergMatrix h c d * (heisenbergMatrix h a b)⁻¹ *
          (heisenbergMatrix h c d)⁻¹ =
        heisenbergMatrix h 0 (h.bar c * a - h.bar a * c)) ∧
      ∀ t ∈ h.traceZero, ∃ b r d : K, h.trace b = -1 ∧ h.trace d = -h.norm r ∧
        heisenbergMatrix h 1 b * heisenbergMatrix h r d * (heisenbergMatrix h 1 b)⁻¹ *
            (heisenbergMatrix h r d)⁻¹ = heisenbergMatrix h 0 t := by
  have hcomm : ∀ a b c d : K,
      heisenbergMatrix h a b * heisenbergMatrix h c d * (heisenbergMatrix h a b)⁻¹ *
          (heisenbergMatrix h c d)⁻¹ =
        heisenbergMatrix h 0 (h.bar c * a - h.bar a * c) := by
    intro a b c d
    rw [heisenbergMatrix_inv, heisenbergMatrix_inv, heisenbergMatrix_mul, heisenbergMatrix_mul,
      heisenbergMatrix_mul]
    congr 1
    · ring
    · simp only [map_add, map_neg]
      ring
  refine ⟨fun a b c d _ _ => hcomm a b c d, fun t ht => ?_⟩
  obtain ⟨r, hr⟩ : ∃ r : K, h.bar r - r = t := by
    have : t ∈ h.barSub.range := by rw [h.range_barSub]; exact ht
    obtain ⟨r, hr⟩ := this
    exact ⟨r, by rw [← hr, UnitaryFieldData.barSub_apply]⟩
  obtain ⟨b, hb⟩ := h.traceLin_surjective (-1)
  obtain ⟨d, hd⟩ := h.traceLin_surjective (-⟨h.norm r, h.norm_mem_fixedField r⟩)
  refine ⟨b, r, d, ?_, ?_, ?_⟩
  · simpa using congrArg Subtype.val hb
  · simpa using congrArg Subtype.val hd
  · rw [hcomm, map_one, one_mul, mul_one, hr]

end Heisenberg

section Transvection

variable {V : Type*} [AddCommGroup V] [Module K V] {σ : K →+* K}

@[expose] def hermTransvection (B : V →ₛₗ[σ] V →ₗ[K] K) (a : V) (c : K) : V →ₗ[K] V :=
  LinearMap.transvection (c • B a) a

theorem hermTransvection_apply (B : V →ₛₗ[σ] V →ₗ[K] K) (a : V) (c : K) (x : V) :
    hermTransvection B a c x = x + (c * B a x) • a := by
  simp [hermTransvection, LinearMap.transvection.apply]

theorem hermTransvection_comp (B : V →ₛₗ[σ] V →ₗ[K] K) {a : V} (ha : B a a = 0) (c d : K) :
    hermTransvection B a c ∘ₗ hermTransvection B a d = hermTransvection B a (c + d) := by
  ext x
  simp only [LinearMap.comp_apply, hermTransvection_apply, map_add, map_smul, ha, mul_zero]
  module

theorem hermTransvection_zero (B : V →ₛₗ[σ] V →ₗ[K] K) (a : V) :
    hermTransvection B a 0 = LinearMap.id := by
  ext x
  simp [hermTransvection_apply]

theorem hermTransvection_isometry {B : V →ₛₗ[σ] V →ₗ[K] K} (hB : B.IsSymm) {a : V}
    (ha : B a a = 0) {c : K} (hc : c + σ c = 0) (x y : V) :
    B (hermTransvection B a c x) (hermTransvection B a c y) = B x y := by
  have hxa : B x a = σ (B a x) := (hB.eq a x).symm
  simp only [hermTransvection_apply, map_add, LinearMap.add_apply, map_smulₛₗ,
    LinearMap.smul_apply, smul_eq_mul, ha, hxa, map_mul]
  linear_combination σ (B a x) * B a y * hc

@[expose] noncomputable def hermTransvectionGL (B : V →ₛₗ[σ] V →ₗ[K] K) {a : V} (ha : B a a = 0)
    (c : K) : LinearMap.GeneralLinearGroup K V :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv
    (LinearEquiv.transvection (f := c • B a) (v := a) (by simp [ha]))

theorem coe_hermTransvectionGL (B : V →ₛₗ[σ] V →ₗ[K] K) {a : V} (ha : B a a = 0) (c : K) :
    (hermTransvectionGL B ha c : V →ₗ[K] V) = hermTransvection B a c :=
  rfl

theorem det_hermTransvection (B : V →ₛₗ[σ] V →ₗ[K] K) {a : V} (ha : B a a = 0) (c : K) :
    LinearMap.det (hermTransvection B a c) = 1 := by
  have := LinearEquiv.transvection.det_eq_one (f := c • B a) (v := a) (by simp [ha])
  rw [← Units.val_inj, LinearEquiv.coe_det, Units.val_one] at this
  exact this

theorem generalLinearGroup_apply_inv_apply (g : LinearMap.GeneralLinearGroup K V) (x : V) :
    (g : V →ₗ[K] V) (((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x) = x := by
  rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, Module.End.one_apply]

theorem conj_hermTransvection {B : V →ₛₗ[σ] V →ₗ[K] K} {g : LinearMap.GeneralLinearGroup K V}
    (hg : g ∈ sesqUnitaryGroup B) (a : V) (c : K) :
    (g : V →ₗ[K] V) ∘ₗ hermTransvection B a c ∘ₗ
        ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) =
      hermTransvection B ((g : V →ₗ[K] V) a) c := by
  ext x
  have hiso := (mem_sesqUnitaryGroup.mp hg) a (((g⁻¹ : LinearMap.GeneralLinearGroup K V) :
    V →ₗ[K] V) x)
  rw [generalLinearGroup_apply_inv_apply] at hiso
  simp only [LinearMap.comp_apply, hermTransvection_apply, map_add, map_smul,
    generalLinearGroup_apply_inv_apply, hiso]

theorem hermTransvectionGL_mul (B : V →ₛₗ[σ] V →ₗ[K] K) {a : V} (ha : B a a = 0) (c d : K) :
    hermTransvectionGL B ha c * hermTransvectionGL B ha d = hermTransvectionGL B ha (c + d) := by
  apply Units.ext
  rw [Units.val_mul, coe_hermTransvectionGL, coe_hermTransvectionGL, coe_hermTransvectionGL,
    Module.End.mul_eq_comp, hermTransvection_comp B ha]

theorem hermTransvectionGL_inv (B : V →ₛₗ[σ] V →ₗ[K] K) {a : V} (ha : B a a = 0) (c : K) :
    (hermTransvectionGL B ha c)⁻¹ = hermTransvectionGL B ha (-c) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [hermTransvectionGL_mul, add_neg_cancel]
  apply Units.ext
  rw [coe_hermTransvectionGL, hermTransvection_zero, Units.val_one]
  rfl

end Transvection

theorem hermitian_unitary_transvection (h : UnitaryFieldData p f K) {V : Type*} [AddCommGroup V]
    [Module K V] {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) {a : V} (ha : B a a = 0) :
    (∀ c x, hermTransvection B a c x = x + (c * B a x) • a) ∧
      (∀ c ∈ h.traceZero, hermTransvectionGL B ha c ∈ sesqSpecialUnitaryGroup B) ∧
      (∀ c ∈ h.traceZero, ∀ d ∈ h.traceZero,
        hermTransvectionGL B ha c * hermTransvectionGL B ha d = hermTransvectionGL B ha (c + d)) ∧
      (∀ c ∈ h.traceZero, (hermTransvectionGL B ha c)⁻¹ = hermTransvectionGL B ha (-c)) ∧
      (∀ c ∈ h.traceZero, ∀ g ∈ sesqUnitaryGroup B,
        (g : V →ₗ[K] V) ∘ₗ hermTransvection B a c ∘ₗ
            ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) =
          hermTransvection B ((g : V →ₗ[K] V) a) c) ∧
      ∀ c ∈ h.traceZero, ∀ μ : K,
        hermTransvection B (μ • a) c = hermTransvection B a (h.norm μ * c) := by
  refine ⟨hermTransvection_apply B a, fun c hc => ?_,
    fun c _ d _ => hermTransvectionGL_mul B ha c d,
    fun c _ => hermTransvectionGL_inv B ha c, fun c _ g hg => conj_hermTransvection hg a c,
    fun c _ μ => ?_⟩
  · rw [mem_sesqSpecialUnitaryGroup, mem_sesqUnitaryGroup, coe_hermTransvectionGL]
    exact ⟨hermTransvection_isometry hB ha hc, det_hermTransvection B ha c⟩
  · ext x
    simp only [hermTransvection_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_smul,
      UnitaryFieldData.norm]
    congr 2
    ring

section Hyperbolic

variable {V : Type*} [AddCommGroup V] [Module K V]

theorem hermitian_hyperbolic_splitting (h : UnitaryFieldData p f K) [FiniteDimensional K V]
    {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft) {a : V} (ha0 : a ≠ 0)
    (ha : B a a = 0) :
    (∃ b : V, B a b = 1 ∧ B b b = 0) ∧
      ∀ b : V, B a b = 1 → B b b = 0 →
        Module.finrank K (Submodule.span K {a, b}) = 2 ∧
        (B.domRestrict₁₂ (Submodule.span K {a, b}) (Submodule.span K {a, b})).SeparatingLeft ∧
        IsCompl (Submodule.span K {a, b}) ((Submodule.span K {a, b}).orthogonalBilin B) ∧
        (B.domRestrict₁₂ ((Submodule.span K {a, b}).orthogonalBilin B)
          ((Submodule.span K {a, b}).orthogonalBilin B)).SeparatingLeft ∧
        Module.finrank K ((Submodule.span K {a, b}).orthogonalBilin B) =
          Module.finrank K V - 2 := by
  have hsymm : ∀ x y, B y x = h.bar (B x y) := fun x y => (hB.eq x y).symm
  refine ⟨?_, fun b hab hbb => ?_⟩
  ·
    obtain ⟨v, hv⟩ : ∃ v, B a v ≠ 0 := by
      by_contra! hz
      exact ha0 (hBl a hz)
    obtain ⟨v', hav'⟩ : ∃ v', B a v' = 1 :=
      ⟨(B a v)⁻¹ • v, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hv]⟩
    obtain ⟨d, hd⟩ : ∃ d, B v' v' = d := ⟨_, rfl⟩
    have hdF : h.bar d = d := by rw [← hd]; exact hB.eq v' v'
    obtain ⟨c, hc⟩ := h.traceLin_surjective (-⟨d, hdF⟩)
    have hc' : c + h.bar c = -d := by simpa [UnitaryFieldData.trace] using congrArg Subtype.val hc
    refine ⟨v' + c • a, ?_, ?_⟩
    · rw [map_add, map_smul, hav', ha, smul_zero, add_zero]
    · simp only [map_add, LinearMap.add_apply, map_smul, map_smulₛₗ, LinearMap.smul_apply,
        smul_eq_mul, ha, mul_zero, add_zero, hav', mul_one, hsymm a v', map_one, hd]
      linear_combination hc'
  · set H := Submodule.span K {a, b} with hH
    set W := H.orthogonalBilin B with hW
    have hba : B b a = 1 := by rw [hsymm, hab, map_one]
    have hdecomp : ∀ x : V, x - (B b x • a + B a x • b) ∈ W := by
      intro x
      rw [hW, Submodule.mem_orthogonalBilin]
      intro n hn
      obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hn
      simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, map_sub,
        smul_eq_mul, ha, hab, hba, hbb, RingHom.id_apply]
      ring
    have hdisj : Disjoint H W := by
      rw [Submodule.disjoint_def]
      intro z hzH hzW
      obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hzH
      have h1 := (Submodule.mem_orthogonalBilin.mp hzW) a (Submodule.subset_span (by simp))
      have h2 := (Submodule.mem_orthogonalBilin.mp hzW) b (Submodule.subset_span (by simp))
      simp only [map_add, map_smul, smul_eq_mul, ha, hab, hba, hbb, mul_zero, zero_add, mul_one,
        add_zero] at h1 h2
      rw [h1, h2, zero_smul, zero_smul, add_zero]
    have hcompl : IsCompl H W := by
      refine ⟨hdisj, ?_⟩
      rw [codisjoint_iff, eq_top_iff]
      intro x _
      have hx : x = (B b x • a + B a x • b) + (x - (B b x • a + B a x • b)) := by abel
      rw [hx]
      refine Submodule.add_mem_sup ?_ (hdecomp x)
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    have hli : LinearIndependent K ![a, b] := by
      rw [LinearIndependent.pair_iff' ha0]
      intro s hs
      have := congrArg (B a) hs
      rw [map_smul, ha, smul_zero, hab] at this
      exact zero_ne_one this
    have hfinH : Module.finrank K H = 2 := by
      have hrange : Set.range ![a, b] = {a, b} := by
        ext x
        simp [eq_comm, or_comm]
      rw [hH, ← hrange, finrank_span_eq_card hli, Fintype.card_fin]
    refine ⟨hfinH, ?_, hcompl, ?_, ?_⟩
    · rintro ⟨z, hz⟩ hz0
      have h1 := hz0 ⟨a, Submodule.subset_span (by simp)⟩
      have h2 := hz0 ⟨b, Submodule.subset_span (by simp)⟩
      simp only [LinearMap.domRestrict₁₂_apply] at h1 h2
      obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hz
      simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, ha,
        hab, hba, hbb, mul_zero, zero_add, mul_one, add_zero] at h1 h2
      have ht : t = 0 := (map_eq_zero h.bar).mp h1
      have hs : s = 0 := (map_eq_zero h.bar).mp h2
      simp [hs, ht]
    · rintro ⟨z, hz⟩ hz0
      simp only [LinearMap.domRestrict₁₂_apply] at hz0
      have hzV : ∀ x : V, B z x = 0 := by
        intro x
        have hx : x = (B b x • a + B a x • b) + (x - (B b x • a + B a x • b)) := by abel
        rw [hx, map_add]
        have hzH : ∀ y ∈ H, B z y = 0 := by
          intro y hy
          rw [hsymm, (Submodule.mem_orthogonalBilin.mp hz) y hy, map_zero]
        rw [hzH _ (Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))), zero_add]
        exact hz0 ⟨_, hdecomp x⟩
      exact Subtype.ext (hBl z hzV)
    · have := Submodule.finrank_add_eq_of_isCompl hcompl
      omega

end Hyperbolic

end CFSG.LinearGroups
