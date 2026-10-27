module

public import CFSG.ClassicalGroups.UnitaryFlag.WittBasis

public section

namespace CFSG.ClassicalGroups.UnitaryFlag

open CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups

variable {p f : ℕ} {E : Type*} [Field E] {V : Type*} [AddCommGroup V] [Module E V]

theorem exists_apply_eq_smul_of_fixes {h : UnitaryFieldData p f E} {B : V →ₛₗ[h.bar] V →ₗ[E] E}
    {σ : E →+* E} {T : V →ₛₗ[σ] V}
    (hfix : ∀ L : Submodule E V, Module.finrank E L = 1 → (∀ x ∈ L, ∀ y ∈ L, B x y = 0) →
      T '' (L : Set V) = L)
    {v : V} (hv : B v v = 0) : ∃ c : E, T v = c • v := by
  by_cases hv0 : v = 0
  · exact ⟨0, by rw [hv0, map_zero, smul_zero]⟩
  have hiso : ∀ x ∈ Submodule.span E {v}, ∀ y ∈ Submodule.span E {v}, B x y = 0 := by
    intro x hx y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hy
    simp only [LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, hv, mul_zero]
  have hmem : T v ∈ (Submodule.span E {v} : Set V) := by
    rw [← hfix _ (finrank_span_singleton hv0) hiso]
    exact ⟨v, Submodule.mem_span_singleton_self v, rfl⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  exact ⟨c, hc.symm⟩

theorem unitary_semilinear_isotropic_point_kernel (h : UnitaryFieldData p f E)
    [FiniteDimensional E V] (hn : 3 ≤ Module.finrank E V) {B : V →ₛₗ[h.bar] V →ₗ[E] E}
    (hB : B.IsSymm) (hBl : B.SeparatingLeft) :
    (∀ (σ : E ≃+* E) (μ : E), μ ≠ 0 → h.bar μ = μ → ∀ T : V →ₛₗ[σ.toRingHom] V,
      Function.Bijective T → (∀ v w, B (T v) (T w) = μ * σ (B v w)) →
      (∀ L : Submodule E V, Module.finrank E L = 1 → (∀ x ∈ L, ∀ y ∈ L, B x y = 0) →
        T '' (L : Set V) = L) →
      σ = RingEquiv.refl E ∧ ∃ c : E, c ≠ 0 ∧ ∀ v, T v = c • v) ∧
    ∀ c : E, c ≠ 0 →
      Function.Bijective (fun v : V => c • v) ∧
      (∃ μ : E, μ ≠ 0 ∧ h.bar μ = μ ∧ ∀ v w, B (c • v) (c • w) = μ * B v w) ∧
      ∀ L : Submodule E V, Module.finrank E L = 1 → (∀ x ∈ L, ∀ y ∈ L, B x y = 0) →
        (fun v : V => c • v) '' (L : Set V) = L := by
  have hsymm : ∀ x y, B y x = h.bar (B x y) := fun x y => (hB.eq x y).symm
  refine ⟨fun σ μ _ _ T hT hsim hfix => ?_, fun c hc => ?_⟩
  · have hσ : ∀ x, σ.toRingHom x = σ x := fun _ => rfl
    obtain ⟨e, he0, he⟩ := (hermitian_witt_basis h hB hBl rfl).2.1 (by omega)
    obtain ⟨⟨f, hef, hff⟩, hsplit⟩ := hermitian_hyperbolic_splitting h hB hBl he0 he
    obtain ⟨-, -, -, -, hWdim⟩ := hsplit f hef hff
    set W := (Submodule.span E {e, f}).orthogonalBilin B with hW
    have hfe : B f e = 1 := by rw [hsymm, hef, map_one]
    have hmemW : ∀ w ∈ W, B e w = 0 ∧ B f w = 0 := fun w hw =>
      ⟨hw e (Submodule.subset_span (by simp)), hw f (Submodule.subset_span (by simp))⟩
    obtain ⟨w₀, hw₀W, hw₀⟩ : ∃ w ∈ W, w ≠ 0 := by
      refine Submodule.exists_mem_ne_zero_of_ne_bot fun hbot => ?_
      rw [hbot, finrank_bot] at hWdim
      omega
    obtain ⟨hew₀, hfw₀⟩ := hmemW w₀ hw₀W
    obtain ⟨a, ha⟩ := exists_apply_eq_smul_of_fixes hfix he
    obtain ⟨b, hb⟩ := exists_apply_eq_smul_of_fixes hfix hff
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_smul, ← map_zero T] at ha
      exact he0 (hT.1 ha)
    have hbar0 : h.bar a ≠ 0 := (map_ne_zero h.bar).2 ha0
    have hbbar0 : h.bar b ≠ 0 := (map_ne_zero h.bar).2 (by
      rintro rfl
      rw [zero_smul, ← map_zero T] at hb
      exact (fun hf0 : f = 0 => by rw [hf0, map_zero] at hef; exact zero_ne_one hef) (hT.1 hb))
    have horth : ∀ w, B e w = 0 → B f w = 0 → B e (T w) = 0 ∧ B f (T w) = 0 := by
      intro w hew hfw
      have h1 := hsim e w
      have h2 := hsim f w
      rw [ha, LinearMap.map_smulₛₗ₂, hew, map_zero, mul_zero, smul_eq_mul] at h1
      rw [hb, LinearMap.map_smulₛₗ₂, hfw, map_zero, mul_zero, smul_eq_mul] at h2
      exact ⟨(mul_eq_zero.1 h1).resolve_left hbar0, (mul_eq_zero.1 h2).resolve_left hbbar0⟩
    have hW' : ∀ w, B e w = 0 → B f w = 0 → T w = a • w := by
      intro w hew hfw
      have hwe : B w e = 0 := by rw [hsymm, hew, map_zero]
      have hwf : B w f = 0 := by rw [hsymm, hfw, map_zero]
      have hww : h.bar (B w w) = B w w := (hsymm w w).symm
      obtain ⟨c, hc⟩ := h.traceLin_surjective (-⟨B w w, hww⟩)
      have hc' : c + h.bar c = -B w w := by
        simpa [UnitaryFieldData.trace] using congrArg Subtype.val hc
      have hv : B (e + w + c • f) (e + w + c • f) = 0 := by
        simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.map_smulₛₗ₂, smul_eq_mul,
          he, hff, hef, hfe, hew, hfw, hwe, hwf]
        linear_combination hc'
      obtain ⟨l, hl⟩ := exists_apply_eq_smul_of_fixes hfix hv
      obtain ⟨hTe, hTf⟩ := horth w hew hfw
      have hTv : T (e + w + c • f) = a • e + T w + (σ c * b) • f := by
        rw [map_add, map_add, map_smulₛₗ, ha, hb, hσ, smul_smul]
      rw [hTv] at hl
      have hlf := congrArg (B f) hl
      have hle := congrArg (B e) hl
      simp only [map_add, map_smul, smul_eq_mul, he, hff, hef, hfe, hew, hfw, hTe, hTf] at hlf hle
      have hla : l = a := by linear_combination -hlf
      have hcb : σ c * b = a * c := by rw [← hla]; linear_combination hle
      rw [hla, hcb] at hl
      have : T w = a • (e + w + c • f) - a • e - (a * c) • f := by rw [← hl]; abel
      rw [this, smul_add, smul_add, smul_smul]
      abel
    have hσid : ∀ x, σ x = x := by
      intro x
      have h1 := hW' (x • w₀) (by rw [map_smul, hew₀, smul_zero])
        (by rw [map_smul, hfw₀, smul_zero])
      rw [map_smulₛₗ, hW' w₀ hew₀ hfw₀, hσ, smul_smul, smul_smul] at h1
      have h2 := smul_left_injective E hw₀ h1
      exact mul_left_cancel₀ ha0 (by rw [mul_comm]; exact h2)
    obtain ⟨t, ht, ht0⟩ := h.exists_mem_traceZero_ne_zero
    have ht' : t + h.bar t = 0 := (UnitaryFieldData.mem_traceZero h).1 ht
    have hba : b = a := by
      have hv : B (e + t • f) (e + t • f) = 0 := by
        simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.map_smulₛₗ₂, smul_eq_mul,
          he, hff, hef, hfe]
        linear_combination ht'
      obtain ⟨l, hl⟩ := exists_apply_eq_smul_of_fixes hfix hv
      rw [map_add, map_smulₛₗ, ha, hb, hσ, hσid, smul_smul] at hl
      have hlf := congrArg (B f) hl
      have hle := congrArg (B e) hl
      simp only [map_add, map_smul, smul_eq_mul, he, hff, hef, hfe] at hlf hle
      have hla : l = a := by linear_combination -hlf
      rw [hla] at hle
      exact mul_left_cancel₀ ht0 (by linear_combination hle)
    refine ⟨RingEquiv.ext hσid, a, ha0, fun x => ?_⟩
    set w := x - (B f x • e + B e x • f) with hw
    have hew : B e w = 0 := by
      simp only [hw, map_sub, map_add, map_smul, smul_eq_mul, he, hef]
      ring
    have hfw : B f w = 0 := by
      simp only [hw, map_sub, map_add, map_smul, smul_eq_mul, hff, hfe]
      ring
    have hx : x = B f x • e + B e x • f + w := by rw [hw]; abel
    rw [hx, map_add, map_add, map_smulₛₗ, map_smulₛₗ, ha, hb, hba, hW' w hew hfw, hσ, hσ, hσid,
      hσid, smul_smul, smul_smul, smul_add, smul_add, smul_smul, smul_smul, mul_comm a,
      mul_comm a]
  · refine ⟨⟨smul_right_injective V hc, fun v => ⟨c⁻¹ • v, by simp only [smul_smul,
      mul_inv_cancel₀ hc, one_smul]⟩⟩,
      ⟨c * h.bar c, mul_ne_zero hc ((map_ne_zero h.bar).2 hc), ?_, fun v w => ?_⟩,
      fun L _ _ => ?_⟩
    · rw [map_mul, UnitaryFieldData.bar_bar, mul_comm]
    · rw [LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, smul_eq_mul]
      ring
    · ext v
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact L.smul_mem c hu
      · intro hv
        exact ⟨c⁻¹ • v, L.smul_mem _ hv, by simp only [smul_smul, mul_inv_cancel₀ hc, one_smul]⟩

end CFSG.ClassicalGroups.UnitaryFlag
