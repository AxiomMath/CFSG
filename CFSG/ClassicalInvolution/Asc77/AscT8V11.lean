module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.ClassicalInvolution.Asc77

open scoped commutatorElement

namespace T8V

section Central

variable {G : Type*} [Group G]



theorem comm_center_mul_left {c : G} (hc : c ∈ Subgroup.center G) (a b : G) :
    ⁅c * a, b⁆ = ⁅a, b⁆ := by
  have h := Subgroup.mem_center_iff.mp hc (a * b * a⁻¹)
  simp only [commutatorElement_def, mul_inv_rev]
  calc c * a * b * (a⁻¹ * c⁻¹) * b⁻¹ = (c * (a * b * a⁻¹)) * c⁻¹ * b⁻¹ := by group
    _ = ((a * b * a⁻¹) * c) * c⁻¹ * b⁻¹ := by rw [← h]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem comm_center_mul_right {c : G} (hc : c ∈ Subgroup.center G) (a b : G) :
    ⁅a, c * b⁆ = ⁅a, b⁆ := by
  have h := Subgroup.mem_center_iff.mp hc (a * b * a⁻¹ * b⁻¹)
  have h2 := Subgroup.mem_center_iff.mp hc a
  simp only [commutatorElement_def, mul_inv_rev]
  calc a * (c * b) * a⁻¹ * (b⁻¹ * c⁻¹) = (a * c) * b * a⁻¹ * b⁻¹ * c⁻¹ := by group
    _ = (c * a) * b * a⁻¹ * b⁻¹ * c⁻¹ := by rw [h2]
    _ = (c * (a * b * a⁻¹ * b⁻¹)) * c⁻¹ := by group
    _ = ((a * b * a⁻¹ * b⁻¹) * c) * c⁻¹ := by rw [← h]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem eq_of_central_ratio (φ : G →* G) {P : Subgroup G} (hP : P ≤ ⁅P, P⁆)
    (h : ∀ p ∈ P, φ p * p⁻¹ ∈ Subgroup.center G) : ∀ p ∈ P, φ p = p := by
  have hfix : ∀ p ∈ ⁅P, P⁆, φ p = p := by
    intro p hp
    refine Subgroup.closure_induction (p := fun p _ => φ p = p) ?_ (by simp) ?_ ?_ hp
    · rintro _ ⟨a, ha, b, hb, rfl⟩
      have hφa : φ a = (φ a * a⁻¹) * a := by group
      have hφb : φ b = (φ b * b⁻¹) * b := by group
      have e : φ ⁅a, b⁆ = ⁅φ a, φ b⁆ := by simp [commutatorElement_def]
      rw [e, hφa, hφb, comm_center_mul_left (h a ha), comm_center_mul_right (h b hb)]
    · intro a b _ _ ha hb
      rw [map_mul, ha, hb]
    · intro a _ ha
      rw [map_inv, ha]
  intro p hp
  exact hfix p (hP hp)

end Central

section Perf

variable {S X : Type*} [Group S] [Group X]

theorem top_le_commutator_of_perfect (hS : Group.IsPerfect S) :
    (⊤ : Subgroup S) ≤ ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ := by
  have h : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ = ⊤ := by
    have := hS.commutator_eq_top
    rwa [commutator_def] at this
  rw [h]

theorem mem_center_of_map_mem_center (hS : Group.IsPerfect S) (ψ : S →* X)
    (hψ : ψ.ker ≤ Subgroup.center S) {s : S} (hs : ψ s ∈ Subgroup.center X) :
    s ∈ Subgroup.center S := by
  have h := eq_of_central_ratio (MulAut.conj s).toMonoidHom (P := ⊤)
    (top_le_commutator_of_perfect hS) (fun y _ => by
    have : (MulAut.conj s).toMonoidHom y * y⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
      have := Subgroup.mem_center_iff.mp hs (ψ y)
      calc ψ s * ψ y * (ψ s)⁻¹ * (ψ y)⁻¹ = (ψ y * ψ s) * (ψ s)⁻¹ * (ψ y)⁻¹ := by rw [this]
        _ = 1 := by group
    exact hψ this)
  rw [Subgroup.mem_center_iff]
  intro y
  have := h y (Subgroup.mem_top y)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  calc y * s = (s * y * s⁻¹) * s := by rw [this]
    _ = s * y := by group

theorem comm_of_map_comm (ψ : S →* X) (hψ : ψ.ker ≤ Subgroup.center S) {R : Subgroup S}
    (hR : R ≤ ⁅R, R⁆) {s : S} (hs : ∀ r ∈ R, ψ s * ψ r = ψ r * ψ s) :
    ∀ r ∈ R, s * r = r * s := by
  have h := eq_of_central_ratio (MulAut.conj s).toMonoidHom (P := R) hR (fun y hy => by
    have : (MulAut.conj s).toMonoidHom y * y⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
      have := hs y hy
      calc ψ s * ψ y * (ψ s)⁻¹ * (ψ y)⁻¹ = (ψ y * ψ s) * (ψ s)⁻¹ * (ψ y)⁻¹ := by rw [this]
        _ = 1 := by group
    exact hψ this)
  intro y hy
  have := h y hy
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  calc s * y = (s * y * s⁻¹) * s := by group
    _ = y * s := by rw [this]

end Perf


section Bridge

variable {S X P : Type*} [Group S] [Group X] [Group P]

theorem sq_eq_one_of_autVac (hS : Group.IsPerfect S) (ψ : S →* X) (hψs : Function.Surjective ψ)
    (hψ : ψ.ker ≤ Subgroup.center S) (π : S →* P) (hπ : Function.Surjective π)
    (hπk : π.ker = Subgroup.center S) {R R' : Subgroup S}
    (hvac : ∀ φ : MulAut P, (∀ r ∈ R, φ (π r) = π r) → (∀ r ∈ R', φ (π r) = π r) →
      φ * φ * (φ * φ) = 1 → φ * φ = 1)
    (σ : MulAut X) (hσR : ∀ r ∈ R, σ (ψ r) = ψ r) (hσR' : ∀ r ∈ R', σ (ψ r) = ψ r)
    (hσ4 : σ * σ * (σ * σ) = 1) : σ * σ = 1 := by
  set Z := Subgroup.center X with hZ
  let ψ' : S →* X ⧸ Z := (QuotientGroup.mk' Z).comp ψ
  have hψ's : Function.Surjective ψ' := (QuotientGroup.mk'_surjective Z).comp hψs
  have hker : π.ker = ψ'.ker := by
    rw [hπk]
    ext s
    constructor
    · intro hs
      rw [MonoidHom.mem_ker]
      show (QuotientGroup.mk (ψ s) : X ⧸ Z) = 1
      rw [QuotientGroup.eq_one_iff]
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨t, rfl⟩ := hψs y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hs t]
    · intro hs
      have : ψ s ∈ Z := (QuotientGroup.eq_one_iff _).mp hs
      exact mem_center_of_map_mem_center hS ψ hψ this
  let e : P ≃* X ⧸ Z :=
    ((QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker)).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ' hψ's)
  have he : ∀ s, e (π s) = ψ' s := by
    intro s
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm (π s) =
        (s : S ⧸ π.ker) := (MulEquiv.symm_apply_eq _).mpr rfl
    show (QuotientGroup.quotientKerEquivOfSurjective ψ' hψ's)
      ((QuotientGroup.quotientMulEquivOfEq hker)
        ((QuotientGroup.quotientKerEquivOfSurjective π hπ).symm (π s))) = ψ' s
    rw [h1, QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  have hσZ : Z.map (σ : X ≃* X).toMonoidHom = Z := Subgroup.map_center_eq σ
  let σb : MulAut (X ⧸ Z) := QuotientGroup.congr Z Z σ hσZ
  have hσb : ∀ y : X, σb (y : X ⧸ Z) = ((σ y : X) : X ⧸ Z) := fun y => rfl
  let φ : MulAut P := (e.trans σb).trans e.symm
  have hφ : ∀ p : P, φ p = e.symm (σb (e p)) := fun p => rfl
  have hφfix : ∀ r : S, σ (ψ r) = ψ r → φ (π r) = π r := by
    intro r hr
    rw [hφ, he, show ψ' r = ((ψ r : X) : X ⧸ Z) from rfl, hσb, hr]
    rw [MulEquiv.symm_apply_eq, he]
    rfl
  have hσb4 : ∀ q : X ⧸ Z, σb (σb (σb (σb q))) = q := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H y =>
      rw [hσb, hσb, hσb, hσb]
      have := congrArg (fun τ : MulAut X => τ y) hσ4
      simp only [MulAut.mul_apply, MulAut.one_apply] at this
      rw [this]
  have hφ4 : φ * φ * (φ * φ) = 1 := by
    ext p
    simp only [MulAut.mul_apply, MulAut.one_apply]
    rw [hφ, hφ, hφ, hφ]
    simp only [MulEquiv.apply_symm_apply]
    rw [hσb4]
    simp
  have hφ2 := hvac φ (fun r hr => hφfix r (hσR r hr)) (fun r hr => hφfix r (hσR' r hr)) hφ4
  have hσ2 : ∀ y : X, (σ * σ).toMonoidHom y * y⁻¹ ∈ Z := by
    intro y
    obtain ⟨s, rfl⟩ := hψs y
    have h1 : φ (φ (π s)) = π s := by
      have := congrArg (fun τ : MulAut P => τ (π s)) hφ2
      simpa using this
    rw [hφ, hφ] at h1
    simp only [MulEquiv.apply_symm_apply] at h1
    have h2 : σb (σb (e (π s))) = e (π s) := by
      have := congrArg e h1
      simpa using this
    rw [he, show ψ' s = ((ψ s : X) : X ⧸ Z) from rfl, hσb, hσb] at h2
    have hz := (QuotientGroup.eq).mp h2
    have hc : (ψ s)⁻¹ * σ (σ (ψ s)) ∈ Z := by
      have := Z.inv_mem hz
      simpa [mul_inv_rev] using this
    show σ (σ (ψ s)) * (ψ s)⁻¹ ∈ Z
    have e1 : σ (σ (ψ s)) * (ψ s)⁻¹ = (ψ s)⁻¹ * σ (σ (ψ s)) := by
      calc σ (σ (ψ s)) * (ψ s)⁻¹ = ψ s * ((ψ s)⁻¹ * σ (σ (ψ s))) * (ψ s)⁻¹ := by group
        _ = ((ψ s)⁻¹ * σ (σ (ψ s))) * ψ s * (ψ s)⁻¹ := by
          rw [← Subgroup.mem_center_iff.mp hc (ψ s)]
        _ = (ψ s)⁻¹ * σ (σ (ψ s)) := by group
    rw [e1]
    exact hc
  have hXperf : (⊤ : Subgroup X) ≤ ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ := by
    have h := top_le_commutator_of_perfect hS
    have h' := Subgroup.map_mono (f := ψ) h
    rw [Subgroup.map_commutator, Subgroup.map_top, MonoidHom.range_eq_top.mpr hψs] at h'
    exact h'
  have hfix := eq_of_central_ratio (σ * σ).toMonoidHom (P := ⊤) hXperf (fun y _ => hσ2 y)
  ext y
  simpa using hfix y (Subgroup.mem_top y)

end Bridge


end T8V

end CFSG.ClassicalInvolution.Asc77
