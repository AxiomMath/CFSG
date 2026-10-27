module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.HardMathSupport.Lang.AnisoE6

@[expose] def cl {G : Type*} [Group G] (E : Subgroup G) : Subgroup G :=
  Subgroup.closure {g | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g}

@[expose] def NormRSub (ℓ : ℕ) {G : Type*} [Group G] (E : Subgroup G) : Prop :=
  ∃ R : Subgroup G, R ≠ ⊥ ∧ IsPGroup ℓ R ∧ ∀ x ∈ E, R.map (MulAut.conj x).toMonoidHom = R

variable {G H : Type*} [Group G] [Group H]

theorem mem_cl_of_commute {E : Subgroup G} {x g : G} (hx : x ∈ E) (hx1 : x ≠ 1)
    (h : g * x = x * g) : g ∈ cl E :=
  Subgroup.subset_closure ⟨x, hx, hx1, h⟩

theorem cl_map_le (φ : G →* H) (hφ : Function.Injective φ) (E : Subgroup G) :
    (cl E).map φ ≤ cl (E.map φ) := by
  rw [cl, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨g, ⟨x, hx, hx1, hgx⟩, rfl⟩
  refine mem_cl_of_commute (x := φ x) ⟨x, hx, rfl⟩ ?_ ?_
  · intro h
    exact hx1 (hφ (by rw [h, map_one]))
  · rw [← map_mul, ← map_mul, hgx]

theorem cl_map (φ : G ≃* H) (E : Subgroup G) :
    cl (E.map φ.toMonoidHom) = (cl E).map φ.toMonoidHom := by
  refine le_antisymm ?_ (cl_map_le φ.toMonoidHom φ.injective E)
  rw [cl, Subgroup.closure_le]
  rintro g ⟨x', ⟨x, hx, rfl⟩, hx1, hgx⟩
  refine ⟨φ.symm g, mem_cl_of_commute hx ?_ ?_, by simp⟩
  · intro h
    exact hx1 (by simp [h])
  · apply φ.injective
    simpa using hgx

theorem cl_eq_top_of_map (φ : G ≃* H) (E : Subgroup G)
    (h : cl (E.map φ.toMonoidHom) = ⊤) : cl E = ⊤ := by
  rw [cl_map] at h
  refine (Subgroup.eq_top_iff' _).2 fun x => ?_
  have hx : φ x ∈ (cl E).map φ.toMonoidHom := h ▸ Subgroup.mem_top _
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := φ.injective hyx
  exact this ▸ hy

theorem normRSub_map {ℓ : ℕ} (φ : G →* H) (hφ : Function.Injective φ) {E : Subgroup G}
    (h : NormRSub ℓ E) : NormRSub ℓ (E.map φ) := by
  obtain ⟨R, hR1, hRp, hRn⟩ := h
  refine ⟨R.map φ, ?_, hRp.map φ, ?_⟩
  · intro h0
    apply hR1
    rw [eq_bot_iff]
    intro r hr
    have : φ r ∈ R.map φ := ⟨r, hr, rfl⟩
    rw [h0] at this
    have : φ r = 1 := this
    simpa using hφ (this.trans (map_one φ).symm)
  · rintro _ ⟨x, hx, rfl⟩
    have := hRn x hx
    ext y
    constructor
    · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
      have hr' : x * r * x⁻¹ ∈ R := by
        rw [← this]
        exact ⟨r, hr, rfl⟩
      exact ⟨x * r * x⁻¹, hr', by simp [MulAut.conj_apply]⟩
    · rintro ⟨r, hr, rfl⟩
      have hr' : x⁻¹ * r * x ∈ R := by
        have := hRn x⁻¹ (inv_mem hx)
        rw [← this]
        exact ⟨r, hr, by simp [MulAut.conj_apply]⟩
      refine ⟨φ (x⁻¹ * r * x), ⟨_, hr', rfl⟩, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]

theorem normRSub_of_map_conj {ℓ : ℕ} (g : G) {E : Subgroup G}
    (h : NormRSub ℓ (E.map (MulAut.conj g).toMonoidHom)) : NormRSub ℓ E := by
  obtain ⟨R, hR1, hRp, hRn⟩ := h
  refine ⟨R.map (MulAut.conj g⁻¹).toMonoidHom, ?_, hRp.map _, ?_⟩
  · intro h0
    apply hR1
    rw [eq_bot_iff]
    intro r hr
    have : (MulAut.conj g⁻¹).toMonoidHom r ∈ R.map (MulAut.conj g⁻¹).toMonoidHom := ⟨r, hr, rfl⟩
    rw [h0] at this
    have h1 : g⁻¹ * r * g = 1 := by simpa [MulAut.conj_apply] using this
    have : r = 1 := by
      calc r = g * (g⁻¹ * r * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
    simp [this]
  · intro x hx
    have hx' := hRn (g * x * g⁻¹) ⟨x, hx, by simp [MulAut.conj_apply]⟩
    ext y
    constructor
    · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
      have hr' : g * x * g⁻¹ * r * (g * x * g⁻¹)⁻¹ ∈ R := by
        rw [← hx']
        exact ⟨r, hr, by simp [MulAut.conj_apply, mul_assoc]⟩
      refine ⟨_, hr', ?_⟩
      simp [MulAut.conj_apply]
      group
    · rintro ⟨r, hr, rfl⟩
      have hr' : (g * x * g⁻¹)⁻¹ * r * (g * x * g⁻¹) ∈ R := by
        have := hRn (g * x * g⁻¹)⁻¹ (inv_mem ⟨x, hx, by simp [MulAut.conj_apply]⟩)
        rw [← this]
        exact ⟨r, hr, by simp [MulAut.conj_apply, mul_assoc]⟩
      refine ⟨g⁻¹ * ((g * x * g⁻¹)⁻¹ * r * (g * x * g⁻¹)) * g, ⟨_, hr', ?_⟩, ?_⟩
      · simp [MulAut.conj_apply]
      · simp [MulAut.conj_apply]
        group

theorem normRSub_of_map_equiv {ℓ : ℕ} (φ : G ≃* H) {E : Subgroup G}
    (h : NormRSub ℓ (E.map φ.toMonoidHom)) : NormRSub ℓ E := by
  have h' := normRSub_map φ.symm.toMonoidHom φ.symm.injective h
  have e : (E.map φ.toMonoidHom).map φ.symm.toMonoidHom = E := by
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨φ x, ⟨x, hx, rfl⟩, by simp⟩
  rwa [e] at h'

end CFSG.HardMathSupport.Lang.AnisoE6
