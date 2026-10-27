module

public import CFSG.LargeExtraspecial.S4SpGen

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Module Subgroup CFSG.LargeExtraspecial.OrthoF2
open scoped commutatorElement

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {β : LinearMap.BilinForm (ZMod 2) V}

omit [FiniteDimensional (ZMod 2) V] in
theorem spTransvection_zero (hβ : β.IsAlt) : spTransvection β hβ 0 = 1 := by
  ext x
  rw [spTransvection_apply, smul_zero, add_zero]
  rfl

omit [FiniteDimensional (ZMod 2) V] in
theorem spTransvection_mul_self (hβ : β.IsAlt) (a : V) :
    spTransvection β hβ a * spTransvection β hβ a = 1 := by
  ext x
  rw [LinearEquiv.mul_apply, spTransvection_apply, spTransvection_apply, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, hβ.self_eq_zero, smul_zero, add_zero, add_assoc,
    vec_add_self, add_zero]
  rfl

omit [FiniteDimensional (ZMod 2) V] in
theorem spTransvection_add_apply (hβ : β.IsAlt) {x y : V} (hxy : β x y = 1) :
    spTransvection β hβ (x + y) x = y := by
  rw [spTransvection_apply, map_add, hβ.self_eq_zero, zero_add, hxy, one_smul, ← add_assoc,
    vec_add_self, zero_add]

theorem exists_isometry_apply_eq (hβ : β.IsAlt) (hnd : β.Nondegenerate) {x y : V} (hx : x ≠ 0)
    (hy : y ≠ 0) : ∃ g ∈ closure {u | ∃ c, u = spTransvection β hβ c}, g x = y := by
  have hmem : ∀ c, spTransvection β hβ c ∈ closure {u | ∃ c, u = spTransvection β hβ c} :=
    fun c => subset_closure ⟨c, rfl⟩
  by_cases hxy : x = y
  · exact ⟨1, one_mem _, by rw [hxy]; rfl⟩
  by_cases hb : β x y = 1
  · exact ⟨_, hmem (x + y), spTransvection_add_apply hβ hb⟩
  have hb0 : β x y = 0 := (zmod2_eq_zero_or_eq_one _).resolve_right hb
  obtain ⟨w, hxw, hyw⟩ : ∃ w, β x w = 1 ∧ β y w = 1 := by
    have hx' : x ∉ Submodule.span (ZMod 2) {x + y, x + y} := by
      rw [Set.pair_eq_singleton]
      intro hmem
      obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hmem
      rcases zmod2_eq_zero_or_eq_one k with rfl | rfl
      · rw [zero_smul] at hk
        exact hx hk.symm
      · rw [one_smul, add_eq_left] at hk
        exact hy hk
    obtain ⟨d, hd, -, hxd⟩ := exists_dual_triple hβ hnd hx'
    refine ⟨d, hxd, ?_⟩
    rw [map_add, LinearMap.add_apply, hxd] at hd
    exact (zmod2_eq_of_add_eq_zero hd).symm
  have hwx : β w x = 1 := by rw [isAlt_symm hβ, hxw]
  refine ⟨spTransvection β hβ (w + y) * spTransvection β hβ (x + w),
    mul_mem (hmem _) (hmem _), ?_⟩
  rw [LinearEquiv.mul_apply, spTransvection_add_apply hβ hxw, spTransvection_add_apply hβ
    (by rw [isAlt_symm hβ, hyw])]

variable (β) in
@[expose] noncomputable def spDer (hβ : β.IsAlt) : Subgroup (V ≃ₗ[ZMod 2] V) :=
  closure {u | ∃ x y : V, x ≠ 0 ∧ y ≠ 0 ∧ u = spTransvection β hβ x * spTransvection β hβ y}

omit [FiniteDimensional (ZMod 2) V] in
theorem spTransvection_mul_mem_spDer (hβ : β.IsAlt) {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    spTransvection β hβ x * spTransvection β hβ y ∈ spDer β hβ :=
  subset_closure ⟨x, y, hx, hy, rfl⟩

omit [FiniteDimensional (ZMod 2) V] in
theorem spDer_le_isometryGroup (hβ : β.IsAlt) : spDer β hβ ≤ TauCeti.BilinForm.isometryGroup β := by
  rw [spDer, closure_le]
  rintro _ ⟨x, y, -, -, rfl⟩
  exact mul_mem (spTransvection_mem_isometryGroup hβ x) (spTransvection_mem_isometryGroup hβ y)

omit [FiniteDimensional (ZMod 2) V] in
theorem conj_mem_spDer (hβ : β.IsAlt) {g u : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ TauCeti.BilinForm.isometryGroup β) (hu : u ∈ spDer β hβ) :
    g * u * g⁻¹ ∈ spDer β hβ := by
  induction hu using closure_induction with
  | mem u hu =>
    obtain ⟨x, y, hx, hy, rfl⟩ := hu
    have e : g * (spTransvection β hβ x * spTransvection β hβ y) * g⁻¹ =
        (g * spTransvection β hβ x * g⁻¹) * (g * spTransvection β hβ y * g⁻¹) := by group
    rw [e, conj_spTransvection hβ x hg, conj_spTransvection hβ y hg]
    exact spTransvection_mul_mem_spDer hβ (by simpa using hx) (by simpa using hy)
  | one => simp
  | mul u w _ _ hu hw =>
    have e : g * (u * w) * g⁻¹ = (g * u * g⁻¹) * (g * w * g⁻¹) := by group
    rw [e]
    exact mul_mem hu hw
  | inv u _ hu =>
    have e : g * u⁻¹ * g⁻¹ = (g * u * g⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem hu

theorem commutator_isometryGroup_eq (hβ : β.IsAlt) (hnd : β.Nondegenerate) :
    ⁅TauCeti.BilinForm.isometryGroup β, TauCeti.BilinForm.isometryGroup β⁆ = spDer β hβ := by
  classical
  apply le_antisymm
  · by_cases hV : ∃ a : V, a ≠ 0
    swap
    · push Not at hV
      have hsub : ∀ g : V ≃ₗ[ZMod 2] V, g = 1 := fun g => LinearEquiv.ext fun v => by
        rw [hV v, map_zero]
        rfl
      intro u _
      rw [hsub u]
      exact one_mem _
    obtain ⟨a, ha⟩ := hV
    set τ := spTransvection β hβ a with hτ
    have hττ : τ * τ = 1 := spTransvection_mul_self hβ a
    have hτI : τ ∈ TauCeti.BilinForm.isometryGroup β := spTransvection_mem_isometryGroup hβ a
    let P : Subgroup (V ≃ₗ[ZMod 2] V) :=
      { carrier := {g | g ∈ TauCeti.BilinForm.isometryGroup β ∧
          (g ∈ spDer β hβ ∨ g * τ ∈ spDer β hβ)}
        mul_mem' := by
          rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
          refine ⟨mul_mem hg hh, ?_⟩
          rcases hg' with hg' | hg' <;> rcases hh' with hh' | hh'
          · exact Or.inl (mul_mem hg' hh')
          · right
            rw [mul_assoc]
            exact mul_mem hg' hh'
          · right
            have h1 := conj_mem_spDer hβ (inv_mem hτI) hh'
            have e : g * h * τ = (g * τ) * (τ⁻¹ * h * τ⁻¹⁻¹) := by group
            rw [e]
            exact mul_mem hg' h1
          · left
            have h1 := conj_mem_spDer hβ (inv_mem hτI) hh'
            have e : (g * τ) * (τ⁻¹ * (h * τ) * τ⁻¹⁻¹) = g * h * (τ * τ) := by group
            have := mul_mem hg' h1
            rwa [e, hττ, mul_one] at this
        one_mem' := ⟨one_mem _, Or.inl (one_mem _)⟩
        inv_mem' := by
          rintro g ⟨hg, hg'⟩
          refine ⟨inv_mem hg, ?_⟩
          rcases hg' with hg' | hg'
          · exact Or.inl (inv_mem hg')
          · right
            have h1 := conj_mem_spDer hβ hτI (inv_mem hg')
            have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hττ
            have e : g⁻¹ * τ = τ * (g * τ)⁻¹ * τ⁻¹ := by rw [hτi]; group
            rw [e]
            exact h1 }
    have hSpP : TauCeti.BilinForm.isometryGroup β ≤ P := by
      have := eq_isometryGroup_of_spTransvection_mem hβ hnd (X := P) (fun g hg => hg.1)
        (fun x => by
          refine ⟨spTransvection_mem_isometryGroup hβ x, ?_⟩
          by_cases hx : x = 0
          · left
            rw [hx, spTransvection_zero]
            exact one_mem _
          · exact Or.inr (spTransvection_mul_mem_spDer hβ hx ha))
      rw [this]
    rw [commutator_le]
    intro g hg h hh
    obtain ⟨-, hg'⟩ := hSpP hg
    obtain ⟨-, hh'⟩ := hSpP hh
    have hDn : ∀ x ∈ TauCeti.BilinForm.isometryGroup β, ∀ u ∈ spDer β hβ,
        x * u * x⁻¹ ∈ spDer β hβ := fun x hx u hu => conj_mem_spDer hβ hx hu
    have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hττ
    obtain ⟨d₁, hd₁, σ₁, hσ₁, rfl⟩ : ∃ d ∈ spDer β hβ, ∃ σ, (σ = 1 ∨ σ = τ) ∧ g = d * σ := by
      rcases hg' with hg' | hg'
      · exact ⟨g, hg', 1, Or.inl rfl, (mul_one g).symm⟩
      · exact ⟨g * τ, hg', τ, Or.inr rfl, by rw [mul_assoc, hττ, mul_one]⟩
    obtain ⟨d₂, hd₂, σ₂, hσ₂, rfl⟩ : ∃ d ∈ spDer β hβ, ∃ σ, (σ = 1 ∨ σ = τ) ∧ h = d * σ := by
      rcases hh' with hh' | hh'
      · exact ⟨h, hh', 1, Or.inl rfl, (mul_one h).symm⟩
      · exact ⟨h * τ, hh', τ, Or.inr rfl, by rw [mul_assoc, hττ, mul_one]⟩
    have hσI : ∀ σ, (σ = 1 ∨ σ = τ) → σ ∈ TauCeti.BilinForm.isometryGroup β := by
      rintro σ (rfl | rfl)
      · exact one_mem _
      · exact hτI
    have hcomm : σ₁ * σ₂ = σ₂ * σ₁ := by
      rcases hσ₁ with rfl | rfl <;> rcases hσ₂ with rfl | rfl <;> simp
    have e : ⁅d₁ * σ₁, d₂ * σ₂⁆ = d₁ * (σ₁ * d₂ * σ₁⁻¹) *
        ((σ₁ * σ₂ * σ₁⁻¹) * d₁⁻¹ * (σ₁ * σ₂ * σ₁⁻¹)⁻¹) * (σ₁ * σ₂ * σ₁⁻¹ * σ₂⁻¹) * d₂⁻¹ := by
      rw [commutatorElement_def]
      group
    have hσσ : σ₁ * σ₂ * σ₁⁻¹ * σ₂⁻¹ = 1 := by rw [hcomm]; group
    rw [e, hσσ, mul_one]
    have h121 : σ₁ * σ₂ * σ₁⁻¹ ∈ TauCeti.BilinForm.isometryGroup β :=
      mul_mem (mul_mem (hσI _ hσ₁) (hσI _ hσ₂)) (inv_mem (hσI _ hσ₁))
    exact mul_mem (mul_mem (mul_mem hd₁ (hDn _ (hσI _ hσ₁) _ hd₂))
      (hDn _ h121 _ (inv_mem hd₁))) (inv_mem hd₂)
  · rw [spDer, closure_le]
    rintro _ ⟨x, y, hx, hy, rfl⟩
    obtain ⟨g, hg, hgx⟩ := exists_isometry_apply_eq hβ hnd hx hy
    have hgI : g ∈ TauCeti.BilinForm.isometryGroup β := by
      refine (closure_le _).mpr ?_ hg
      rintro _ ⟨c, rfl⟩
      exact spTransvection_mem_isometryGroup hβ c
    have h1 := commutator_mem_commutator (spTransvection_mem_isometryGroup hβ x) hgI
    have e : ⁅spTransvection β hβ x, g⁆ = spTransvection β hβ x * spTransvection β hβ y := by
      rw [commutatorElement_def, ← hgx, ← conj_spTransvection hβ x hgI,
        inv_eq_of_mul_eq_one_right (spTransvection_mul_self hβ x)]
      group
    rw [← e]
    exact h1

omit [FiniteDimensional (ZMod 2) V] in
theorem spRho_one_eq_mul (hβ : β.IsAlt) {a d : V} (had : β a d = 0) :
    spRho hβ had 1 = spTransvection β hβ d * spTransvection β hβ (a + d) := by
  have hda : β d a = 0 := by rw [isAlt_symm hβ, had]
  ext x
  simp only [LinearEquiv.mul_apply, spTransvection_apply, spRho_apply, map_add, map_smul,
    had, hβ.self_eq_zero]
  match_scalars <;> (ring_nf; try reduce_mod_char)

omit [FiniteDimensional (ZMod 2) V] in
theorem spRho_zero_zero (hβ : β.IsAlt) (c : V) (h : β c 0 = 0) : spRho hβ h 0 = 1 := by
  ext x
  rw [spRho_apply, smul_zero, add_zero, map_zero, zero_mul, add_zero, zero_smul, add_zero]
  rfl

theorem exists_ne_zero_perp_pair (hnd : β.Nondegenerate) (h3 : 3 ≤ finrank (ZMod 2) V)
    (x y : V) : ∃ w : V, w ≠ 0 ∧ β x w = 0 ∧ β y w = 0 := by
  classical
  set P := Submodule.span (ZMod 2) ({x, y} : Set V) with hP
  have h1 := LinearMap.BilinForm.finrank_orthogonal hnd P
  have h2 : finrank (ZMod 2) P ≤ 2 := by
    have := finrank_span_finset_le_card (R := ZMod 2) ({x, y} : Finset V)
    rw [Finset.coe_insert, Finset.coe_singleton] at this
    exact this.trans ((Finset.card_insert_le _ _).trans (by simp))
  have hne : LinearMap.BilinForm.orthogonal β P ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at h1
    have := Submodule.finrank_le P
    omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨w, hw0, (LinearMap.BilinForm.mem_orthogonal_iff.mp hw) x (Submodule.subset_span (by simp)),
    (LinearMap.BilinForm.mem_orthogonal_iff.mp hw) y (Submodule.subset_span (by simp))⟩

theorem eq_commutator_of_transitive_four (hβ : β.IsAlt) (hnd : β.Nondegenerate)
    (h4 : finrank (ZMod 2) V = 4) {X : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hX : X ≤ TauCeti.BilinForm.isometryGroup β) {a : V} (ha : a ≠ 0)
    {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hEX : E ≤ X) (hEU : E ≤ spPointRadical β a)
    (hidx : Nat.card (spPointRadical β a) ≤ 2 * Nat.card E) (hτ : spTransvection β hβ a ∉ E)
    (htr : ∀ v : V, v ≠ 0 → ∃ x ∈ X, x a = v)
    (hgen : X ≤ closure {u | ∃ x ∈ X, ∃ e ∈ E, u = x * e * x⁻¹})
    (hno : ∀ d (hd : β a d = 0), d ∉ Submodule.span (ZMod 2) {a} → spRho hβ hd 0 ∉ E) :
    X = ⁅TauCeti.BilinForm.isometryGroup β, TauCeti.BilinForm.isometryGroup β⁆ := by
  classical
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv_of_finite
  rw [commutator_isometryGroup_eq hβ hnd]
  apply le_antisymm
  · refine hgen.trans ((closure_le _).mpr ?_)
    rintro _ ⟨x, hxX, e, he, rfl⟩
    have hxI := hX hxX
    obtain ⟨d, hd, l, rfl⟩ := exists_eq_spRho hβ hnd ha (hEU he)
    by_cases hdP : d ∈ Submodule.span (ZMod 2) {a}
    · have h0 : β a 0 = 0 := map_zero _
      have hρ : spRho hβ hd l = spRho hβ h0 l := by
        rcases mem_span_singleton_iff.mp hdP with rfl | rfl
        · rfl
        · rw [← spRho_add_self hβ h0 l (by rw [zero_add]; exact hd)]
          exact spRho_congr hβ _ _ rfl (zero_add d).symm rfl
      rw [hρ] at he ⊢
      rcases zmod2_eq_zero_or_eq_one l with rfl | rfl
      · rw [spRho_zero_zero, mul_one, mul_inv_cancel]
        exact one_mem _
      · exact absurd (by rwa [spRho_zero_one] at he) hτ
    · rcases zmod2_eq_zero_or_eq_one l with rfl | rfl
      · exact absurd he (hno d hd hdP)
      · rw [spRho_one_eq_mul, show x * (spTransvection β hβ d * spTransvection β hβ (a + d)) * x⁻¹
          = (x * spTransvection β hβ d * x⁻¹) * (x * spTransvection β hβ (a + d) * x⁻¹) by group,
          conj_spTransvection hβ _ hxI, conj_spTransvection hβ _ hxI]
        refine spTransvection_mul_mem_spDer hβ ?_ ?_
        · intro h0
          exact hdP ((x.map_eq_zero_iff.mp h0) ▸ Submodule.zero_mem _)
        · intro h0
          apply hdP
          have := x.map_eq_zero_iff.mp h0
          rw [show d = a by
            have h2 := congrArg (· + d) this
            simpa [add_assoc, vec_add_self] using h2.symm]
          exact Submodule.mem_span_singleton_self a
  ·
    have hP : ∀ b : V, b ≠ 0 → ∀ d (hbd : β b d = 0), d ∉ Submodule.span (ZMod 2) {b} →
        spTransvection β hβ d * spTransvection β hβ (b + d) ∈ X := by
      intro b hb d hbd hdb
      obtain ⟨z, hzX, hza⟩ := htr b hb
      have hzI := hX hzX
      set Eb := E.map (MulAut.conj z).toMonoidHom with hEb
      have hEbU : Eb ≤ spPointRadical β b := by
        rintro _ ⟨e, he, rfl⟩
        have := conj_mem_spPointRadical hβ hzI (hEU he)
        rwa [hza] at this
      have hEbcard : Nat.card (spPointRadical β b) ≤ 2 * Nat.card Eb := by
        rw [hEb, card_map_of_injective (MulAut.conj z).injective, card_spPointRadical hβ hnd hb,
          ← card_spPointRadical hβ hnd ha]
        exact hidx
      have hEbτ : spTransvection β hβ b ∉ Eb := by
        rintro ⟨e, he, hec⟩
        apply hτ
        have h1 := conj_spTransvection hβ b (inv_mem hzI)
        have hzb : z⁻¹ b = a := by rw [← hza]; exact z.symm_apply_apply a
        rw [hzb] at h1
        have he' : e = z⁻¹ * spTransvection β hβ b * z⁻¹⁻¹ := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hec
          rw [← hec]
          group
        rw [← h1, ← he']
        exact he
      rcases mem_or_mul_mem_of_card hEbU hEbcard (spTransvection_mem_U hβ b) hEbτ
          (spRho_mem_spPointRadical hβ hbd 0) with h | h
      · exfalso
        obtain ⟨e, he, hec⟩ := h
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hec
        have hzd : β (z⁻¹ b) (z⁻¹ d) = 0 := by
          rw [TauCeti.BilinForm.mem_isometryGroup_iff.mp (inv_mem hzI), hbd]
        have h1 := conj_spRho hβ hbd 0 (inv_mem hzI) hzd
        have hzb : z⁻¹ b = a := by rw [← hza]; exact z.symm_apply_apply a
        have hzd' : β a (z⁻¹ d) = 0 := by rw [← hzb]; exact hzd
        rw [spRho_congr hβ hzd hzd' hzb rfl rfl] at h1
        have he' : e = z⁻¹ * spRho hβ hbd 0 * z⁻¹⁻¹ := by
          rw [← hec]
          group
        refine hno (z⁻¹ d) hzd' ?_ (h1 ▸ he' ▸ he)
        intro hmem
        apply hdb
        rw [← hzb] at hmem
        obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hmem
        rw [Submodule.mem_span_singleton]
        refine ⟨k, ?_⟩
        have := congrArg z hk
        rwa [map_smul, show z (z⁻¹ b) = b from z.apply_symm_apply b,
          show z (z⁻¹ d) = d from z.apply_symm_apply d] at this
      · rw [← spRho_one_eq, spRho_one_eq_mul] at h
        have hEbX : Eb ≤ X := by
          rintro _ ⟨e, he, rfl⟩
          exact mul_mem (mul_mem hzX (hEX he)) (inv_mem hzX)
        exact hEbX h
    have hQ : ∀ x y : V, x ≠ 0 → y ≠ 0 → β x y = 0 →
        spTransvection β hβ x * spTransvection β hβ y ∈ X := by
      intro x y hx hy hxy
      by_cases hxy' : x = y
      · rw [hxy', spTransvection_mul_self]
        exact one_mem _
      have hb : x + y ≠ 0 := fun h => hxy' (by
        have := congrArg (· + y) h
        simpa [add_assoc, vec_add_self] using this)
      have hbd : β (x + y) x = 0 := by
        rw [map_add, LinearMap.add_apply, hβ.self_eq_zero, zero_add, isAlt_symm hβ, hxy]
      have hdb : x ∉ Submodule.span (ZMod 2) {x + y} := by
        intro hmem
        obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hmem
        rcases zmod2_eq_zero_or_eq_one k with rfl | rfl
        · rw [zero_smul] at hk
          exact hx hk.symm
        · rw [one_smul, add_eq_left] at hk
          exact hy hk
      have := hP (x + y) hb x hbd hdb
      rwa [show x + y + x = y by rw [add_comm x y, add_assoc, vec_add_self, add_zero]] at this
    rw [spDer, closure_le]
    rintro _ ⟨x, y, hx, hy, rfl⟩
    by_cases hxy : β x y = 0
    · exact hQ x y hx hy hxy
    · have hxy1 : β x y = 1 := zmod2_eq_one_of_ne_zero hxy
      obtain ⟨w, hw0, hxw, hyw⟩ := exists_ne_zero_perp_pair hnd (by omega) x y
      have hwy : β w y = 0 := by rw [isAlt_symm hβ, hyw]
      have e : spTransvection β hβ x * spTransvection β hβ y =
          (spTransvection β hβ x * spTransvection β hβ w) *
            (spTransvection β hβ w * spTransvection β hβ y) := by
        rw [show (spTransvection β hβ x * spTransvection β hβ w) *
          (spTransvection β hβ w * spTransvection β hβ y) = spTransvection β hβ x *
            (spTransvection β hβ w * spTransvection β hβ w) * spTransvection β hβ y by group,
          spTransvection_mul_self, mul_one]
      rw [e]
      exact mul_mem (hQ x w hx hw0 hxw) (hQ w y hw0 hy hwy)

end CFSG.LargeExtraspecial.S4
