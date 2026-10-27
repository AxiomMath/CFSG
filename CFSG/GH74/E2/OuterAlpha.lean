module

public import Mathlib.GroupTheory.Subgroup.Center

public section

namespace CFSG.GH74.E2

@[expose] def Q8C2Rel {H : Type*} [Group H] (a b c : H) : Prop :=
  a ^ 4 = 1 ∧ a ^ 2 ≠ 1 ∧ b ^ 2 = a ^ 2 ∧ b * a * b⁻¹ = a⁻¹ ∧ c ^ 2 = 1 ∧ c ≠ 1 ∧ c ≠ a ^ 2 ∧
    c * a = a * c ∧ c * b = b * c

theorem Q8C2Rel.map {H H' : Type*} [Group H] [Group H'] (φ : H →* H')
    (hφ : Function.Injective φ) {a b c : H} (h : Q8C2Rel a b c) :
    Q8C2Rel (φ a) (φ b) (φ c) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, h1, map_one]
  · intro h
    exact h2 (hφ (by rw [map_pow, h, map_one]))
  · rw [← map_pow, ← map_pow, h3]
  · rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, h4]
  · rw [← map_pow, h5, map_one]
  · intro h
    exact h6 (hφ (by rw [h, map_one]))
  · intro h
    exact h7 (hφ (by rw [map_pow, h]))
  · rw [← map_mul, ← map_mul, h8]
  · rw [← map_mul, ← map_mul, h9]

@[expose] def NoQ8C2 (A : Type*) [Group A] : Prop :=
  ¬ ∃ a b c : A, Q8C2Rel a b c

theorem NoQ8C2.of_injective {A B : Type*} [Group A] [Group B] (h : NoQ8C2 B) (φ : A →* B)
    (hφ : Function.Injective φ) : NoQ8C2 A := by
  rintro ⟨a, b, c, hrel⟩
  exact h ⟨φ a, φ b, φ c, hrel.map φ hφ⟩

theorem q8c2_of_alpha {S H : Type*} [Group S] [Group H] (θ : S →* H) (α : S ≃* S)
    {t i j f : S} (hi : i ^ 2 = t) (hi4 : i ^ 4 = 1) (hj : j ^ 2 = t) (hji : j * i * j⁻¹ = i⁻¹)
    (ht2 : t ^ 2 = 1) (ht : t ∈ Subgroup.center S) (ht' : α t ∈ Subgroup.center S)
    (hne : α t ≠ t) (hf2 : f ^ 2 = 1) (hf : f ∉ Subgroup.center S) (hfi : f * i = i * f)
    (hfj : f * j = j * f)
    (huniq : ∀ u : S, θ u = 1 → u ^ 2 = 1 → u = 1 ∨ u = t) :
    Q8C2Rel (θ (α.symm i)) (θ (α.symm j)) (θ (α.symm f)) := by
  let φ : S →* H := θ.comp α.symm.toMonoidHom
  have hφ : ∀ x, φ x = θ (α.symm x) := fun x => rfl
  have key : ∀ u : S, φ u = 1 → u ^ 2 = 1 → u = 1 ∨ u = α t := by
    intro u hu hu2
    have h2 : (α.symm u) ^ 2 = 1 := by rw [← map_pow, hu2, map_one]
    rcases huniq (α.symm u) hu h2 with h | h
    · left
      have := congrArg α h
      rwa [MulEquiv.apply_symm_apply, map_one] at this
    · right
      have := congrArg α h
      rwa [MulEquiv.apply_symm_apply] at this
  have ht1 : t ≠ 1 := by
    intro h
    apply hne
    rw [h, map_one]
  have hφt : φ t ≠ 1 := by
    intro h
    rcases key t h ht2 with h1 | h1
    · exact ht1 h1
    · exact hne h1.symm
  have hcen : ∀ x ∈ Subgroup.center S, ∀ y : S, y * x = x * y := fun x hx y =>
    (Subgroup.mem_center_iff.1 hx y)
  have hφf : φ f ≠ 1 := by
    intro h
    rcases key f h hf2 with h1 | h1
    · exact hf (h1 ▸ Subgroup.one_mem _)
    · exact hf (h1 ▸ ht')
  have hφft : φ f ≠ φ t := by
    intro h
    have h1 : φ (f * t⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
    have h2 : (f * t⁻¹) ^ 2 = 1 := by
      have hc : Commute f t⁻¹ := hcen t⁻¹ (Subgroup.inv_mem _ ht) f
      rw [hc.mul_pow, hf2, inv_pow, ht2]
      simp
    rcases key _ h1 h2 with h3 | h3
    · apply hf
      have : f = t := by
        have := congrArg (· * t) h3
        simpa using this
      exact this ▸ ht
    · apply hf
      have : f = α t * t := by
        have := congrArg (· * t) h3
        simpa using this
      exact this ▸ Subgroup.mul_mem _ ht' ht
  show Q8C2Rel (φ i) (φ j) (φ f)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, hi4, map_one]
  · rw [← map_pow, hi]
    exact hφt
  · rw [← map_pow, ← map_pow, hj, hi]
  · rw [← map_inv, ← map_mul, ← map_mul, hji, map_inv]
  · rw [← map_pow, hf2, map_one]
  · exact hφf
  · rw [← map_pow, hi]
    exact hφft
  · rw [← map_mul, ← map_mul, hfi]
  · rw [← map_mul, ← map_mul, hfj]

theorem no_alpha_of_noQ8C2 {S A : Type*} [Group S] [Group A] (hA : NoQ8C2 A) (θ : S →* A)
    {t i j f : S} (hi : i ^ 2 = t) (hi4 : i ^ 4 = 1) (hj : j ^ 2 = t) (hji : j * i * j⁻¹ = i⁻¹)
    (ht2 : t ^ 2 = 1) (ht : t ∈ Subgroup.center S) (hf2 : f ^ 2 = 1)
    (hf : f ∉ Subgroup.center S) (hfi : f * i = i * f) (hfj : f * j = j * f)
    (huniq : ∀ u : S, θ u = 1 → u ^ 2 = 1 → u = 1 ∨ u = t) :
    ∀ ψ : MulAut S, ψ t ∈ Subgroup.center S → ψ t = t := by
  intro ψ hψ
  by_contra hne
  exact hA ⟨_, _, _, q8c2_of_alpha θ ψ hi hi4 hj hji ht2 ht hψ hne hf2 hf hfi hfj huniq⟩

end CFSG.GH74.E2
