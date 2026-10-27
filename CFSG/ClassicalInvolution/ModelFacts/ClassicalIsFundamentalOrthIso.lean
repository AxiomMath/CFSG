module

public import CFSG.ClassicalGroups.Orthogonal.Restrict
public import CFSG.RankThree.Classical.OddQuadraticFrame

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

section Iso

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem exists_isotropic_of_finrank_ge_three [Finite K] (hodd : Odd (Nat.card K))
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : (polarBilin Q).Nondegenerate)
    (h3 : 3 ≤ Module.finrank K V) : ∃ v : V, v ≠ 0 ∧ Q v = 0 := by
  have := Fintype.ofFinite K
  have hK' : Fintype.card K % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mp hodd
  have h2 : (2 : K) ≠ 0 := CFSG.RankThree.Classical.two_ne_zero_of_card_odd hK'
  have : Invertible (2 : K) := invertibleOfNonzero h2
  obtain ⟨e, he⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (CFSG.RankThree.Classical.isSymm_polarBilin Q)
  have hv₀ : ∀ i j, i ≠ j → polar Q (e i) (e j) = 0 := fun i j hij => by
    rw [← polarBilin_apply_apply]
    exact he hij
  have hQ₀ : ∀ i, Q (e i) ≠ 0 := fun i hi => by
    have h := LinearMap.BilinForm.iIsOrtho.not_isOrtho_basis_self_of_nondegenerate he hQ i
    rw [polarBilin_apply_apply, polar_self, hi, smul_zero] at h
    exact h rfl
  set i₀ : Fin (Module.finrank K V) := ⟨0, by omega⟩
  set i₁ : Fin (Module.finrank K V) := ⟨1, by omega⟩
  set i₂ : Fin (Module.finrank K V) := ⟨2, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have h02 : i₀ ≠ i₂ := by simp [i₀, i₂, Fin.ext_iff]
  have h12 : i₁ ≠ i₂ := by simp [i₁, i₂, Fin.ext_iff]
  obtain ⟨s, t, hst⟩ := CFSG.RankThree.Classical.exists_mul_sq_add_mul_sq_eq hK' (hQ₀ i₀) (hQ₀ i₁)
    (-Q (e i₂))
  refine ⟨s • e i₀ + t • e i₁ + e i₂, ?_, ?_⟩
  · intro h0
    have := congrArg (fun v => e.repr v i₂) h0
    simp [map_add, map_smul, Module.Basis.repr_self, h02.symm, h12.symm] at this
  · have hxy : polar Q (s • e i₀ + t • e i₁) (e i₂) = 0 := by
      rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, hv₀ _ _ h02, hv₀ _ _ h12]
      simp
    rw [QuadraticMap.map_add Q, hxy, CFSG.RankThree.Classical.quad_smul_add_smul Q (hv₀ _ _ h01)]
    linear_combination hst

theorem finrank_hypPair_perp [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) (P : HypPair Q) :
    Module.finrank K P.perp + 2 = Module.finrank K V := by
  have hperp : P.perp = LinearMap.BilinForm.orthogonal (polarBilin Q)
      (Submodule.span K {P.e, P.f}) := by
    ext x
    rw [LinearMap.BilinForm.mem_orthogonal_iff, HypPair.mem_perp]
    constructor
    · rintro ⟨h1, h2⟩ n hn
      induction hn using Submodule.span_induction with
      | mem y hy =>
        rcases hy with rfl | rfl
        · rw [polarBilin_apply_apply]; exact h1
        · rw [polarBilin_apply_apply]; exact h2
      | zero => simp
      | add y z _ _ hy hz => rw [LinearMap.BilinForm.add_left, hy, hz, add_zero]
      | smul a y _ hy => rw [LinearMap.BilinForm.smul_left, hy, mul_zero]
    · intro h
      exact ⟨by simpa [polarBilin_apply_apply] using h P.e (Submodule.subset_span (by simp)),
        by simpa [polarBilin_apply_apply] using h P.f (Submodule.subset_span (by simp))⟩
  have hspan : Module.finrank K (Submodule.span K {P.e, P.f}) = 2 := by
    have hli : LinearIndependent K ![P.e, P.f] := by
      rw [LinearIndependent.pair_iff]
      intro a b hab
      have h1 := congrArg (fun z => polar Q z P.f) hab
      have h2 := congrArg (fun z => polar Q z P.e) hab
      simp only [polar_add_left, polar_smul_left_eq, P.polar_ef, P.polar_ff, P.polar_fe, P.polar_ee,
        polar_zero_left] at h1 h2
      exact ⟨by linear_combination h1, by linear_combination h2⟩
    have hrange : Set.range ![P.e, P.f] = {P.e, P.f} := by
      ext x
      simp [or_comm]
    have := finrank_span_eq_card hli
    rw [hrange] at this
    simpa using this
  rw [hperp, LinearMap.BilinForm.finrank_orthogonal hQ, hspan]
  have : 2 ≤ Module.finrank K V := hspan ▸ Submodule.finrank_le _
  omega

end Iso

section TotSing

universe u

variable {K : Type*} [Field K] [Finite K]

theorem exists_totallySingular_of_two_mul_add_one_le (hodd : Odd (Nat.card K)) :
    ∀ (k : ℕ) {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (Q : QuadraticForm K V), (polarBilin Q).Nondegenerate → 2 * k + 1 ≤ Module.finrank K V →
      ∃ T : Submodule K V, Module.finrank K T = k ∧ ∀ x ∈ T, Q x = 0 := by
  intro k
  induction k with
  | zero =>
    intro V _ _ _ Q _ _
    exact ⟨⊥, finrank_bot K V, fun x hx => by
      rw [(Submodule.mem_bot K).mp hx]
      exact QuadraticMap.map_zero Q⟩
  | succ k ih =>
    intro V _ _ _ Q hQ hd
    obtain ⟨e, he0, hQe⟩ := exists_isotropic_of_finrank_ge_three hodd Q hQ (by omega)
    obtain ⟨P, hPe⟩ := exists_hypPair hQ hQe he0
    have hW := nondegenerate_polarBilin_restrict (HypPair.polarNondegOn_perp hQ P)
    have hdW : 2 * k + 1 ≤ Module.finrank K P.perp := by
      have := finrank_hypPair_perp hQ P
      omega
    obtain ⟨T₀, hT₀d, hT₀Q⟩ := ih (Q.restrict P.perp) hW hdW
    set A : Submodule K V := T₀.map P.perp.subtype with hA
    have hAW : ∀ x ∈ A, x ∈ P.perp := by
      rintro _ ⟨a, -, rfl⟩
      exact a.2
    have hAQ : ∀ x ∈ A, Q x = 0 := by
      rintro _ ⟨a, ha, rfl⟩
      exact hT₀Q a ha
    have hinf : A ⊓ Submodule.span K {e} = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxA, hxe⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxe
      have h1 := (HypPair.mem_perp.mp (hAW _ hxA)).2
      rw [polar_smul_right_eq, ← hPe, P.polar_fe, mul_one] at h1
      rw [h1, zero_smul]
      exact Submodule.zero_mem _
    refine ⟨A ⊔ Submodule.span K {e}, ?_, ?_⟩
    · have h1 := Submodule.finrank_sup_add_finrank_inf_eq A (Submodule.span K {e})
      rw [hinf, finrank_bot, finrank_span_singleton he0, hA,
        Submodule.finrank_map_subtype_eq, hT₀d] at h1
      omega
    · intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
      have h1 := (HypPair.mem_perp.mp (hAW _ ha)).1
      rw [hPe] at h1
      rw [QuadraticMap.map_add Q, hAQ a ha, map_smul_eq_sq, hQe, polar_smul_right_eq,
        polar_comm, h1]
      ring

end TotSing

end CFSG.ClassicalInvolution.ModelFacts
