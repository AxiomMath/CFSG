module

public import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.SevenSpan
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalWittFlags

public section

namespace CFSG.AGLEmbedding.TrialityTwo.Seven

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {t : Module.End K V}

section Line

variable [FiniteDimensional K V] (hK : Nat.card K = 2) (h7 : t ^ 7 = 1) (ht : t ≠ 1)
  (hQt : ∀ v, Q (t v) = Q v) (hB : (polarBilin Q).Nondegenerate) (hV : finrank K V = 8)
include hK h7 ht hQt hB hV

theorem exists_singular_ne_zero_mem_fixC
    (hT : ∃ T : Submodule K V, finrank K T = 4 ∧ ∀ x ∈ T, Q x = 0) :
    ∃ c ∈ fixC t, c ≠ 0 ∧ Q c = 0 := by
  have h2 := two_eq_zero_of_card hK
  obtain ⟨u, hu, hu0⟩ := exists_ne_zero_mem_spU₁ hK h7 ht hQt hB hV
  set e : Fin 3 → V := ![u, t u, t (t u)] with he
  have hli : LinearIndependent K e := linearIndependent_of_mem_spU₁ hK h7 ht hQt hB hV hu hu0
  set W : ℕ → Submodule K V := fun i => Submodule.span K (e '' {j : Fin 3 | (j : ℕ) < i})
    with hW
  have hWd : ∀ i ≤ 3, finrank K (W i) = i := fun i hi =>
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.finrank_span_image_lt hli hi
  have hWm : ∀ i < 3, W i ≤ W (i + 1) := fun i _ =>
    Submodule.span_mono (Set.image_mono fun j (hj : (j : ℕ) < i) => Nat.lt_succ_of_lt hj)
  have hW3 : W 3 = spU₁ t := by
    have hset : e '' {j : Fin 3 | (j : ℕ) < 3} = Set.range e := by
      rw [← Set.image_univ]
      congr 1
      ext j
      simp
    simp only [hW]
    rw [hset]
    exact span_eq_spU₁ hK h7 ht hQt hB hV hu hu0
  have hWs : ∀ x ∈ W 3, Q x = 0 := fun x hx => map_eq_zero_of_mem_spU₁ hQt h7 h2 (hW3 ▸ hx)
  obtain ⟨b, hbQ, -, hbB, hbW, -⟩ :=
    (CFSG.LocalAnalysis.ComponentInitial.orthogonal_geometry_split_Witt_flags hB (r := 4)
      (by rw [hV]) hT).1 3 (by norm_num) W hWd hWm hWs
  set v := b (Sum.inl 3) with hv
  have hU : spU₁ t = Submodule.span K (b '' (Sum.inl '' {j : Fin 4 | (j : ℕ) < 3})) := by
    rw [← hW3]
    exact hbW 3 le_rfl
  have hvperp : ∀ x ∈ spU₁ t, polar Q x v = 0 := by
    intro x hx
    rw [hU] at hx
    have hle : Submodule.span K (b '' (Sum.inl '' {j : Fin 4 | (j : ℕ) < 3})) ≤
        LinearMap.ker ((polarBilin Q).flip v) := by
      rw [Submodule.span_le]
      rintro _ ⟨_, ⟨j, -, rfl⟩, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.flip_apply,
        polarBilin_apply_apply]
      exact (hbB j 3).1
    have := hle hx
    simpa using this
  have hvU : v ∉ spU₁ t := by
    rw [hU]
    exact b.linearIndependent.notMem_span_image (by simp)
  have hv2 : projU₂ t v = 0 := by
    apply eq_zero_of_mem_spU₂_of_polar hQt h7 h2 hB (projU₂_apply_mem v)
    intro y hy
    rw [polar_comm, ← polar_projU₁_left hQt h7, (mem_spU₁_iff h7 h2).1 hy]
    exact hvperp y hy
  have hdec : v = projC t v + projU₁ t v := by
    have := projC_add_projU₁_add_projU₂_apply h7 h2 v
    rw [hv2, add_zero] at this
    exact this.symm
  have hc := projC_apply_mem_fixC h7 h2 v
  refine ⟨projC t v, hc, fun h0 => hvU ?_, ?_⟩
  · rw [hdec, h0, zero_add]
    exact projU₁_apply_mem v
  · have hQv : Q v = 0 := (hbQ 3).1
    rw [hdec, QuadraticMap.map_add (⇑Q), map_eq_zero_of_mem_spU₁ hQt h7 h2 (projU₁_apply_mem v),
      polar_eq_zero_of_mem_fixC_of_mem_spU₁ hQt h7 h2 hc (projU₁_apply_mem v), add_zero,
      add_zero] at hQv
    exact hQv

theorem exists_hypPair_fixC (hT : ∃ T : Submodule K V, finrank K T = 4 ∧ ∀ x ∈ T, Q x = 0) :
    ∃ w₁ ∈ fixC t, ∃ w₂ ∈ fixC t, Q w₁ = 0 ∧ Q w₂ = 0 ∧ polar Q w₁ w₂ = 1 := by
  have h2 := two_eq_zero_of_card hK
  obtain ⟨c, hc, hc0, hcQ⟩ := exists_singular_ne_zero_mem_fixC hK h7 ht hQt hB hV hT
  obtain ⟨y, hy, hcy⟩ : ∃ y ∈ fixC t, polar Q c y ≠ 0 := by
    by_contra! h
    exact hc0 (eq_zero_of_mem_fixC_of_polar hQt h7 h2 hB hc h)
  have hd : (polar Q c y)⁻¹ • y ∈ fixC t := Submodule.smul_mem _ _ hy
  have hcd : polar Q c ((polar Q c y)⁻¹ • y) = 1 := by
    rw [polar_smul_right_eq, inv_mul_cancel₀ hcy]
  exact ⟨c, hc, _, sub_mem hd (Submodule.smul_mem _ _ hc), hcQ,
    (HypPair.ofPolarEqOne hcQ hcd).Q_f, (HypPair.ofPolarEqOne hcQ hcd).polar_ef⟩

variable {w₁ w₂ : V} (hw₁ : w₁ ∈ fixC t) (hw₂ : w₂ ∈ fixC t) (hQ₁ : Q w₁ = 0) (hQ₂ : Q w₂ = 0)
  (hw : polar Q w₁ w₂ = 1)
include hw₁ hw₂ hQ₁ hQ₂ hw

theorem fixC_eq_span_pair : fixC t = Submodule.span K {w₁, w₂} := by
  have hli : LinearIndependent K ![w₁, w₂] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have e1 := congrArg (fun x => polar Q x w₂) hab
    have e2 := congrArg (fun x => polar Q x w₁) hab
    simp only [polar_add_left, polar_smul_left_eq, hw, polar_self_eq_zero hQ₂,
      polar_zero_left, mul_zero, add_zero, mul_one] at e1
    simp only [polar_add_left, polar_smul_left_eq, polar_comm Q w₂ w₁, hw,
      polar_self_eq_zero hQ₁, polar_zero_left, mul_zero, zero_add, mul_one] at e2
    exact ⟨e1, e2⟩
  have hrank := finrank_span_eq_card hli
  rw [Fintype.card_fin, Matrix.range_cons_cons_empty] at hrank
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact hw₁
    · exact hw₂
  · rw [hrank, finrank_fixC_eq_two hK h7 ht hQt hB hV]

theorem eq_or_eq_of_mem_fixC {x : V} (hx : x ∈ fixC t) (hxQ : Q x = 0) (hx0 : x ≠ 0) :
    x = w₁ ∨ x = w₂ := by
  rw [fixC_eq_span_pair hK h7 ht hQt hB hV hw₁ hw₂ hQ₁ hQ₂ hw, Submodule.mem_span_pair] at hx
  obtain ⟨a, b, rfl⟩ := hx
  rw [QuadraticMap.map_add (⇑Q), map_smul_eq_sq, map_smul_eq_sq, hQ₁, hQ₂, polar_smul_left_eq,
    polar_smul_right_eq, hw] at hxQ
  simp only [mul_zero, zero_add, mul_one] at hxQ
  rcases eq_zero_or_eq_one_of_card hK a with rfl | rfl <;>
    rcases eq_zero_or_eq_one_of_card hK b with rfl | rfl
  · simp at hx0
  · right; simp
  · left; simp
  · simp at hxQ

end Line

theorem map_add_pair_eq_one {w₁ w₂ : V} (hQ₁ : Q w₁ = 0) (hQ₂ : Q w₂ = 0)
    (hw : polar Q w₁ w₂ = 1) : Q (w₁ + w₂) = 1 := by
  rw [QuadraticMap.map_add (⇑Q), hQ₁, hQ₂, hw, zero_add, zero_add]

end CFSG.AGLEmbedding.TrialityTwo.Seven
