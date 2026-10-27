module

public import CFSG.ClassicalGroups.Orthogonal.CharTwo
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasTwo

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem orthogonal_char_two_anisotropic_plane_generation [CharP K 2] (hdim : finrank K V = 2)
    (hQ : (polarBilin Q).Nondegenerate) (han : ∀ x : V, Q x = 0 → x = 0) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    ∃ l : List V, l.length ≤ 2 ∧ (∀ v ∈ l, v ≠ 0) ∧ g = (l.map (reflect Q)).prod := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨x, hx0⟩ := exists_ne (0 : V)
  have hQx : Q x ≠ 0 := fun h => hx0 (han x h)
  by_cases hgx : g x = x
  · rcases orthogonal_char_two_plane_vector_stabilizer hdim hQ hQx hg hgx with h1 | h1
    · exact ⟨[], by simp, by simp, by simp [h1]⟩
    · exact ⟨[x], by simp, by simpa using hx0, by simp [h1]⟩
  · obtain ⟨v, hv⟩ : ∃ v, v = g x - x := ⟨_, rfl⟩
    have hv0 : v ≠ 0 := by rw [hv]; exact sub_ne_zero.2 hgx
    have hQv : Q v ≠ 0 := fun h => hv0 (han _ h)
    have hgxgx : polar Q (g x) (g x) = 0 := by rw [polar_self_eq_two_mul, h2, zero_mul]
    have hQv' : Q v = -polar Q (g x) x := by
      have : Q v = 2 * Q x - polar Q (g x) x := by
        rw [hv, sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, polar_neg_right,
          map_of_mem hg]
        ring
      rw [this, h2, zero_mul, zero_sub]
    have hpol : polar Q v (g x) = -polar Q (g x) x := by
      rw [hv, polar_sub_left, hgxgx, zero_sub, polar_comm]
    have hsv : reflect Q v (g x) = x := by
      rw [reflect_apply hQv, hpol, ← hQv', div_self hQv, one_smul, hv, sub_sub_cancel]
    have hsvO := reflect_mem_orthogonalGroup Q v
    have hdecomp : g = reflect Q v * (reflect Q v * g) := by
      rw [← mul_assoc, reflect_mul_self, one_mul]
    rcases orthogonal_char_two_plane_vector_stabilizer hdim hQ hQx (mul_mem hsvO hg)
      (by rw [LinearEquiv.mul_apply, hsv]) with h1 | h1
    · refine ⟨[v], by simp, by simpa using hv0, ?_⟩
      calc g = reflect Q v * (reflect Q v * g) := hdecomp
        _ = ([v].map (reflect Q)).prod := by rw [h1]; simp
    · refine ⟨[v, x], by simp, ?_, ?_⟩
      · intro w hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact hv0
        · exact hx0
      · calc g = reflect Q v * (reflect Q v * g) := hdecomp
          _ = ([v, x].map (reflect Q)).prod := by rw [h1]; simp

theorem eq_smul_of_polar_eq_zero_of_finrank_two {A : Submodule K V} [FiniteDimensional K A]
    (hA2 : finrank K A = 2) (hAn : PolarNondegOn Q A) {x : V} (hxA : x ∈ A) (hx0 : x ≠ 0)
    (hxx : polar Q x x = 0) {y : V} (hyA : y ∈ A) (hxy : polar Q x y = 0) :
    ∃ c : K, y = c • x := by
  obtain ⟨z₀, hz₀A, hz₀⟩ := hAn.exists_polar_ne_zero hxA hx0
  set z := (polar Q x z₀)⁻¹ • z₀ with hz
  have hzA : z ∈ A := A.smul_mem _ hz₀A
  have hxz : polar Q x z = 1 := by rw [hz, polar_smul_right_eq, inv_mul_cancel₀ hz₀]
  have hli : LinearIndependent K ![x, z] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (polar Q x) hst
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hxx, hxz, polar_zero_right]
      at h1
    have ht : t = 0 := by simpa using h1
    rw [ht, zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.1 hst).resolve_right hx0, ht⟩
  have hle : Submodule.span K (Set.range ![x, z]) ≤ A := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hxA
    · exact hzA
  have hspan : Submodule.span K (Set.range ![x, z]) = A :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_span_eq_card hli, Fintype.card_fin, hA2])
  have hy : y ∈ Submodule.span K (Set.range ![x, z]) := hspan ▸ hyA
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hy
  rw [Fin.sum_univ_two] at hc
  have h1 := congrArg (polar Q x) hc
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, polar_add_right,
    polar_smul_right_eq, hxx, hxz, hxy] at h1
  have hc1 : c 1 = 0 := by simpa using h1
  refine ⟨c 0, ?_⟩
  rw [← hc]
  simp [hc1]

theorem orthogonal_char_two_derived_elementary [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {P : ℕ → HypPair Q} {r : ℕ}
    (hP : ∀ i j, i < r → j < r → i ≠ j → (P i).Orth (P j)) (hr : 3 ≤ r)
    (hA : ∀ x ∈ tailSpace P r, Q x = 0 → x = 0)
    (hdim : finrank K (tailSpace P r) = 0 ∨ finrank K (tailSpace P r) = 2) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      orthElementaryGroup Q := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hA' : ∀ x ∈ tailSpace P r, x ≠ 0 → ∀ y ∈ tailSpace P r, polar Q x y = 0 →
      ∃ c : K, y = c • x := by
    intro x hx hx0 y hy hxy
    rcases hdim with h0 | h2'
    · exact absurd ((Submodule.finrank_eq_zero.1 h0) ▸ hx : x ∈ (⊥ : Submodule K V))
        (by rw [Submodule.mem_bot]; exact hx0)
    · exact eq_smul_of_polar_eq_zero_of_finrank_two h2' (polarNondegOn_tailSpace hP hQ le_rfl)
        hx hx0 (by rw [polar_self_eq_two_mul, h2, zero_mul]) hy hxy
  exact commutator_orthogonalGroup_eq_of_two_eq_zero hP hQ h2 hA hA' hr

end CFSG.LocalAnalysis.ComponentInitial
