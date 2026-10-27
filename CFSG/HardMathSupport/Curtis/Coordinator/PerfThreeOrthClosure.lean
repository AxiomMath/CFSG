module

public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic
public import CFSG.ClassicalGroups.Orthogonal.Eichler

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

section Closure

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def Good (Q : QuadraticForm K V) (J : Subgroup (V ≃ₗ[K] V)) (e w : V) : Prop :=
  polar Q e w = 0 ∧ w ∉ Submodule.span K {e} ∧ Q w = 0 ∧
    ∀ y, polar Q e y = 0 → polar Q w y = 0 → eichler Q w y ∈ J

theorem two_smul_eq_zero' [CharP K 2] (v : V) : (2 : K) • v = 0 := by
  rw [CharTwo.two_eq_zero (R := K), zero_smul]

theorem add_self_eq_zero' [CharP K 2] (v : V) : v + v = 0 := by
  rw [← two_smul K v, two_smul_eq_zero' (K := K)]

theorem eq_of_add_eq_zero' [CharP K 2] {x y : V} (h : x + y = 0) : x = y :=
  add_right_cancel (h.trans (add_self_eq_zero' (K := K) y).symm)

theorem Good.map {J : Subgroup (V ≃ₗ[K] V)} (hJ : J ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    {e w : V} (hw : Good Q J e w) {g : V ≃ₗ[K] V} (hg : g ∈ J) (hge : g e = e) :
    Good Q J e (g w) := by
  have hgO := hJ hg
  obtain ⟨h1, h2, h3, h4⟩ := hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := polar_map_of_mem hgO e w
    rw [hge] at this
    rw [this, h1]
  · intro hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    apply h2
    refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
    apply g.injective
    rw [map_smul, hge]
    exact hc
  · rw [map_of_mem hgO, h3]
  · intro y hy1 hy2
    set y' := g⁻¹ y with hy'
    have hgy' : g y' = y := LinearEquiv.apply_inv_apply' g y
    have e1 : polar Q e y' = 0 := by
      have := polar_map_of_mem hgO e y'
      rw [hge, hgy'] at this
      rw [← this, hy1]
    have e2 : polar Q w y' = 0 := by
      have := polar_map_of_mem hgO w y'
      rw [hgy'] at this
      rw [← this, hy2]
    have := J.mul_mem (J.mul_mem hg (h4 y' e1 e2)) (J.inv_mem hg)
    rwa [eichler_conj hgO, hgy'] at this

theorem Good.add_center [CharP K 2] [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    {J : Subgroup (V ≃ₗ[K] V)} (hJ : J ≤ TauCeti.QuadraticMap.orthogonalGroup Q) {e w : V}
    (he0 : e ≠ 0) (heQ : Q e = 0) (hRe : ∀ y, eichler Q e y ∈ J)
    (hw : Good Q J e w) : Good Q J e (w + e) := by
  have hli : LinearIndependent K ![e, w] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero, smul_eq_zero] at hst
      exact ⟨hst.resolve_right he0, rfl⟩
    · exfalso
      apply hw.2.1
      refine Submodule.mem_span_singleton.mpr ⟨-(s / t), ?_⟩
      have : t • w = -(s • e) := eq_neg_of_add_eq_zero_right hst
      have h2 : w = -(s / t) • e := by
        have h3 : w = t⁻¹ • (t • w) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        rw [h3, this, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
      exact h2.symm
  obtain ⟨g, hg⟩ := exists_dual_family hQ hli
  have hy0 : polar Q e (g 1) = 0 := by simpa using hg 0 1
  have hy1 : polar Q w (g 1) = 1 := by simpa using hg 1 1
  have hwe : polar Q w e = 0 := by rw [polar_comm]; exact hw.1
  have hx : eichler Q e (g 1) w = w + e := by
    rw [eichler_apply heQ hy0, hwe, hy1]
    simp only [zero_smul, add_zero, mul_zero, one_smul]
    linear_combination (norm := module) (-1 : K) • two_smul_eq_zero' (K := K) e
  have := Good.map hJ hw (hRe (g 1)) (eichler_apply_self e (g 1))
  rwa [hx] at this

theorem Good.of_partner [CharP K 2] {J : Subgroup (V ≃ₗ[K] V)}
    (hJ : J ≤ TauCeti.QuadraticMap.orthogonalGroup Q) {e : V} (hfix : ∀ g ∈ J, g e = e)
    {w w₂ w' : V} (h₂ : Good Q J e w₂) (hw : Good Q J e w) (hww₂ : polar Q w w₂ = 1)
    (h1 : polar Q e w' = 0) (h3 : Q w' = 0)
    (hw'w₂ : polar Q w' w₂ = 1) : Good Q J e w' := by
  have hw₂w : polar Q w₂ w = 1 := by rw [polar_comm]; exact hww₂
  have hw₂w' : polar Q w₂ w' = 1 := by rw [polar_comm]; exact hw'w₂
  have hy : polar Q w₂ (w + w') = 0 := by
    rw [polar_add_right, hw₂w, hw₂w', one_add_one_eq_two, CharTwo.two_eq_zero (R := K)]
  have hye : polar Q e (w + w') = 0 := by rw [polar_add_right, hw.1, h1, add_zero]
  have hgJ := h₂.2.2.2 (w + w') hye hy
  have hQ2 := h₂.2.2.1
  have hgw : eichler Q w₂ (w + w') w = w' := by
    rw [eichler_apply hQ2 hy, polar_add_right, polar_self_eq_zero hw.2.2.1, hww₂,
      QuadraticMap.map_add Q w w', hw.2.2.1, h3, zero_add, zero_add, zero_add, one_smul, mul_one]
    have hh : polar Q w w' + polar Q w w' = 0 := add_self_eq_zero' (K := K) (V := K) _
    rw [hh, zero_smul]
    linear_combination (norm := module) (1 : K) • two_smul_eq_zero' (K := K) w
  have := Good.map hJ hw hgJ (hfix _ hgJ)
  rwa [hgw] at this

theorem exists_common_dual [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) (hK2 : ∀ c : K, c = 0 ∨ c = 1) {e w₂ w' : V}
    (hw₂ : w₂ ∉ Submodule.span K {e}) (hw' : w' ∉ Submodule.span K {e}) (hne : w' ≠ w₂)
    (hne' : w' ≠ w₂ + e) :
    ∃ y, polar Q e y = 0 ∧ polar Q w₂ y = 1 ∧ polar Q w' y = 1 := by
  by_cases he0 : e = 0
  · subst he0
    have hw₂0 : w₂ ≠ 0 := fun h => hw₂ (by simp [h])
    have hw'0 : w' ≠ 0 := fun h => hw' (by simp [h])
    have hli : LinearIndependent K ![w₂, w'] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      rcases hK2 s with rfl | rfl <;> rcases hK2 t with rfl | rfl
      · exact ⟨rfl, rfl⟩
      · simp at hst
        exact absurd hst hw'0
      · simp at hst
        exact absurd hst hw₂0
      · simp at hst
        exact absurd (eq_of_add_eq_zero' (K := K) hst).symm hne
    obtain ⟨g, hg⟩ := exists_dual_family hQ hli
    refine ⟨g 0 + g 1, by rw [polar_zero_left], ?_, ?_⟩
    · rw [polar_add_right]
      have h0 : polar Q w₂ (g 0) = 1 := by simpa using hg 0 0
      have h1 : polar Q w₂ (g 1) = 0 := by simpa using hg 0 1
      rw [h0, h1, add_zero]
    · rw [polar_add_right]
      have h0 : polar Q w' (g 0) = 0 := by simpa using hg 1 0
      have h1 : polar Q w' (g 1) = 1 := by simpa using hg 1 1
      rw [h0, h1, zero_add]
  · have hli : LinearIndependent K ![e, w₂, w'] := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      rw [Fin.sum_univ_three] at hg
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons] at hg
      have hw₂0 : w₂ ≠ 0 := fun h => hw₂ (by simp [h])
      have hw'0 : w' ≠ 0 := fun h => hw' (by simp [h])
      have hall : g 0 = 0 ∧ g 1 = 0 ∧ g 2 = 0 := by
        rcases hK2 (g 0) with h0 | h0 <;> rcases hK2 (g 1) with h1 | h1 <;>
          rcases hK2 (g 2) with h2 | h2 <;>
          simp only [h0, h1, h2, one_smul, zero_smul, zero_add, add_zero] at hg
        · exact ⟨h0, h1, h2⟩
        · exact absurd hg hw'0
        · exact absurd hg hw₂0
        · exact absurd (eq_of_add_eq_zero' (K := K) hg).symm hne
        · exact absurd hg he0
        · exact (hw' (by rw [← eq_of_add_eq_zero' (K := K) hg]; exact Submodule.mem_span_singleton_self e)).elim
        · exact (hw₂ (by rw [← eq_of_add_eq_zero' (K := K) hg]; exact Submodule.mem_span_singleton_self e)).elim
        · exact absurd (by rw [add_comm w₂ e]; exact (eq_of_add_eq_zero' (K := K) hg).symm) hne'
      intro i
      fin_cases i
      · exact hall.1
      · exact hall.2.1
      · exact hall.2.2
    obtain ⟨g, hg⟩ := exists_dual_family hQ hli
    refine ⟨g 1 + g 2, ?_, ?_, ?_⟩
    · rw [polar_add_right]
      have h1 : polar Q e (g 1) = 0 := by simpa using hg 0 1
      have h2 : polar Q e (g 2) = 0 := by simpa using hg 0 2
      rw [h1, h2, add_zero]
    · rw [polar_add_right]
      have h1 : polar Q w₂ (g 1) = 1 := by simpa using hg 1 1
      have h2 : polar Q w₂ (g 2) = 0 := by simpa using hg 1 2
      rw [h1, h2, add_zero]
    · rw [polar_add_right]
      have h1 : polar Q w' (g 1) = 0 := by simpa using hg 2 1
      have h2 : polar Q w' (g 2) = 1 := by simpa using hg 2 2
      rw [h1, h2, zero_add]

theorem good_of_pair [CharP K 2] [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    (hK2 : ∀ c : K, c = 0 ∨ c = 1) {J : Subgroup (V ≃ₗ[K] V)}
    (hJ : J ≤ TauCeti.QuadraticMap.orthogonalGroup Q) {e : V} (heQ : Q e = 0)
    (hRe : ∀ y, eichler Q e y ∈ J) (hfix : ∀ g ∈ J, g e = e) {w w₂ : V} (hw : Good Q J e w)
    (hw₂ : Good Q J e w₂) (hpair : polar Q w w₂ = 1) {w' : V} (hw'e : polar Q e w' = 0)
    (hw'span : w' ∉ Submodule.span K {e}) (hw'Q : Q w' = 0) : Good Q J e w' := by
  rcases hK2 (polar Q w' w₂) with h0 | h1'
  · by_cases hw'2 : w' = w₂
    · rw [hw'2]
      exact hw₂
    by_cases hw'3 : w' = w₂ + e
    · have he0 : e ≠ 0 := by
        rintro rfl
        apply hw'2
        rw [hw'3, add_zero]
      rw [hw'3]
      exact Good.add_center hQ hJ he0 heQ hRe hw₂
    obtain ⟨y, hy0, hy1, hy2⟩ := exists_common_dual hQ hK2 hw₂.2.1 hw'span hw'2 hw'3
    set x := y + Q y • w₂ with hx
    have hw₂Q := hw₂.2.2.1
    have hpw₂ : polar Q w₂ w₂ = 0 := polar_self_eq_zero hw₂Q
    have hxe : polar Q e x = 0 := by
      rw [hx, polar_add_right, polar_smul_right_eq, hy0, hw₂.1, mul_zero, add_zero]
    have hxw₂ : polar Q x w₂ = 1 := by
      rw [hx, polar_add_left, polar_smul_left_eq, hpw₂, mul_zero, add_zero, polar_comm, hy1]
    have hxQ : Q x = 0 := by
      rw [hx, QuadraticMap.map_add Q, map_smul_eq_sq, hw₂Q, mul_zero, polar_smul_right_eq,
        polar_comm Q y w₂, hy1, mul_one, add_zero]
      exact CharTwo.add_self_eq_zero (Q y)
    have hwx : polar Q w' x = 1 := by
      rw [hx, polar_add_right, polar_smul_right_eq, hy2, h0, mul_zero, add_zero]
    have hGx : Good Q J e x := Good.of_partner hJ hfix hw₂ hw hpair hxe hxQ hxw₂
    exact Good.of_partner hJ hfix hGx hw₂ (by rw [polar_comm]; exact hxw₂) hw'e hw'Q hwx
  · exact Good.of_partner hJ hfix hw₂ hw hpair hw'e hw'Q h1'

theorem exists_totSingular_of_pairFree [CharP K 2] (hK2 : ∀ c : K, c = 0 ∨ c = 1)
    {J : Subgroup (V ≃ₗ[K] V)} (hJ : J ≤ TauCeti.QuadraticMap.orthogonalGroup Q) {e : V}
    (heQ : Q e = 0) (hfix : ∀ g ∈ J, g e = e)
    (hno : ∀ w w₂, Good Q J e w → Good Q J e w₂ → polar Q w w₂ ≠ 1) :
    ∃ W : Submodule K V, (∀ x ∈ W, Q x = 0) ∧ (∀ g ∈ J, ∀ x ∈ W, g x ∈ W) ∧ e ∈ W ∧
      ∀ w, Good Q J e w → w ∈ W := by
  set S : Set V := insert e {w | Good Q J e w} with hS
  refine ⟨Submodule.span K S, ?_, ?_, Submodule.subset_span (Set.mem_insert _ _),
    fun w hw => Submodule.subset_span (Set.mem_insert_of_mem _ hw)⟩
  · intro x hx
    refine map_eq_zero_of_mem_span (S := S) ?_ ?_ hx
    · rintro u (rfl | hu)
      · exact heQ
      · exact hu.2.2.1
    · rintro u hu w hw
      rcases hu with rfl | hu <;> rcases hw with rfl | hw
      · exact polar_self_eq_zero heQ
      · exact hw.1
      · rw [polar_comm]
        exact hu.1
      · rcases hK2 (polar Q u w) with h | h
        · exact h
        · exact absurd h (hno u w hu hw)
  · intro g hg x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      rcases hy with rfl | hy
      · rw [hfix g hg]
        exact Submodule.subset_span (Set.mem_insert _ _)
      · exact Submodule.subset_span (Set.mem_insert_of_mem _ (Good.map hJ hy hg (hfix g hg)))
    | zero => simp
    | add _ _ _ _ h1 h2 =>
      rw [map_add]
      exact add_mem h1 h2
    | smul a y _ h =>
      rw [map_smul]
      exact Submodule.smul_mem _ _ h

end Closure

end CFSG.HardMathSupport.Curtis.Coordinator
