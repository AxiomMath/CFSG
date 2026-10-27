module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasThree

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module
open CFSG.LocalAnalysis.ComponentInitial (orthogonal_norm_shell_transitive
  quadratic_three_hyperbolic_pairs)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

variable (Q) in
@[expose] def ShellAdj (a : K) (x y : V) : Prop :=
  x ≠ 0 ∧ y ≠ 0 ∧ Q x = a ∧ Q y = a ∧ polar Q x y = 2 * a

theorem shellAdj_symm {a : K} {x y : V} (h : ShellAdj Q a x y) : ShellAdj Q a y x :=
  ⟨h.2.1, h.1, h.2.2.2.1, h.2.2.1, by rw [polar_comm]; exact h.2.2.2.2⟩

theorem polar_eichler_apply_self {u v : V} (hu : Q u = 0) (hv : Q v = 0) (huv : polar Q u v = 0)
    (z : V) : polar Q z (eichler Q u v z) = 2 * Q z := by
  rw [eichler_apply hu huv, hv, zero_mul, add_zero, polar_sub_right, polar_add_right,
    polar_smul_right_eq, polar_smul_right_eq, polar_self_eq_two_mul]
  ring

theorem exists_singular_decomposition [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {u : V} (hu : Q u = 0)
    (hu0 : u ≠ 0) {v : V} (huv : polar Q u v = 0) :
    ∃ w : Fin 6 → V, (∀ j, Q (w j) = 0 ∧ polar Q u (w j) = 0) ∧ ∑ j, w j = v := by
  obtain ⟨P₁, P₂, -, hP₁, h₁₂, -, -⟩ := quadratic_three_hyperbolic_pairs hQ hT hu hu0
  subst hP₁
  set c := polar Q v P₁.f with hc
  set w := v - c • P₁.e with hw
  set α := polar Q w P₂.f with hα
  set β := polar Q w P₂.e with hβ
  set w₂ := w - α • P₂.e - β • P₂.f with hw₂
  have hw₂e : polar Q P₂.e w₂ = 0 := by
    rw [hw₂, polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
      P₂.polar_ee, P₂.polar_ef, polar_comm Q P₂.e w, hβ]
    ring
  have hw₂f : polar Q P₂.f w₂ = 0 := by
    rw [hw₂, polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
      P₂.polar_fe, P₂.polar_ff, polar_comm Q P₂.f w, hα]
    ring
  have hwu : polar Q P₁.e w = 0 := by
    rw [hw, polar_sub_right, polar_smul_right_eq, P₁.polar_ee, huv]
    ring
  have hw₂u : polar Q P₁.e w₂ = 0 := by
    rw [hw₂, polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq, hwu,
      h₁₂.ee, h₁₂.ef]
    ring
  set t := Q w₂ with ht
  set s := P₂.e + w₂ - t • P₂.f with hs
  have hQs : Q s = 0 := by
    rw [hs, sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_add Q, QuadraticMap.map_neg,
      QuadraticMap.map_smul, P₂.Q_e, P₂.Q_f, polar_neg_right, polar_add_left, polar_smul_right_eq,
      polar_smul_right_eq, P₂.polar_ef, polar_comm Q w₂ P₂.f, hw₂f, hw₂e, ← ht]
    ring
  have hsu : polar Q P₁.e s = 0 := by
    rw [hs, polar_sub_right, polar_add_right, polar_smul_right_eq, h₁₂.ee, h₁₂.ef, hw₂u]
    ring
  refine ⟨![c • P₁.e, α • P₂.e, β • P₂.f, s, -P₂.e, t • P₂.f], fun j => ?_, ?_⟩
  · fin_cases j
    · exact ⟨by simp [QuadraticMap.map_smul, P₁.Q_e],
        by simp [P₁.polar_ee]⟩
    · exact ⟨by simp [QuadraticMap.map_smul, P₂.Q_e],
        by simp [h₁₂.ee]⟩
    · exact ⟨by simp [QuadraticMap.map_smul, P₂.Q_f],
        by simp [h₁₂.ef]⟩
    · exact ⟨by simpa using hQs, by simpa using hsu⟩
    · exact ⟨by simp [P₂.Q_e], by simp [polar_neg_right, h₁₂.ee]⟩
    · exact ⟨by simp [QuadraticMap.map_smul, P₂.Q_f],
        by simp [h₁₂.ef]⟩
  · rw [Fin.sum_univ_six]
    show c • P₁.e + α • P₂.e + β • P₂.f + s + -P₂.e + t • P₂.f = v
    rw [hs, hw₂, hw]
    abel

theorem exists_singular_plane_of_orth {P₁ P₂ : HypPair Q} (h : P₁.Orth P₂) :
    ∃ T : Submodule K V, finrank K T = 2 ∧ ∀ x ∈ T, Q x = 0 := by
  have hli : LinearIndependent K ![P₁.e, P₂.e] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (fun v => polar Q v P₁.f) hst
    have h2 := congrArg (fun v => polar Q v P₂.f) hst
    simp only [polar_add_left, polar_smul_left_eq, P₁.polar_ef, P₂.polar_ef, h.ef,
      polar_zero_left] at h1 h2
    rw [polar_comm Q P₂.e P₁.f, h.fe] at h1
    constructor
    · linear_combination h1
    · linear_combination h2
  refine ⟨Submodule.span K (Set.range ![P₁.e, P₂.e]), ?_, fun x hx => ?_⟩
  · rw [finrank_span_eq_card hli, Fintype.card_fin]
  · obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx
    rw [Fin.sum_univ_two]
    show Q (c 0 • P₁.e + c 1 • P₂.e) = 0
    rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul, P₁.Q_e, P₂.Q_e,
      polar_smul_left_eq, polar_smul_right_eq, h.ee]
    ring

theorem orthogonal_geometry_norm_shell_connected {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {a : K} {x y : V}
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hx : Q x = a) (hy : Q y = a) :
    ∃ l : List V, List.IsChain (ShellAdj Q a) (x :: l) ∧
      (x :: l).getLast (List.cons_ne_nil x l) = y := by
  set R := Relation.ReflTransGen (ShellAdj Q a) with hR
  have hRsymm : ∀ {z z' : V}, R z z' → R z' z := by
    intro z z' h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact Relation.ReflTransGen.head (shellAdj_symm hbc) ih
  set H : Subgroup (V ≃ₗ[K] V) :=
    { carrier := {g | g ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧
        ∀ z, z ≠ 0 → Q z = a → R z (g z)}
      mul_mem' := by
        rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
        refine ⟨mul_mem hg hh, fun z hz0 hz => ?_⟩
        have hhz0 : h z ≠ 0 := fun h0 => hz0 (h.injective (by rw [h0, map_zero]))
        exact (hh' z hz0 hz).trans (hg' (h z) hhz0 (by rw [map_of_mem hh, hz]))
      one_mem' := ⟨one_mem _, fun z _ _ => Relation.ReflTransGen.refl⟩
      inv_mem' := by
        rintro g ⟨hg, hg'⟩
        refine ⟨inv_mem hg, fun z hz0 hz => ?_⟩
        have hgz0 : (g⁻¹ : V ≃ₗ[K] V) z ≠ 0 := fun h0 =>
          hz0 ((g⁻¹ : V ≃ₗ[K] V).injective (by rw [h0, map_zero]))
        have h1 := hg' _ hgz0 (by rw [map_of_mem (inv_mem hg), hz])
        have h2 : g ((g⁻¹ : V ≃ₗ[K] V) z) = z := by
          rw [← LinearEquiv.mul_apply, mul_inv_cancel, LinearEquiv.coe_one, id_eq]
        rw [h2] at h1
        exact hRsymm h1 } with hH
  have hgen : ∀ u w, Q u = 0 → polar Q u w = 0 → eichler Q u w ∈ H := by
    intro u w hu huw
    refine ⟨eichler_mem_orthogonalGroup Q u w, ?_⟩
    by_cases hu0 : u = 0
    · intro z _ _
      rw [hu0, eichler_zero_left]
      exact Relation.ReflTransGen.refl
    have hgood : ∀ w' : V, Q w' = 0 → polar Q u w' = 0 →
        ∀ z, z ≠ 0 → Q z = a → R z (eichler Q u w' z) := by
      intro w' hw' huw' z hz0 hz
      refine Relation.ReflTransGen.single ⟨hz0, fun h0 => hz0 ?_, hz, ?_, ?_⟩
      · exact (eichler Q u w').injective (by rw [h0, map_zero])
      · rw [map_of_mem (eichler_mem_orthogonalGroup Q u w'), hz]
      · rw [polar_eichler_apply_self hu hw' huw', hz]
    obtain ⟨ws, hws, hsum⟩ := exists_singular_decomposition hQ hT hu hu0 huw
    have hpart : ∀ s : Finset (Fin 6), polar Q u (∑ j ∈ s, ws j) = 0 ∧
        ∀ z, z ≠ 0 → Q z = a → R z (eichler Q u (∑ j ∈ s, ws j) z) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        refine ⟨by rw [Finset.sum_empty, polar_zero_right], fun z _ _ => ?_⟩
        rw [Finset.sum_empty, eichler_zero_right]
        exact Relation.ReflTransGen.refl
      | insert j s hj ih =>
        obtain ⟨hs0, hs⟩ := ih
        refine ⟨by rw [Finset.sum_insert hj, polar_add_right, (hws j).2, hs0, zero_add],
          fun z hz0 hz => ?_⟩
        rw [Finset.sum_insert hj, ← eichler_mul (hws j).2 hs0, LinearEquiv.mul_apply]
        have hz' := hs z hz0 hz
        have hO := eichler_mem_orthogonalGroup Q u (∑ j ∈ s, ws j)
        have hz1 : eichler Q u (∑ j ∈ s, ws j) z ≠ 0 := fun h0 =>
          hz0 ((eichler Q u _).injective (by rw [h0, map_zero]))
        exact hz'.trans (hgood _ (hws j).1 (hws j).2 _ hz1 (by rw [map_of_mem hO, hz]))
    intro z hz0 hz
    have := (hpart Finset.univ).2 z hz0 hz
    rwa [hsum] at this
  have hEH : orthElementaryGroup Q ≤ H := elementaryGroup_le_of_eichler_mem hgen
  have hT2 : ∃ T : Submodule K V, finrank K T = 2 ∧ ∀ v ∈ T, Q v = 0 := by
    obtain ⟨T, hT3, hTs⟩ := hT
    obtain ⟨e, heT, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := T) (fun h => by
      rw [h, finrank_bot] at hT3
      omega)
    obtain ⟨P₁, P₂, -, -, h₁₂, -, -⟩ := quadratic_three_hyperbolic_pairs hQ ⟨T, hT3, hTs⟩
      (hTs e heT) he0
    exact exists_singular_plane_of_orth h₁₂
  obtain ⟨g, hg, hgx⟩ := (orthogonal_norm_shell_transitive hQ hT2).1 x y hx0 hy0 (by rw [hx, hy])
  have hR' := (hEH hg).2 x hx0 hx
  rw [hgx] at hR'
  exact List.exists_isChain_cons_of_relationReflTransGen hR'

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
