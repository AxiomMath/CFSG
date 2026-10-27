module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.F2

public section

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

variable {K V : Type*} [Field K] [IsF2 K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem add_self_eq_zero_f2 (K : Type*) [Field K] [IsF2 K] {V : Type*} [AddCommGroup V]
    [Module K V] (x : V) : x + x = 0 := by
  have h := neg_eq_self_of_two_eq_zero (K := K) (V := V) IsF2.two_eq_zero x
  calc x + x = x + -x := by rw [h]
    _ = 0 := add_neg_cancel x

theorem polar_self_f2 (x : V) : polar Q x x = 0 := by
  rw [polar_self_eq_two_mul, IsF2.two_eq_zero, zero_mul]

theorem reflect_mul_reflect_mem_of_polar_eq_zero {a w : V} (ha : Q a = 1) (hw : Q w = 1)
    (haw : polar Q a w = 0) : reflect Q a * reflect Q w ∈ elementaryGroup Q := by
  have hwa : polar Q w a = 0 := by rw [polar_comm, haw]
  have hu : Q (a + w) = 0 := by
    rw [QuadraticMap.map_add Q, ha, hw, haw, add_zero]
    exact IsF2.one_add_one
  have hua : polar Q (a + w) a = 0 := by
    rw [polar_add_left, polar_self_f2, hwa, add_zero]
  have key := eichler_eq_reflect_mul_reflect IsF2.two_eq_zero hu hua ha
  rw [← add_assoc, add_self_eq_zero_f2 K, zero_add] at key
  rw [← key]
  exact eichler_mem_elementaryGroup Q _ _

variable [FiniteDimensional K V]

omit [IsF2 K] in
theorem exists_smul_of_forall_polar_eq_zero (hQ : (polarBilin Q).Nondegenerate) {x u : V}
    (h : ∀ w, polar Q u w = 0 → polar Q x w = 0) : ∃ c : K, x = c • u := by
  have hB : (polarBilin Q).IsRefl := fun x y hxy => by
    simpa [polarBilin_apply_apply, polar_comm Q x y] using hxy
  have hmem : x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (LinearMap.BilinForm.orthogonal (polarBilin Q)
      (Submodule.span K {u})) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hw
    have hw' := hw u (Submodule.mem_span_singleton_self u)
    have : polar Q u w = 0 := by simpa [polarBilin_apply_apply] using hw'
    have := h w this
    simpa [polarBilin_apply_apply, polar_comm Q w x] using this
  rw [LinearMap.BilinForm.orthogonal_orthogonal hQ hB] at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  exact ⟨c, hc.symm⟩

theorem exists_polar_eq_one_of_polar_eq_zero (hQ : (polarBilin Q).Nondegenerate) {u a : V}
    (hu : Q u = 0) (ha : Q a = 1) : ∃ w, polar Q u w = 0 ∧ polar Q w a = 1 := by
  by_contra! hne
  have h0 : ∀ w, polar Q u w = 0 → polar Q a w = 0 := fun w hw => by
    rw [polar_comm]
    rcases IsF2.eq_zero_or_one (polar Q w a) with h | h
    · exact h
    · exact absurd h (hne w hw)
  obtain ⟨c, hc⟩ := exists_smul_of_forall_polar_eq_zero hQ h0
  rw [hc, map_smul_eq_sq, hu, mul_zero] at ha
  exact zero_ne_one ha

theorem eichler_mem_commutator_of_map_eq_one (hQ : (polarBilin Q).Nondegenerate) {u a : V}
    (hu : Q u = 0) (hua : polar Q u a = 0) (ha : Q a = 1) :
    eichler Q u a ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  obtain ⟨w, huw, hwa⟩ := exists_polar_eq_one_of_polar_eq_zero hQ hu ha
  have hO := reflect_mem_orthogonalGroup Q a
  have hEO := eichler_mem_orthogonalGroup Q u w
  have hau : polar Q u a = 0 := hua
  have hua' : polar Q u a = 0 := hua
  have hreu : reflect Q a u = u := by
    rw [reflect_apply_of_map_eq_one' ha, hua', zero_smul, add_zero]
  have hrew : reflect Q a w = w + a := by
    rw [reflect_apply_of_map_eq_one' ha, hwa, one_smul]
  have hwa' : polar Q u (w + a) = 0 := by rw [polar_add_right, huw, hua, add_zero]
  have hnw : polar Q u (-w) = 0 := by rw [polar_neg_right, huw, neg_zero]
  have : eichler Q u a = ⁅reflect Q a, eichler Q u w⁆ := by
    rw [commutatorElement_def, eichler_conj hO, hreu, hrew, eichler_inv huw,
      eichler_mul hwa' hnw, add_neg_cancel_comm]
  rw [this]
  exact Subgroup.commutator_mem_commutator hO hEO

theorem eichler_mem_commutator (hQ : (polarBilin Q).Nondegenerate)
    (hE : 5 ≤ finrank K V ∨
      ¬ ∃ W : Submodule K V, finrank K W = 2 ∧ ∀ w ∈ W, Q w = 0)
    {u w : V} (hu : Q u = 0) (huw : polar Q u w = 0) :
    eichler Q u w ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  by_cases hw : Q w = 0
  · rcases hE with h5 | hplane
    · obtain ⟨a, hua, hwa, ha⟩ := exists_polar_eq_zero_map_ne_zero hQ h5 u w
      have ha1 := IsF2.eq_one_of_ne_zero ha
      have huwa : polar Q u (w - a) = 0 := by rw [polar_sub_right, huw, hua, sub_zero]
      have hQwa : Q (w - a) = 1 := by
        rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, polar_neg_right, hw,
          ha1, hwa, neg_zero, add_zero, zero_add]
      have : eichler Q u w = eichler Q u a * eichler Q u (w - a) := by
        rw [eichler_mul hua huwa, add_sub_cancel]
      rw [this]
      exact mul_mem (eichler_mem_commutator_of_map_eq_one hQ hu hua ha1)
        (eichler_mem_commutator_of_map_eq_one hQ hu huwa hQwa)
    · rw [eichler_eq_one_of_not_exists_plane' hplane hu hw huw]
      exact one_mem _
  · exact eichler_mem_commutator_of_map_eq_one hQ hu huw (IsF2.eq_one_of_ne_zero hw)

theorem elementaryGroup_le_commutator (hQ : (polarBilin Q).Nondegenerate)
    (hE : 5 ≤ finrank K V ∨
      ¬ ∃ W : Submodule K V, finrank K W = 2 ∧ ∀ w ∈ W, Q w = 0) :
    elementaryGroup Q ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
  elementaryGroup_le_of_eichler_mem fun _ _ hu huw => eichler_mem_commutator hQ hE hu huw

theorem exists_map_eq_one_polar_eq_zero (hQ : (polarBilin Q).Nondegenerate)
    (hd : 4 ≤ finrank K V) {a b : V} (hab : polar Q a b = 1) :
    ∃ w, Q w = 1 ∧ polar Q a w = 0 ∧ polar Q b w = 0 := by
  set f := (polarBilin Q a).prod (polarBilin Q b)
  have hmem : ∀ x, x ∈ LinearMap.ker f ↔ polar Q a x = 0 ∧ polar Q b x = 0 := fun x => by
    simp [f]
  by_contra! hne
  have hQ0 : ∀ x ∈ LinearMap.ker f, Q x = 0 := fun x hx => by
    obtain ⟨h1, h2⟩ := (hmem x).mp hx
    by_contra h0
    exact hne x (IsF2.eq_one_of_ne_zero h0) h1 h2
  have hle : LinearMap.ker f ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) (LinearMap.ker f) := by
    intro a' ha'
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro b' hb'
    have hs : b' + a' ∈ LinearMap.ker f := Submodule.add_mem _ hb' ha'
    rw [polarBilin_apply_apply, polar, hQ0 _ hs, hQ0 _ hb', hQ0 _ ha', sub_zero, sub_zero]
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hQ] at h1
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  have h3 : finrank K (LinearMap.range f) ≤ 2 :=
    (Submodule.finrank_le _).trans (by simp)
  have heq : LinearMap.ker f = LinearMap.BilinForm.orthogonal (polarBilin Q) (LinearMap.ker f) := by
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    rw [LinearMap.BilinForm.finrank_orthogonal hQ]
    omega
  have haorth : a ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (LinearMap.ker f) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    have := ((hmem y).mp hy).1
    simpa [polarBilin_apply_apply, polar_comm Q y a] using this
  rw [← heq, hmem] at haorth
  have h := haorth.2
  rw [polar_comm, hab] at h
  exact one_ne_zero h

theorem reflect_mul_reflect_mem_elementaryGroup (hQ : (polarBilin Q).Nondegenerate)
    (hd : 4 ≤ finrank K V) {a b : V} (ha : Q a = 1) (hb : Q b = 1) :
    reflect Q a * reflect Q b ∈ elementaryGroup Q := by
  rcases IsF2.eq_zero_or_one (polar Q a b) with hab | hab
  · exact reflect_mul_reflect_mem_of_polar_eq_zero ha hb hab
  · obtain ⟨w, hw, haw, hbw⟩ := exists_map_eq_one_polar_eq_zero hQ hd hab
    have h1 := reflect_mul_reflect_mem_of_polar_eq_zero ha hw haw
    have h2 := reflect_mul_reflect_mem_of_polar_eq_zero hw hb (by rw [polar_comm, hbw])
    have := mul_mem h1 h2
    rwa [mul_assoc, ← mul_assoc (reflect Q w), reflect_mul_self, one_mul] at this

theorem commutatorElement_reflect_mem_f2 (hQ : (polarBilin Q).Nondegenerate)
    (hd : 4 ≤ finrank K V) (u v : V) : ⁅reflect Q u, reflect Q v⁆ ∈ elementaryGroup Q := by
  by_cases hu : Q u = 0
  · rw [reflect_of_map_eq_zero hu, commutatorElement_one_left]
    exact one_mem _
  by_cases hv : Q v = 0
  · rw [reflect_of_map_eq_zero hv, commutatorElement_one_right]
    exact one_mem _
  have hab := reflect_mul_reflect_mem_elementaryGroup hQ hd (IsF2.eq_one_of_ne_zero hu)
    (IsF2.eq_one_of_ne_zero hv)
  rw [commutatorElement_def, reflect_inv, reflect_inv]
  have := mul_mem hab hab
  simpa only [mul_assoc] using this

theorem commutator_orthogonalGroup_le_elementaryGroup (hQ : (polarBilin Q).Nondegenerate)
    (hd : 4 ≤ finrank K V)
    (hE : 5 ≤ finrank K V ∨
      ¬ ∃ W : Submodule K V, finrank K W = 2 ∧ ∀ w ∈ W, Q w = 0) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
      elementaryGroup Q := by
  have hgen := orthogonalGroup_eq_closure_reflect' hQ (by omega) hE
  refine commutator_le_of_le_closure (S := Set.range (reflect Q))
    (fun g hg x hx => conj_mem_elementaryGroup hg hx) (elementaryGroup_le_orthogonalGroup Q) ?_ ?_ ?_
  · rintro _ ⟨v, rfl⟩
    exact reflect_mem_orthogonalGroup Q v
  · rw [hgen]
    exact Subgroup.closure_mono Set.subset_union_left
  · rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    exact commutatorElement_reflect_mem_f2 hQ hd u v

theorem commutator_orthogonalGroup_eq_elementaryGroup_f2
    (hQ : (polarBilin Q).Nondegenerate) (hd : 4 ≤ finrank K V)
    (hE : 5 ≤ finrank K V ∨
      ¬ ∃ W : Submodule K V, finrank K W = 2 ∧ ∀ w ∈ W, Q w = 0) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q :=
  le_antisymm (commutator_orthogonalGroup_le_elementaryGroup hQ hd hE)
    (elementaryGroup_le_commutator hQ hE)

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
