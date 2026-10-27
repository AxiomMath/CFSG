module

public import CFSG.ClassicalGroups.Orthogonal.CharTwoTransvection

public section

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal

class IsF2 (K : Type*) [Field K] : Prop where
  eq_zero_or_one : ∀ c : K, c = 0 ∨ c = 1

instance : IsF2 (ZMod 2) := ⟨by decide⟩

namespace IsF2

variable {K : Type*} [Field K] [IsF2 K]

theorem eq_one_of_ne_zero {a : K} (h : a ≠ 0) : a = 1 :=
  (eq_zero_or_one a).resolve_left h

theorem one_add_one : (1 : K) + 1 = 0 := by
  rcases eq_zero_or_one ((1 : K) + 1) with h | h
  · exact h
  · exact absurd (add_eq_right.mp h) one_ne_zero

theorem two_eq_zero : (2 : K) = 0 := by
  rw [← one_add_one_eq_two]
  exact one_add_one

theorem neg_eq_self (c : K) : -c = c := by
  rw [neg_eq_iff_add_eq_zero, ← two_mul, two_eq_zero, zero_mul]

theorem add_self_eq_zero (c : K) : c + c = 0 := by
  rw [← two_mul, two_eq_zero, zero_mul]

omit [IsF2 K] in
theorem of_natCard_eq_two (hK : Nat.card K = 2) : IsF2 K := by
  refine ⟨fun c => ?_⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  by_contra! h
  obtain ⟨hc0, hc1⟩ := h
  have hinj : Function.Injective (fun i : Fin 3 => ![(0 : K), 1, c] i) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have := Nat.card_le_card_of_injective _ hinj
  simp at this
  omega

omit [IsF2 K] in
theorem finite_of_isF2 [IsF2 K] : Finite K :=
  Finite.of_surjective (fun b : Bool => if b then (1 : K) else 0) fun c => by
    rcases IsF2.eq_zero_or_one c with rfl | rfl
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩

end IsF2

instance (priority := low) {K : Type*} [Field K] [IsF2 K] : Finite K := IsF2.finite_of_isF2

variable {K V : Type*} [Field K] [IsF2 K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem reflect_apply_of_map_eq_one' {v : V} (hv : Q v = 1) (x : V) :
    reflect Q v x = x + polar Q x v • v := by
  rw [reflect_apply (by rw [hv]; exact one_ne_zero), hv, div_one, polar_comm, sub_eq_add_neg,
    ← neg_smul, IsF2.neg_eq_self]

theorem exists_ne_zero_map_eq_zero_of_linearIndependent' {v : Fin 3 → V}
    (hv : LinearIndependent K v) : ∃ x : V, x ≠ 0 ∧ Q x = 0 := by
  by_contra! h
  have hQ1 : ∀ x : V, x ≠ 0 → Q x = 1 := fun x hx => IsF2.eq_one_of_ne_zero (h x hx)
  have key : ∀ g : Fin 3 → K, g ≠ 0 → ∑ i, g i • v i ≠ 0 := fun g hg h0 =>
    hg (funext (Fintype.linearIndependent_iff.mp hv g h0))
  have hne : ∀ g : Fin 3 → K, (∃ i, g i ≠ 0) → g ≠ 0 := fun g ⟨i, hi⟩ h0 => hi (by simp [h0])
  have h0 := key ![1, 0, 0] (hne _ ⟨0, by simp⟩)
  have h1 := key ![0, 1, 0] (hne _ ⟨1, by simp⟩)
  have h2 := key ![0, 0, 1] (hne _ ⟨2, by simp⟩)
  have h01 := key ![1, 1, 0] (hne _ ⟨0, by simp⟩)
  have h02 := key ![1, 0, 1] (hne _ ⟨0, by simp⟩)
  have h12 := key ![0, 1, 1] (hne _ ⟨1, by simp⟩)
  have h012 := key ![1, 1, 1] (hne _ ⟨0, by simp⟩)
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, one_smul, zero_smul, add_zero,
    zero_add] at h0 h1 h2 h01 h02 h12 h012
  apply h _ h012
  rw [map_add_add, hQ1 _ h0, hQ1 _ h1, hQ1 _ h2, hQ1 _ h01, hQ1 _ h02, hQ1 _ h12]
  ring

theorem exists_ne_zero_map_eq_zero' [FiniteDimensional K V]
    (h3 : 3 ≤ finrank K V) : ∃ x : V, x ≠ 0 ∧ Q x = 0 := by
  let b := Module.finBasis K V
  exact exists_ne_zero_map_eq_zero_of_linearIndependent'
    (b.linearIndependent.comp _ (Fin.castLE_injective h3))

theorem exists_eq_smul_of_anisotropic' {A : Submodule K V}
    (hA : ∀ x ∈ A, Q x = 0 → x = 0) {x : V} (hx : x ∈ A) (hx0 : x ≠ 0) {y : V} (hy : y ∈ A)
    (hxy : polar Q x y = 0) : ∃ c : K, y = c • x := by
  by_cases hy0 : y = 0
  · exact ⟨0, by rw [hy0, zero_smul]⟩
  have hQx : Q x = 1 := IsF2.eq_one_of_ne_zero fun h0 => hx0 (hA x hx h0)
  have hQy : Q y = 1 := IsF2.eq_one_of_ne_zero fun h0 => hy0 (hA y hy h0)
  have hQxy : Q (x + y) = 0 := by
    rw [QuadraticMap.map_add Q, hQx, hQy, hxy, add_zero]
    exact IsF2.one_add_one
  refine ⟨-1, ?_⟩
  rw [neg_one_smul, eq_neg_iff_add_eq_zero, add_comm]
  exact hA _ (A.add_mem hx hy) hQxy

theorem eichler_eq_one_of_not_exists_plane'
    (hplane : ¬ ∃ W : Submodule K V, finrank K W = 2 ∧ ∀ w ∈ W, Q w = 0)
    {u w : V} (hu : Q u = 0) (hw : Q w = 0) (huw : polar Q u w = 0) : eichler Q u w = 1 := by
  by_cases hu0 : u = 0
  · rw [hu0, eichler_zero_left]
  by_cases hw0 : w = 0
  · rw [hw0, eichler_zero_right]
  by_cases hwu : w = u
  · rw [hwu]
    have := eichler_add_smul_self hu 0 1
    rwa [zero_add, one_smul, eichler_zero_right] at this
  refine absurd ⟨Submodule.span K {u, w}, ?_, fun x hx => map_eq_zero_of_mem_span ?_ ?_ hx⟩
    hplane
  · have hli : LinearIndependent K ![u, w] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      rcases IsF2.eq_zero_or_one s with rfl | rfl <;> rcases IsF2.eq_zero_or_one t with rfl | rfl
      · exact ⟨rfl, rfl⟩
      · rw [zero_smul, one_smul, zero_add] at hst
        exact absurd hst hw0
      · rw [zero_smul, one_smul, add_zero] at hst
        exact absurd hst hu0
      · rw [one_smul, one_smul] at hst
        refine absurd ?_ hwu
        rw [← neg_eq_of_add_eq_zero_right hst]
        exact neg_eq_self_of_two_eq_zero (K := K) IsF2.two_eq_zero u
    rw [← Matrix.range_cons_cons_empty u w ![], finrank_span_eq_card hli, Fintype.card_fin]
  · rintro z (rfl | rfl)
    · exact hu
    · exact hw
  · rintro z (rfl | rfl) z' (rfl | rfl)
    · exact polar_self_eq_zero hu
    · exact huw
    · rw [polar_comm]; exact huw
    · exact polar_self_eq_zero hw

theorem orthogonalGroup_eq_closure_reflect' [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) (h3 : 3 ≤ finrank K V)
    (hE : 5 ≤ finrank K V ∨
      ¬ ∃ W : Submodule K V, finrank K W = 2 ∧ ∀ w ∈ W, Q w = 0) :
    TauCeti.QuadraticMap.orthogonalGroup Q = Subgroup.closure (Set.range (reflect Q)) := by
  have h2 : (2 : K) = 0 := IsF2.two_eq_zero
  refine le_antisymm ?_ ((Subgroup.closure_le _).mpr ?_)
  · obtain ⟨x₀, hx₀, hQx₀⟩ := exists_ne_zero_map_eq_zero' (Q := Q) h3
    obtain ⟨P₀, -⟩ := exists_hypPair hQ hQx₀ hx₀
    obtain ⟨r, P, hP, hA⟩ := exists_family_anisotropic hQ P₀
    have hr : 1 ≤ r := by
      by_contra! hr0
      rw [Nat.lt_one_iff.mp hr0] at hA
      exact hx₀ (hA x₀ Submodule.mem_top hQx₀)
    have hgen := orthogonalGroup_le_closure_of_two_eq_zero hP hQ h2 hA
      (fun x hx hx0 y hy hxy => exists_eq_smul_of_anisotropic' hA hx hx0 hy hxy) hr
    have hEle : elementaryGroup Q ≤ Subgroup.closure (Set.range (reflect Q)) := by
      refine elementaryGroup_le_of_eichler_mem fun u w hu huw => ?_
      by_cases hw : Q w = 0
      · rcases hE with h5 | hplane
        · obtain ⟨a, hua, hwa, ha⟩ := exists_polar_eq_zero_map_ne_zero hQ h5 u w
          exact eichler_mem_closure_reflect_of_polar_eq_zero h2 hu huw hw hua hwa
            (IsF2.eq_one_of_ne_zero ha)
        · rw [eichler_eq_one_of_not_exists_plane' hplane hu hw huw]
          exact one_mem _
      · exact eichler_mem_closure_reflect_of_map_eq_one h2 hu huw (IsF2.eq_one_of_ne_zero hw)
    refine hgen.trans ((Subgroup.closure_le _).mpr (Set.union_subset Subgroup.subset_closure ?_))
    exact hEle
  · rintro _ ⟨v, rfl⟩
    exact reflect_mem_orthogonalGroup Q v

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
