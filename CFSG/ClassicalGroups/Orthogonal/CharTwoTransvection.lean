module

public import CFSG.ClassicalGroups.Orthogonal.CharTwo
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.Finiteness.Prod

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem tailSpace_congr {P P' : ℕ → HypPair Q} {j : ℕ} (h : ∀ i < j, P i = P' i) :
    tailSpace P j = tailSpace P' j := by
  ext x
  simp only [mem_tailSpace]
  exact forall₂_congr fun i hi => by rw [h i hi]

theorem exists_family_succ (hQ : (polarBilin Q).Nondegenerate) {P : ℕ → HypPair Q} {r : ℕ}
    (hP : ∀ i j, i < r → j < r → i ≠ j → (P i).Orth (P j)) {x : V} (hx : x ∈ tailSpace P r)
    (hx0 : x ≠ 0) (hQx : Q x = 0) :
    ∃ P₂ : ℕ → HypPair Q, (∀ i j, i < r + 1 → j < r + 1 → i ≠ j → (P₂ i).Orth (P₂ j)) ∧
      tailSpace P₂ (r + 1) < tailSpace P r := by
  obtain ⟨y, hyW, hxy⟩ := (polarNondegOn_tailSpace hP hQ le_rfl).exists_polar_ne_zero hx hx0
  have h1 : polar Q x ((polar Q x y)⁻¹ • y) = 1 := by
    rw [polar_smul_right_eq, inv_mul_cancel₀ hxy]
  set P' := HypPair.ofPolarEqOne hQx h1 with hP'
  have hfW : P'.f ∈ tailSpace P r := by
    rw [hP', HypPair.ofPolarEqOne_f]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hyW) (Submodule.smul_mem _ _ hx)
  have horth : ∀ i < r, (P i).Orth P' := fun i hi =>
    ⟨(mem_tailSpace.mp hx i hi).1, (mem_tailSpace.mp hfW i hi).1,
      (mem_tailSpace.mp hx i hi).2, (mem_tailSpace.mp hfW i hi).2⟩
  set P₂ : ℕ → HypPair Q := fun i => if i < r then P i else P' with hP₂
  have hlt : ∀ i < r, P₂ i = P i := fun i hi => by simp [hP₂, hi]
  have hr : P₂ r = P' := by simp [hP₂]
  refine ⟨P₂, fun i j hi hj hij => ?_, ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl <;>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [hlt i hi, hlt j hj]
      exact hP i j hi hj hij
    · rw [hlt i hi, hr]
      exact horth i hi
    · rw [hr, hlt j hj]
      exact (horth j hj).symm
    · exact absurd rfl hij
  · rw [tailSpace_succ, tailSpace_congr hlt, hr]
    refine lt_of_le_of_ne inf_le_left fun heq => ?_
    have hmem : x ∈ tailSpace P r ⊓ P'.perp := by rw [heq]; exact hx
    have := (HypPair.mem_perp.mp hmem.2).2
    rw [show x = P'.e from rfl, P'.polar_fe] at this
    exact one_ne_zero this

theorem exists_family_anisotropic [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    (P₀ : HypPair Q) :
    ∃ (r : ℕ) (P : ℕ → HypPair Q), (∀ i j, i < r → j < r → i ≠ j → (P i).Orth (P j)) ∧
      ∀ x ∈ tailSpace P r, Q x = 0 → x = 0 := by
  suffices H : ∀ (k r : ℕ) (P : ℕ → HypPair Q),
      (∀ i j, i < r → j < r → i ≠ j → (P i).Orth (P j)) → finrank K (tailSpace P r) ≤ k →
      ∃ (r : ℕ) (P : ℕ → HypPair Q), (∀ i j, i < r → j < r → i ≠ j → (P i).Orth (P j)) ∧
        ∀ x ∈ tailSpace P r, Q x = 0 → x = 0 from
    H _ 0 (fun _ => P₀) (fun i _ hi => absurd hi (Nat.not_lt_zero i)) le_rfl
  intro k
  induction k with
  | zero =>
    intro r P hP hk
    refine ⟨r, P, hP, fun x hx _ => ?_⟩
    rw [Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hk)] at hx
    exact (Submodule.mem_bot K).mp hx
  | succ k ih =>
    intro r P hP hk
    by_cases h : ∀ x ∈ tailSpace P r, Q x = 0 → x = 0
    · exact ⟨r, P, hP, h⟩
    push Not at h
    obtain ⟨x, hx, hQx, hx0⟩ := h
    obtain ⟨P₂, hP₂, hlt⟩ := exists_family_succ hQ hP hx hx0 hQx
    exact ih (r + 1) P₂ hP₂ (by have := Submodule.finrank_lt_finrank_of_lt hlt; omega)

variable (Q) in
theorem map_add_add (a b c : V) :
    Q (a + b + c) = Q (a + b) + Q (a + c) + Q (b + c) - Q a - Q b - Q c := by
  rw [QuadraticMap.map_add Q (a + b) c, polar_add_left, polar, polar]
  ring

section CharTwo

variable (h2 : (2 : K) = 0)
include h2

theorem eichler_eq_reflect_mul_reflect {u a : V} (hu : Q u = 0) (hua : polar Q u a = 0)
    (ha : Q a = 1) : eichler Q u a = reflect Q a * reflect Q (a + u) := by
  have hau : polar Q a u = 0 := by rw [polar_comm, hua]
  have hQau : Q (a + u) = 1 := by rw [QuadraticMap.map_add Q, ha, hu, hau, add_zero, add_zero]
  have haa : polar Q a a = 0 := by rw [polar_self_eq_two_mul, h2, zero_mul]
  have h2a : (2 : K) • a = 0 := by rw [h2, zero_smul]
  refine LinearEquiv.ext fun x => ?_
  rw [LinearEquiv.mul_apply, eichler_apply hu hua, reflect_apply (by rw [ha]; exact one_ne_zero),
    reflect_apply (by rw [hQau]; exact one_ne_zero), hQau, ha, div_one, div_one, polar_sub_right,
    polar_smul_right_eq, polar_add_right Q a a u, haa, hau, polar_add_left Q a u x,
    polar_comm Q a x, polar_comm Q u x]
  linear_combination (norm := module) (polar Q x a + polar Q x u) • h2a

theorem eichler_mem_closure_reflect_of_map_eq_one {u w : V} (hu : Q u = 0)
    (huw : polar Q u w = 0) (hw : Q w = 1) :
    eichler Q u w ∈ Subgroup.closure (Set.range (reflect Q)) := by
  rw [eichler_eq_reflect_mul_reflect h2 hu huw hw]
  exact mul_mem (reflect_mem_closure _) (reflect_mem_closure _)

theorem eichler_mem_closure_reflect_of_polar_eq_zero {u w a : V} (hu : Q u = 0)
    (huw : polar Q u w = 0) (hw : Q w = 0) (hua : polar Q u a = 0) (hwa : polar Q w a = 0)
    (ha : Q a = 1) : eichler Q u w ∈ Subgroup.closure (Set.range (reflect Q)) := by
  have huwa : polar Q u (w - a) = 0 := by rw [polar_sub_right, huw, hua, sub_zero]
  have hQwa : Q (w - a) = 1 := by
    rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, polar_neg_right, hw, ha,
      hwa, neg_zero, add_zero, zero_add]
  have : eichler Q u w = eichler Q u a * eichler Q u (w - a) := by
    rw [eichler_mul hua huwa, add_sub_cancel]
  rw [this]
  exact mul_mem (eichler_mem_closure_reflect_of_map_eq_one h2 hu hua ha)
    (eichler_mem_closure_reflect_of_map_eq_one h2 hu huwa hQwa)

end CharTwo

theorem exists_polar_eq_zero_map_ne_zero [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) (h5 : 5 ≤ finrank K V) (u w : V) :
    ∃ a, polar Q u a = 0 ∧ polar Q w a = 0 ∧ Q a ≠ 0 := by
  set f := (polarBilin Q u).prod (polarBilin Q w)
  have hmem : ∀ a, a ∈ LinearMap.ker f ↔ polar Q u a = 0 ∧ polar Q w a = 0 := fun a => by
    simp [f]
  by_contra! hU
  have hle : LinearMap.ker f ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) (LinearMap.ker f) := by
    intro a ha
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro b hb
    obtain ⟨hua, hwa⟩ := (hmem a).mp ha
    obtain ⟨hub, hwb⟩ := (hmem b).mp hb
    have hab : polar Q u (b + a) = 0 := by rw [polar_add_right, hub, hua, add_zero]
    have hwab : polar Q w (b + a) = 0 := by rw [polar_add_right, hwb, hwa, add_zero]
    rw [polarBilin_apply_apply, polar, hU _ hab hwab, hU _ hub hwb, hU _ hua hwa, sub_zero,
      sub_zero]
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hQ] at h1
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  have h3 : finrank K (LinearMap.range f) ≤ 2 :=
    (Submodule.finrank_le _).trans (by simp)
  omega

section ZModTwo

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

theorem zmod_two_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  revert a
  decide

theorem reflect_apply_of_map_eq_one {v : V} (hv : Q v = 1) (x : V) :
    reflect Q v x = x + polar Q x v • v := by
  rw [reflect_apply (by rw [hv]; exact one_ne_zero), hv, div_one, polar_comm, sub_eq_add_neg,
    ← neg_smul, ZMod.neg_eq_self_mod_two]

theorem exists_ne_zero_map_eq_zero_of_linearIndependent {v : Fin 3 → V}
    (hv : LinearIndependent (ZMod 2) v) : ∃ x : V, x ≠ 0 ∧ Q x = 0 := by
  by_contra! h
  have hQ1 : ∀ x : V, x ≠ 0 → Q x = 1 := fun x hx => zmod_two_eq_one_of_ne_zero (h x hx)
  have key : ∀ g : Fin 3 → ZMod 2, g ≠ 0 → ∑ i, g i • v i ≠ 0 := fun g hg h0 =>
    hg (funext (Fintype.linearIndependent_iff.mp hv g h0))
  have h0 := key ![1, 0, 0] (by decide)
  have h1 := key ![0, 1, 0] (by decide)
  have h2 := key ![0, 0, 1] (by decide)
  have h01 := key ![1, 1, 0] (by decide)
  have h02 := key ![1, 0, 1] (by decide)
  have h12 := key ![0, 1, 1] (by decide)
  have h012 := key ![1, 1, 1] (by decide)
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, one_smul, zero_smul, add_zero,
    zero_add] at h0 h1 h2 h01 h02 h12 h012
  apply h _ h012
  rw [map_add_add, hQ1 _ h0, hQ1 _ h1, hQ1 _ h2, hQ1 _ h01, hQ1 _ h02, hQ1 _ h12]
  ring

theorem exists_ne_zero_map_eq_zero [FiniteDimensional (ZMod 2) V]
    (h3 : 3 ≤ finrank (ZMod 2) V) : ∃ x : V, x ≠ 0 ∧ Q x = 0 := by
  let b := Module.finBasis (ZMod 2) V
  exact exists_ne_zero_map_eq_zero_of_linearIndependent
    (b.linearIndependent.comp _ (Fin.castLE_injective h3))

theorem exists_eq_smul_of_anisotropic {A : Submodule (ZMod 2) V}
    (hA : ∀ x ∈ A, Q x = 0 → x = 0) {x : V} (hx : x ∈ A) (hx0 : x ≠ 0) {y : V} (hy : y ∈ A)
    (hxy : polar Q x y = 0) : ∃ c : ZMod 2, y = c • x := by
  by_cases hy0 : y = 0
  · exact ⟨0, by rw [hy0, zero_smul]⟩
  have hQx : Q x = 1 := zmod_two_eq_one_of_ne_zero fun h0 => hx0 (hA x hx h0)
  have hQy : Q y = 1 := zmod_two_eq_one_of_ne_zero fun h0 => hy0 (hA y hy h0)
  have hQxy : Q (x + y) = 0 := by
    rw [QuadraticMap.map_add Q, hQx, hQy, hxy, add_zero]
    decide
  refine ⟨-1, ?_⟩
  rw [neg_one_smul, eq_neg_iff_add_eq_zero, add_comm]
  exact hA _ (A.add_mem hx hy) hQxy

theorem eichler_eq_one_of_not_exists_plane
    (hplane : ¬ ∃ W : Submodule (ZMod 2) V, finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0)
    {u w : V} (hu : Q u = 0) (hw : Q w = 0) (huw : polar Q u w = 0) : eichler Q u w = 1 := by
  by_cases hu0 : u = 0
  · rw [hu0, eichler_zero_left]
  by_cases hw0 : w = 0
  · rw [hw0, eichler_zero_right]
  by_cases hwu : w = u
  · rw [hwu]
    have := eichler_add_smul_self hu 0 1
    rwa [zero_add, one_smul, eichler_zero_right] at this
  refine absurd ⟨Submodule.span (ZMod 2) {u, w}, ?_, fun x hx => map_eq_zero_of_mem_span ?_ ?_ hx⟩
    hplane
  · have hli : LinearIndependent (ZMod 2) ![u, w] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
      rcases h01 s with rfl | rfl <;> rcases h01 t with rfl | rfl
      · exact ⟨rfl, rfl⟩
      · rw [zero_smul, one_smul, zero_add] at hst
        exact absurd hst hw0
      · rw [zero_smul, one_smul, add_zero] at hst
        exact absurd hst hu0
      · rw [one_smul, one_smul] at hst
        refine absurd ?_ hwu
        rw [← neg_eq_of_add_eq_zero_right hst]
        exact neg_eq_self_of_two_eq_zero (K := ZMod 2) (by decide) u
    rw [← Matrix.range_cons_cons_empty u w ![], finrank_span_eq_card hli, Fintype.card_fin]
  · rintro z (rfl | rfl)
    · exact hu
    · exact hw
  · rintro z (rfl | rfl) z' (rfl | rfl)
    · exact polar_self_eq_zero hu
    · exact huw
    · rw [polar_comm]; exact huw
    · exact polar_self_eq_zero hw

theorem orthogonalGroup_eq_closure_reflect [FiniteDimensional (ZMod 2) V]
    (hQ : (polarBilin Q).Nondegenerate) (h3 : 3 ≤ finrank (ZMod 2) V)
    (hE : 5 ≤ finrank (ZMod 2) V ∨
      ¬ ∃ W : Submodule (ZMod 2) V, finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0) :
    TauCeti.QuadraticMap.orthogonalGroup Q = Subgroup.closure (Set.range (reflect Q)) := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  refine le_antisymm ?_ ((Subgroup.closure_le _).mpr ?_)
  ·
    obtain ⟨x₀, hx₀, hQx₀⟩ := exists_ne_zero_map_eq_zero (Q := Q) h3
    obtain ⟨P₀, -⟩ := exists_hypPair hQ hQx₀ hx₀
    obtain ⟨r, P, hP, hA⟩ := exists_family_anisotropic hQ P₀
    have hr : 1 ≤ r := by
      by_contra! hr0
      rw [Nat.lt_one_iff.mp hr0] at hA
      exact hx₀ (hA x₀ Submodule.mem_top hQx₀)
    have hgen := orthogonalGroup_le_closure_of_two_eq_zero hP hQ h2 hA
      (fun x hx hx0 y hy hxy => exists_eq_smul_of_anisotropic hA hx hx0 hy hxy) hr
    have hEle : elementaryGroup Q ≤ Subgroup.closure (Set.range (reflect Q)) := by
      refine elementaryGroup_le_of_eichler_mem fun u w hu huw => ?_
      by_cases hw : Q w = 0
      · rcases hE with h5 | hplane
        · obtain ⟨a, hua, hwa, ha⟩ := exists_polar_eq_zero_map_ne_zero hQ h5 u w
          exact eichler_mem_closure_reflect_of_polar_eq_zero h2 hu huw hw hua hwa
            (zmod_two_eq_one_of_ne_zero ha)
        · rw [eichler_eq_one_of_not_exists_plane hplane hu hw huw]
          exact one_mem _
      · exact eichler_mem_closure_reflect_of_map_eq_one h2 hu huw (zmod_two_eq_one_of_ne_zero hw)
    refine hgen.trans ((Subgroup.closure_le _).mpr (Set.union_subset Subgroup.subset_closure ?_))
    exact hEle
  · rintro _ ⟨v, rfl⟩
    exact reflect_mem_orthogonalGroup Q v

end ZModTwo

end CFSG.ClassicalGroups.Orthogonal
