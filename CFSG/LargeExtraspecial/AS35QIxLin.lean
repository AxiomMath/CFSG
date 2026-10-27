module

public import CFSG.LargeExtraspecial.AS35QThCoordA
public import CFSG.RankThree.OrthogonalInvolutions.OmegaClasses

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QIx

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions Submodule

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

section Fpf

variable {ζ : V ≃ₗ[ZMod 2] V} (hζ : ∀ v, ζ (ζ v) + ζ v + v = 0)
include hζ

theorem zeta_zeta (v : V) : ζ (ζ v) = ζ v + v :=
  AS35QTh.zeta_zeta (ζ := (ζ : V →ₗ[ZMod 2] V)) hζ v

theorem zeta_cube (v : V) : ζ (ζ (ζ v)) = v :=
  AS35QTh.zeta_cube (ζ := (ζ : V →ₗ[ZMod 2] V)) hζ v

theorem eq_zero_of_zeta_eq {v : V} (hv : ζ v = v) : v = 0 := by
  have h := hζ v
  rwa [hv, hv, AS35QTh.add_self_V, zero_add] at h

theorem eq_zero_of_zeta_zeta_eq {v : V} (hv : ζ (ζ v) = v) : v = 0 := by
  have h := hζ v
  rw [hv, add_comm v, add_assoc, AS35QTh.add_self_V, add_zero] at h
  exact eq_zero_of_zeta_eq hζ (by rw [h, ← hv, h, map_zero])

omit hζ in
theorem mem_span_pair_zeta {a x : V} :
    x ∈ span (ZMod 2) {a, ζ a} ↔ ∃ c d : ZMod 2, c • a + d • ζ a = x :=
  mem_span_pair

theorem zeta_mem_span_pair {a x : V} (hx : x ∈ span (ZMod 2) {a, ζ a}) :
    ζ x ∈ span (ZMod 2) {a, ζ a} := by
  obtain ⟨c, d, rfl⟩ := mem_span_pair_zeta.mp hx
  refine mem_span_pair_zeta.mpr ⟨d, c + d, ?_⟩
  rw [map_add, map_smul, map_smul, zeta_zeta hζ, add_smul, smul_add]
  abel

theorem linearIndependent_four {a w : V} (ha : a ≠ 0) (hw : w ∉ span (ZMod 2) {a, ζ a}) :
    LinearIndependent (ZMod 2) ![a, ζ a, w, ζ w] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg'
  have hg : g 0 • a + g 1 • ζ a + g 2 • w + g 3 • ζ w = 0 := by
    rw [Fin.sum_univ_four] at hg'
    exact hg'
  have hmem : g 0 • a + g 1 • ζ a ∈ span (ZMod 2) {a, ζ a} :=
    mem_span_pair_zeta.mpr ⟨g 0, g 1, rfl⟩
  have h23 : g 2 = 0 ∧ g 3 = 0 := by
    rcases AS35QTh.zmod2_cases (g 2) with h2 | h2 <;>
      rcases AS35QTh.zmod2_cases (g 3) with h3 | h3
    · exact ⟨h2, h3⟩
    · exfalso
      rw [h2, h3, zero_smul, add_zero, one_smul, add_assoc] at hg
      have e := AS35QTh.eq_of_add_eq_zero_V (by rw [← add_assoc] at hg; exact hg)
      apply hw
      rw [← zeta_cube hζ w, ← e]
      exact zeta_mem_span_pair hζ (zeta_mem_span_pair hζ hmem)
    · exfalso
      rw [h2, h3, zero_smul, add_zero, one_smul] at hg
      exact hw (AS35QTh.eq_of_add_eq_zero_V hg ▸ hmem)
    · exfalso
      rw [h2, h3, one_smul, one_smul, add_assoc] at hg
      have e := AS35QTh.eq_of_add_eq_zero_V hg
      have h' : ζ (ζ w) ∈ span (ZMod 2) {a, ζ a} := by
        rw [zeta_zeta hζ, add_comm, ← e]
        exact hmem
      apply hw
      rw [← zeta_cube hζ w]
      exact zeta_mem_span_pair hζ h'
  rw [h23.1, h23.2, zero_smul, zero_smul, add_zero, add_zero] at hg
  clear hg'
  have h01 : g 0 = 0 ∧ g 1 = 0 := by
    rcases AS35QTh.zmod2_cases (g 0) with h0 | h0 <;>
      rcases AS35QTh.zmod2_cases (g 1) with h1 | h1
    · exact ⟨h0, h1⟩
    · exfalso
      rw [h0, h1, zero_smul, zero_add, one_smul] at hg
      exact ha (ζ.injective (by rw [hg, map_zero]))
    · exfalso
      rw [h0, h1, zero_smul, add_zero, one_smul] at hg
      exact ha hg
    · exfalso
      rw [h0, h1, one_smul, one_smul] at hg
      exact ha (eq_zero_of_zeta_eq hζ (AS35QTh.eq_of_add_eq_zero_V hg).symm)
  intro i
  fin_cases i
  · exact h01.1
  · exact h01.2
  · exact h23.1
  · exact h23.2

theorem linearIndependent_pair {a : V} (ha : a ≠ 0) :
    LinearIndependent (ZMod 2) ![a, ζ a] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  rcases AS35QTh.zmod2_cases s with hs | hs <;> rcases AS35QTh.zmod2_cases t with ht | ht
  · exact ⟨hs, ht⟩
  · exfalso
    rw [hs, ht, zero_smul, zero_add, one_smul] at hst
    exact ha (ζ.injective (by rw [hst, map_zero]))
  · exfalso
    rw [hs, ht, zero_smul, add_zero, one_smul] at hst
    exact ha hst
  · exfalso
    rw [hs, ht, one_smul, one_smul] at hst
    exact ha (eq_zero_of_zeta_eq hζ (AS35QTh.eq_of_add_eq_zero_V hst).symm)

theorem finrank_span_pair [FiniteDimensional (ZMod 2) V] {a : V} (ha : a ≠ 0) :
    finrank (ZMod 2) (span (ZMod 2) {a, ζ a}) = 2 := by
  have h := finrank_span_eq_card (linearIndependent_pair hζ ha)
  have hr : Set.range ![a, ζ a] = {a, ζ a} := by
    ext x
    simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (h | h) <;> [exact Or.inl h.symm; exact Or.inr h.symm]
    · rintro (h | h) <;> [exact Or.inl h.symm; exact Or.inr h.symm]
  rw [hr] at h
  simpa using h

end Fpf

section Iso

variable [FiniteDimensional (ZMod 2) V] {q : QuadraticForm (ZMod 2) V} {ζ : V ≃ₗ[ZMod 2] V}

omit [FiniteDimensional (ZMod 2) V] in
theorem polar_span_of_forall {ι : Type*} {v : ι → V} (h : ∀ i j, polar q (v i) (v j) = 0)
    {x y : V} (hx : x ∈ span (ZMod 2) (Set.range v)) (hy : y ∈ span (ZMod 2) (Set.range v)) :
    polar q x y = 0 := by
  have h1 : ∀ j, polar q x (v j) = 0 := by
    intro j
    induction hx using span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      exact h i j
    | zero => rw [polar_zero_left]
    | add a b _ _ ha hb => rw [polar_add_left, ha, hb, add_zero]
    | smul c a _ ha => rw [polar_smul_left, ha, smul_zero]
  induction hy using span_induction with
  | mem z hz =>
    obtain ⟨j, rfl⟩ := hz
    exact h1 j
  | zero => rw [polar_zero_right]
  | add a b _ _ ha hb => rw [polar_add_right, ha, hb, add_zero]
  | smul c a _ ha => rw [polar_smul_right, ha, smul_zero]

omit [FiniteDimensional (ZMod 2) V] in
theorem q_span_of_forall {ι : Type*} {v : ι → V} (h : ∀ i j, polar q (v i) (v j) = 0)
    (hq0 : ∀ i, q (v i) = 0) {x : V} (hx : x ∈ span (ZMod 2) (Set.range v)) : q x = 0 := by
  induction hx using span_induction with
  | mem z hz =>
    obtain ⟨i, rfl⟩ := hz
    exact hq0 i
  | zero => rw [QuadraticMap.map_zero]
  | add a b ha' hb' ha hb =>
    rw [QuadraticMap.map_add q, ha, hb, polar_span_of_forall h ha' hb', add_zero, add_zero]
  | smul c a _ ha => rw [QuadraticMap.map_smul, ha, smul_zero]

omit [FiniteDimensional (ZMod 2) V] in
theorem q_eq_polar (hζ : ∀ v, ζ (ζ v) + ζ v + v = 0) (hqζ : ∀ v, q (ζ v) = q v) (v : V) :
    q v = polar q v (ζ v) :=
  AS35QTh.q_eq_polar_zeta (ζ := (ζ : V →ₗ[ZMod 2] V)) hζ hqζ v

variable (hq : q.polarBilin.Nondegenerate) (hV : finrank (ZMod 2) V = 6)
  (hζ : ∀ v, ζ (ζ v) + ζ v + v = 0) (hqζ : ∀ v, q (ζ v) = q v)
include hq hV hζ hqζ

theorem false_of_four {a w : V} (ha : a ≠ 0) (hw : w ∉ span (ZMod 2) {a, ζ a})
    (h1 : polar q a w = 0) (h2 : polar q a (ζ w) = 0) (h3 : polar q (ζ a) w = 0)
    (h4 : polar q (ζ a) (ζ w) = 0) (hqa : q a = 0) (hqw : q w = 0) : False := by
  set v : Fin 4 → V := ![a, ζ a, w, ζ w] with hv
  have haζ : polar q a (ζ a) = 0 := by rw [← q_eq_polar hζ hqζ, hqa]
  have hwζ : polar q w (ζ w) = 0 := by rw [← q_eq_polar hζ hqζ, hqw]
  have hpol : ∀ i j, polar q (v i) (v j) = 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [hv, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Fin.isValue,
        Matrix.tail_cons, Matrix.head_cons] <;>
      first
        | exact AS35QTh.polar_self_zmod q _
        | assumption
        | (rwa [polar_comm])
  have hq0 : ∀ i, q (v i) = 0 := by
    intro i
    fin_cases i <;>
      simp only [hv, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Fin.isValue, hqζ,
        Matrix.tail_cons, Matrix.head_cons] <;>
      assumption
  have hsing : ∀ x ∈ span (ZMod 2) (Set.range v), q x = 0 := fun x hx =>
    q_span_of_forall hpol hq0 hx
  have hle := two_mul_finrank_le_of_forall_eq_zero hq hsing
  have hcard := finrank_span_eq_card (linearIndependent_four hζ ha hw)
  rw [Fintype.card_fin] at hcard
  rw [hcard, hV] at hle
  omega

theorem le_span_of_isotropic {U : Submodule (ZMod 2) V} (hUζ : ∀ u ∈ U, ζ u ∈ U)
    (hUi : ∀ u ∈ U, ∀ u' ∈ U, polar q u u' = 0) {a : V} (haU : a ∈ U) (ha : a ≠ 0) :
    U ≤ span (ZMod 2) {a, ζ a} := by
  intro w hwU
  by_contra hw
  exact false_of_four hq hV hζ hqζ ha hw (hUi _ haU _ hwU) (hUi _ haU _ (hUζ _ hwU))
    (hUi _ (hUζ _ haU) _ hwU) (hUi _ (hUζ _ haU) _ (hUζ _ hwU))
    (by rw [q_eq_polar hζ hqζ]; exact hUi _ haU _ (hUζ _ haU))
    (by rw [q_eq_polar hζ hqζ]; exact hUi _ hwU _ (hUζ _ hwU))

end Iso

end CFSG.LargeExtraspecial.AS35QIx
