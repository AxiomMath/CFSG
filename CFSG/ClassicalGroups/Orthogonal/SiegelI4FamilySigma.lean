module

public import CFSG.ClassicalGroups.Orthogonal.SiegelI4FamilyPi
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.HardMathSupport.Kantor79 CFSG.HardMathSupport.GuralnickMalle QuadraticMap Module

variable {K : Type*} [Field K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
  {Qf : QuadraticForm K V}

@[expose] def sigmaGroup (Qf : QuadraticForm K V) (U : Submodule K V) : Subgroup (V ≃ₗ[K] V) :=
  Subgroup.closure {s | IsLongRootElement Qf s ∧ movedSpace s ≤ U}

@[expose] def altEnd (Qf : QuadraticForm K V) (U : Submodule K V) : Submodule K (V →ₗ[K] V) where
  carrier := {φ | (∀ x, φ x ∈ U) ∧
    (∀ x ∈ LinearMap.BilinForm.orthogonal (polarBilin Qf) U, φ x = 0) ∧
    ∀ x, polar Qf x (φ x) = 0}
  add_mem' := by
    rintro φ ψ ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    refine ⟨fun x => U.add_mem (h1 x) (h1' x), fun x hx => ?_, fun x => ?_⟩
    · rw [LinearMap.add_apply, h2 x hx, h2' x hx, add_zero]
    · rw [LinearMap.add_apply, polar_add_right, h3, h3', add_zero]
  zero_mem' := ⟨fun x => U.zero_mem, fun x _ => rfl, fun x => by simp⟩
  smul_mem' := by
    rintro c φ ⟨h1, h2, h3⟩
    refine ⟨fun x => U.smul_mem c (h1 x), fun x hx => ?_, fun x => ?_⟩
    · rw [LinearMap.smul_apply, h2 x hx, smul_zero]
    · rw [LinearMap.smul_apply, polar_smul_right, h3, smul_zero]

structure DualTriple (Qf : QuadraticForm K V) (U : Submodule K V) (t g : Fin 3 → V) : Prop where
  span : Submodule.span K (Set.range t) = U
  dual : ∀ i j, polar Qf (t i) (g j) = if i = j then 1 else 0

omit [CharP K 2] in
theorem dualTriple_polar_sum_left {ι : Type*} [Fintype ι] (c : ι → K) (v : ι → V) (y : V) :
    polar Qf (∑ i, c i • v i) y = ∑ i, c i * polar Qf (v i) y := by
  rw [← polarBilin_apply_apply, _root_.map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [_root_.map_smul, LinearMap.smul_apply, polarBilin_apply_apply, smul_eq_mul]

omit [CharP K 2] in
theorem dualTriple_polar_sum_right {ι : Type*} [Fintype ι] (x : V) (c : ι → K) (v : ι → V) :
    polar Qf x (∑ i, c i • v i) = ∑ i, c i * polar Qf x (v i) := by
  rw [← polarBilin_apply_apply, _root_.map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [_root_.map_smul, polarBilin_apply_apply, smul_eq_mul]

theorem exists_dualTriple [FiniteDimensional K V]
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {U : Submodule K V}
    (hU3 : finrank K U = 3) : ∃ t g : Fin 3 → V, DualTriple Qf U t g := by
  let b : Basis (Fin 3) K U := Module.finBasisOfFinrankEq K U hU3
  have ht : LinearIndependent K (fun i => (b i : V)) :=
    b.linearIndependent.map' U.subtype U.ker_subtype
  have hspan : Submodule.span K (Set.range (fun i => (b i : V))) = U := by
    have h := congrArg (Submodule.map U.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp] at h
    exact h
  obtain ⟨g, hg⟩ := exists_dual_family (nondegenerate_polarBilin hnd) ht
  exact ⟨fun i => (b i : V), g, ⟨hspan, fun i j => hg i j⟩⟩

theorem DualTriple.eq_sum {U : Submodule K V} {t g : Fin 3 → V} (h : DualTriple Qf U t g) {v : V}
    (hv : v ∈ U) : v = ∑ k, polar Qf v (g k) • t k := by
  have hv' : v ∈ Submodule.span K (Set.range t) := by
    rw [h.span]
    exact hv
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hv'
  have hcoef : ∀ k, polar Qf v (g k) = c k := by
    intro k
    rw [← hc, dualTriple_polar_sum_left]
    simp [h.dual, mul_ite]
  simp only [hcoef]
  exact hc.symm

theorem DualTriple.eq_zero_of_polar_eq_zero {U : Submodule K V} {t g : Fin 3 → V}
    (h : DualTriple Qf U t g) {z : V} (hz : z ∈ U) (h0 : ∀ k, polar Qf z (g k) = 0) : z = 0 := by
  have hz' := h.eq_sum hz
  simp only [h0, zero_smul, Finset.sum_const_zero] at hz'
  exact hz'

theorem DualTriple.map_eq_sum {U : Submodule K V} {t g : Fin 3 → V} (h : DualTriple Qf U t g)
    {φ : V →ₗ[K] V} (hφ : φ ∈ altEnd Qf U) (x : V) :
    φ x = ∑ j, polar Qf (t j) x • φ (g j) := by
  have hti : ∀ i, polar Qf (t i) (x - ∑ j, polar Qf (t j) x • g j) = 0 := by
    intro i
    rw [polar_sub_right, dualTriple_polar_sum_right, sub_eq_zero]
    simp [h.dual, mul_ite]
  have hy : x - ∑ j, polar Qf (t j) x • g j ∈
      LinearMap.BilinForm.orthogonal (polarBilin Qf) U := by
    rw [mem_orthogonal_iff_polar]
    intro m hm
    rw [← h.span] at hm
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hm
    rw [dualTriple_polar_sum_left]
    exact Finset.sum_eq_zero fun i _ => by rw [hti i, mul_zero]
  have hφy := hφ.2.1 _ hy
  rw [_root_.map_sub, _root_.map_sum] at hφy
  simp only [_root_.map_smul] at hφy
  exact sub_eq_zero.mp hφy

theorem DualTriple.eq_zero_of_coords {U : Submodule K V} {t g : Fin 3 → V}
    (h : DualTriple Qf U t g) {φ : V →ₗ[K] V} (hφ : φ ∈ altEnd Qf U)
    (h0 : ∀ j k, polar Qf (φ (g j)) (g k) = 0) : φ = 0 := by
  have hgj : ∀ j, φ (g j) = 0 := fun j =>
    h.eq_zero_of_polar_eq_zero (hφ.1 (g j)) (fun k => h0 j k)
  apply LinearMap.ext
  intro x
  rw [LinearMap.zero_apply, h.map_eq_sum hφ x]
  simp [hgj]

theorem polar_apply_symm_of_alt {φ : V →ₗ[K] V} (halt : ∀ x, polar Qf x (φ x) = 0)
    (x y : V) : polar Qf x (φ y) = polar Qf y (φ x) := by
  have h := halt (x + y)
  rw [map_add, polar_add_left, polar_add_right, polar_add_right, halt x, halt y, zero_add,
    add_zero] at h
  exact CharTwo.add_eq_zero.mp h

theorem eq_zero_of_finrank_range_eq_one [FiniteDimensional K V]
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {φ : V →ₗ[K] V}
    (halt : ∀ x, polar Qf x (φ x) = 0) (h1 : finrank K (LinearMap.range φ) = 1) : φ = 0 := by
  by_contra hφ
  obtain ⟨v, hv0, hv⟩ := exists_ne_zero_span_eq_of_finrank_eq_one h1
  obtain ⟨x₁, hx₁⟩ : ∃ x, φ x ≠ 0 := by
    by_contra! h
    exact hφ (LinearMap.ext h)
  have hmem : ∀ y, ∃ c : K, φ y = c • v := fun y => by
    have : φ y ∈ LinearMap.range φ := ⟨y, rfl⟩
    rw [hv] at this
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp this
    exact ⟨c, hc.symm⟩
  obtain ⟨c₁, hc₁⟩ := hmem x₁
  have hc₁0 : c₁ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc₁
    exact hx₁ hc₁
  have h2 : polar Qf x₁ v = 0 := by
    have h := halt x₁
    rw [hc₁, polar_smul_right, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_left hc₁0
  apply hv0
  apply hnd
  intro y
  obtain ⟨c, hc⟩ := hmem y
  have h3 := polar_apply_symm_of_alt halt x₁ y
  rw [hc, hc₁, polar_smul_right, polar_smul_right, h2, smul_eq_mul, smul_eq_mul, mul_zero] at h3
  rw [polar_comm]
  exact (mul_eq_zero.mp h3.symm).resolve_left hc₁0

theorem rootEnd_mem_altEnd {U : Submodule K V} (hU : ∀ w ∈ U, Qf w = 0) {a b : V} (ha : a ∈ U)
    (hb : b ∈ U) : rootEnd Qf a b ∈ altEnd Qf U := by
  refine ⟨fun x => ?_, fun x hx => ?_, fun x => polar_self_rootEnd Qf a b x⟩
  · rw [rootEnd_apply]
    exact U.add_mem (U.smul_mem _ ha) (U.smul_mem _ hb)
  · have hx' : ∀ w ∈ U, polar Qf w x = 0 := by
      intro w hw
      have hw' := LinearMap.BilinForm.mem_orthogonal_iff.1 hx w hw
      rwa [QuadraticMap.polarBilin_apply_apply] at hw'
    rw [rootEnd_apply, polar_comm Qf x b, polar_comm Qf x a, hx' b hb, hx' a ha, zero_smul,
      zero_smul, add_zero]

noncomputable def altCoord (Qf : QuadraticForm K V) (U : Submodule K V) (g : Fin 3 → V) :
    altEnd Qf U →ₗ[K] (Fin 3 → K) where
  toFun φ := ![polar Qf (φ.1 (g 0)) (g 1), polar Qf (φ.1 (g 0)) (g 2),
    polar Qf (φ.1 (g 1)) (g 2)]
  map_add' := by
    intro φ ψ
    ext i
    fin_cases i <;> simp [polar_add_left]
  map_smul' := by
    intro c φ
    ext i
    fin_cases i <;> simp [polar_smul_left]

theorem DualTriple.altCoord_injective {U : Submodule K V} {t g : Fin 3 → V}
    (h : DualTriple Qf U t g) : Function.Injective (altCoord Qf U g) := by
  rw [injective_iff_map_eq_zero]
  intro φ hφ
  obtain ⟨-, -, halt⟩ := φ.2
  have hc : ![polar Qf (φ.1 (g 0)) (g 1), polar Qf (φ.1 (g 0)) (g 2),
      polar Qf (φ.1 (g 1)) (g 2)] = 0 := hφ
  have c01 : polar Qf (φ.1 (g 0)) (g 1) = 0 := congrFun hc 0
  have c02 : polar Qf (φ.1 (g 0)) (g 2) = 0 := congrFun hc 1
  have c12 : polar Qf (φ.1 (g 1)) (g 2) = 0 := congrFun hc 2
  have hdiag : ∀ j, polar Qf (φ.1 (g j)) (g j) = 0 := fun j =>
    (polar_comm Qf _ _).trans (halt (g j))
  have hsymm : ∀ j k, polar Qf (φ.1 (g j)) (g k) = polar Qf (φ.1 (g k)) (g j) := by
    intro j k
    rw [polar_comm Qf (φ.1 (g j)), polar_comm Qf (φ.1 (g k))]
    exact (polar_apply_symm_of_alt halt (g j) (g k)).symm
  have h0 : ∀ j k, polar Qf (φ.1 (g j)) (g k) = 0 := by
    intro j k
    fin_cases j <;> fin_cases k
    · exact hdiag 0
    · exact c01
    · exact c02
    · exact (hsymm 0 1).symm.trans c01
    · exact hdiag 1
    · exact c12
    · exact (hsymm 0 2).symm.trans c02
    · exact (hsymm 1 2).symm.trans c12
    · exact hdiag 2
  exact Subtype.ext (h.eq_zero_of_coords φ.2 h0)

theorem DualTriple.altCoord_surjective {U : Submodule K V} {t g : Fin 3 → V}
    (hU : ∀ w ∈ U, Qf w = 0) (h : DualTriple Qf U t g) :
    Function.Surjective (altCoord Qf U g) := by
  have ht : ∀ i, t i ∈ U := by
    intro i
    rw [← h.span]
    exact Submodule.subset_span (Set.mem_range_self i)
  have hd : ∀ i j, polar Qf (g j) (t i) = if i = j then 1 else 0 := fun i j =>
    (polar_comm Qf _ _).trans (h.dual i j)
  obtain ⟨E01, hE01⟩ : ∃ E : altEnd Qf U, E.1 = rootEnd Qf (t 0) (t 1) :=
    ⟨⟨_, rootEnd_mem_altEnd hU (ht 0) (ht 1)⟩, rfl⟩
  obtain ⟨E02, hE02⟩ : ∃ E : altEnd Qf U, E.1 = rootEnd Qf (t 0) (t 2) :=
    ⟨⟨_, rootEnd_mem_altEnd hU (ht 0) (ht 2)⟩, rfl⟩
  obtain ⟨E12, hE12⟩ : ∃ E : altEnd Qf U, E.1 = rootEnd Qf (t 1) (t 2) :=
    ⟨⟨_, rootEnd_mem_altEnd hU (ht 1) (ht 2)⟩, rfl⟩
  have c01 : altCoord Qf U g E01 = ![1, 0, 0] := by
    ext i
    fin_cases i <;>
      simp [altCoord, hE01, rootEnd_apply, polar_add_left, polar_smul_left, hd, h.dual]
  have c02 : altCoord Qf U g E02 = ![0, 1, 0] := by
    ext i
    fin_cases i <;>
      simp [altCoord, hE02, rootEnd_apply, polar_add_left, polar_smul_left, hd, h.dual]
  have c12 : altCoord Qf U g E12 = ![0, 0, 1] := by
    ext i
    fin_cases i <;>
      simp [altCoord, hE12, rootEnd_apply, polar_add_left, polar_smul_left, hd, h.dual]
  intro c
  refine ⟨c 0 • E01 + c 1 • E02 + c 2 • E12, ?_⟩
  rw [map_add, map_add, map_smul, map_smul, map_smul, c01, c02, c12]
  ext i
  fin_cases i <;> simp

theorem DualTriple.natCard_altEnd [Finite K] {U : Submodule K V} {t g : Fin 3 → V}
    (hU : ∀ w ∈ U, Qf w = 0) (h : DualTriple Qf U t g) :
    Nat.card (altEnd Qf U) = Nat.card K ^ 3 := by
  have hbij : Function.Bijective (altCoord Qf U g) :=
    ⟨h.altCoord_injective, h.altCoord_surjective hU⟩
  rw [Nat.card_eq_of_bijective (altCoord Qf U g) hbij, Nat.card_fun, Nat.card_fin]

theorem DualTriple.finrank_range_eq_two [FiniteDimensional K V]
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {U : Submodule K V} {t g : Fin 3 → V}
    (h : DualTriple Qf U t g) (hU3 : finrank K U = 3) {φ : V →ₗ[K] V} (hφ : φ ∈ altEnd Qf U)
    (hφ0 : φ ≠ 0) : finrank K (LinearMap.range φ) = 2 := by
  have halt := hφ.2.2
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set v : Fin 3 → V := fun j => φ (g j) with hvdef
  have hv : ∀ j, v j ∈ U := fun j => hφ.1 _
  set m : Fin 3 → Fin 3 → K := fun j k => polar Qf (v j) (g k) with hm
  have hsym : ∀ j k, m j k = m k j := fun j k => by
    simp only [hm, hvdef]
    rw [polar_comm Qf (φ (g j)) (g k), polar_comm Qf (φ (g k)) (g j)]
    exact polar_apply_symm_of_alt halt (g k) (g j)
  have hdiag : ∀ j, m j j = 0 := fun j => by
    simp only [hm, hvdef]
    rw [polar_comm]
    exact halt (g j)
  have hl : ∀ l, m 1 2 * m 0 l + m 0 2 * m 1 l + m 0 1 * m 2 l = 0 := by
    intro l
    fin_cases l
    · simp only [Fin.zero_eta]
      rw [hdiag 0, hsym 1 0, hsym 2 0]
      linear_combination (m 0 1 * m 0 2) * h2
    · simp only [Fin.mk_one]
      rw [hdiag 1, hsym 2 1]
      linear_combination (m 0 1 * m 1 2) * h2
    · have e : (⟨2, by omega⟩ : Fin 3) = 2 := rfl
      rw [e, hdiag 2]
      linear_combination (m 1 2 * m 0 2) * h2
  have rel : m 1 2 • v 0 + m 0 2 • v 1 + m 0 1 • v 2 = 0 := by
    apply h.eq_zero_of_polar_eq_zero
    · exact U.add_mem (U.add_mem (U.smul_mem _ (hv 0)) (U.smul_mem _ (hv 1)))
        (U.smul_mem _ (hv 2))
    · intro l
      rw [polar_add_left, polar_add_left, polar_smul_left, polar_smul_left, polar_smul_left,
        smul_eq_mul, smul_eq_mul, smul_eq_mul]
      exact hl l
  have hne : ¬ (m 0 1 = 0 ∧ m 0 2 = 0 ∧ m 1 2 = 0) := by
    rintro ⟨h01, h02, h12⟩
    apply hφ0
    apply h.eq_zero_of_coords hφ
    have h10 : m 1 0 = 0 := by rw [hsym 1 0]; exact h01
    have h20 : m 2 0 = 0 := by rw [hsym 2 0]; exact h02
    have h21 : m 2 1 = 0 := by rw [hsym 2 1]; exact h12
    have h00 := hdiag 0
    have h11 := hdiag 1
    have h22 := hdiag 2
    intro j k
    fin_cases j <;> fin_cases k <;> assumption
  have hrange : LinearMap.range φ = Submodule.span K (Set.range v) := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [h.map_eq_sum hφ x]
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact ⟨g j, rfl⟩
  have hle3 : finrank K (LinearMap.range φ) ≤ 3 := by
    rw [← hU3]
    exact Submodule.finrank_mono (by rintro _ ⟨x, rfl⟩; exact hφ.1 x)
  have hne3 : finrank K (LinearMap.range φ) ≠ 3 := by
    intro h3
    have hli : LinearIndependent K v := by
      rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, ← hrange, h3,
        Fintype.card_fin]
    rw [Fintype.linearIndependent_iff] at hli
    have hz := hli ![m 1 2, m 0 2, m 0 1] (by rw [Fin.sum_univ_three]; simpa using rel)
    exact hne ⟨by simpa using hz 2, by simpa using hz 1, by simpa using hz 0⟩
  have h0 : finrank K (LinearMap.range φ) ≠ 0 := fun h0 =>
    hφ0 (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h0))
  have h1 : finrank K (LinearMap.range φ) ≠ 1 := fun h1 =>
    hφ0 (eq_zero_of_finrank_range_eq_one hnd halt h1)
  omega

theorem comp_eq_zero_of_mem_altEnd {U : Submodule K V} (hU : ∀ w ∈ U, Qf w = 0)
    {φ ψ : V →ₗ[K] V} (hφ : φ ∈ altEnd Qf U) (hψ : ψ ∈ altEnd Qf U) (x : V) : φ (ψ x) = 0 :=
  hφ.2.1 _ (le_orthogonal_of_totallySingular hU (hψ.1 x))

def altGroup (Qf : QuadraticForm K V) (U : Submodule K V) (hU : ∀ w ∈ U, Qf w = 0) :
    Subgroup (V ≃ₗ[K] V) where
  carrier := {s | ∃ φ ∈ altEnd Qf U, ∀ x, s x = x + φ x}
  one_mem' := ⟨0, zero_mem _, fun x => by simp⟩
  mul_mem' := by
    rintro s s' ⟨φ, hφ, hs⟩ ⟨φ', hφ', hs'⟩
    refine ⟨φ + φ', add_mem hφ hφ', fun x => ?_⟩
    rw [LinearEquiv.mul_apply, hs' x, hs (x + φ' x), map_add, comp_eq_zero_of_mem_altEnd hU hφ hφ',
      LinearMap.add_apply]
    abel
  inv_mem' := by
    rintro s ⟨φ, hφ, hs⟩
    have hss : s * s = 1 := by
      ext x
      have hx : φ x + φ x = 0 := by rw [← two_smul K (φ x), CharTwo.two_eq_zero, zero_smul]
      rw [LinearEquiv.mul_apply, hs x, hs (x + φ x), map_add, comp_eq_zero_of_mem_altEnd hU hφ hφ,
        LinearEquiv.coe_one, id_eq]
      calc x + φ x + (φ x + 0) = x + (φ x + φ x) := by abel
        _ = x := by rw [hx, add_zero]
    rw [inv_eq_of_mul_eq_one_right hss]
    exact ⟨φ, hφ, hs⟩

theorem sigmaGroup_le_altGroup (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    {U : Submodule K V} (hU : ∀ w ∈ U, Qf w = 0) : sigmaGroup Qf U ≤ altGroup Qf U hU := by
  rw [sigmaGroup, Subgroup.closure_le]
  rintro s ⟨hs, hsU⟩
  refine ⟨(s : V →ₗ[K] V) - 1, ⟨fun x => ?_, fun x hx => ?_, fun x => ?_⟩, fun x => ?_⟩
  · exact hsU (sub_mem_movedSpace s x)
  · have : x ∈ LinearMap.ker ((s : V →ₗ[K] V) - 1) := by
      rw [ker_sub_one_eq_orthogonal_movedSpace hnd hs.isometry]
      exact LinearMap.BilinForm.orthogonal_le hsU hx
    exact this
  · simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply]
    rw [polar_sub_right, hs.polar_apply_self x, polar_self_eq_zero, sub_zero]
  · simp

theorem altGroup_le_sigmaGroup [FiniteDimensional K V]
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {U : Submodule K V}
    (hU : ∀ w ∈ U, Qf w = 0) (hU3 : finrank K U = 3) : altGroup Qf U hU ≤ sigmaGroup Qf U := by
  rintro s ⟨φ, hφ, hs⟩
  by_cases hφ0 : φ = 0
  · have : s = 1 := LinearEquiv.ext fun x => by simp [hs, hφ0]
    rw [this]
    exact one_mem _
  obtain ⟨t, g, h⟩ := exists_dualTriple hnd hU3
  have hmoved : movedSpace s = LinearMap.range φ := by
    have : (s : V →ₗ[K] V) - 1 = φ := LinearMap.ext fun x => by simp [hs]
    rw [movedSpace, this]
  have hiso : ∀ v, Qf (s v) = Qf v := by
    intro v
    rw [hs, QuadraticMap.map_add Qf v (φ v), hU _ (hφ.1 v), hφ.2.2 v, add_zero, add_zero]
  have hsing : ∀ w ∈ movedSpace s, Qf w = 0 := by
    rw [hmoved]
    rintro _ ⟨x, rfl⟩
    exact hU _ (hφ.1 x)
  have hfin : finrank K (movedSpace s) = 2 := by
    rw [hmoved]
    exact h.finrank_range_eq_two hnd hU3 hφ hφ0
  refine Subgroup.subset_closure
    ⟨isLongRootElement_of_totallySingular_movedSpace hnd hiso hfin hsing, ?_⟩
  rw [hmoved]
  rintro _ ⟨x, rfl⟩
  exact hφ.1 x

theorem natCard_altGroup [Finite K] [FiniteDimensional K V]
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {U : Submodule K V}
    (hU : ∀ w ∈ U, Qf w = 0) (hU3 : finrank K U = 3) :
    Nat.card (altGroup Qf U hU) = Nat.card K ^ 3 := by
  obtain ⟨t, g, h⟩ := exists_dualTriple hnd hU3
  rw [← h.natCard_altEnd hU]
  have hmem : ∀ s : altGroup Qf U hU, ((s.1 : V →ₗ[K] V) - 1) ∈ altEnd Qf U := by
    rintro ⟨s, φ, hφ, hs⟩
    have : (s : V →ₗ[K] V) - 1 = φ := LinearMap.ext fun x => by simp [hs]
    simpa [this] using hφ
  let f : altGroup Qf U hU → altEnd Qf U := fun s => ⟨(s.1 : V →ₗ[K] V) - 1, hmem s⟩
  have hf : Function.Bijective f := by
    constructor
    · intro s s' hss'
      have h1 : (s.1 : V →ₗ[K] V) - 1 = (s'.1 : V →ₗ[K] V) - 1 := congrArg Subtype.val hss'
      refine Subtype.ext (LinearEquiv.ext fun x => ?_)
      have := LinearMap.congr_fun h1 x
      simpa using this
    · rintro ⟨φ, hφ⟩
      have hinv : Function.Involutive (LinearMap.id + φ : V →ₗ[K] V) := fun x => by
        have hx : φ x + φ x = 0 := by rw [← two_smul K (φ x), CharTwo.two_eq_zero, zero_smul]
        simp only [LinearMap.add_apply, LinearMap.id_apply, map_add,
          comp_eq_zero_of_mem_altEnd hU hφ hφ]
        calc x + φ x + (φ x + 0) = x + (φ x + φ x) := by abel
          _ = x := by rw [hx, add_zero]
      let s : V ≃ₗ[K] V := LinearEquiv.ofInvolutive (LinearMap.id + φ) hinv
      have hs : ∀ x, s x = x + φ x := fun x => rfl
      refine ⟨⟨s, φ, hφ, hs⟩, Subtype.ext (LinearMap.ext fun x => ?_)⟩
      change s x - x = φ x
      rw [hs, add_sub_cancel_left]
  exact Nat.card_eq_of_bijective f hf

theorem sigmaGroup_eq_altGroup [FiniteDimensional K V]
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {U : Submodule K V}
    (hU : ∀ w ∈ U, Qf w = 0) (hU3 : finrank K U = 3) :
    sigmaGroup Qf U = altGroup Qf U hU :=
  le_antisymm (sigmaGroup_le_altGroup hnd hU) (altGroup_le_sigmaGroup hnd hU hU3)

theorem natCard_sigmaGroup [Finite K] [FiniteDimensional K V]
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {U : Submodule K V}
    (hU : ∀ w ∈ U, Qf w = 0) (hU3 : finrank K U = 3) :
    Nat.card (sigmaGroup Qf U) = Nat.card K ^ 3 := by
  rw [sigmaGroup_eq_altGroup hnd hU hU3]
  exact natCard_altGroup hnd hU hU3

theorem mem_sigmaGroup_iff_of_ne_one [FiniteDimensional K V]
    (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0) {U : Submodule K V}
    (hU : ∀ w ∈ U, Qf w = 0) (hU3 : finrank K U = 3) {s : V ≃ₗ[K] V} (hs1 : s ≠ 1) :
    s ∈ sigmaGroup Qf U ↔ IsLongRootElement Qf s ∧ movedSpace s ≤ U := by
  refine ⟨fun hs => ?_, fun ⟨h1, h2⟩ => Subgroup.subset_closure ⟨h1, h2⟩⟩
  obtain ⟨φ, hφ, hsφ⟩ := sigmaGroup_le_altGroup hnd hU hs
  obtain ⟨t, g, h⟩ := exists_dualTriple hnd hU3
  have hφ0 : φ ≠ 0 := fun h0 => hs1 (LinearEquiv.ext fun x => by simp [hsφ, h0])
  have hmoved : movedSpace s = LinearMap.range φ := by
    have : (s : V →ₗ[K] V) - 1 = φ := LinearMap.ext fun x => by simp [hsφ]
    rw [movedSpace, this]
  have hiso : ∀ v, Qf (s v) = Qf v := by
    intro v
    rw [hsφ, QuadraticMap.map_add Qf v (φ v), hU _ (hφ.1 v), hφ.2.2 v, add_zero, add_zero]
  have hsing : ∀ w ∈ movedSpace s, Qf w = 0 := by
    rw [hmoved]
    rintro _ ⟨x, rfl⟩
    exact hU _ (hφ.1 x)
  have hfin : finrank K (movedSpace s) = 2 := by
    rw [hmoved]
    exact h.finrank_range_eq_two hnd hU3 hφ hφ0
  refine ⟨isLongRootElement_of_totallySingular_movedSpace hnd hiso hfin hsing, ?_⟩
  rw [hmoved]
  rintro _ ⟨x, rfl⟩
  exact hφ.1 x

theorem sigmaGroup_mul_comm (hnd : ∀ x : V, (∀ y, polar Qf x y = 0) → x = 0)
    {U : Submodule K V} (hU : ∀ w ∈ U, Qf w = 0) {s t : V ≃ₗ[K] V} (hs : s ∈ sigmaGroup Qf U)
    (ht : t ∈ sigmaGroup Qf U) : s * t = t * s := by
  obtain ⟨φ, hφ, hsφ⟩ := sigmaGroup_le_altGroup hnd hU hs
  obtain ⟨ψ, hψ, htψ⟩ := sigmaGroup_le_altGroup hnd hU ht
  refine LinearEquiv.ext fun x => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, htψ x, hsφ (x + ψ x), hsφ x, htψ (x + φ x),
    map_add, map_add, comp_eq_zero_of_mem_altEnd hU hφ hψ, comp_eq_zero_of_mem_altEnd hU hψ hφ]
  abel

theorem isLongRootElement_mem_sigmaGroup {U : Submodule K V} {s : V ≃ₗ[K] V}
    (hs : IsLongRootElement Qf s) (hU : movedSpace s ≤ U) : s ∈ sigmaGroup Qf U :=
  Subgroup.subset_closure ⟨hs, hU⟩

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
