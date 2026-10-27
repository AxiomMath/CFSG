module

public import CFSG.LocalAnalysis.ComponentInitial.LinearIsometry
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Transvection.Basic
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

public section

namespace CFSG.ClassicalGroups.Alternating

open Module Submodule
open LinearMap (BilinForm)
open CFSG.LocalAnalysis.ComponentInitial

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem alternating_pairing_surjectivity [FiniteDimensional K V] {B : BilinForm K V}
    (hB : B.Nondegenerate) {k : ℕ} {a : Fin k → V} (ha : LinearIndependent K a) :
    Function.Surjective (LinearMap.pi fun i => B (a i)) := by
  rw [← LinearMap.range_eq_top]
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  have hfy : ∀ y : Fin k → K, f y = ∑ i, y i * f (Pi.single i 1) := by
    intro y
    conv_lhs => rw [← Finset.univ_sum_single y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← smul_eq_mul, ← map_smul, ← Pi.single_smul, smul_eq_mul, mul_one]
  have hc : ∀ i, f (Pi.single i 1) = 0 := by
    refine Fintype.linearIndependent_iff.mp ha _ (hB.1 _ fun x => ?_)
    have hx := hf (LinearMap.mem_range_self (LinearMap.pi fun i => B (a i)) x)
    rw [LinearMap.mem_ker, hfy] at hx
    simp only [LinearMap.pi_apply] at hx
    rw [map_sum, LinearMap.sum_apply, ← hx]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, mul_comm]
  exact hf0 (LinearMap.ext fun y => by rw [hfy, LinearMap.zero_apply]; simp [hc])

@[expose] def symplecticTransvection (B : BilinForm K V) (hB : B.IsAlt) (a : V) (c : K) :
    LinearMap.GeneralLinearGroup K V :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv
    (LinearEquiv.transvection (f := c • B.flip a) (v := a)
      (show c • B a a = 0 by rw [hB.self_eq_zero, smul_zero]))

variable {B : BilinForm K V}

theorem symplecticTransvection_apply (hB : B.IsAlt) (a : V) (c : K) (x : V) :
    (symplecticTransvection B hB a c : V →ₗ[K] V) x = x + (c * B x a) • a :=
  rfl

private theorem gl_ext {g h : LinearMap.GeneralLinearGroup K V}
    (H : ∀ x, (g : V →ₗ[K] V) x = (h : V →ₗ[K] V) x) : g = h :=
  Units.ext (LinearMap.ext H)

theorem symplecticTransvection_mul (hB : B.IsAlt) (a : V) (c d : K) :
    symplecticTransvection B hB a c * symplecticTransvection B hB a d =
      symplecticTransvection B hB a (c + d) := by
  refine gl_ext fun x => ?_
  rw [Units.val_mul, Module.End.mul_apply, symplecticTransvection_apply,
    symplecticTransvection_apply, symplecticTransvection_apply, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, hB.self_eq_zero, smul_zero, add_zero]
  module

theorem symplecticTransvection_zero (hB : B.IsAlt) (a : V) :
    symplecticTransvection B hB a 0 = 1 :=
  gl_ext fun x => by rw [symplecticTransvection_apply, zero_mul, zero_smul, add_zero]; rfl

theorem symplecticTransvection_inv (hB : B.IsAlt) (a : V) (c : K) :
    (symplecticTransvection B hB a c)⁻¹ = symplecticTransvection B hB a (-c) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [symplecticTransvection_mul, add_neg_cancel, symplecticTransvection_zero]

theorem symplecticTransvection_mem_bilinIsometryGroup (hB : B.IsAlt) (a : V) (c : K) :
    symplecticTransvection B hB a c ∈ bilinIsometryGroup B := by
  intro x y
  rw [symplecticTransvection_apply, symplecticTransvection_apply]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hB.self_eq_zero]
  rw [← hB.neg_eq a y]
  ring

theorem alternating_transvection_identities (hB : B.IsAlt) (a : V) :
    (∀ (c : K) (x : V),
      (symplecticTransvection B hB a c : V →ₗ[K] V) x = x + (c * B x a) • a) ∧
    (∀ c : K, symplecticTransvection B hB a c ∈ bilinIsometryGroup B) ∧
    (∀ c d : K, symplecticTransvection B hB a c * symplecticTransvection B hB a d =
      symplecticTransvection B hB a (c + d)) ∧
    (∀ c : K, (symplecticTransvection B hB a c)⁻¹ = symplecticTransvection B hB a (-c)) ∧
    symplecticTransvection B hB a 0 = 1 :=
  ⟨symplecticTransvection_apply hB a, symplecticTransvection_mem_bilinIsometryGroup hB a,
    symplecticTransvection_mul hB a, symplecticTransvection_inv hB a,
    symplecticTransvection_zero hB a⟩

theorem symplecticTransvection_apply_of_apply_eq_zero (hB : B.IsAlt) {a x : V} (c : K)
    (hx : B x a = 0) : (symplecticTransvection B hB a c : V →ₗ[K] V) x = x := by
  rw [symplecticTransvection_apply, hx, mul_zero, zero_smul, add_zero]

theorem symplecticTransvection_sub_apply_self (hB : B.IsAlt) {x y : V} (hxy : B x y ≠ 0) :
    (symplecticTransvection B hB (y - x) (B x y)⁻¹ : V →ₗ[K] V) x = y := by
  rw [symplecticTransvection_apply, map_sub, hB.self_eq_zero, sub_zero, inv_mul_cancel₀ hxy,
    one_smul, add_sub_cancel]

theorem list_prod_map_symplecticTransvection_mem_closure (hB : B.IsAlt) (l : List (V × K)) :
    (l.map fun p => symplecticTransvection B hB p.1 p.2).prod ∈
      Subgroup.closure {g | ∃ (a : V) (c : K), g = symplecticTransvection B hB a c} := by
  refine Subgroup.list_prod_mem _ fun g hg => Subgroup.subset_closure ?_
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hg
  exact ⟨p.1, p.2, rfl⟩

theorem closure_symplecticTransvection_le_bilinIsometryGroup (hB : B.IsAlt) :
    Subgroup.closure {g | ∃ (a : V) (c : K), g = symplecticTransvection B hB a c} ≤
      bilinIsometryGroup B :=
  (Subgroup.closure_le _).mpr fun _ ⟨a, c, hg⟩ =>
    hg ▸ symplecticTransvection_mem_bilinIsometryGroup hB a c

theorem alternating_common_nonorthogonal_vector [FiniteDimensional K V] (_hB : B.IsAlt)
    (hBn : B.Nondegenerate) {u v : V} (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ w, B u w ≠ 0 ∧ B v w ≠ 0 := by
  have hex : ∀ x : V, x ≠ 0 → ∃ y, B x y ≠ 0 := fun x hx => by
    by_contra h
    push Not at h
    exact hx (hBn.1 x h)
  obtain ⟨y₁, hy₁⟩ := hex u hu
  obtain ⟨y₂, hy₂⟩ := hex v hv
  by_cases h₁ : B v y₁ = 0
  · by_cases h₂ : B u y₂ = 0
    · refine ⟨y₁ + y₂, ?_, ?_⟩
      · rwa [map_add, h₂, add_zero]
      · rwa [map_add, h₁, zero_add]
    · exact ⟨y₂, h₂, hy₂⟩
  · exact ⟨y₁, hy₁, h₁⟩

theorem alternating_fixed_vector_pair_adjustment (hB : B.IsAlt) {a x y : V} (hx : B a x = 1)
    (hy : B a y = 1) :
    ∃ l : List (V × K), l.length ≤ 2 ∧ (∀ p ∈ l, B a p.1 = 0) ∧
      ((l.map fun p => symplecticTransvection B hB p.1 p.2).prod : V →ₗ[K] V) a = a ∧
      ((l.map fun p => symplecticTransvection B hB p.1 p.2).prod : V →ₗ[K] V) x = y := by
  have hfix : ∀ l : List (V × K), (∀ p ∈ l, B a p.1 = 0) →
      ((l.map fun p => symplecticTransvection B hB p.1 p.2).prod : V →ₗ[K] V) a = a := by
    intro l hl
    induction l with
    | nil => rfl
    | cons p l ih =>
      rw [List.map_cons, List.prod_cons, Units.val_mul, Module.End.mul_apply,
        ih fun q hq => hl q (List.mem_cons_of_mem p hq)]
      exact symplecticTransvection_apply_of_apply_eq_zero hB _ (hl p List.mem_cons_self)
  by_cases hxy : B x y = 0
  ·
    set z := y + a with hz
    have hxz : B x z ≠ 0 := by
      rw [hz, map_add, hxy, zero_add, ← hB.neg_eq, hx]
      exact neg_ne_zero.mpr one_ne_zero
    have hzy : B z y ≠ 0 := by
      rw [hz, map_add, LinearMap.add_apply, hB.self_eq_zero, hy, zero_add]
      exact one_ne_zero
    have hl : ∀ p ∈ [(y - z, (B z y)⁻¹), (z - x, (B x z)⁻¹)], B a p.1 = 0 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        map_sub, hz, map_add, hB.self_eq_zero, hx, hy]
      constructor <;> simp
    refine ⟨[(y - z, (B z y)⁻¹), (z - x, (B x z)⁻¹)], by simp, hl, hfix _ hl, ?_⟩
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      Units.val_mul, Module.End.mul_apply]
    rw [symplecticTransvection_sub_apply_self hB hxz, symplecticTransvection_sub_apply_self hB hzy]
  ·
    have hl : ∀ p ∈ [(y - x, (B x y)⁻¹)], B a p.1 = 0 := by
      simp [hx, hy]
    refine ⟨[(y - x, (B x y)⁻¹)], by simp, hl, hfix _ hl, ?_⟩
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact symplecticTransvection_sub_apply_self hB hxy

theorem apply_smul_add_smul_of_apply_eq_one (hB : B.IsAlt) {a b : V} (hab : B a b = 1)
    (s t : K) : B a (s • a + t • b) = t ∧ B b (s • a + t • b) = -s := by
  have hba : B b a = -1 := by rw [← hB.neg_eq, hab]
  simp only [map_add, map_smul, smul_eq_mul, hB.self_eq_zero, hab, hba]
  constructor <;> ring

theorem linearIndependent_pair_of_apply_eq_one (hB : B.IsAlt) {a b : V} (hab : B a b = 1) :
    LinearIndependent K ![a, b] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  obtain ⟨h1, h2⟩ := apply_smul_add_smul_of_apply_eq_one hB hab s t
  rw [hst, map_zero] at h1 h2
  exact ⟨neg_eq_zero.mp h2.symm, h1.symm⟩

theorem alternating_hyperbolic_splitting [FiniteDimensional K V] (hB : B.IsAlt)
    (hBn : B.Nondegenerate) {a : V} (ha : a ≠ 0) :
    (∃ b, B a b = 1) ∧ ∀ b, B a b = 1 →
      finrank K (span K {a, b}) = 2 ∧ (B.restrict (span K {a, b})).Nondegenerate ∧
      (∀ x, x ∈ B.orthogonal (span K {a, b}) ↔ ∀ h ∈ span K {a, b}, B x h = 0) ∧
      IsCompl (span K {a, b}) (B.orthogonal (span K {a, b})) ∧
      (B.restrict (B.orthogonal (span K {a, b}))).Nondegenerate ∧
      finrank K (B.orthogonal (span K {a, b})) = finrank K V - 2 := by
  refine ⟨?_, fun b hab => ?_⟩
  · obtain ⟨y, hy⟩ : ∃ y, B a y ≠ 0 := by
      by_contra h
      push Not at h
      exact ha (hBn.1 a h)
    exact ⟨(B a y)⁻¹ • y, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hy]⟩
  have hdim : finrank K (span K {a, b}) = 2 := by
    rw [← Matrix.range_cons_cons_empty a b ![], finrank_span_eq_card
      (linearIndependent_pair_of_apply_eq_one hB hab), Fintype.card_fin]
  have hdisj : Disjoint (span K {a, b}) (B.orthogonal (span K {a, b})) := by
    rw [Submodule.disjoint_def]
    intro x hx hxo
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hx
    obtain ⟨h1, h2⟩ := (LinearMap.BilinForm.mem_orthogonal_span_pair_iff B).mp hxo
    obtain ⟨h1', h2'⟩ := apply_smul_add_smul_of_apply_eq_one hB hab s t
    rw [h1'] at h1
    rw [h2', neg_eq_zero] at h2
    rw [h1, h2, zero_smul, zero_smul, add_zero]
  have hnd : (B.restrict (span K {a, b})).Nondegenerate :=
    B.nondegenerate_restrict_of_disjoint_orthogonal hB.isRefl hdisj
  have hpair : span K {a, b} = span K {b, a} := by rw [Set.pair_comm]
  refine ⟨hdim, hnd, fun x => ?_, ?_, ?_, ?_⟩
  · rw [LinearMap.BilinForm.mem_orthogonal_iff]
    exact forall₂_congr fun h _ => hB.eq_iff
  · exact LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hB.isRefl hnd
  · rw [hpair]
    exact hB.restrict_nondegenerate_orthogonal_span_pair hab hBn
  · rw [LinearMap.BilinForm.finrank_orthogonal hBn, hdim]

theorem alternating_transvection_vector_transitivity [FiniteDimensional K V] (hB : B.IsAlt)
    (hBn : B.Nondegenerate) :
    (∀ u v : V, u ≠ 0 → v ≠ 0 → ∃ l : List (V × K), l.length ≤ 2 ∧
      ((l.map fun p => symplecticTransvection B hB p.1 p.2).prod : V →ₗ[K] V) u = v) ∧
    ∀ u v : V, u ≠ 0 → v ≠ 0 →
      ∃ g ∈ Subgroup.closure {g | ∃ (a : V) (c : K), g = symplecticTransvection B hB a c},
        (g : V →ₗ[K] V) u = v := by
  have h1 : ∀ u v : V, u ≠ 0 → v ≠ 0 → ∃ l : List (V × K), l.length ≤ 2 ∧
      ((l.map fun p => symplecticTransvection B hB p.1 p.2).prod : V →ₗ[K] V) u = v := by
    intro u v hu hv
    by_cases huv : B u v = 0
    ·
      obtain ⟨w, huw, hvw⟩ := alternating_common_nonorthogonal_vector hB hBn hu hv
      have hwv : B w v ≠ 0 := by
        rw [← hB.neg_eq]
        exact neg_ne_zero.mpr hvw
      refine ⟨[(v - w, (B w v)⁻¹), (w - u, (B u w)⁻¹)], by simp, ?_⟩
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        Units.val_mul, Module.End.mul_apply]
      rw [symplecticTransvection_sub_apply_self hB huw,
        symplecticTransvection_sub_apply_self hB hwv]
    ·
      refine ⟨[(v - u, (B u v)⁻¹)], by simp, ?_⟩
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      exact symplecticTransvection_sub_apply_self hB huv
  refine ⟨h1, fun u v hu hv => ?_⟩
  obtain ⟨l, -, hl⟩ := h1 u v hu hv
  exact ⟨_, list_prod_map_symplecticTransvection_mem_closure hB l, hl⟩

end CFSG.ClassicalGroups.Alternating
