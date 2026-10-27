module

public import Mathlib.GroupTheory.Focal
import CFSG.FeitThompson.Foundations.AbelianSylowFusionNormalizer
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow

open Pointwise Subgroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {G : Type*} [Group G] {p : ℕ}

theorem setOf_focal_gen_eq (P : Subgroup G) :
    {z : G | ∃ x ∈ P, ∃ y ∈ P, (∃ g : G, y = g⁻¹ * x * g) ∧ z = x⁻¹ * y}
      = {z : G | z ∈ P ∧ ∃ x ∈ P, ∃ u : G, z = x * u * x⁻¹ * u⁻¹} := by
  ext z
  constructor
  · rintro ⟨x, hx, y, hy, ⟨g, rfl⟩, rfl⟩
    exact ⟨P.mul_mem (P.inv_mem hx) hy, x⁻¹, P.inv_mem hx, g⁻¹, by group⟩
  · rintro ⟨hz, x, hx, u, rfl⟩
    refine ⟨x⁻¹, P.inv_mem hx, u * x⁻¹ * u⁻¹, ?_, ⟨u⁻¹, by group⟩, by group⟩
    have h : u * x⁻¹ * u⁻¹ = x⁻¹ * (x * u * x⁻¹ * u⁻¹) := by group
    rw [h]
    exact P.mul_mem (P.inv_mem hx) hz

theorem closure_focal_gen_eq_focalSubgroup (P : Subgroup G) :
    closure {z : G | ∃ x ∈ P, ∃ y ∈ P, (∃ g : G, y = g⁻¹ * x * g) ∧ z = x⁻¹ * y}
      = P.focalSubgroup := by
  rw [focalSubgroup_def, setOf_focal_gen_eq]
  simp only [commutatorElement_def]

theorem normalizer_comm_iff_normalizer_le_centralizer (P : Subgroup G) :
    (∀ n ∈ normalizer (P : Set G), ∀ x ∈ P, n * x = x * n) ↔
      normalizer (P : Set G) ≤ centralizer (P : Set G) :=
  ⟨fun h _ hn => mem_centralizer_iff.mpr fun x hx => (h _ hn x hx).symm,
   fun h _ hn x hx => (mem_centralizer_iff.mp (h hn) x hx).symm⟩

theorem isMulCommutative_of_normalizer_comm {P : Subgroup G}
    (hcomm : ∀ n ∈ normalizer (P : Set G), ∀ x ∈ P, n * x = x * n) : IsMulCommutative P :=
  isMulCommutative_iff.mpr fun a b =>
    Subtype.ext (by simpa using hcomm a (le_normalizer a.2) b b.2)

variable [Finite G] [Fact p.Prime]

theorem conj_inv_eq_self_of_normalizer_comm {P : Subgroup G}
    (hP : Nat.card P = p ^ (Nat.card G).factorization p)
    (hcomm : ∀ n ∈ normalizer (P : Set G), ∀ x ∈ P, n * x = x * n)
    {x g : G} (hx : x ∈ P) (hxg : g⁻¹ * x * g ∈ P) : g⁻¹ * x * g = x := by
  have : IsMulCommutative P := isMulCommutative_of_normalizer_comm hcomm
  obtain ⟨n, hn, hn2⟩ := exists_mem_normalizer_conj_inv_eq hP hx hxg rfl
  have h := hcomm n hn x hx
  rw [← hn2]
  calc n⁻¹ * x * n = n⁻¹ * (x * n) := by group
    _ = n⁻¹ * (n * x) := by rw [← h]
    _ = x := by group

theorem focalSubgroup_eq_bot_of_normalizer_comm {P : Subgroup G}
    (hP : Nat.card P = p ^ (Nat.card G).factorization p)
    (hcomm : ∀ n ∈ normalizer (P : Set G), ∀ x ∈ P, n * x = x * n) :
    P.focalSubgroup = ⊥ := by
  rw [← closure_focal_gen_eq_focalSubgroup, closure_eq_bot_iff]
  rintro z ⟨x, hx, y, hy, ⟨g, rfl⟩, rfl⟩
  rw [conj_inv_eq_self_of_normalizer_comm hP hcomm hx hy]
  simp

theorem closure_focal_gen_eq_bot_of_conj_comm {P : Subgroup G}
    (hP : Nat.card P = p ^ (Nat.card G).factorization p)
    (hcomm : ∀ n : G, MulAut.conj n⁻¹ • P = P → ∀ x ∈ P, n * x = x * n) :
    closure {z : G | ∃ x ∈ P, ∃ y ∈ P, (∃ g : G, y = g⁻¹ * x * g) ∧ z = x⁻¹ * y} = ⊥ := by
  rw [closure_focal_gen_eq_focalSubgroup]
  exact focalSubgroup_eq_bot_of_normalizer_comm hP fun n hn =>
    hcomm n (mem_normalizer_iff_conj_inv_smul_eq.mp hn)

theorem focalSubgroup_sylow_eq_bot_of_normalizer_comm (P : Sylow p G)
    (hcomm : ∀ n ∈ normalizer ((P : Subgroup G) : Set G), ∀ x ∈ (P : Subgroup G), n * x = x * n) :
    (P : Subgroup G).focalSubgroup = ⊥ :=
  focalSubgroup_eq_bot_of_normalizer_comm P.card_eq_multiplicity hcomm

theorem focalSubgroupOf_eq_bot_of_normalizer_comm {P : Subgroup G}
    (hP : Nat.card P = p ^ (Nat.card G).factorization p)
    (hcomm : ∀ n ∈ normalizer (P : Set G), ∀ x ∈ P, n * x = x * n) :
    P.focalSubgroupOf = ⊥ := by
  rw [focalSubgroupOf_def, focalSubgroup_eq_bot_of_normalizer_comm hP hcomm]
  simp [subgroupOf]

theorem commutator_inf_eq_bot_of_normalizer_comm (P : Sylow p G)
    (hcomm : ∀ n ∈ normalizer ((P : Subgroup G) : Set G), ∀ x ∈ (P : Subgroup G), n * x = x * n) :
    _root_.commutator G ⊓ (P : Subgroup G) = ⊥ := by
  rw [commutator_inf_eq_focalSubgroup, focalSubgroup_sylow_eq_bot_of_normalizer_comm P hcomm]

end

end CFSG.FeitThompson
