module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.GroupTheory.Subgroup.Simple

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {H : Type*} [Group H]

theorem sec128_comm_eq_map (K : Subgroup H) :
    ⁅K, K⁆ = (_root_.commutator ↥K).map K.subtype := by
  rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]

theorem sec128_comm_eq_of_perfect (K : Subgroup H) (hK : _root_.commutator ↥K = ⊤) :
    ⁅K, K⁆ = K := by
  rw [sec128_comm_eq_map, hK, Subgroup.map_top, Subgroup.range_subtype]

theorem sec128_perfect_of_comm_eq (K : Subgroup H) (hK : ⁅K, K⁆ = K) :
    _root_.commutator ↥K = ⊤ := by
  apply Subgroup.map_injective K.subtype_injective
  rw [← sec128_comm_eq_map, hK, Subgroup.map_top, Subgroup.range_subtype]

theorem sec128_commutator_top_of_mulEquiv {K L : Type*} [Group K] [Group L] (e : K ≃* L)
    (h : _root_.commutator L = ⊤) : _root_.commutator K = ⊤ := by
  have hrange : e.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr e.surjective
  have h1 : (_root_.commutator K).map e.toMonoidHom = _root_.commutator L := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      hrange]
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [h1, h, Subgroup.map_top, hrange]

theorem sec128_normalClosure_perfect (X : Subgroup H) (hX : ⁅X, X⁆ = X) :
    ⁅normalClosure (X : Set H), normalClosure (X : Set H)⁆ = normalClosure (X : Set H) := by
  have hXN : X ≤ normalClosure (X : Set H) := Subgroup.le_normalClosure
  refine le_antisymm (Subgroup.commutator_le_left _ _) ?_
  haveI : ⁅normalClosure (X : Set H), normalClosure (X : Set H)⁆.Normal :=
    Subgroup.commutator_normal _ _
  refine Subgroup.normalClosure_le_normal fun x hx => ?_
  have hx' : x ∈ ⁅X, X⁆ := by rw [hX]; exact hx
  exact Subgroup.commutator_mono hXN hXN hx'

theorem sec128_perfect_le_ker {A : Type*} [Group A] (hA : ∀ a b : A, a * b = b * a)
    (P : Subgroup H) (hP : ⁅P, P⁆ = P) (φ : H →* A) : P ≤ φ.ker := by
  have h : ⁅P, P⁆ ≤ φ.ker := by
    rw [Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hA _ _
  rwa [hP] at h

theorem sec128_perfect_le_index_two (E : Subgroup H) [E.Normal] (hE : E.index = 2)
    (P : Subgroup H) (hP : ⁅P, P⁆ = P) : P ≤ E := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (H ⧸ E) = 2 := hE
  haveI : IsCyclic (H ⧸ E) := isCyclic_of_prime_card hcard
  have hcomm : ∀ a b : H ⧸ E, a * b = b * a :=
    fun a b => (inferInstance : IsMulCommutative (H ⧸ E)).is_comm.comm a b
  have := sec128_perfect_le_ker hcomm P hP (QuotientGroup.mk' E)
  rwa [QuotientGroup.ker_mk'] at this

theorem sec128_eq_of_simple (E : Subgroup H) [IsSimpleGroup ↥E] (P : Subgroup H) [hPn : P.Normal]
    (hPE : P ≤ E) (hP1 : P ≠ ⊥) : P = E := by
  haveI : (P.subgroupOf E).Normal := hPn.subgroupOf E
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P.subgroupOf E) with h | h
  · exfalso
    apply hP1
    refine (Subgroup.eq_bot_iff_forall P).mpr fun x hx => ?_
    have hx' : (⟨x, hPE hx⟩ : ↥E) ∈ P.subgroupOf E := hx
    rw [h, Subgroup.mem_bot] at hx'
    exact congrArg Subtype.val hx'
  · refine le_antisymm hPE fun x hx => ?_
    have hx' : (⟨x, hx⟩ : ↥E) ∈ P.subgroupOf E := by rw [h]; exact Subgroup.mem_top _
    exact hx'

end CFSG.OddStandard.SmallF3.Omega
