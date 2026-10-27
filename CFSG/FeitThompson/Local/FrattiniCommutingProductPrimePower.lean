module

public import CFSG.FeitThompson.Local.FrattiniQuotientPPowerElementaryAbelian
import CFSG.FeitThompson.Foundations.ProductSubgroupsCardinality
import CFSG.FeitThompson.Local.SolvableDerivedKernelCommutators
import CFSG.FeitThompson.OddOrder.CommutingSubgroupsJoinProduct

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G] {p a b : ℕ} {U V : Subgroup G}

def commutatorSupPowClosureIn (p : ℕ) (H : Subgroup G) : Subgroup G :=
  ⁅H, H⁆ ⊔ Subgroup.closure ((· ^ p) '' (H : Set G))

theorem commutator_mem_commutatorSupPowClosureIn {H : Subgroup G} {x y : G} (hx : x ∈ H)
    (hy : y ∈ H) : ⁅x, y⁆ ∈ commutatorSupPowClosureIn p H :=
  Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hx hy)

theorem pow_mem_commutatorSupPowClosureIn {H : Subgroup G} {x : G} (hx : x ∈ H) :
    x ^ p ∈ commutatorSupPowClosureIn p H :=
  Subgroup.mem_sup_right (Subgroup.subset_closure ⟨x, hx, rfl⟩)

theorem commutatorSupPowClosureIn_le {H K : Subgroup G} :
    commutatorSupPowClosureIn p H ≤ K ↔
      (∀ x ∈ H, ∀ y ∈ H, ⁅x, y⁆ ∈ K) ∧ ∀ x ∈ H, x ^ p ∈ K := by
  rw [commutatorSupPowClosureIn, sup_le_iff, Subgroup.commutator_le, Subgroup.closure_le]
  refine and_congr_right fun _ => ?_
  exact ⟨fun h x hx => h ⟨x, hx, rfl⟩, fun h y hy => by
    obtain ⟨x, hx, rfl⟩ := hy; exact h x hx⟩

theorem commutatorSupPowClosureIn_mono {H K : Subgroup G} (h : H ≤ K) :
    commutatorSupPowClosureIn p H ≤ commutatorSupPowClosureIn p K :=
  commutatorSupPowClosureIn_le.2
    ⟨fun _ hx _ hy => commutator_mem_commutatorSupPowClosureIn (h hx) (h hy),
      fun _ hx => pow_mem_commutatorSupPowClosureIn (h hx)⟩

theorem commutatorSupPowClosureIn_le_self (p : ℕ) (H : Subgroup G) :
    commutatorSupPowClosureIn p H ≤ H :=
  commutatorSupPowClosureIn_le.2
    ⟨fun _ hx _ hy => H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy),
      fun _ hx => H.pow_mem hx _⟩

theorem map_subtype_commutatorSupPowClosure (p : ℕ) (H : Subgroup G) :
    (commutatorSupPowClosure p H).map H.subtype = commutatorSupPowClosureIn p H := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap, commutatorSupPowClosure_le]
    refine ⟨?_, fun x => ?_⟩
    · rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_subtype_commutator]
      exact le_sup_left
    · exact pow_mem_commutatorSupPowClosureIn (p := p) x.2
  · refine commutatorSupPowClosureIn_le.2 ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · exact ⟨⁅(⟨x, hx⟩ : H), (⟨y, hy⟩ : H)⁆,
        commutator_le_commutatorSupPowClosure
          (Subgroup.commutator_mem_commutator (mem_top _) (mem_top _)), rfl⟩
    · exact ⟨(⟨x, hx⟩ : H) ^ p, pow_mem_commutatorSupPowClosure _, rfl⟩

theorem exists_mul_eq_of_mem_sup_of_commute (hcomm : ∀ x ∈ U, ∀ y ∈ V, Commute x y) {g : G}
    (hg : g ∈ U ⊔ V) : ∃ u ∈ U, ∃ v ∈ V, u * v = g := by
  have hg' : g ∈ ((U ⊔ V : Subgroup G) : Set G) := hg
  rw [coe_sup_eq_mul_of_commute hcomm] at hg'
  obtain ⟨u, hu, v, hv, huv⟩ := Set.mem_mul.1 hg'
  exact ⟨u, hu, v, hv, huv⟩

theorem commutatorSupPowClosureIn_sup_of_commute (hcomm : ∀ x ∈ U, ∀ y ∈ V, Commute x y) :
    commutatorSupPowClosureIn p (U ⊔ V)
      = commutatorSupPowClosureIn p U ⊔ commutatorSupPowClosureIn p V := by
  refine le_antisymm (commutatorSupPowClosureIn_le.2 ⟨fun x hx y hy => ?_, fun x hx => ?_⟩)
    (sup_le (commutatorSupPowClosureIn_mono le_sup_left)
      (commutatorSupPowClosureIn_mono le_sup_right))
  · obtain ⟨u₁, hu₁, v₁, hv₁, rfl⟩ := exists_mul_eq_of_mem_sup_of_commute hcomm hx
    obtain ⟨u₂, hu₂, v₂, hv₂, rfl⟩ := exists_mul_eq_of_mem_sup_of_commute hcomm hy
    rw [commutatorElement_mul_mul_of_forall_commute hcomm hu₁ hu₂ hv₁ hv₂]
    exact mul_mem (Subgroup.mem_sup_left (commutator_mem_commutatorSupPowClosureIn hu₁ hu₂))
      (Subgroup.mem_sup_right (commutator_mem_commutatorSupPowClosureIn hv₁ hv₂))
  · obtain ⟨u, hu, v, hv, rfl⟩ := exists_mul_eq_of_mem_sup_of_commute hcomm hx
    rw [(hcomm u hu v hv).mul_pow]
    exact mul_mem (Subgroup.mem_sup_left (pow_mem_commutatorSupPowClosureIn hu))
      (Subgroup.mem_sup_right (pow_mem_commutatorSupPowClosureIn hv))

theorem natCard_sup_mul_natCard_inf_of_commute (hcomm : ∀ x ∈ U, ∀ y ∈ V, Commute x y) :
    Nat.card (U ⊔ V : Subgroup G) * Nat.card (U ⊓ V : Subgroup G) = Nat.card U * Nat.card V := by
  have h : Nat.card (U ⊔ V : Subgroup G) = Nat.card ((U : Set G) * (V : Set G)) := by
    rw [← coe_sup_eq_mul_of_commute hcomm]; rfl
  rw [h, natCard_mul_mul_natCard_inf U V]

theorem exists_natCard_sup_eq_pow (hp : p.Prime) (hU : Nat.card U = p ^ a)
    (hV : Nat.card V = p ^ b) (hcomm : ∀ x ∈ U, ∀ y ∈ V, Commute x y) :
    ∃ c ≤ a + b, Nat.card (U ⊔ V : Subgroup G) = p ^ c := by
  have hdvd : Nat.card (U ⊔ V : Subgroup G) ∣ p ^ (a + b) :=
    ⟨Nat.card (U ⊓ V : Subgroup G), by
      rw [natCard_sup_mul_natCard_inf_of_commute hcomm, hU, hV, pow_add]⟩
  obtain ⟨c, hc, hcard⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  exact ⟨c, hc, hcard⟩

theorem isPGroup_sup_of_commute (hp : p.Prime) (hU : Nat.card U = p ^ a)
    (hV : Nat.card V = p ^ b) (hcomm : ∀ x ∈ U, ∀ y ∈ V, Commute x y) :
    IsPGroup p (U ⊔ V : Subgroup G) := by
  obtain ⟨c, -, hc⟩ := exists_natCard_sup_eq_pow hp hU hV hcomm
  exact IsPGroup.of_card hc

theorem map_subtype_frattini (hp : p.Prime) {H : Subgroup G} {n : ℕ} (hH : Nat.card H = p ^ n) :
    (frattini H).map H.subtype = commutatorSupPowClosureIn p H := by
  rw [frattini_eq_commutatorSupPowClosure hp hH, map_subtype_commutatorSupPowClosure]

theorem map_subtype_frattini_sup (hp : p.Prime) (hU : Nat.card U = p ^ a)
    (hV : Nat.card V = p ^ b) (hcomm : ∀ x ∈ U, ∀ y ∈ V, Commute x y) :
    (frattini (U ⊔ V : Subgroup G)).map (U ⊔ V).subtype
      = (frattini U).map U.subtype ⊔ (frattini V).map V.subtype := by
  obtain ⟨c, -, hW⟩ := exists_natCard_sup_eq_pow hp hU hV hcomm
  rw [map_subtype_frattini hp hW, map_subtype_frattini hp hU, map_subtype_frattini hp hV,
    commutatorSupPowClosureIn_sup_of_commute hcomm]

theorem coe_map_subtype_frattini_sup (hp : p.Prime) (hU : Nat.card U = p ^ a)
    (hV : Nat.card V = p ^ b) (hcomm : ∀ x ∈ U, ∀ y ∈ V, Commute x y) :
    (((frattini (U ⊔ V : Subgroup G)).map (U ⊔ V).subtype : Subgroup G) : Set G)
      = (((frattini U).map U.subtype : Subgroup G) : Set G)
        * (((frattini V).map V.subtype : Subgroup G) : Set G) := by
  rw [map_subtype_frattini_sup hp hU hV hcomm]
  refine coe_sup_eq_mul_of_commute fun x hx y hy =>
    hcomm x (Subgroup.map_subtype_le _ hx) y (Subgroup.map_subtype_le _ hy)

end

end CFSG.FeitThompson
