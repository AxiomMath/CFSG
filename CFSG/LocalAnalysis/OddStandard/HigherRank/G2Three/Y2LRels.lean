module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Ext26

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec2

open Subgroup
open scoped commutatorElement

structure Y2LRels {G : Type} [Group G] (n : ℕ) (e : Bool) (u v w r s : G) : Prop where
  cuv : Commute u v
  cuw : Commute u w
  cvw : Commute v w
  pu : u ^ 2 ^ n = 1
  pv : v ^ 2 ^ n = 1
  pw : w ^ 2 ^ n = 1
  r2 : r ^ 2 = 1
  crs : r⁻¹ * s * r = s⁻¹
  cru : r⁻¹ * u * r = w⁻¹
  crv : r⁻¹ * v * r = v⁻¹
  crw : r⁻¹ * w * r = u⁻¹
  csu : s⁻¹ * u * s = v
  csv : s⁻¹ * v * s = w
  csw : s⁻¹ * w * s = u * v⁻¹ * w
  s4 : s ^ 4 = if e then u * w else 1

theorem y2l_rels_iff {G : Type} [Group G] {n : ℕ} {e : Bool} {u v w r s : G} :
    (∀ x ∈ rels26 n e, FreeGroup.lift (![u, v, w, r, s] : Fin 5 → G) x = 1) ↔
      Y2LRels n e u v w r s := by
  have h0 : FreeGroup.lift (![u, v, w, r, s] : Fin 5 → G) (FreeGroup.of 0) = u :=
    FreeGroup.lift_apply_of
  have h1 : FreeGroup.lift (![u, v, w, r, s] : Fin 5 → G) (FreeGroup.of 1) = v :=
    FreeGroup.lift_apply_of
  have h2 : FreeGroup.lift (![u, v, w, r, s] : Fin 5 → G) (FreeGroup.of 2) = w :=
    FreeGroup.lift_apply_of
  have h3 : FreeGroup.lift (![u, v, w, r, s] : Fin 5 → G) (FreeGroup.of 3) = r :=
    FreeGroup.lift_apply_of
  have h4 : FreeGroup.lift (![u, v, w, r, s] : Fin 5 → G) (FreeGroup.of 4) = s :=
    FreeGroup.lift_apply_of
  cases e <;>
  simp only [rels26, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, map_mul, map_inv, map_pow, map_commutatorElement, map_one, h0,
    h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte, mul_one, commutatorElement_eq_one_iff_commute,
    mul_inv_eq_one, mul_eq_one_iff_eq_inv, inv_inv] <;>
  exact ⟨fun ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ =>
      ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, by simpa using a15⟩,
    fun h => ⟨h.cuv, h.cuw, h.cvw, h.pu, h.pv, h.pw, h.r2, h.crs, h.cru, h.crv, h.crw, h.csu,
      h.csv, h.csw, by simpa using h.s4⟩⟩

end CFSG.OddStandard.HigherRank.G2Three.Sec2
