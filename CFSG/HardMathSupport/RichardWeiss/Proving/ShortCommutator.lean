module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

open scoped commutatorElement

attribute [local instance] IsMulCommutative.instCommGroup

variable {G : Type*} [Group G]

theorem commutator_le_commutator_of_perfect {Q L V : Subgroup G} [IsMulCommutative V]
    (hperf : ⁅L, L⁆ = L) (hQL : ⁅Q, L⁆ ≤ V) : ⁅Q, L⁆ ≤ ⁅V, L⁆ := by
  rw [Subgroup.commutator_le]
  intro q hq l hl
  let U' : Subgroup V := ⁅V, L⁆.subgroupOf V
  let c : L → V := fun l => ⟨⁅q, (l : G)⁆, hQL (Subgroup.commutator_mem_commutator hq l.2)⟩
  have hmem : ∀ a b : L, ((c (a * b))⁻¹ * (c a * c b)) ∈ U' := by
    intro a b
    rw [Subgroup.mem_subgroupOf]
    have hbV : ⁅q, (b : G)⁆ ∈ V := (c b).2
    have e : (((c (a * b))⁻¹ * (c a * c b) : V) : G) = ⁅(a : G), ⁅q, (b : G)⁆⁻¹⁆ := by
      simp only [c, Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [e]
    have := Subgroup.commutator_mem_commutator a.2 (V.inv_mem hbV)
    rwa [Subgroup.commutator_comm] at this
  let φ : L →* (V ⧸ U') :=
    { toFun := fun l => QuotientGroup.mk (c l)
      map_one' := by
        apply (QuotientGroup.eq_one_iff _).2
        have : c 1 = 1 := Subtype.ext (by simp [c])
        rw [this]; exact U'.one_mem
      map_mul' := by
        intro a b
        rw [← QuotientGroup.mk_mul]
        exact QuotientGroup.eq.2 (hmem a b) }
  have hker : ⁅L, L⁆ ≤ φ.ker.map L.subtype := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    refine Subgroup.mem_map.2 ⟨⁅(⟨x, hx⟩ : L), (⟨y, hy⟩ : L)⁆, ?_, rfl⟩
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
  rw [hperf] at hker
  obtain ⟨k, hk, hkl⟩ := Subgroup.mem_map.1 (hker hl)
  have hk' : k = ⟨l, hl⟩ := Subtype.ext hkl
  rw [hk'] at hk
  have h1 : φ ⟨l, hl⟩ = 1 := hk
  have h2 : c ⟨l, hl⟩ ∈ U' := (QuotientGroup.eq_one_iff _).1 h1
  exact (Subgroup.mem_subgroupOf.1 h2)

end CFSG.HardMathSupport.RichardWeiss.Proving
