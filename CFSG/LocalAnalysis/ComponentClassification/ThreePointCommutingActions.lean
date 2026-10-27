module

public import CFSG.Assembly.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

open scoped Pointwise

namespace CFSG.ComponentClassification.ThreePointCommutingActions

theorem unique_fixed (swap : Equiv.Perm (Fin 3))
    (hswap : swap = Equiv.swap 0 1 ∨ swap = Equiv.swap 0 2 ∨ swap = Equiv.swap 1 2) :
    ∃ fixed : Fin 3, ∀ point : Fin 3, swap point = point ↔ point = fixed := by
  have hfinite : ∀ swap : Equiv.Perm (Fin 3),
      (swap = Equiv.swap 0 1 ∨ swap = Equiv.swap 0 2 ∨ swap = Equiv.swap 1 2) →
      ∃ fixed : Fin 3, ∀ point : Fin 3, swap point = point ↔ point = fixed := by decide
  exact hfinite swap hswap

theorem moved_pair (swap : Equiv.Perm (Fin 3))
    (hswap : swap = Equiv.swap 0 1 ∨ swap = Equiv.swap 0 2 ∨ swap = Equiv.swap 1 2)
    (fixed : Fin 3) (hfixed : ∀ point : Fin 3, swap point = point ↔ point = fixed) :
    ∃ first second : Fin 3, first ≠ fixed ∧ second ≠ fixed ∧ first ≠ second ∧
      swap first = second ∧ swap second = first ∧ ∀ point : Fin 3, point = fixed ∨ point = first ∨ point = second := by
  have hfinite : ∀ swap : Equiv.Perm (Fin 3),
      (swap = Equiv.swap 0 1 ∨ swap = Equiv.swap 0 2 ∨ swap = Equiv.swap 1 2) →
      ∀ fixed : Fin 3, (∀ point : Fin 3, swap point = point ↔ point = fixed) →
        ∃ first second : Fin 3, first ≠ fixed ∧ second ≠ fixed ∧ first ≠ second ∧
          swap first = second ∧ swap second = first ∧
            ∀ point : Fin 3, point = fixed ∨ point = first ∨ point = second := by decide
  exact hfinite swap hswap fixed hfixed

theorem swaps_complement (swap : Equiv.Perm (Fin 3))
    (hswap : swap = Equiv.swap 0 1 ∨ swap = Equiv.swap 0 2 ∨ swap = Equiv.swap 1 2)
    (fixed first second : Fin 3) (hfixed : ∀ point : Fin 3, swap point = point ↔ point = fixed)
    (hfirst : first ≠ fixed) (hsecond : second ≠ fixed) (hdistinct : first ≠ second) :
    swap first = second ∧ swap second = first := by
  have hfixedSelf := (hfixed fixed).mpr rfl
  rcases hswap with rfl | rfl | rfl <;>
    fin_cases fixed <;> fin_cases first <;> fin_cases second <;> simp_all

theorem involution_swap (permutation : Equiv.Perm (Fin 3))
    (hsquare : permutation ^ 2 = 1) (hne : permutation ≠ 1) :
    permutation = Equiv.swap 0 1 ∨ permutation = Equiv.swap 0 2 ∨ permutation = Equiv.swap 1 2 := by
  have hfinite : ∀ permutation : Equiv.Perm (Fin 3), permutation ^ 2 = 1 → permutation ≠ 1 →
      permutation = Equiv.swap 0 1 ∨ permutation = Equiv.swap 0 2 ∨ permutation = Equiv.swap 1 2 := by decide
  exact hfinite permutation hsquare hne

theorem centralizer_swap (permutation swap : Equiv.Perm (Fin 3))
    (hswap : swap = Equiv.swap 0 1 ∨ swap = Equiv.swap 0 2 ∨ swap = Equiv.swap 1 2)
    (hcommutes : permutation * swap = swap * permutation) : permutation = 1 ∨ permutation = swap := by
  have hfinite : ∀ permutation swap : Equiv.Perm (Fin 3),
      (swap = Equiv.swap 0 1 ∨ swap = Equiv.swap 0 2 ∨ swap = Equiv.swap 1 2) →
      permutation * swap = swap * permutation → permutation = 1 ∨ permutation = swap := by decide
  exact hfinite permutation swap hswap hcommutes

theorem even_orbit_even_card (subgroup : Subgroup (Equiv.Perm (Fin 3))) (pair : Set (Fin 3))
    (hodd : Even (Nat.card ↥(MulAction.orbit subgroup pair))) : Even (Nat.card subgroup) := by
  have hindex : (MulAction.stabilizer subgroup pair).index = Nat.card ↥(MulAction.orbit subgroup pair) :=
    (Nat.card_congr (MulAction.orbitEquivQuotientStabilizer subgroup pair)).symm
  apply even_iff_two_dvd.mpr
  have hdivides := (MulAction.stabilizer subgroup pair).index_dvd_card
  rw [hindex] at hdivides
  exact (even_iff_two_dvd.mp hodd).trans hdivides

theorem swap_mem (subgroup : Subgroup (Equiv.Perm (Fin 3))) (heven : Even (Nat.card subgroup)) :
    ∃ swap ∈ subgroup, swap = Equiv.swap 0 1 ∨ swap = Equiv.swap 0 2 ∨ swap = Equiv.swap 1 2 := by
  obtain ⟨member, horder⟩ := exists_prime_orderOf_dvd_card' (G := subgroup) 2 (even_iff_two_dvd.mp heven)
  have horderAmbient : orderOf member.val = 2 :=
    (orderOf_injective subgroup.subtype subgroup.subtype_injective member).trans horder
  have hsquare : member.val ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (horderAmbient ▸ dvd_rfl)
  have hne : member.val ≠ 1 := by
    intro hone
    rw [hone, orderOf_one] at horderAmbient
    omega
  exact ⟨member.val, member.property, involution_swap member.val hsquare hne⟩

theorem common_swap {Index : Type*} (subgroups : Index → Subgroup (Equiv.Perm (Fin 3)))
    (hother : ∀ index : Index, ∃ other : Index, index ≠ other)
    (hcommutes : Pairwise (fun first second => ⁅subgroups first, subgroups second⁆ = ⊥))
    (heven : ∀ index : Index, Even (Nat.card (subgroups index)))
    (base : Index) :
    ∃ swap : Equiv.Perm (Fin 3),
      (swap = Equiv.swap 0 1 ∨ swap = Equiv.swap 0 2 ∨ swap = Equiv.swap 1 2) ∧
      ∀ index : Index, ∀ permutation : Equiv.Perm (Fin 3),
        permutation ∈ subgroups index ↔ permutation = 1 ∨ permutation = swap := by
  obtain ⟨swap, hswap, hswapForm⟩ := swap_mem (subgroups base) (heven base)
  have hbaseBound : ∀ permutation ∈ subgroups base, permutation = 1 ∨ permutation = swap := by
    obtain ⟨other, hother⟩ := hother base
    obtain ⟨otherSwap, hotherSwap, hotherSwapForm⟩ := swap_mem (subgroups other) (heven other)
    have hcentral := Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcommutes hother)
    have hswapsCommute := Subgroup.mem_centralizer_iff.mp (hcentral hswap) otherSwap hotherSwap
    have hequal := centralizer_swap otherSwap swap hswapForm hswapsCommute
    have hotherNe : otherSwap ≠ 1 := by
      rcases hotherSwapForm with heq | heq | heq <;> rw [heq] <;> decide
    have hotherEq := hequal.resolve_left hotherNe
    intro permutation hpermutation
    apply centralizer_swap permutation swap hswapForm
    rw [← hotherEq]
    exact (Subgroup.mem_centralizer_iff.mp (hcentral hpermutation) otherSwap hotherSwap).symm
  refine ⟨swap, hswapForm, ?_⟩
  intro index permutation
  by_cases hindex : index = base
  · rw [hindex]
    exact ⟨hbaseBound permutation, fun hmember => hmember.elim (fun heq => heq ▸ (subgroups base).one_mem)
      (fun heq => heq ▸ hswap)⟩
  · have hcentral := Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcommutes hindex)
    have hbound : ∀ member ∈ subgroups index, member = 1 ∨ member = swap := by
      intro member hmember
      apply centralizer_swap member swap hswapForm
      exact (Subgroup.mem_centralizer_iff.mp (hcentral hmember) swap hswap).symm
    obtain ⟨indexSwap, hindexSwap, hindexSwapForm⟩ := swap_mem (subgroups index) (heven index)
    have hindexSwapNe : indexSwap ≠ 1 := by
      rcases hindexSwapForm with heq | heq | heq <;> rw [heq] <;> decide
    have hindexSwapEq := (hbound indexSwap hindexSwap).resolve_left hindexSwapNe
    exact ⟨hbound permutation, fun hmember => hmember.elim (fun heq => heq ▸ (subgroups index).one_mem)
      (fun heq => heq ▸ (hindexSwapEq ▸ hindexSwap))⟩

end CFSG.ComponentClassification.ThreePointCommutingActions
