module

public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersMonster
import all CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersMonster

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P

open CFSG.EvenSmallLie.CatalogOrders CFSG.YGroups CFSG.Blueprint.NativeSporadic CFSG.SectionRank

def a10Ord8 : Equiv.Perm (Fin 10) :=
  Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4 * Equiv.swap 4 5 *
    Equiv.swap 5 6 * Equiv.swap 6 7 * Equiv.swap 8 9

theorem a10Ord8_mem : a10Ord8 ∈ alternatingGroup (Fin 10) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  simp [a10Ord8, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap]

theorem a10Ord8_pow_eight : a10Ord8 ^ 8 = 1 := by decide +kernel

theorem a10Ord8_pow_four : a10Ord8 ^ 4 ≠ 1 := by decide +kernel

theorem exists_order_eight_of_mulEquiv_M
    {T : Type} [Group T] [Nontrivial T]
    (e : T ≃* CFSG.Blueprint.NativeSporadic.M) : ∃ x : T, x ^ 8 = 1 ∧ x ^ 4 ≠ 1 := by
  have : Nontrivial M := e.injective.nontrivial
  have hG : commutator Y443 ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot _).1 this
  have hord : orderOf (y443Gen 0 * y443Gen 1) = 3 :=
    orderOf_mul_eq_three_of_adj y443Graph y443Graph_connected y443Graph_cliqueFree y443Gen
      y443_closure y443Gen_sq y443Gen_edge y443Gen_commute hG (y443Graph_adj 0 1 rfl)
  have hc : s10Gen 0 * s10Gen 1 ∈ alternatingGroup (Fin 10) :=
    Equiv.Perm.mul_mem_alternatingGroup_of_isSwap ⟨4, 5, by decide, by decide⟩
      ⟨3, 4, by decide, by decide⟩
  have := alternatingGroup.isSimpleGroup (α := Fin 10) (by simp)
  let f : alternatingGroup (Fin 10) →* commutator Y443 :=
    (s10ToY443.comp (alternatingGroup (Fin 10)).subtype).codRestrict _
      fun σ => s10ToY443_mem_commutator σ.2
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker).resolve_right fun htop => ?_
    have hmem : (⟨_, hc⟩ : alternatingGroup (Fin 10)) ∈ f.ker := htop ▸ Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at hmem
    have h1 : y443Gen 0 * y443Gen 1 = 1 := by
      rw [← s10ToY443_threeCycle]
      exact congrArg Subtype.val hmem
    rw [h1, orderOf_one] at hord
    exact absurd hord (by norm_num)
  set σ : alternatingGroup (Fin 10) := ⟨a10Ord8, a10Ord8_mem⟩ with hσ
  have h8 : σ ^ 8 = 1 := Subtype.ext (by simpa [hσ] using a10Ord8_pow_eight)
  have h4 : σ ^ 4 ≠ 1 := fun h => a10Ord8_pow_four (by simpa [hσ] using congrArg Subtype.val h)
  refine ⟨e.symm (f σ), ?_, fun h => h4 ?_⟩
  · rw [← map_pow, ← map_pow, h8, map_one, map_one]
  · apply hf
    apply e.symm.injective
    rw [map_pow, map_pow, map_one, map_one] at *
    simpa using h

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P
