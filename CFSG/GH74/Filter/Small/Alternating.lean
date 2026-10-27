module

public import CFSG.GH74.Filter.Statements
public import CFSG.GH74.Filter.ElemAbelian
public import CFSG.LocalAnalysis.SectionRank.AlternatingCover
public import CFSG.GH74.SmallRanks.AltM11
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Filter

open Equiv Blueprint Assembly.LowTwoRank

theorem t_alt_small : S_alt_small := by
  intro G _ _ n _ h7 ⟨e⟩
  rw [twoRank_eq_of_mulEquiv e]
  exact (CFSG.SectionRank.pRank_top_le_of_injective Nat.one_lt_two (CFSG.SectionRank.altEmbed h7)
    (CFSG.SectionRank.altEmbed_injective h7)).trans
    SmallRanks.twoRank_alternatingGroup_seven_le_two

@[expose] def u12 (i : Fin 5) : Perm (Fin 12) :=
  swap ⟨2 * i.val, by omega⟩ ⟨2 * i.val + 1, by omega⟩ * swap 10 11

theorem u12_sq : ∀ i, u12 i ^ 2 = 1 := by decide +kernel

theorem u12_comm : ∀ i j, u12 i * u12 j = u12 j * u12 i := by decide +kernel

theorem u12_sign : ∀ i, Perm.sign (u12 i) = 1 := by decide +kernel

theorem u12_ker :
    ∀ a : Fin 5 → Fin 2, a ≠ 0 → (List.ofFn fun i => u12 i ^ (a i : ℕ)).prod ≠ 1 := by
  decide +kernel

@[expose] def u12Alt (i : Fin 5) : alternatingGroup (Fin 12) := ⟨u12 i, u12_sign i⟩

theorem not_gen4_alternating_twelve : ¬ Gen4 (alternatingGroup (Fin 12)) := by
  refine not_gen4_of_commuting_involutions (r := 5) le_rfl u12Alt (fun i => ?_) (fun i j => ?_)
    (fun a ha h => ?_)
  · exact Subtype.ext (u12_sq i)
  · exact Subtype.ext (u12_comm i j)
  · refine u12_ker a ha ?_
    have := congrArg (alternatingGroup (Fin 12)).subtype h
    rw [map_list_prod, List.map_ofFn] at this
    simpa [Function.comp_def, u12Alt] using this

theorem t_alt_large : S_alt_large := by
  intro G _ _ n hn ⟨e⟩
  refine not_gen4_of_mulEquiv e.symm fun h => not_gen4_alternating_twelve ?_
  exact Gen4.of_injective (CFSG.SectionRank.altEmbed hn) (CFSG.SectionRank.altEmbed_injective hn) h

end CFSG.GH74.Filter
