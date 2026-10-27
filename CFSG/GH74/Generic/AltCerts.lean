module

public import CFSG.GH74.Generic.Certificates
public import CFSG.LocalAnalysis.SectionRank.AlternatingCover

public section

namespace CFSG.GH74.Generic

open Equiv

@[expose] def v8 (i : Fin 4) : Perm (Fin 8) :=
  ![swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 4 5 * swap 6 7, swap 4 6 * swap 5 7] i

theorem v8_sq : ∀ i, v8 i ^ 2 = 1 := by decide +kernel

theorem v8_comm : ∀ i j, v8 i * v8 j = v8 j * v8 i := by decide +kernel

theorem v8_sign : ∀ i, Perm.sign (v8 i) = 1 := by decide +kernel

theorem v8_ker :
    ∀ a : Fin 4 → Fin 2, a ≠ 0 → (List.ofFn fun i => v8 i ^ (a i : ℕ)).prod ≠ 1 := by
  decide +kernel

@[expose] def v8Alt (i : Fin 4) : alternatingGroup (Fin 8) := ⟨v8 i, v8_sign i⟩

theorem rankCertified_alternating_eight : RankCertified (alternatingGroup (Fin 8)) 3 := by
  refine rankCertified_of_commuting_involutions (r := 4) v8Alt (fun i => ?_) (fun i j => ?_)
    (fun a ha h => ?_) (by norm_num)
  · exact Subtype.ext (v8_sq i)
  · exact Subtype.ext (v8_comm i j)
  · refine v8_ker a ha ?_
    have := congrArg (alternatingGroup (Fin 8)).subtype h
    rw [map_list_prod, List.map_ofFn] at this
    simpa [Function.comp_def, v8Alt] using this

theorem rankCertified_alternating {n : ℕ} (hn : 8 ≤ n) :
    RankCertified (alternatingGroup (Fin n)) 3 :=
  rankCertified_alternating_eight.of_injective (CFSG.SectionRank.altEmbed hn)
    (CFSG.SectionRank.altEmbed_injective hn)

end CFSG.GH74.Generic
