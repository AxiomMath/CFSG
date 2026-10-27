module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.CaseB.GolaySpan
public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.CocodeFacts

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open CFSG.EvenSporadicStandard.Wong77.Module CFSG.EvenSporadicStandard.Wong77.Module.Masks

@[expose] def finOfMask (x : ℕ) : Finset (Fin 23) := Finset.univ.filter fun i => x.testBit i

theorem ind_finOfMask (x : ℕ) : ind (finOfMask x) = wordOfNat x := by
  ext i
  simp [ind, wordOfNat, finOfMask]

@[expose] def golayBlocks : List (Finset (Fin 23)) :=
  (codeList.filter fun x => Nat.beq (bitCount x 23) 7).map finOfMask

theorem mem_golayBlocks_iff (s : Finset (Fin 23)) :
    s ∈ golayBlocks ↔ s.card = 7 ∧ ind s ∈ golayCode := by
  simp only [golayBlocks, List.mem_map, List.mem_filter, Nat.beq_eq]
  constructor
  · rintro ⟨x, ⟨hx, h7⟩, rfl⟩
    refine ⟨?_, (mem_codeList_iff _).2 ⟨x, hx, (ind_finOfMask x).symm⟩⟩
    rw [← hammingNorm_ind, ind_finOfMask, hammingNorm_wordOfNat', h7]
  · rintro ⟨h7, hs⟩
    obtain ⟨x, hx, hxs⟩ := (mem_codeList_iff _).1 hs
    refine ⟨x, ⟨hx, ?_⟩, ind_injective (by rw [ind_finOfMask, hxs])⟩
    rw [← hammingNorm_wordOfNat', hxs, hammingNorm_ind, h7]

theorem golayBlocks_nodup : golayBlocks.Nodup := by
  have h := nodup_map_codeList.sublist
    (List.Sublist.map wordOfNat (List.filter_sublist (p := fun x => Nat.beq (bitCount x 23) 7)))
  refine List.Nodup.of_map ind ?_
  rw [golayBlocks, List.map_map]
  have : ind ∘ finOfMask = wordOfNat := funext ind_finOfMask
  rwa [this]

theorem image_mem_golayBlocks {g : Equiv.Perm (Fin 23)} (hg : g ∈ permStab golayCode)
    {s : Finset (Fin 23)} (hs : s ∈ golayBlocks) : s.image g ∈ golayBlocks := by
  rw [mem_golayBlocks_iff] at hs ⊢
  refine ⟨?_, ?_⟩
  · rw [Finset.card_image_of_injective _ g.injective]
    exact hs.1
  · rw [← permLin_ind]
    exact (hg (ind s)).2 hs.2

end CFSG.EvenSporadicStandard.TwoFi22.DS81
