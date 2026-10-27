module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupChunk0
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupChunk1
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupChunk2
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupChunk3
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupChunk4
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupChunk5
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupChunk6
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupChunk7
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupChunk8
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupChunk9
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupChunk10
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupChunk11
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupChunk12
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupChunk13

public section

namespace CFSG.LargeEvenClassification.Helpers

theorem c8Four_record_property_of_chunks (P : C8FourSubgroupRecord → Prop)
    (h0 : ∀ j : Fin 64, P (c8FourRecordChunk0[j.val]!))
    (h1 : ∀ j : Fin 64, P (c8FourRecordChunk1[j.val]!))
    (h2 : ∀ j : Fin 64, P (c8FourRecordChunk2[j.val]!))
    (h3 : ∀ j : Fin 64, P (c8FourRecordChunk3[j.val]!))
    (h4 : ∀ j : Fin 64, P (c8FourRecordChunk4[j.val]!))
    (h5 : ∀ j : Fin 64, P (c8FourRecordChunk5[j.val]!))
    (h6 : ∀ j : Fin 64, P (c8FourRecordChunk6[j.val]!))
    (h7 : ∀ j : Fin 64, P (c8FourRecordChunk7[j.val]!))
    (h8 : ∀ j : Fin 64, P (c8FourRecordChunk8[j.val]!))
    (h9 : ∀ j : Fin 64, P (c8FourRecordChunk9[j.val]!))
    (h10 : ∀ j : Fin 64, P (c8FourRecordChunk10[j.val]!))
    (h11 : ∀ j : Fin 64, P (c8FourRecordChunk11[j.val]!))
    (h12 : ∀ j : Fin 64, P (c8FourRecordChunk12[j.val]!))
    (h13 : ∀ j : Fin 64, P (c8FourRecordChunk13[j.val]!))
    (i : Fin 896) : P (c8FourRecord i) := by
  let chunk : Fin 14 := ⟨i.val / 64, by omega⟩
  let offset : Fin 64 := ⟨i.val % 64, Nat.mod_lt _ (by decide)⟩
  have hi : i.val / 64 = chunk.val := rfl
  unfold c8FourRecord
  rw [hi]
  clear_value chunk
  clear hi
  fin_cases chunk
  · exact h0 offset
  · exact h1 offset
  · exact h2 offset
  · exact h3 offset
  · exact h4 offset
  · exact h5 offset
  · exact h6 offset
  · exact h7 offset
  · exact h8 offset
  · exact h9 offset
  · exact h10 offset
  · exact h11 offset
  · exact h12 offset
  · exact h13 offset

theorem c8Four_all_records_valid (i : Fin 896) : c8FourRecordValid (c8FourRecord i) :=
  c8Four_record_property_of_chunks c8FourRecordValid
    c8Four_chunk0_valid
    c8Four_chunk1_valid
    c8Four_chunk2_valid
    c8Four_chunk3_valid
    c8Four_chunk4_valid
    c8Four_chunk5_valid
    c8Four_chunk6_valid
    c8Four_chunk7_valid
    c8Four_chunk8_valid
    c8Four_chunk9_valid
    c8Four_chunk10_valid
    c8Four_chunk11_valid
    c8Four_chunk12_valid
    c8Four_chunk13_valid
    i

theorem c8Four_all_kernels (i : Fin 896) : c8FourKernelListsValid (c8FourRecord i) :=
  c8Four_record_property_of_chunks c8FourKernelListsValid
    c8Four_chunk0_kernels
    c8Four_chunk1_kernels
    c8Four_chunk2_kernels
    c8Four_chunk3_kernels
    c8Four_chunk4_kernels
    c8Four_chunk5_kernels
    c8Four_chunk6_kernels
    c8Four_chunk7_kernels
    c8Four_chunk8_kernels
    c8Four_chunk9_kernels
    c8Four_chunk10_kernels
    c8Four_chunk11_kernels
    c8Four_chunk12_kernels
    c8Four_chunk13_kernels
    i

theorem c8Four_all_vectors (i : Fin 896) : c8FourGeneratorVectorsValid (c8FourRecord i) :=
  c8Four_record_property_of_chunks c8FourGeneratorVectorsValid
    c8Four_chunk0_vectors
    c8Four_chunk1_vectors
    c8Four_chunk2_vectors
    c8Four_chunk3_vectors
    c8Four_chunk4_vectors
    c8Four_chunk5_vectors
    c8Four_chunk6_vectors
    c8Four_chunk7_vectors
    c8Four_chunk8_vectors
    c8Four_chunk9_vectors
    c8Four_chunk10_vectors
    c8Four_chunk11_vectors
    c8Four_chunk12_vectors
    c8Four_chunk13_vectors
    i

@[expose] def c8FourListedSubgroup (i : Fin 896) : Subgroup C8FourCode :=
  c8FourRecordSubgroup (c8FourRecord i) (c8Four_all_records_valid i)

set_option maxRecDepth 10000 in
@[expose] def c8FourRecordCharacter (i : Fin 896) (q : Fin 32) :
    c8FourListedSubgroup i →* Multiplicative (ZMod 2) where
  toFun g := Multiplicative.ofAdd (c8FourPairing (c8FourVector (c8FourRecord i) g.val) q)
  map_one' := by
    change Multiplicative.ofAdd (c8FourPairing (c8FourVector (c8FourRecord i) 1) q) = 1
    rw [(c8Four_all_records_valid i).2.2.2.2.2.1]
    rw [c8FourPairing_zero]
    rfl
  map_mul' g h := by
    have hv := (c8Four_all_records_valid i).2.2.2.2.2.2.1
    have hg := ((c8Four_all_records_valid i).1 g.val).mp g.property
    have hh := ((c8Four_all_records_valid i).1 h.val).mp h.property
    have heq := (certificateListAll_iff _ _).mp ((certificateListAll_iff _ _).mp hv g.val hg) h.val hh
    change c8FourVector (c8FourRecord i) (g.val * h.val) = _ at heq
    change Multiplicative.ofAdd (c8FourPairing (c8FourVector (c8FourRecord i) (g.val * h.val)) q) = _
    rw [heq, c8FourPairing_xor]
    rfl

theorem c8Four_record_character_kernels (i : Fin 896) (q : Fin 32) :
    let j := (c8FourRecord i).children[q.val]!
    ∀ g : C8FourCode, c8FourRecordMem (c8FourRecord j) g ↔
      c8FourRecordMem (c8FourRecord i) g ∧ c8FourPairing (c8FourVector (c8FourRecord i) g) q = 0 := by
  intro j g
  rw [(c8Four_all_records_valid j).1 g, (c8Four_all_records_valid i).1 g]
  have hlist := c8Four_all_kernels i q
  change (c8FourRecord j).elements = _ at hlist
  rw [hlist, List.mem_filter]
  simp

end CFSG.LargeEvenClassification.Helpers
