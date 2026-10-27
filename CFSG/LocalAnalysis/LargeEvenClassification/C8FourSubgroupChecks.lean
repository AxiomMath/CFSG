module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupData
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourCharacterCoordinates

public section

namespace CFSG.LargeEvenClassification.Helpers

instance c8FourRecordInhabited : Inhabited C8FourSubgroupRecord := ⟨c8FourRecordData0⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
@[expose, irreducible] def c8FourRecord (i : Fin 896) : C8FourSubgroupRecord :=
  match i.val / 64 with
  | 0 => c8FourRecordChunk0[i.val % 64]!
  | 1 => c8FourRecordChunk1[i.val % 64]!
  | 2 => c8FourRecordChunk2[i.val % 64]!
  | 3 => c8FourRecordChunk3[i.val % 64]!
  | 4 => c8FourRecordChunk4[i.val % 64]!
  | 5 => c8FourRecordChunk5[i.val % 64]!
  | 6 => c8FourRecordChunk6[i.val % 64]!
  | 7 => c8FourRecordChunk7[i.val % 64]!
  | 8 => c8FourRecordChunk8[i.val % 64]!
  | 9 => c8FourRecordChunk9[i.val % 64]!
  | 10 => c8FourRecordChunk10[i.val % 64]!
  | 11 => c8FourRecordChunk11[i.val % 64]!
  | 12 => c8FourRecordChunk12[i.val % 64]!
  | 13 => c8FourRecordChunk13[i.val % 64]!
  | _ => c8FourRecordData0

@[expose] def c8FourKernelListsValid (r : C8FourSubgroupRecord) : Prop :=
  ∀ q : Fin 32,
    let child := c8FourRecord (r.children[q.val]!)
    child.elements = r.elements.filter (fun g => c8FourPairing (c8FourVector r g) q = 0)

instance c8FourKernelListsValid_decidable (r : C8FourSubgroupRecord) :
    Decidable (c8FourKernelListsValid r) :=
  Fintype.decidableForallFintype

@[expose] def c8FourGeneratorVectorsValid (r : C8FourSubgroupRecord) : Prop :=
  ∀ k : Fin 5, k.val < r.generators.length →
    c8FourVector r r.generators[k.val]! = Fin.ofNat 32 (2 ^ k.val)

instance c8FourGeneratorVectorsValid_decidable (r : C8FourSubgroupRecord) :
    Decidable (c8FourGeneratorVectorsValid r) := inferInstanceAs (Decidable (∀ k : Fin 5,
      k.val < r.generators.length → c8FourVector r r.generators[k.val]! = Fin.ofNat 32 (2 ^ k.val)))

end CFSG.LargeEvenClassification.Helpers
