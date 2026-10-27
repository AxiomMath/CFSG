module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.SplitBTransport
public import Certificates.Certificate24856
public import Certificates.Certificate24857

public section

namespace CFSG.EvenSporadicStandard.M24Std

open SplitB

variable {G : Type} [Group G]

theorem liftDataB_of_type
    {L B : Subgroup G} (h : OctadType L B) : LiftDataB L B := by
  obtain ⟨hBL, e, he⟩ := h
  obtain ⟨hf, hinj, -, -, -⟩ := Certificates.certificate24856
  obtain ⟨hnS, hnT, hS, hT, hST, hA1, hA2⟩ := Certificates.certificate24857
  refine ⟨fun i => iotaE e (fB i), iotaE e liftS, iotaE e liftT,
    fun i => (iotaE_mem_B_iff he _).2 (hf i), ?_, iotaE_mem_egNL hBL he hnS,
    iotaE_mem_egNL hBL he hnT, ?_, ?_, ?_, ?_, ?_⟩
  · intro c d hcd
    rw [← map_ebasis4, ← map_ebasis4] at hcd
    exact hinj c d (iotaE_injective e hcd)
  · rw [← map_mul, hS, map_one]
  · rw [← map_mul, hT, map_one]
  · rw [← map_mul, ← map_mul, hST, map_one]
  · intro i
    rw [← map_inv, ← map_mul, ← map_mul, hA1 i, map_ebasis4]
  · intro i
    rw [← map_inv, ← map_mul, ← map_mul, hA2 i, map_ebasis4]

end CFSG.EvenSporadicStandard.M24Std
