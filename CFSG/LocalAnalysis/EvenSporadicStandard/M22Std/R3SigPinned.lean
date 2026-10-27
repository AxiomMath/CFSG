module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3SigFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3Pinned
public import Certificates.Certificate25911

public section

namespace CFSG.EvenSporadicStandard.M22Std

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.FusionCheck
  CFSG.EvenSporadicStandard.M22Std.OutCheck CFSG.EvenSporadicStandard.M22Std.E32Check
  CFSG.Blueprint.NativeSporadic

theorem jSub_exists_x
    {F1 : Subgroup (Carrier .M22)} (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) :
    ∃ x ∈ jSub, x ∉ innerImage (Carrier .M22) ⊤ ∧
      Nat.card {v : Carrier .M22 // v ∈ F1 ∧ x v = v} = 4 := by
  have hx : xProp := of_decide_eq_true Certificates.certificate25911
  obtain ⟨l, hlJ, hlO, -, hlf⟩ := hx
  obtain ⟨a, ha⟩ := exists_of_mem_s0Outer hlO
  have hmem : a ∈ jSub := by
    rw [mem_jSub, ha]
    exact hlJ
  refine ⟨a, hmem, ((mem_s0_outer_iff a).2 (by rw [ha]; exact hlO)).2, ?_⟩
  rw [card_fixed_eq hmem1 a, ha]
  exact hlf

theorem e32FactsX_pinned
    {F1 : Subgroup (Carrier .M22)}
    (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) (hF16 : Nat.card F1 = 16) :
    ∃ J : Subgroup (MulAut (Carrier .M22)), E32FactsX (Carrier .M22) s0 F1 J :=
  ⟨jSub,
    { le := jSub_le
      comm := jSub_comm
      sq := jSub_sq
      card := card_jSub
      unique := fun E hE hc hsq h32 => jSub_unique E hE hc hsq h32
      exists_b := jSub_exists_b hmem1
      normal_E16 := fun V hVS hVn hVc hVsq hV16 hVJ =>
        jSub_normal_E16 hmem1 hF16 V hVS hVn hVc hVsq hV16 hVJ
      exists_x := jSub_exists_x hmem1 }⟩

theorem autSylowE32X_m22 :
    AutSylowWith3 (fun Y _ S F => ∃ J : Subgroup (MulAut Y), E32FactsX Y S F J)
      (Carrier .M22) := by
  obtain ⟨t, F1, hmem1, hF16, W⟩ := sylowWitness_m22_s0
  exact AutSylowWith3.of_sylow isoInv3_e32x isPGroup_s0 index_s0_odd W
    (e32FactsX_pinned hmem1 hF16)

end CFSG.EvenSporadicStandard.M22Std
