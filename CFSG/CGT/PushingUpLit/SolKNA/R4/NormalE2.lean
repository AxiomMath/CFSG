module

public import CFSG.ClassicalInvolution.Q3.TL3Induct

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG.Open CFSG.ClassicalInvolution.Q3

theorem tightInO2_oddQuot_of_normal {H : Type} [Group H] [Finite H] {X : Subgroup H} [X.Normal]
    {τ : H} (hτ : τ ∈ X)
    (h2 : TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore H) τ)) :
    TightInO2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥X) (⟨τ, hτ⟩ : X)) := by
  obtain ⟨Pb, hPbn, hPb2, hm⟩ := h2
  let P : Subgroup H := Pb.comap (QuotientGroup.mk' (classicalInvolutionOddCore H))
  have hPn : P.Normal := hPbn.comap _
  have hτP : τ ∈ P := Subgroup.mem_comap.mpr hm
  have hcard : Nat.card ↥((classicalInvolutionOddCore H).subgroupOf X) =
      Nat.card ↥(classicalInvolutionOddCore H ⊓ X) := by
    rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective X.subtype_injective]
  have hdvd : Nat.card ↥((classicalInvolutionOddCore H).subgroupOf X) ∣
      Nat.card ↥(classicalInvolutionOddCore H) := by
    rw [hcard]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hoddH : Odd (Nat.card ↥(classicalInvolutionOddCore H)) :=
    CFSG.ComponentClassification.OddCore.odd_card H
  have hNX : (classicalInvolutionOddCore H).subgroupOf X ≤ classicalInvolutionOddCore ↥X :=
    CFSG.ComponentClassification.OddCore.maximal ↥X ((classicalInvolutionOddCore H).subgroupOf X)
      inferInstance (hoddH.of_dvd_nat hdvd)
  refine ⟨(P.subgroupOf X).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥X)), ?_, ?_, ?_⟩
  · exact Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  · intro g
    obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp g.2
    have hyP : (y : H) ∈ P := Subgroup.mem_subgroupOf.mp hy
    obtain ⟨k, hk⟩ := hPb2 ⟨QuotientGroup.mk' (classicalInvolutionOddCore H) (y : H),
      Subgroup.mem_comap.mp hyP⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hk' : QuotientGroup.mk' (classicalInvolutionOddCore H) ((y : H) ^ 2 ^ k) = 1 := by
      rw [map_pow]
      simpa using congrArg Subtype.val hk
    have hyN : y ^ 2 ^ k ∈ (classicalInvolutionOddCore H).subgroupOf X := by
      rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
      exact (QuotientGroup.eq_one_iff ((y : H) ^ 2 ^ k)).mp hk'
    have hyM : y ^ 2 ^ k ∈ classicalInvolutionOddCore ↥X := hNX hyN
    show (g : ↥X ⧸ classicalInvolutionOddCore ↥X) ^ 2 ^ k = 1
    rw [← hyg, ← map_pow]
    exact (QuotientGroup.eq_one_iff (y ^ 2 ^ k)).mpr hyM
  · have hτQ : (⟨τ, hτ⟩ : X) ∈ P.subgroupOf X := Subgroup.mem_subgroupOf.mpr hτP
    exact Subgroup.mem_map_of_mem _ hτQ

end CFSG.CGT.PushingUpLit.SolKNA.R4
