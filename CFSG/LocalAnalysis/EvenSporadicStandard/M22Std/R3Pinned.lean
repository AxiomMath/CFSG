module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3HE32
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3Fusion1
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions

public section

namespace CFSG.EvenSporadicStandard.M22Std

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.FusionCheck
  CFSG.EvenSporadicStandard.M22Std.OutCheck CFSG.Blueprint.NativeSporadic
  CFSG.QuasithinUnique.Unc25G2.M2x CFSG.EvenSporadicStandard.M23Std

theorem sylowWitness_m22_s0 :
    ∃ (t : Carrier .M22) (F1 : Subgroup (Carrier .M22)), (∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) ∧
      Nat.card F1 = 16 ∧ SylowWitness (Carrier .M22) s0 t F1 := by
  have hS := (Certificates.certificate24781).1
  have hP : IsPGroup 2 sylowS := IsPGroup.of_card (card_sylowS hS)
  have h2E : TwoEAt sylowS := twoE_M22.exists_at hP sylowS_index_odd
  obtain ⟨F1, F2, hD, hN, hmem1⟩ := m22_fusionData_pinned h2E
  refine ⟨tEl, F1, hmem1, hN.F_card, ?_⟩
  obtain ⟨hsq, hne⟩ := tEl_involution
  exact
    { sq := hsq
      ne := hne
      fourth := ⟨sylowGens.getD 0 1, sylowGen_fourth⟩
      mem := by
        rw [mem_s0_iff, autTab_conj_tEl, s0Tabs_eq]
        refine List.mem_append_left _ (mem_s0Inner_iff.2 ⟨tEl, hD.t_mem, tab_tEl⟩)
      center := s0_center
      t_mem := hD.t_mem_F1
      nd := hN
      e16 :=
        { card := hN.F_card
          sq := hN.F_sq
          comm := hN.F_comm
          normal := s0_normal hmem1
          inner_le := innerImage_le_s0 hD.F1_le
          cent := aut_cent hmem1 hN
          orbit8 := s0_orbit8 hmem1
          unique := s0_unique hmem1 hN.F_card }
      card_S := card_s0
      outer_inv := s0_outer_inv
      count_ne := s0_count_ne }

theorem autSylowE32_m22 :
    AutSylowWith3 (fun Y _ S F => ∃ J : Subgroup (MulAut Y), E32Facts Y S F J)
      (Carrier .M22) := by
  obtain ⟨t, F1, hmem1, hF16, W⟩ := sylowWitness_m22_s0
  exact AutSylowWith3.of_sylow isoInv3_e32 isPGroup_s0 index_s0_odd W
    (e32Facts_pinned hmem1 hF16)

end CFSG.EvenSporadicStandard.M22Std
