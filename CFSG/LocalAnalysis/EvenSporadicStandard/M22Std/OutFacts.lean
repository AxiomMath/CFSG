module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFactsUnique
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFactsCent
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinM22
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFactsS0c

public section

namespace CFSG.EvenSporadicStandard.M22Std

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.FusionCheck
  CFSG.EvenSporadicStandard.M22Std.OutCheck CFSG.Blueprint.NativeSporadic
  CFSG.QuasithinUnique.Unc25G2.M2x CFSG.EvenSporadicStandard.M23Std

theorem sylowGen_fourth :
    (sylowGens.getD 0 1) * (sylowGens.getD 0 1) * ((sylowGens.getD 0 1) * (sylowGens.getD 0 1)) =
      tEl := by
  apply tab_injective
  simp only [tab_mul, tab_getD, tab_sylowGens, tab_tEl]
  decide

theorem sylowWitness_m22_pinned :
    ∃ (S₀ : Subgroup (MulAut (Carrier .M22))) (t : Carrier .M22) (F1 : Subgroup (Carrier .M22)),
      IsPGroup 2 S₀ ∧ ¬ 2 ∣ S₀.index ∧ (∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) ∧
        SylowWitness (Carrier .M22) S₀ t F1 := by
  have hS := (Certificates.certificate24781).1
  have hP : IsPGroup 2 sylowS := IsPGroup.of_card (card_sylowS hS)
  have h2E : TwoEAt sylowS := twoE_M22.exists_at hP sylowS_index_odd
  obtain ⟨F1, F2, hD, hN, hmem1⟩ := m22_fusionData_pinned h2E
  obtain ⟨hsq, hne⟩ := tEl_involution
  refine ⟨s0, tEl, F1, isPGroup_s0, index_s0_odd, hmem1, ?_⟩
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

end CFSG.EvenSporadicStandard.M22Std
