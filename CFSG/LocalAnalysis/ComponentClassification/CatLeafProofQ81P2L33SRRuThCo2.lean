module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRCommon
public import CFSG.Sporadic.Co2Schreier.FullAut
public import CFSG.Sporadic.Co2Schreier.OddCore
public import CFSG.Sporadic.Schreier.RuAutInner
public import CFSG.Sporadic.ThSchreier.NodeCentralCentralizer
public import CFSG.Sporadic.ThSchreier.ThSchreierCase

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.SR

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.RuSchreier CFSG.Sporadic.Co2Cert
open CFSG.Sporadic.Co2Schreier

theorem sporNoTwoFix_Ru :
    SporNoTwoFix .Ru := by
  obtain ⟨hZ, hbij, -, hL⟩ := CTUC_Ru_full_inner_automorphisms_and_second_centralizer
  refine sporNoTwoFix_of_mulEquiv (P := ↥ruP) ruEquivP
    (forall_of_inner hZ (inner_of_bijective hbij) fun t ht => ?_)
  apply not_isPGroup_centralizer_of_inf
  have ht' : (t : Equiv.Perm (Fin 4060)) ∈ {t | t ∈ ruP ∧ orderOf t = 2} :=
    ⟨t.2, by rw [Subgroup.orderOf_coe]; exact ht⟩
  rw [ruInvolutions_eq] at ht'
  rcases ht' with ⟨g, hg, he⟩ | ⟨g, hg, he⟩
  · rw [← he]
    refine not_isPGroup_inf_centralizer_conj hg ?_
    rw [← ruC_eq_centralizer]
    exact not_isPGroup_of_three_dvd (by rw [card_ruC]; norm_num)
  · rw [← he]
    refine not_isPGroup_inf_centralizer_conj hg ?_
    rw [hL]
    exact not_isPGroup_of_prime_dvd Nat.prime_five (by norm_num) (by rw [card_ruL]; norm_num)

theorem sporNoTwoFix_Th :
    SporNoTwoFix .Th := by
  intro Y _ _ ⟨e⟩
  have e' : Y ≃* ↥CFSG.Sporadic.Th.J := e.trans CFSG.Sporadic.Th.thEquivJ
  have hs : IsSimpleGroup CFSG.Sporadic.Th.J :=
    CFSG.Sporadic.Th.Kernel.isSimpleGroup_J
      CFSG.Sporadic.Th.th_kernel_facts
  have hsY : IsSimpleGroup Y := @MulEquiv.isSimpleGroup _ _ _ _ hs e'
  have hZ : center Y = ⊥ := center_eq_bot_of_not_prime hsY
    ((Nat.card_congr e'.toEquiv).trans CFSG.Sporadic.Th.Max3.natCard_J) (by norm_num)
  obtain ⟨hinn, -⟩ := CFSG.Sporadic.ThSchreier.ctuc_Th_full_automorphism_group.2 Y ⟨e⟩
  obtain ⟨-, hCa, -⟩ := CFSG.Sporadic.ThSchreier.ctuc_Th_full_central_involution_centralizer
  refine forall_of_inner hZ (fun α => ?_) fun t ht => ?_
  · have hα : α ∈ OuterAutomorphisms.inner Y := hinn ▸ Subgroup.mem_top α
    obtain ⟨t, ht⟩ := hα
    exact ⟨t, ht.symm⟩
  · have ht' : orderOf (e' t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht
    have h1 := not_isPGroup_centralizer_of_isConj
      (CFSG.Sporadic.Th.Max3.all_involutions_conjugate _ ht')
      (not_isPGroup_of_three_dvd (by rw [hCa]; norm_num))
    exact @not_isPGroup_of_mulEquiv _ _ _ (Subgroup.toGroup _)
      (@centralizerMap Y _ _ (Subgroup.toGroup _) e' t) h1

theorem sporNoTwoFix_Co2 :
    SporNoTwoFix .Co2 := by
  have hS : IsSimpleGroup NativeSporadic.Co2 := CFSG.Sporadic.Co2.isSimpleGroup_Co2
  have hs : IsSimpleGroup co2P := @MulEquiv.isSimpleGroup _ _ _ _ hS co2PermEquiv.symm
  have hZ : center co2P = ⊥ := center_eq_bot_of_not_prime hs
    ((Nat.card_congr co2PermEquiv.toEquiv).symm.trans CFSG.Sporadic.Co2.card_Co2) (by norm_num)
  refine sporNoTwoFix_of_mulEquiv (P := ↥co2P) co2PermEquiv
    (forall_of_inner_reps hZ CTUC_Co2_full_automorphisms_inner [zP, tP, uP]
      (fun t ht => ?_) ?_)
  · have ht2 : t * t = 1 := by
      have h := pow_orderOf_eq_one t
      rwa [ht, pow_two] at h
    have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht; norm_num at ht
    rcases invol_cases t ht2 ht1 with h | h | h
    · exact ⟨zP, by simp, h.symm⟩
    · exact ⟨tP, by simp, h.symm⟩
    · exact ⟨uP, by simp, h.symm⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact not_isPGroup_of_mulEquiv ((MulEquiv.subgroupCongr locC_subgroupOf_eq.symm).trans
        (Subgroup.subgroupOfEquivOfLe locC_le_P))
        (not_isPGroup_of_three_dvd (by rw [card_locC]; norm_num))
    · exact not_isPGroup_of_mulEquiv ((MulEquiv.subgroupCongr locD_subgroupOf_eq.symm).trans
        (Subgroup.subgroupOfEquivOfLe locD_le_P))
        (not_isPGroup_of_three_dvd (by rw [card_locD]; norm_num))
    · exact not_isPGroup_of_mulEquiv ((MulEquiv.subgroupCongr centralizer_uP).trans
        (Subgroup.subgroupOfEquivOfLe (inf_le_left : locH3 ≤ co2P)))
        (not_isPGroup_of_three_dvd (by rw [card_locH3]; norm_num))

end CFSG.ComponentClassification.HarrisLit.L33.SR
