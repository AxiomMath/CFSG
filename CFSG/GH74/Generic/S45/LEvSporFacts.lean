module

public import CFSG.GH74.Generic.S45.LEvSporJ2Spec
public import CFSG.GH74.Generic.S45.LEvSporJ2Aut
public import CFSG.GH74.Generic.S45.LEvSporM12Spec
public import CFSG.GH74.Generic.S45.LEvSporLeaf23
public import Certificates.Certificate5150

public section

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.ComponentClassification.M12Cover
open scoped commutatorElement

namespace CFSG.GH74.Generic.S45.EvSpor

theorem j2_facts :
    J2Facts j2P := by
  obtain ⟨hreps, hC2A, hC2B, hcent5, -, hKb, hder, hnorm, hE16, -, -, -, -, -⟩ :=
    Certificates.certificate5150
  obtain ⟨-, hrepA, hrepB⟩ := j2_reps hreps
  obtain ⟨hEA, -⟩ := j2_C2A_enums hC2A
  obtain ⟨hEB, hinvB⟩ := j2_C2B_enums hC2B
  obtain ⟨hMenum, hMcard, hMP, hA, hB⟩ := j2_Kb_facts hKb
  obtain ⟨E, hEN, hEa, hEc⟩ := j2_E16_facts hKb hE16
  have hc5 := (cent5_spec (by norm_num) hEA hrepA hcent5).1
  have hdc := derivedIn_spec hEB hMenum hinvB hder
  refine ⟨card_j2P, tp 315 j2Row2A.rep, tp 315 j2Row2B.rep,
    closure (tp 315 '' {x | x ∈ j2KbGens.toArray}), E, j2_row_mem_P j2Row2A_mem j2Row2A_outer,
    j2_row_mem_P j2Row2B_mem j2Row2B_outer, (j2_rows_spec.1 _ j2Row2A_mem).2.1,
    (j2_rows_spec.1 _ j2Row2B_mem).2.1, j2_cover,
    ((j2_rows_spec.1 _ j2Row2A_mem).2.2.2.2).trans j2Row2A_centOrder,
    ((j2_rows_spec.1 _ j2Row2B_mem).2.2.2.2).trans j2Row2B_centOrder,
    fun z hz hzc hz5 c hc hcc hcz => hc5 z ⟨hz, hzc⟩ hz5 c ⟨hc, hcc⟩ hcz, hMP, hMcard,
    fun x hx hxc y hy hyc => hdc x ⟨hx, hxc⟩ y ⟨hy, hyc⟩, j2_norm_card hKb hnorm, hEN, hEa, hEc⟩

theorem j2_autFacts :
    J2AutFacts j2R j2P := by
  obtain ⟨hreps, hC2A, -, hcent5, houter, -, -, -, -, -, -, -, -, -⟩ :=
    Certificates.certificate5150
  obtain ⟨hrepU, hrepA, hrepB⟩ := j2_reps hreps
  obtain ⟨hEA, -⟩ := j2_C2A_enums hC2A
  obtain ⟨hcA1, hcA2⟩ := cent5_spec (by norm_num) hEA hrepA hcent5
  obtain ⟨hU2, -, hUP, hmap, -, -⟩ := ctuc_j2_normalizing_involution_permutation_model
  have hUn : ∀ p ∈ j2P, j2u * p * j2u⁻¹ ∈ j2P := fun p hp => by
    rw [← hmap]
    exact ⟨p, hp, rfl⟩
  simp only [j2OuterOK, Bool.and_eq_true] at houter
  obtain ⟨hvA, hvB⟩ := houter
  have hpA : permOK 315 j2VA = true := by
    simp only [outerCommOK, Bool.and_eq_true] at hvA
    exact hvA.1.1.1.1
  have hpB : permOK 315 j2VB = true := by
    simp only [outerCommOK, Bool.and_eq_true] at hvB
    exact hvB.1.1.1.1
  obtain ⟨hvA_R, hvA_P, hvA_o, hvA_c⟩ :=
    outerComm_spec j2_groupData hrepU hU2 hUn hrepA (rep_tp hpA) hvA
  obtain ⟨hvB_R, hvB_P, hvB_o, hvB_c⟩ :=
    outerComm_spec j2_groupData hrepU hU2 hUn hrepB (rep_tp hpB) hvB
  have h0 := j2_rows_spec.1 j2Row0 j2Row0_mem
  have hB := j2_rows_spec.1 j2Row2B j2Row2B_mem
  have hA := j2_rows_spec.1 j2Row2A j2Row2A_mem
  refine ⟨tp 315 j2Row0.rep, tp 315 j2Row2B.rep, tp 315 j2Row2A.rep, tp 315 j2VA, tp 315 j2VB,
    h0.1, h0.2.2.1.1 j2Row0_outer, j2_row_mem_P j2Row2B_mem j2Row2B_outer,
    j2_row_mem_P j2Row2A_mem j2Row2A_outer, hvA_R, hvA_P, hvB_R, hvB_P, h0.2.1, hB.2.1, hA.2.1,
    hvA_o, hvB_o, hvA_c, hvB_c, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy hy2
    obtain ⟨r, hr, g, hg, hyg⟩ := j2_rows_spec.2 y hy hy2
    refine ⟨g, (show j2P ≤ j2R from le_sup_left) hg, ?_⟩
    rcases j2Rows_cases' r hr with rfl | rfl | rfl
    · exact Or.inl hyg
    · exact Or.inr (Or.inl hyg)
    · exact Or.inr (Or.inr hyg)
  · rw [inf_comm]
    exact h0.2.2.2.2.trans j2Row0_centOrder
  · rw [inf_comm]
    exact hB.2.2.2.2.trans j2Row2B_centOrder
  · rw [inf_comm]
    exact hA.2.2.2.2.trans j2Row2A_centOrder
  · exact fun z hz hzc hz5 c hc hcc hcz => hcA1 z ⟨hz, hzc⟩ hz5 c ⟨hc, hcc⟩ hcz
  · exact fun z hz hzc hz5 c hc hcc => hcA2 (tp 315 j2VA) (rep_tp hpA) z ⟨hz, hzc⟩ hz5 c ⟨hc, hcc⟩

theorem m12_autFacts :
    M12AutFacts autModel blockGroup := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨-, -, -, -, -, -, -, -, -, hreps, hC2A, hKa, hder, hout⟩ :=
    Certificates.certificate5150
  obtain ⟨hEC, hinv⟩ := m12_C2A_enums hC2A
  obtain ⟨hEK, hKcard, hKW, hKrep⟩ := m12_Ka_facts hC2A hKa
  simp only [m12RepsOK, Bool.and_eq_true] at hreps
  obtain ⟨⟨⟨⟨⟨-, hZi⟩, -⟩, hAi⟩, -⟩, hSi⟩ := hreps
  have hZo : orderOf (blockHom (permZ, permZ)) = 2 :=
    orderOf_eq_two_of_involOK hn (rep_toTable hn _) hZi
  have hAo : orderOf m12A1 = 2 := orderOf_eq_two_of_involOK hn (rep_toTable hn _) hAi
  have hSo : orderOf m12Sigma = 2 := orderOf_eq_two_of_involOK hn (rep_toTable hn _) hSi
  have hZD : blockHom (permZ, permZ) ∈ blockGroup := by
    rw [← m12EquivD_elemZ]
    exact (m12EquivD elemZ).2
  have hAD : m12A1 ∈ blockGroup := m12_gens_memD _ (by simp)
  simp only [m12OuterOK, Bool.and_eq_true] at hout
  obtain ⟨⟨hoZ, hoA⟩, hoK⟩ := hout
  have hσrep : Rep 24 m12ST m12Sigma := rep_toTable hn _
  have hσZ : m12Sigma * blockHom (permZ, permZ) = blockHom (permZ, permZ) * m12Sigma :=
    (commTT_iff hσrep (rep_toTable hn _)).1 hoZ
  have hσM : ∀ m ∈ Subgroup.closure (tp 24 '' {x | x ∈ m12KaGens.toArray}),
      m * m12Sigma = m12Sigma * m := by
    intro m hm
    have : Subgroup.closure (tp 24 '' {x | x ∈ m12KaGens.toArray}) ≤
        Subgroup.centralizer ({m12Sigma} : Set (Equiv.Perm (Fin 24))) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ m12KaGens := List.mem_toArray.mp hx
      have hmem : x = m12AT ∨ x = m12KaB := by simpa [m12KaGens] using hx'
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      rcases hmem with rfl | rfl
      · exact ((commTT_iff hσrep (hKrep _ hx')).1 hoA).symm
      · exact ((commTT_iff hσrep (hKrep _ hx')).1 hoK).symm
    exact mem_centralizer_singleton_iff.1 (this hm)
  refine ⟨m12Sigma, m12A1, blockHom (permZ, permZ),
    Subgroup.closure (tp 24 '' {x | x ∈ m12KaGens.toArray}), sigma_mem_autModel,
    sigma_not_mem_blockGroup, hAD, hZD, hSo, hAo, hZo, ?_, ?_, ?_, ?_, hKcard, ?_, hσZ, hσM⟩
  · intro y hy hy2
    obtain ⟨r, hr, c, hc, hyc⟩ := autModel_involution_cover hy hy2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨c, hc, Or.inr (Or.inl hyc)⟩
    · exact ⟨c, hc, Or.inr (Or.inr hyc)⟩
    · exact ⟨c, hc, Or.inl hyc⟩
  · have h := q5Q_spec
    rw [inf_comm]
    have h2 := h.2.1
    rw [h.1] at h2
    exact h2
  · have h := q2Q_spec
    rw [inf_comm]
    have h2 := h.2.1
    rw [h.1] at h2
    exact h2
  · have h := q4Q_spec
    rw [inf_comm]
    have h2 := h.2.1
    rw [h.1] at h2
    exact h2
  · intro x hx hxc y hy hyc
    exact innerDerived_spec (D := m12C2A) hEC hEK hinv hder
      (P := fun g => g ∈ blockGroup ∧ g ∈ Subgroup.centralizer
        ({blockHom (permZ, permZ)} : Set (Equiv.Perm (Fin 24))))
      (fun g hg => ⟨blockGroup_le_autModel hg.1, hg.2⟩)
      (fun g hg => innerT_of_mem_blockGroup hg.1) x y ⟨hx, hxc⟩ ⟨hy, hyc⟩

end CFSG.GH74.Generic.S45.EvSpor
