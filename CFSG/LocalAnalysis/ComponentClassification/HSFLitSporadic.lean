module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitSporadicBase
public import CFSG.Walter.J1Props.Hyp
public import CFSG.ClassicalInvolution.Generic.Generation.Endgame
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J3
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.LyAssembly
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M12
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M22
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M23
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.McL
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutOddCore

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Blueprint CFSG.Certificates CFSG.Sporadic.Schreier CFSG.ClassicalInvolution

theorem excluded_M12 : ∀ y : NativeSporadic.M12, orderOf y = 2 → Excluded y := by
  obtain ⟨hcov, hcent⟩ := m12_cover_and_centralizers
  have h1 : centralizerIn m12Certificate.originalSubgroup m12Rep1 =
      m12CentQ1.originalSubgroup := hcent (m12Rep1, m12CentQ1.originalSubgroup) (by simp)
  have h2 : centralizerIn m12Certificate.originalSubgroup m12Rep2 =
      m12CentQ2.originalSubgroup := hcent (m12Rep2, m12CentQ2.originalSubgroup) (by simp)
  have hc1 := m12_rep_data1.2.2.2.1
  have hc2 := m12_rep_data2.2.2.2.1
  rw [← m12Certificate_originalSubgroup]
  refine excluded_of_reps _ [m12Rep1, m12Rep2] ?_ ?_
  · intro u hu ho
    obtain ⟨d, hd, c, hc, hud⟩ := hcov u (by simpa using hu) ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨_, by simp, c, hc, hud⟩
    · exact ⟨_, by simp, c, hc, hud⟩
  · intro r hr hrH
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact excluded_of_ambient_card _ hrH h1 (by rw [hc1]; norm_num) (by rw [hc1]; norm_num)
        (by rw [hc1]; norm_num)
    · exact excluded_of_ambient_card _ hrH h2 (by rw [hc2]; norm_num) (by rw [hc2]; norm_num)
        (by rw [hc2]; norm_num)

theorem excluded_M22 : ∀ y : NativeSporadic.M22, orderOf y = 2 → Excluded y := by
  obtain ⟨hcov, hcent⟩ := m22_cover_and_centralizers
  have h1 : centralizerIn m22Certificate.originalSubgroup m22Rep1 =
      m22CentQ1.originalSubgroup := hcent (m22Rep1, m22CentQ1.originalSubgroup) (by simp)
  have hc1 := m22_rep_data1.2.2.2.1
  rw [← m22Certificate_originalSubgroup]
  refine excluded_of_reps _ [m22Rep1] ?_ ?_
  · intro u hu ho
    obtain ⟨d, hd, c, hc, hud⟩ := hcov u (by simpa using hu) ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    exact ⟨_, by simp, c, hc, hud⟩
  · intro r hr hrH
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact excluded_of_ambient_card _ hrH h1 (by rw [hc1]; norm_num) (by rw [hc1]; norm_num)
      (by rw [hc1]; norm_num)

theorem excluded_M23 : ∀ y : NativeSporadic.M23, orderOf y = 2 → Excluded y := by
  obtain ⟨hcov, hcent⟩ := m23_cover_and_centralizers
  have hQ1 : ValidSchreier m23CentQ1 := m23_oddcore_cent1.1
  have h1 : centralizerIn m23Certificate.originalSubgroup m23Rep1 =
      m23CentQ1.originalSubgroup := hcent (m23Rep1, m23CentQ1.originalSubgroup) (by simp)
  rw [← m23Certificate_originalSubgroup]
  refine excluded_of_reps _ [m23Rep1] ?_ ?_
  · intro u hu ho
    obtain ⟨d, hd, c, hc, hud⟩ := hcov u (by simpa using hu) ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    exact ⟨_, by simp, c, hc, hud⟩
  · intro r hr hrH
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact excluded_of_ambient_normal_pGroup _ hrH h1
      (exists_normal_pGroup_of_check _ (enumerationTab m23CentQ1) _
        (mem_enumerationTab_iff m23CentQ1 hQ1) 4 m23_U1_check)

theorem excluded_J1 : ∀ y : NativeSporadic.J1, orderOf y = 2 → Excluded y := by
  refine excluded_of_mulEquiv_all (Y := ↥Open.walterJ1) ?e ?_
  case e =>
    exact ProperTwoGeneratedCore.j1_exact_model_equiv.symm.trans
      (MulEquiv.subgroupCongr properTwoGenCoreJ1_eq_walterJ1)
  intro y hy
  have hc := Walter.J1.JankoHyp.card_centralizer_involution Walter.J1Props.jankoHyp hy
  right; right; right
  rw [hc]
  norm_num

theorem excluded_J2 : ∀ y : NativeSporadic.J2, orderOf y = 2 → Excluded y := by
  refine excluded_of_mulEquiv_all (Y := ↥J2Cover.P) ?e ?_
  case e => exact J2Cover.nativeEquivP
  obtain ⟨hcov, -, he1, -, he2⟩ := J2Cover.inner_classes
  refine excluded_of_reps J2Cover.P [J2Cover.permA, J2Cover.permTwoA] hcov ?_
  intro r hr hrP
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have hc := J2Cover.cent2B_facts.2.1
    exact excluded_of_ambient_card _ hrP he1 (by rw [hc]; norm_num) (by rw [hc]; norm_num)
      (by rw [hc]; norm_num)
  · have hc := J2Cover.cent2A_facts.2.1
    exact excluded_of_ambient_card _ hrP he2 (by rw [hc]; norm_num) (by rw [hc]; norm_num)
      (by rw [hc]; norm_num)

theorem excluded_J3 : ∀ y : NativeSporadic.J3, orderOf y = 2 → Excluded y := by
  refine excluded_of_mulEquiv_all (Y := ↥J3Proof.P3) ?e ?_
  case e => exact J3Proof.nativeEquivP3
  have hP := J3Proof.card_P3
  have hS2 : IsPGroup 2 J3Proof.sChain.originalSubgroup :=
    IsPGroup.of_card (n := 7) (by rw [J3Proof.card_sChain]; norm_num)
  have hidx : ¬ 2 ∣ (J3Proof.sChain.originalSubgroup.subgroupOf J3Proof.P3).index := by
    have h := (J3Proof.sChain.originalSubgroup.subgroupOf J3Proof.P3).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe J3Proof.sChain_le_P3).toEquiv, J3Proof.card_sChain,
      hP] at h
    omega
  have hc := J3Proof.card_kChain
  exact excluded_of_sylow_cover _ _ hS2 hidx J3Proof.pa_mem J3Proof.cover_S
    (excluded_of_ambient_card _ _ (J3Proof.centralizerIn_P3 hP) (by rw [hc]; norm_num)
      (by rw [hc]; norm_num) (by rw [hc]; norm_num))

theorem excluded_McL : ∀ y : NativeSporadic.McL, orderOf y = 2 → Excluded y := by
  refine excluded_of_mulEquiv_all (Y := ↥McLProof.P) ?e ?_
  case e => exact McLProof.mclEquivP
  have hP := McLProof.card_P
  have hS2 : IsPGroup 2 McLProof.S :=
    IsPGroup.of_card (n := 7) (by rw [McLProof.card_S]; norm_num)
  exact excluded_of_sylow_cover _ _ hS2 (McLProof.S_index_odd hP) McLProof.pa_mem
    McLProof.cover_S (excluded_of_ambient_quasisimple _ _ (McLProof.centralizerIn_P hP)
      McLProof.K_quasisimple.1)

theorem excluded_Ly : ∀ y : NativeSporadic.Ly, orderOf y = 2 → Excluded y := by
  refine excluded_of_mulEquiv_all (Y := ↥Sporadic.Ly.J) ?e ?_
  case e => exact Sporadic.Ly.lyEquivJ
  intro y hy
  obtain ⟨hCK, hq, -, -⟩ := LyProof.K_facts
  obtain ⟨hSp, hidx⟩ := LyProof.S_sylow
  obtain ⟨-, hcover⟩ := LyProof.S_facts
  have hz : Excluded LyProof.zJ := Or.inr (Or.inr (Or.inl (by rw [hCK]; exact hq)))
  have hSz : ∀ s ∈ LyProof.SJ, orderOf s = 2 → ∃ c ∈ (⊤ : Subgroup Sporadic.Ly.J),
      s = c * LyProof.zJ * c⁻¹ := by
    intro s hs hord
    have hss : s * s = 1 := by
      have := pow_orderOf_eq_one s
      rwa [hord, pow_two] at this
    have hs1 : s ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hord
      exact absurd hord (by norm_num)
    obtain ⟨c, hc⟩ := hcover s hs hss hs1
    exact ⟨c, mem_top c, hc⟩
  obtain ⟨c, -, hc⟩ := cover_of_sylow ⊤ LyProof.SJ hSp hidx LyProof.zJ hSz y (mem_top _) hy
  rw [hc]
  exact hz.conj c

theorem excluded_of_sporadic_items : ∀ s : TauCeti.SporadicName, (s = .M12 ∨ s = .M22 ∨
    s = .M23 ∨ s = .J1 ∨ s = .J2 ∨ s = .J3 ∨ s = .McL ∨ s = .Ly) →
    ∀ y : NativeSporadic.Carrier s, orderOf y = 2 → Excluded y := by
  intro s hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact excluded_M12
  · exact excluded_M22
  · exact excluded_M23
  · exact excluded_J1
  · exact excluded_J2
  · exact excluded_J3
  · exact excluded_McL
  · exact excluded_Ly

end CFSG.ComponentClassification.HSFLit
