module

public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveEndConfig
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J3
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.LyAssembly
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M22
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M23
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.McL
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitSporadicBase

public section

namespace CFSG.OddStandard

open CFSG Subgroup Blueprint CFSG.Certificates CFSG.Sporadic.Schreier CFSG.ClassicalInvolution
open CFSG.ComponentClassification.HSFLit (centralizerEquivIn)

theorem not_fiveConfig_of_mulEquiv_all {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : ∀ y : Y, orderOf y = 2 → ¬ FiveConfig y) (x : X) (hx : orderOf x = 2) :
    ¬ FiveConfig x :=
  fun hF => h (e x) (by rw [MulEquiv.orderOf_eq]; exact hx) (hF.of_mulEquiv e)

section Helpers

variable {M : Type} [Group M] (H : Subgroup M)

theorem not_fiveConfig_of_reps (reps : List M)
    (hcov : ∀ u ∈ H, orderOf u = 2 → ∃ r ∈ reps, ∃ c ∈ H, u = c * r * c⁻¹)
    (hgood : ∀ r ∈ reps, ∀ hr : r ∈ H, ¬ FiveConfig (⟨r, hr⟩ : H)) (y : H) (hy : orderOf y = 2) :
    ¬ FiveConfig y := by
  intro hF
  obtain ⟨r, hr, c, hc, hyr⟩ := hcov y y.2 (by rw [orderOf_coe]; exact hy)
  have hrH : r ∈ H := by
    have e : r = c⁻¹ * y * c := by rw [hyr]; group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hc) y.2) hc
  have h2 := hF.of_mulEquiv (MulAut.conj (⟨c, hc⟩ : H)⁻¹)
  have e2 : MulAut.conj (⟨c, hc⟩ : H)⁻¹ y = ⟨r, hrH⟩ := by
    apply Subtype.ext
    rw [MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hyr]
    group
  rw [e2] at h2
  exact hgood r hr hrH h2

theorem not_fiveConfig_of_ambient_card {r : M} (hr : r ∈ H) {K : Subgroup M}
    (hK : centralizerIn H r = K) (h1 : Nat.card K ≠ 120) (h2 : Nat.card K ≠ 240) :
    ¬ FiveConfig (⟨r, hr⟩ : H) := fun hF => by
  have h := Nat.card_congr (centralizerEquivIn H hr hK).toEquiv
  exact hF.false_of_card_ne (by rw [h]; exact h1) (by rw [h]; exact h2)

theorem not_fiveConfig_of_sylow_cover [Finite H] (S : Subgroup M) (hS : IsPGroup 2 S)
    (hidx : ¬ 2 ∣ (S.subgroupOf H).index) {r : M} (hr : r ∈ H)
    (hSr : ∀ s ∈ S, orderOf s = 2 → ∃ c ∈ H, s = c * r * c⁻¹)
    (hgood : ¬ FiveConfig (⟨r, hr⟩ : H)) (y : H) (hy : orderOf y = 2) : ¬ FiveConfig y := by
  refine not_fiveConfig_of_reps H [r] (fun u hu ho => ?_) (fun r' hr' hr'H => ?_) y hy
  · obtain ⟨c, hc, hu'⟩ := ClassicalInvolution.cover_of_sylow H S hS hidx r hSr u hu ho
    exact ⟨r, List.mem_singleton_self r, c, hc, hu'⟩
  · rw [List.mem_singleton] at hr'
    subst hr'
    exact hgood

end Helpers

theorem fiveConfig_false_M22 :
    ∀ y : NativeSporadic.M22, orderOf y = 2 → ¬ FiveConfig y := by
  obtain ⟨hcov, hcent⟩ := m22_cover_and_centralizers
  have h1 : centralizerIn m22Certificate.originalSubgroup m22Rep1 =
      m22CentQ1.originalSubgroup := hcent (m22Rep1, m22CentQ1.originalSubgroup) (by simp)
  have hc1 := m22_rep_data1.2.2.2.1
  rw [← m22Certificate_originalSubgroup]
  refine not_fiveConfig_of_reps _ [m22Rep1] ?_ ?_
  · intro u hu ho
    obtain ⟨d, hd, c, hc, hud⟩ := hcov u (by simpa using hu) ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    exact ⟨_, by simp, c, hc, hud⟩
  · intro r hr hrH
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact not_fiveConfig_of_ambient_card _ hrH h1 (by rw [hc1]; norm_num)
      (by rw [hc1]; norm_num)

theorem fiveConfig_false_M23 :
    ∀ y : NativeSporadic.M23, orderOf y = 2 → ¬ FiveConfig y := by
  obtain ⟨hcov, hcent⟩ := m23_cover_and_centralizers
  have h1 : centralizerIn m23Certificate.originalSubgroup m23Rep1 =
      m23CentQ1.originalSubgroup := hcent (m23Rep1, m23CentQ1.originalSubgroup) (by simp)
  have hc1 := m23_rep_data1.2.2.2.1
  rw [← m23Certificate_originalSubgroup]
  refine not_fiveConfig_of_reps _ [m23Rep1] ?_ ?_
  · intro u hu ho
    obtain ⟨d, hd, c, hc, hud⟩ := hcov u (by simpa using hu) ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    exact ⟨_, by simp, c, hc, hud⟩
  · intro r hr hrH
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact not_fiveConfig_of_ambient_card _ hrH h1 (by rw [hc1]; norm_num)
      (by rw [hc1]; norm_num)

theorem fiveConfig_false_J3 :
    ∀ y : NativeSporadic.J3, orderOf y = 2 → ¬ FiveConfig y := by
  refine not_fiveConfig_of_mulEquiv_all (Y := ↥J3Proof.P3) ?e ?_
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
  exact not_fiveConfig_of_sylow_cover _ _ hS2 hidx J3Proof.pa_mem J3Proof.cover_S
    (not_fiveConfig_of_ambient_card _ _ (J3Proof.centralizerIn_P3 hP) (by rw [hc]; norm_num)
      (by rw [hc]; norm_num))

theorem fiveConfig_false_McL :
    ∀ y : NativeSporadic.McL, orderOf y = 2 → ¬ FiveConfig y := by
  refine not_fiveConfig_of_mulEquiv_all (Y := ↥McLProof.P) ?e ?_
  case e => exact McLProof.mclEquivP
  have hP := McLProof.card_P
  have hS2 : IsPGroup 2 McLProof.S :=
    IsPGroup.of_card (n := 7) (by rw [McLProof.card_S]; norm_num)
  have hc := McLProof.card_K hP
  exact not_fiveConfig_of_sylow_cover _ _ hS2 (McLProof.S_index_odd hP) McLProof.pa_mem
    McLProof.cover_S (not_fiveConfig_of_ambient_card _ _ (McLProof.centralizerIn_P hP)
      (by rw [hc]; norm_num) (by rw [hc]; norm_num))

theorem fiveConfig_false_Ly :
    ∀ y : NativeSporadic.Ly, orderOf y = 2 → ¬ FiveConfig y := by
  refine not_fiveConfig_of_mulEquiv_all (Y := ↥Sporadic.Ly.J) ?e ?_
  case e => exact Sporadic.Ly.lyEquivJ
  intro y hy hF
  obtain ⟨hCK, -, -, hcardK⟩ := LyProof.K_facts
  obtain ⟨hSp, hidx⟩ := LyProof.S_sylow
  obtain ⟨-, hcover⟩ := LyProof.S_facts
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
  rw [hc] at hF
  have hz := hF.of_mulEquiv (MulAut.conj c⁻¹)
  rw [MulAut.conj_apply, inv_inv, show c⁻¹ * (c * LyProof.zJ * c⁻¹) * c = LyProof.zJ by group] at hz
  rw [← hCK] at hcardK
  exact hz.false_of_card_ne (by rw [hcardK]; norm_num) (by rw [hcardK]; norm_num)

end CFSG.OddStandard
