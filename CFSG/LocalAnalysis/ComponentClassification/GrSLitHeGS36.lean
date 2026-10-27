module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeGSGen
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHe36Check

public noncomputable section

namespace CFSG.ComponentClassification.GrSLit.HeGS

open CFSG Subgroup CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.Sporadic.HeldB CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CFSG.Monster.B.Co2
  CFSG.ComponentClassification.GrSLit.HeldFix CFSG.ComponentClassification.UnbalancedGS

@[expose] def heGS36C : Equiv.Perm (Fin 8330) :=
  (heGenPerm 1 * heGSKW (heDWords.getD 1 []) * (heGenPerm 1)⁻¹ * heT1P) ^ 8 * heGenPerm 1

@[expose] def heGS36W1 : Equiv.Perm (Fin 8330) := heGS36C * heGenPerm 0 * heGS36C⁻¹

@[expose] def heGS36W2 : Equiv.Perm (Fin 8330) := heGS36W1 * heT1P

theorem rep_heGS36Pow {t : Tab} {g : Equiv.Perm (Fin 8330)} (h : Rep 8330 t g) :
    ∀ k : ℕ, Rep 8330 (heGS36Pow t k) (g ^ k)
  | 0 => by rw [heGS36Pow, pow_zero]; exact rep_idTab
  | k + 1 => by rw [heGS36Pow, pow_succ']; exact rep_comp h (rep_heGS36Pow h k)

theorem heGS36D_lt : ∀ p < 4, ∀ j < 4, ∀ i ∈ heGS36D p j, i < 9 := by decide

theorem hfCW_heGS36Word_split (p : ℕ) : hfCW (heGS36Word p) =
    hfCW (heGS36D p 0) * hfCW heGSXWord ^ (3 + p / 2) * hfCW (heGS36D p 1) *
      (hfCW (heGS36D p 2) * hfCW heGSXWord ^ (3 + p / 2) * hfCW (heGS36D p 3)) := by
  simp only [heGS36Word, hfCW_append, hfCW_rep, mul_assoc]

section Conj


theorem heGS36C_mem : heGS36C ∈ heP := by
  have h1 := heGenPerm_mem (k := 1) (by norm_num)
  have he := (mem_centralizerIn.mp (heGSKW_mem (heDWords_lt 1))).1
  exact mul_mem (pow_mem (mul_mem (mul_mem (mul_mem h1 he) (inv_mem h1)) heT1P_mem) 8) h1

theorem rep_heGS36C : Rep 8330 heGS36CTab heGS36C := by
  have ha1 := rep_heGen (k := 1) (by norm_num)
  have ha1i := rep_heGen_inv (k := 1) (by norm_num)
  have he1 := (tabRep_heGSKTab (heDWords_lt 1)).2
  rw [heGS36CTab, heGS36C]
  exact rep_comp (rep_heGS36Pow (rep_comp (rep_comp (rep_comp ha1 he1) ha1i) rep_heT1) 8) ha1

theorem heGSKW_one_comm :
    heGSKW (heDWords.getD 1 []) * heGenPerm 0 = heGenPerm 0 * heGSKW (heDWords.getD 1 []) :=
  (mem_centralizerIn.mp (heGSKW_mem (heDWords_lt 1))).2

theorem gsFixedLayer_w1 :
    gsFixedLayer heP heGS36W1 = heK0.map (MulAut.conj heGS36C).toMonoidHom :=
  HeLay.gsFixedLayer_conj heGS36C_mem (heGenPerm 0)


theorem rep_heGS36C_inv :
    Rep 8330 (CFSG.Monster.B.Co2.Native.invCand 8330 heGS36CTab) heGS36C⁻¹ := by
  have h := permChk_spec heGS36_check.2.1
  rw [h.1.unique rep_heGS36C] at h
  exact h.2

theorem heGS36C_conj : heGS36C * heGSKW (heDWords.getD 1 []) * heGS36C⁻¹ = heT1P := by
  have h1 := rep_comp rep_heGS36C (tabRep_heGSKTab (heDWords_lt 1)).2
  have h2 := rep_comp rep_heT1 rep_heGS36C
  rw [heGS36_check.1] at h1
  rw [h1.unique h2, mul_inv_cancel_right]

theorem tabRep_heGS36W1 : TabRep heGS36W1Tab heGS36W1 :=
  tabRep_comp_of_rep (rep_comp rep_heGS36C (rep_heGen (k := 0) (by norm_num))) rep_heGS36C_inv

theorem tabRep_heGS36W2 : TabRep heGS36W2Tab heGS36W2 :=
  tabRep_comp_of_rep tabRep_heGS36W1.2 rep_heT1

theorem heGS36W1_mem : heGS36W1 ∈ centralizerIn heP heT1P := by
  refine mem_centralizerIn.mpr ⟨mul_mem (mul_mem heGS36C_mem (heGenPerm_mem (by norm_num)))
    (inv_mem heGS36C_mem), ?_⟩
  rw [heGS36W1, ← heGS36C_conj]
  calc heGS36C * heGenPerm 0 * heGS36C⁻¹ * (heGS36C * heGSKW (heDWords.getD 1 []) * heGS36C⁻¹)
      = heGS36C * (heGSKW (heDWords.getD 1 []) * heGenPerm 0)⁻¹⁻¹ * heGS36C⁻¹ := by
        rw [heGSKW_one_comm]; group
    _ = heGS36C * heGSKW (heDWords.getD 1 []) * heGS36C⁻¹ *
        (heGS36C * heGenPerm 0 * heGS36C⁻¹) := by group

theorem heGS36W2_mem : heGS36W2 ∈ centralizerIn heP heT1P :=
  mul_mem heGS36W1_mem (mem_centralizerIn.mpr ⟨heT1P_mem, rfl⟩)

theorem heGS36W2_eq : heGS36W2 = heGS36C * (heGSV : Equiv.Perm (Fin 8330)) * heGS36C⁻¹ := by
  have hv : (heGSV : Equiv.Perm (Fin 8330)) = heGenPerm 0 * heGSKW (heDWords.getD 1 []) := rfl
  rw [heGS36W2, heGS36W1, hv, ← heGS36C_conj]
  group

theorem gsFixedLayer_w2 : gsFixedLayer heP heGS36W2 =
    (gsFixedLayer heP (heGSV : Equiv.Perm (Fin 8330))).map (MulAut.conj heGS36C).toMonoidHom := by
  rw [heGS36W2_eq]
  exact HeLay.gsFixedLayer_conj heGS36C_mem _


theorem heGS36W2_mem_conjClass : heGS36W2 ∈ Sporadic.Schreier.conjClass heP (heGenPerm 0) := by
  refine ⟨heGS36C * heGSG, mul_mem heGS36C_mem heGSG_mem, ?_⟩
  rw [heGS36W2_eq, ← heGSG_conj, mul_inv_rev]
  group

end Conj

theorem hfCW_heGS36Word_mem
    {N : Subgroup (Equiv.Perm (Fin 8330))}
    (hNle : N ≤ centralizerIn heP heT1P) (hNn : (N.subgroupOf (centralizerIn heP heT1P)).Normal)
    {p : ℕ} (hp : p < 4) (hx : hfCW heGSXWord ^ (3 + p / 2) ∈ N) :
    hfCW (heGS36Word p) ∈ N := by
  obtain ⟨h01, h23, -⟩ := heGS36_check.2.2.1 p hp
  have hD := heGS36D_lt p hp
  have hinv : ∀ a b : ℕ, a < 4 → b < 4 → hfCTab (heGS36D p a ++ heGS36D p b) = idTab 8330 →
      hfCW (heGS36D p b) = (hfCW (heGS36D p a))⁻¹ := by
    intro a b ha hb h
    have hab : ∀ j ∈ heGS36D p a ++ heGS36D p b, j < 9 :=
      List.forall_mem_append.mpr ⟨hD a ha, hD b hb⟩
    have h1 := ((tabRep_hfCTab hab).eq_iff TabRep.idTab).1 h
    rw [hfCW_append] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hconj : ∀ a : ℕ, a < 4 →
      hfCW (heGS36D p a) * hfCW heGSXWord ^ (3 + p / 2) * (hfCW (heGS36D p a))⁻¹ ∈ N := by
    intro a ha
    have h1 := hNn.conj_mem ⟨_, hNle hx⟩ (mem_subgroupOf.mpr hx) ⟨_, hfCW_mem_C1 (hD a ha)⟩
    exact mem_subgroupOf.mp h1
  rw [hfCW_heGS36Word_split, hinv 0 1 (by norm_num) (by norm_num) h01,
    hinv 2 3 (by norm_num) (by norm_num) h23]
  exact mul_mem (hconj 0 (by norm_num)) (hconj 2 (by norm_num))

theorem hfCW_heGS36Word
    {p : ℕ} (hp : p < 4) :
    hfCW (heGS36Word p) = if p % 2 = 0 then heGS36W1 else heGS36W2 := by
  have hD := heGS36D_lt p hp
  have hR := lt_of_mem_hfRep heGSXWord_lt (3 + p / 2)
  have hlt : ∀ j ∈ heGS36Word p, j < 9 := by
    simp only [heGS36Word, List.forall_mem_append]
    exact ⟨⟨⟨⟨⟨hD 0 (by norm_num), hR⟩, hD 1 (by norm_num)⟩, hD 2 (by norm_num)⟩, hR⟩,
      hD 3 (by norm_num)⟩
  have hT : TabRep (heGS36Target p) (if p % 2 = 0 then heGS36W1 else heGS36W2) := by
    unfold heGS36Target
    split_ifs
    · exact tabRep_heGS36W1
    · exact tabRep_heGS36W2
  rw [← (heGS36_check.2.2.1 p hp).2.2] at hT
  exact (tabRep_hfCTab hlt).perm_eq hT

section Facts


theorem sup_gsFixedLayer_w : gsFixedLayer heP heGS36W1 ⊔ gsFixedLayer heP heGS36W2 = heP := by
  rw [gsFixedLayer_w1, gsFixedLayer_w2, ← Subgroup.map_sup, sup_gsFixedLayer_v]
  exact mem_normalizer_iff_map_conj_eq.mp (le_normalizer heGS36C_mem)

theorem heGSKW_zero_mem : heGSKW (heDWords.getD 0 []) ∈ heK0 :=
  mem_heK0_of_rho0_mem (x := heGSE 0) (by rw [rho0_heGSE]; exact heDPerm_mem_D (by norm_num))

theorem heT1P_not_mem_centralizer_w1 :
    heT1P ∉ centralizer (gsFixedLayer heP heGS36W1 : Set (Equiv.Perm (Fin 8330))) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hnc, -⟩ := heGS_layer_check
  have hE0T := tabRep_heGSKTab (heDWords_lt 0)
  have hE1T := tabRep_heGSKTab (heDWords_lt 1)
  intro h
  apply hnc
  rw [(hE0T.comp hE1T).eq_iff (hE1T.comp hE0T)]
  have hmem : heGS36C * heGSKW (heDWords.getD 0 []) * heGS36C⁻¹ ∈ gsFixedLayer heP heGS36W1 := by
    rw [gsFixedLayer_w1]
    exact ⟨_, heGSKW_zero_mem, rfl⟩
  have h1 := mem_centralizer_iff.mp h _ hmem
  rw [← heGS36C_conj] at h1
  have h2 : heGS36C * (heGSKW (heDWords.getD 0 []) * heGSKW (heDWords.getD 1 [])) * heGS36C⁻¹ =
      heGS36C * (heGSKW (heDWords.getD 1 []) * heGSKW (heDWords.getD 0 [])) * heGS36C⁻¹ := by
    calc _ = heGS36C * heGSKW (heDWords.getD 0 []) * heGS36C⁻¹ *
          (heGS36C * heGSKW (heDWords.getD 1 []) * heGS36C⁻¹) := by group
      _ = _ := h1
      _ = _ := by group
  exact mul_left_cancel (mul_right_cancel h2)

theorem heT1P_not_mem_centralizer_w2 :
    heT1P ∉ centralizer (gsFixedLayer heP heGS36W2 : Set (Equiv.Perm (Fin 8330))) := by
  have hnc := heGS36_check.2.2.2.1
  have hE0T := tabRep_heGSKTab (heDWords_lt 0)
  have hE1T := tabRep_heGSKTab (heDWords_lt 1)
  have hG : TabRep heGSInit[5]!.1 (heGSG * heGSKW (heDWords.getD 0 []) * heGSG⁻¹) := by
    rw [heGSInit_get_ge (k := 5) (by norm_num) (by norm_num), show (5 : ℕ) % 5 = 0 from rfl]
    dsimp only
    exact tabRep_comp_of_rep (rep_comp rep_heGSG hE0T.2) rep_heGSG_inv
  intro h
  apply hnc
  rw [(hE1T.comp hG).eq_iff (hG.comp hE1T)]
  set y := heGSG * heGSKW (heDWords.getD 0 []) * heGSG⁻¹ with hy
  have hmem : heGS36C * y * heGS36C⁻¹ ∈ gsFixedLayer heP heGS36W2 := by
    rw [gsFixedLayer_w2, gsFixedLayer_v]
    exact ⟨y, ⟨_, heGSKW_zero_mem, rfl⟩, rfl⟩
  have h1 := mem_centralizer_iff.mp h _ hmem
  rw [← heGS36C_conj] at h1
  have h2 : heGS36C * (heGSKW (heDWords.getD 1 []) * y) * heGS36C⁻¹ =
      heGS36C * (y * heGSKW (heDWords.getD 1 [])) * heGS36C⁻¹ := by
    calc _ = heGS36C * heGSKW (heDWords.getD 1 []) * heGS36C⁻¹ *
          (heGS36C * y * heGS36C⁻¹) := by group
      _ = _ := h1.symm
      _ = _ := by group
  exact mul_left_cancel (mul_right_cancel h2)

theorem heldTwoBTwelveModel :
    HeldTwoBTwelveModel := by
  refine ⟨hfCW heGSXWord, hfCW_mem_C1 heGSXWord_lt, heGSX_pow, heGS36W1, heGS36W1_mem, heGS36W2,
    heGS36W2_mem, ⟨heGS36C, heGS36C_mem, rfl⟩, heGS36W2_mem_conjClass, ?_,
    heT1P_not_mem_centralizer_w1, heT1P_not_mem_centralizer_w2, sup_gsFixedLayer_w⟩
  intro N hNle hNn hx
  have hw : ∀ p < 4, hfCW heGSXWord ^ (3 + p / 2) ∈ N →
      (if p % 2 = 0 then heGS36W1 else heGS36W2) ∈ N := fun p hp h => by
    rw [← hfCW_heGS36Word hp]
    exact hfCW_heGS36Word_mem hNle hNn hp h
  rcases hx with h4 | h3
  · exact ⟨hw 2 (by norm_num) h4, hw 3 (by norm_num) h4⟩
  · exact ⟨hw 0 (by norm_num) h3, hw 1 (by norm_num) h3⟩

theorem heldTwoAFourModel : HeldTwoAFourModel := by
  obtain ⟨-, -, -, -, hu1, hut, -⟩ := heGS_layer_check
  have hU := tabRep_heGSKTab (heGSComm2_lt heGSUComm)
  refine ⟨heGenPerm 0, mem_map_of_mem _ heGST0_mem_layer, (heGSU : Equiv.Perm (Fin 8330)),
    mem_map_of_mem _ heGSU_mem_layer, heGenPerm0_sq, ?_, heA0_ne_one, ?_, ?_, ?_⟩
  · rw [coe_heGSU]
    exact ((hU.comp hU).eq_iff TabRep.idTab).1 heGS36_check.2.2.2.2
  · intro h
    exact hu1 ((hU.eq_iff TabRep.idTab).2 (by rw [← coe_heGSU]; exact h))
  · intro h
    exact hut ((hU.eq_iff tabRep_heGen0).2 (by rw [← coe_heGSU]; exact h.symm))
  · exact congrArg Subtype.val (ker_comm heGST0_mem_ker heGSU_mem_ker)

end Facts

end CFSG.ComponentClassification.GrSLit.HeGS
