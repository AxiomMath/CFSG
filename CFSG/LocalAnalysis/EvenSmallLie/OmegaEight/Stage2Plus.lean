module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2PlusCheck
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Cases

public section


namespace CFSG.EvenSmallLie.OmegaEight.Stage2.Plus

open CFSG.EvenSmallLie.OmegaEight.Stage2 CFSG.EvenSmallLie.UnitarySix.YamadaPar Subgroup Matrix

theorem phiK_lt : phiK < 2 ^ 144 := by
  unfold phiK
  decide

theorem bK_lt : bK < 2 ^ 144 := by
  unfold bK
  decide

theorem phi_parts : fixCount phiK ≤ 128 ∧ imgCheckW phiK wit.imgX = true ∧
    invPair phiK phiK = true ∧
    phiK ≠ idK ∧ bK ≠ idK ∧ bK ≠ phiK ∧ mulK bK bK = idK ∧ mulK bK phiK = mulK phiK bK ∧
    commGens cGensPlus phiK = true := by
  have h := phi_check
  simp only [PlusW.phiCheck, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
    beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2,
    h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem rep_tbar : Rep phiK tbarG := rep_glOf phi_parts.2.2.1

theorem invPair_b : invPair bK bK = true := by
  simp [invPair, phi_parts.2.2.2.2.2.2.1]

@[expose] def bG : GL12 := glOf bK bK

theorem rep_b : Rep bK bG := rep_glOf invPair_b

theorem tbar_sq : tbarG * tbarG = 1 := by
  have h := phi_parts.2.2.1
  simp only [invPair, Bool.and_eq_true, beq_iff_eq] at h
  exact (rep_tbar.mul rep_tbar).unique (by rw [h.1]; exact rep_one)

theorem b_sq : bG * bG = 1 :=
  (rep_b.mul rep_b).unique (by rw [phi_parts.2.2.2.2.2.2.1]; exact rep_one)

theorem tbar_ne_one : tbarG ≠ 1 := fun e =>
  phi_parts.2.2.2.1 (rep_tbar.key_unique (e ▸ rep_one) phiK_lt idK_lt)

theorem c_parts : enumOK cGensPlus cEnumW = true ∧ cEnumW.keys.size = 40320 := by
  have h := c_check
  simp only [PlusW.cCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem tc_parts : enumOK tGensPlus tcEnumW = true ∧ tcEnumW.keys.size = 128 ∧
    gensIn tGensPlus cEnumW = true ∧
    centerCheck tGensPlus tcEnumW [idK, phiK, bK, mulK phiK bK] = true ∧
    commGens tGensPlus phiK = true ∧ commGens tGensPlus bK = true ∧
    memK tcEnumW.keys bK = true := by
  have h := tc_check
  simp only [PlusW.tcCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem u_parts : enumOK uGens uEnumW = true ∧ uEnumW.keys.size = 64 ∧ gensIn uGens tcEnumW = true ∧
    invFixCheckW uEnumW 8 wit.uB = true := by
  have h := u_check
  simp only [PlusW.uCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem c2_parts : enumOK c2Gens c2EnumW = true ∧ c2EnumW.keys.size = 384 ∧
    gensIn c2Gens cEnumW = true ∧ commGens c2Gens phiK = true ∧ commGens c2Gens bK = true ∧
    centInCheck cEnumW bK c2EnumW = true := by
  have h := c2_check
  simp only [PlusW.c2Check, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem p3_parts : enumOK p3Gens p3EnumW = true ∧ p3EnumW.keys.size = 3 ∧
    gensIn p3Gens c2EnumW = true := by
  have h := p3_check
  simp only [PlusW.p3Check, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem card_CC : Nat.card (grpOf cGensPlus) = 40320 := by
  rw [Enum.card_eq c_parts.1, c_parts.2]

theorem card_TC : Nat.card (grpOf tGensPlus) = 128 := by
  rw [Enum.card_eq tc_parts.1, tc_parts.2.1]

theorem card_U : Nat.card (grpOf uGens) = 64 := by
  rw [Enum.card_eq u_parts.1, u_parts.2.1]

theorem card_C2 : Nat.card (grpOf c2Gens) = 384 := by
  rw [Enum.card_eq c2_parts.1, c2_parts.2.1]

theorem card_P3 : Nat.card (grpOf p3Gens) = 3 := by
  rw [Enum.card_eq p3_parts.1, p3_parts.2.1]

theorem TC_le_CC : grpOf tGensPlus ≤ grpOf cGensPlus :=
  grpOf_le_of_gensIn (Enum.of_enumOK tc_parts.1).1 c_parts.1 tc_parts.2.2.1

theorem U_le_TC : grpOf uGens ≤ grpOf tGensPlus :=
  grpOf_le_of_gensIn (Enum.of_enumOK u_parts.1).1 tc_parts.1 u_parts.2.2.1

theorem C2_le_CC : grpOf c2Gens ≤ grpOf cGensPlus :=
  grpOf_le_of_gensIn (Enum.of_enumOK c2_parts.1).1 c_parts.1 c2_parts.2.2.1

theorem P3_le_C2 : grpOf p3Gens ≤ grpOf c2Gens :=
  grpOf_le_of_gensIn (Enum.of_enumOK p3_parts.1).1 c2_parts.1 p3_parts.2.2

theorem tbar_mem_TC : tbarG ∈ grpOf tGensPlus := Subgroup.subset_closure ⟨0, by decide, rfl⟩

theorem b_mem_TC : bG ∈ grpOf tGensPlus := Enum.mem_of_memK tc_parts.1 tc_parts.2.2.2.2.2.2 rep_b

theorem TC_pgroup : IsPGroup 2 (grpOf tGensPlus) := IsPGroup.of_card (n := 7) card_TC

theorem TC_max (Y : Subgroup GL12) (hY : IsPGroup 2 Y) (hTY : grpOf tGensPlus ≤ Y)
    (hYC : Y ≤ grpOf cGensPlus) : Y = grpOf tGensPlus := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hY.exists_card_eq
  have hdvd : Nat.card Y ∣ 40320 := card_CC ▸ Subgroup.card_dvd_of_le hYC
  have hk7 : k ≤ 7 := by
    by_contra hc
    have h8 : 2 ^ 8 ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega)
    rw [hk] at hdvd
    have := h8.trans hdvd
    omega
  refine (Subgroup.eq_of_le_of_card_ge hTY ?_).symm
  rw [hk, card_TC]
  calc 2 ^ k ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) hk7
    _ = 128 := by norm_num

theorem modelFacts : ModelFacts modelPlus where
  card_fixM_tbar := by
    show Nat.card (fixM (tbarG : Mat12)) ≤ 2 ^ 7
    rw [← rep_tbar, card_fixM_eq]
    exact phi_parts.1
  exists_of_fixM_tbar := by
    intro v hv
    change (tbarG : Mat12) *ᵥ v = v at hv
    show ∃ x : Vec12, (tbarG : Mat12) *ᵥ x + x = v
    rw [← rep_tbar] at hv ⊢
    exact exists_of_imgCheckW phi_parts.2.1 hv
  offender_m2 := by
    intro E hE hsq hne
    refine offender_bound tc_parts.1 (fun v hv hfix => ?_) m2_check hE hsq hne
    refine List.mem_filter.2 ⟨List.mem_range.2 hv, ?_⟩
    have h1 : toVec 12 (mulVecK phiK v) = toVec 12 v := by
      rw [toVec_mulVecK, rep_tbar]
      exact hfix
    rw [toVec_injOn (mulVecK_lt _ _) hv h1, beq_self_eq_true]

@[expose] def caseData : CaseData := ⟨bG, grpOf c2Gens, grpOf p3Gens⟩

theorem commute_tbar_TC {x : GL12} (hx : x ∈ grpOf tGensPlus) : tbarG * x = x * tbarG :=
  commute_of_commGens (Enum.of_enumOK tc_parts.1).1 rep_tbar tc_parts.2.2.2.2.1 x hx

theorem commute_b_TC {x : GL12} (hx : x ∈ grpOf tGensPlus) : bG * x = x * bG :=
  commute_of_commGens (Enum.of_enumOK tc_parts.1).1 rep_b tc_parts.2.2.2.2.2.1 x hx

theorem tbar_b_comm : bG * tbarG = tbarG * bG := commute_b_TC tbar_mem_TC

theorem caseFacts : CaseFacts modelPlus caseData where
  tbar_sq := tbar_sq
  tbar_ne_one := tbar_ne_one
  b_sq := b_sq
  b_ne_one := fun e => phi_parts.2.2.2.2.1
    (rep_b.key_unique (show Rep idK bG from (show bG = 1 from e) ▸ rep_one) bK_lt idK_lt)
  b_ne_tbar := fun e => phi_parts.2.2.2.2.2.1
    (rep_b.key_unique (show Rep phiK bG from (show bG = tbarG from e) ▸ rep_tbar) bK_lt phiK_lt)
  b_comm := tbar_b_comm
  tbar_mem_TC := tbar_mem_TC
  TC_le_CC := TC_le_CC
  TC_pgroup := TC_pgroup
  TC_max := TC_max
  tbar_central := fun _ hx => commute_tbar_TC hx
  b_central := fun _ hx => commute_b_TC hx
  b_mem_TC := b_mem_TC
  center := by
    intro z hz hc
    obtain ⟨k, hk, hr⟩ := exists_of_centerCheck tc_parts.1 tc_parts.2.2.2.1 hz hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact Or.inl (hr.unique rep_one)
    · exact Or.inr (Or.inl (hr.unique rep_tbar))
    · exact Or.inr (Or.inr (Or.inl (hr.unique rep_b)))
    · exact Or.inr (Or.inr (Or.inr (hr.unique (rep_tbar.mul rep_b))))
  C2_le := C2_le_CC
  C2_comm := by
    intro c hc
    exact ⟨(commute_of_commGens (Enum.of_enumOK c2_parts.1).1 rep_tbar c2_parts.2.2.2.1 c
      hc).symm, (commute_of_commGens (Enum.of_enumOK c2_parts.1).1 rep_b
      c2_parts.2.2.2.2.1 c hc).symm⟩
  C2_ge := fun c hc hcb => mem_of_centInCheck c_parts.1 c2_parts.1 c2_parts.2.2.2.2.2 hc rep_b hcb
  P3_le := P3_le_C2
  P3_pgroup := IsPGroup.of_card (n := 1) (show Nat.card (grpOf p3Gens) = 3 ^ 1 by
    rw [card_P3]; norm_num)
  P3_index := by
    have h := Subgroup.card_mul_index ((grpOf p3Gens).subgroupOf (grpOf c2Gens))
    have hc : Nat.card ((grpOf p3Gens).subgroupOf (grpOf c2Gens)) = 3 := by
      rw [← card_P3]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe P3_le_C2).toEquiv
    rw [hc, card_C2] at h
    have : ((grpOf p3Gens).subgroupOf (grpOf c2Gens)).index = 128 := by omega
    show ¬ 3 ∣ ((grpOf p3Gens).subgroupOf (grpOf c2Gens)).index
    rw [this]
    norm_num
  card_C2_dvd := by
    show Nat.card (grpOf c2Gens) ∣ 2 ^ 7 * 9
    rw [card_C2]
    norm_num

section Branches

variable {G : Type*} [Group G] {t : G} {TH W : Subgroup G}
  {φ : W ≃* Multiplicative (Fin 12 → ZMod 2)}

theorem genG_append_left {xs ys : Array (ℕ × ℕ)} {j : ℕ} (hj : j < xs.size) :
    genG (xs ++ ys) j = genG xs j := by
  simp only [genG, genK, Array.getD_eq_getD_getElem?, Array.getElem?_append_left hj]

theorem genG_append_right {xs ys : Array (ℕ × ℕ)} {j : ℕ} (hj : xs.size ≤ j) :
    genG (xs ++ ys) j = genG ys (j - xs.size) := by
  simp only [genG, genK, Array.getD_eq_getD_getElem?, Array.getElem?_append_right hj]

theorem base_mem_X (h : Stage2Hyp modelPlus t TH W φ) {i : ℕ}
    (hr : glOf (reps.getD i (idK, idK)).1 (reps.getD i (idK, idK)).2 ∈ Xof W φ) :
    ∀ j < (base i).size, genG (base i) j ∈ Xof W φ := by
  intro j hj
  have hC : ∀ k < cGensPlus.size, genG cGensPlus k ∈ Xof W φ := fun k hk =>
    h.CC_le_X (genG_mem_grpOf hk)
  have hT : ∀ k < tGensPlus.size, genG tGensPlus k ∈ Xof W φ := fun k hk =>
    h.TC_le_X (genG_mem_grpOf hk)
  unfold base at hj ⊢
  by_cases h1 : j < (cGensPlus ++ tGensPlus).size
  · rw [genG_append_left h1]
    by_cases h2 : j < cGensPlus.size
    · rw [genG_append_left h2]
      exact hC j h2
    · rw [genG_append_right (by omega)]
      exact hT _ (by simp only [Array.size_append] at h1; omega)
  · rw [genG_append_right (by omega)]
    have h3 : j - (cGensPlus ++ tGensPlus).size = 0 := by
      simp only [Array.size_append, List.size_toArray, List.length_cons,
        List.length_nil] at hj h1 ⊢
      omega
    rw [h3]
    exact hr

theorem false_of_bray (h : Stage2Hyp modelPlus t TH W φ) {i : ℕ}
    (hr : glOf (reps.getD i (idK, idK)).1 (reps.getD i (idK, idK)).2 ∈ Xof W φ)
    {prog : List (ℕ × ℕ × ℕ)} {out : ℕ} (hb : brayCheck (base i) prog out phiK cEnumW = true) :
    False := by
  obtain ⟨z, hzX, hzt, hzC⟩ := exists_of_brayCheck c_parts.1 hb (base_mem_X h hr) rep_tbar
  exact hzC (h.mem_CC_of_commute hzX hzt)

theorem relIndex_of_card {Y S : Subgroup GL12} (hYS : Y ≤ S) {a : ℕ} (hY : Nat.card Y = a)
    (hS : Nat.card S = 2 * a) (ha : 0 < a) : Y.relIndex S = 2 := by
  have h := Subgroup.relIndex_mul_card (H := Y) (K := S)
  rw [inf_of_le_left hYS, hY, hS] at h
  exact Nat.eq_of_mul_eq_mul_right ha h

theorem false_of_sbar [Finite G] (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (h : Stage2Hyp modelPlus t TH W φ) {i : ℕ}
    (hr : glOf (reps.getD i (idK, idK)).1 (reps.getD i (idK, idK)).2 ∈ Xof W φ)
    {prog : List (ℕ × ℕ × ℕ)} {outs : List ℕ} {mG : Array (ℕ × ℕ)} {sE mE : Enum}
    {sB : ℕ → List ℕ} {sY : ℕ → ℕ}
    (hs : (gensOK (base i) && gensOK (slpGens (base i) prog outs) &&
      enumOK (slpGens (base i) prog outs) sE && sE.keys.size == 8192 &&
      gensIn tGensPlus sE && oneClassCheckW sE phiK sB sY && enumOK mG mE && mE.keys.size == 4096 &&
      gensIn mG sE && !(mE.keys.contains phiK)) = true) : False := by
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hb, hg⟩, hsE⟩, hsz⟩, hTS⟩, hcls⟩, hmE⟩, hmz⟩, hMS⟩, hnt⟩ := hs
  have hcardS : Nat.card (grpOf (slpGens (base i) prog outs)) = 8192 := by
    rw [Enum.card_eq hsE, hsz]
  have hcardM : Nat.card (grpOf mG) = 4096 := by rw [Enum.card_eq hmE, hmz]
  have hYS : grpOf mG ≤ grpOf (slpGens (base i) prog outs) :=
    grpOf_le_of_gensIn (Enum.of_enumOK hmE).1 hsE hMS
  refine h.false_of_oneClass hG hnab modelFacts (S := grpOf (slpGens (base i) prog outs))
    (Y := grpOf mG) (grpOf_slpGens_le hb (base_mem_X h hr) hg)
    (IsPGroup.of_card (n := 13) (by rw [hcardS]; norm_num))
    (grpOf_le_of_gensIn (Enum.of_enumOK tc_parts.1).1 hsE hTS)
    (fun s hs hs2 hfix => conj_of_oneClassCheckW hsE hcls rep_tbar hs hs2 hfix) hYS
    (relIndex_of_card hYS hcardM (by rw [hcardS]) (by norm_num))
    (Enum.not_mem hmE phiK_lt rep_tbar hnt)

theorem false_of_degenerate [Finite G] (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (h : Stage2Hyp modelPlus t TH W φ)
    (hdeg : ∀ Z : Subgroup GL12, Z ≤ Xof W φ → IsPGroup 2 Z → modelPlus.TC ≤ Z →
      Z = modelPlus.TC) : False :=
  h.false_of_offender hG hnab modelFacts h.TC_le_X TC_pgroup le_rfl hdeg
    (fun A hA hsq hne => offender_bound tc_parts.1 (fun v hv _ => List.mem_range.2 hv) off_check
      hA hsq hne)
    (relIndex_of_card U_le_TC card_U (show Nat.card (grpOf tGensPlus) = 2 * 64 by rw [card_TC])
      (by norm_num))
    (fun y hy hy2 => fix_of_invFixCheckW u_parts.1 u_parts.2.2.2 hy hy2)

theorem key_eq_of_conj {m p q : GL12} {pK qK : ℕ} (hp : Rep pK p) (hq : Rep qK q)
    (h : m * q * m⁻¹ = p) : mulK pK (keyOfMat m) = mulK (keyOfMat m) qK := by
  have e : p * m = m * q := by rw [← h]; group
  exact (hp.mul (rep_keyOfMat m)).key_unique (e ▸ (rep_keyOfMat m).mul hq) (mulK_lt _ _)
    (mulK_lt _ _)

theorem gen_P3_ne_one : genG p3Gens 0 ≠ 1 := by
  intro e
  have hle : grpOf p3Gens ≤ ⊥ := by
    rw [grpOf, Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    have hj0 : j = 0 := by
      have : p3Gens.size = 1 := rfl
      omega
    subst hj0
    rw [e]
    exact one_mem _
  have := card_P3
  rw [le_bot_iff.1 hle, Subgroup.card_bot] at this
  omega

theorem exists_rep {m : GL12}
    (hcase : CaseI modelPlus caseData.b m ∨ CaseII modelPlus caseData.b m)
    (hP3 : ∀ y ∈ caseData.P3, m * y * m⁻¹ ∈ caseData.P3) (hm2 : m * m ∈ caseData.C2)
    (hm256 : m ^ 256 = 1) (hC2 : ∀ c ∈ caseData.C2, m * c * m⁻¹ ∈ caseData.C2) :
    ∃ r ∈ reps, (glOf r.1 r.2)⁻¹ * m ∈ grpOf cGensPlus := by
  have hc := cand_check
  simp only [PlusW.candChk, Bool.and_eq_true] at hc
  obtain ⟨⟨hcand, hreps⟩, hsamp⟩ := hc
  have hyP3 : genG p3Gens 0 ∈ grpOf p3Gens := genG_mem_grpOf (by decide)
  have hzP3 := hP3 _ hyP3
  obtain ⟨i, hi, hzr⟩ := Enum.exists_key p3_parts.1 hzP3
  have hz1 : p3EnumW.keys.getD i 0 ≠ idK := by
    intro e
    rw [e] at hzr
    have h1 : m * genG p3Gens 0 * m⁻¹ = 1 := hzr.unique rep_one
    apply gen_P3_ne_one
    calc genG p3Gens 0 = m⁻¹ * (m * genG p3Gens 0 * m⁻¹) * m := by group
      _ = 1 := by rw [h1]; group
  have hzs : [p3EnumW.keys.getD i 0] ∈ PlusW.tuples wit := by
    refine List.mem_map.2 ⟨_, List.mem_filter.2 ⟨?_, by simpa using hz1⟩, rfl⟩
    rw [getD_mem hi]
    exact Array.getElem_mem_toList hi
  obtain ⟨b, hb, hbz⟩ := List.mem_iff_getElem.1 hzs
  have hbz' : (PlusW.tuples wit).getD b [] = [p3EnumW.keys.getD i 0] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb, Option.getD_some, hbz]
  have hys : ys = [(genK p3Gens 0).1] := rfl
  have hy := rep_genG (Enum.of_enumOK p3_parts.1).1 0
  have hz := key_eq_of_conj hzr hy rfl
  have hc0 : cases.getD 0 [] = [(mulK phiK bK, phiK), (bK, bK)] := rfl
  have hc1 : cases.getD 1 [] = [(bK, phiK), (phiK, bK)] := rfl
  rcases hcase with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · refine exists_rep_of_candCheckW c_parts.1 c2_parts.1 (by rw [c2_parts.2.1]; norm_num) hcand
      hreps hsamp (a := 0) (by decide) hb ?_ hm2 hm256 hC2
    intro c hc
    rw [hbz', hc0, candCons, hys] at hc
    simp only [List.zipWith_cons_cons, List.zipWith_nil_left, List.nil_append, List.cons_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hz
    · exact key_eq_of_conj (rep_tbar.mul rep_b) rep_tbar e1
    · exact key_eq_of_conj rep_b rep_b e2
  · refine exists_rep_of_candCheckW c_parts.1 c2_parts.1 (by rw [c2_parts.2.1]; norm_num) hcand
      hreps hsamp (a := 1) (by decide) hb ?_ hm2 hm256 hC2
    intro c hc
    rw [hbz', hc1, candCons, hys] at hc
    simp only [List.zipWith_cons_cons, List.zipWith_nil_left, List.nil_append, List.cons_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hz
    · exact key_eq_of_conj rep_b rep_tbar e1
    · exact key_eq_of_conj rep_tbar rep_b e2

theorem false_of_stage2Hyp [Finite G] (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (h : Stage2Hyp modelPlus t TH W φ) : False := by
  rcases h.degenerate_or_exists caseFacts with hdeg | ⟨m, hmX, hcase, hP3, hm2, hm256, hC2⟩
  · exact false_of_degenerate hG hnab h hdeg
  obtain ⟨r, hr, hrC⟩ := exists_rep hcase hP3 hm2 hm256 hC2
  have hrX : glOf r.1 r.2 ∈ Xof W φ := by
    have h1 : (glOf r.1 r.2)⁻¹ * m ∈ Xof W φ := h.CC_le_X hrC
    have e : glOf r.1 r.2 = m * ((glOf r.1 r.2)⁻¹ * m)⁻¹ := by group
    rw [e]
    exact (Xof W φ).mul_mem hmX ((Xof W φ).inv_mem h1)
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hr
  have hri : reps.getD i (idK, idK) = reps[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  rw [← hri] at hrX
  have hlen : reps.length = 8 := rfl
  have hi8 : i < 8 := hlen ▸ hi
  interval_cases i
  · exact false_of_bray h hrX bray_check0
  · exact false_of_bray h hrX bray_check1
  · exact false_of_bray h hrX bray_check2
  · exact false_of_bray h hrX bray_check3
  · exact false_of_sbar hG hnab h hrX s_check4
  · exact false_of_sbar hG hnab h hrX s_check5
  · exact false_of_bray h hrX bray_check6
  · exact false_of_bray h hrX bray_check7

end Branches

end CFSG.EvenSmallLie.OmegaEight.Stage2.Plus
