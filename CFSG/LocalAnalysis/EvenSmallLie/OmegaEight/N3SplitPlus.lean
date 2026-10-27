module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitPlusCheck
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitCases
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitNC
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitBasic

public section


namespace CFSG.EvenSmallLie.OmegaEight.N3Split.Plus

open CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Stage2
open CFSG.EvenSmallLie.UnitarySix.YamadaPar Subgroup Matrix

theorem phiK_lt : phiK < 2 ^ 144 := by
  unfold phiK
  decide

theorem phi_parts : fixCount phiK = 64 ∧ imgCheckW phiK wit.imgX = true ∧
    invPair phiK phiK = true ∧
    phiK ≠ idK ∧ bK ≠ idK ∧ bK ≠ phiK ∧ mulK bK bK = idK ∧ mulK bK phiK = mulK phiK bK ∧
    commGens cGens phiK = true := by
  have h := phi_check
  simp only [PlusW.phiCheck, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
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

theorem bK_lt : bK < 2 ^ 144 := by
  unfold bK
  decide

theorem m2_roots : allRoots 256 (invsOf tcEnumW.keys)
    ((List.range 4096).filter fun v => mulVecK phiK v == v) = true := by
  rw [← allRootsF_eq fun v hv => List.mem_range.1 (List.mem_filter.1 hv).1]
  exact m2_check

theorem off_roots : allRoots 2048 (invsOf tcEnumW.keys) (List.range 4096) = true := by
  rw [← allRootsF_eq fun v hv => List.mem_range.1 hv]
  exact off_check


theorem c_parts : enumOK cGens cEnumW = true ∧ cEnumW.keys.size = 80640 := by
  have h := c_check
  simp only [PlusW.cCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem tc_parts : enumOK tGens tcEnumW = true ∧ tcEnumW.keys.size = 256 ∧
    gensIn tGens cEnumW = true ∧
    centerCheck tGens tcEnumW [idK, phiK, bK, mulK phiK bK] = true ∧
    commGens tGens phiK = true ∧ commGens tGens bK = true ∧ memK tcEnumW.keys bK = true := by
  have h := tc_check
  simp only [PlusW.tcCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem uk_parts : enumOK ukGens ukEnumW = true ∧ ukEnumW.keys.size = 128 ∧
    gensIn ukGens tcEnumW = true ∧ avoidCheck tcEnumW ukEnumW = true := by
  have h := uk_check
  simp only [PlusW.ukCheck, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem c2_parts : enumOK c2Gens c2EnumW = true ∧ c2EnumW.keys.size = 768 ∧
    gensIn c2Gens cEnumW = true ∧ commGens c2Gens phiK = true ∧ commGens c2Gens bK = true ∧
    centInCheck cEnumW bK c2EnumW = true ∧
    (c2EnumW.keys.all fun c => fpowK c 1152 == idK) = true := by
  have h := c2_check
  simp only [PlusW.c2Check, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem p3_parts : enumOK p3Gens p3EnumW = true ∧ p3EnumW.keys.size = 3 ∧
    gensIn p3Gens c2EnumW = true := by
  have h := p3_check
  simp only [PlusW.p3Check, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem card_CC : Nat.card (grpOf cGens) = 80640 := by
  rw [Enum.card_eq c_parts.1, c_parts.2]

theorem card_TC : Nat.card (grpOf tGens) = 256 := by
  rw [Enum.card_eq tc_parts.1, tc_parts.2.1]

theorem card_UK : Nat.card (grpOf ukGens) = 128 := by
  rw [Enum.card_eq uk_parts.1, uk_parts.2.1]

theorem card_C2 : Nat.card (grpOf c2Gens) = 768 := by
  rw [Enum.card_eq c2_parts.1, c2_parts.2.1]

theorem card_P3 : Nat.card (grpOf p3Gens) = 3 := by
  rw [Enum.card_eq p3_parts.1, p3_parts.2.1]

theorem TC_le_CC : grpOf tGens ≤ grpOf cGens :=
  grpOf_le_of_gensIn (Enum.of_enumOK tc_parts.1).1 c_parts.1 tc_parts.2.2.1

theorem UK_le_TC : grpOf ukGens ≤ grpOf tGens :=
  grpOf_le_of_gensIn (Enum.of_enumOK uk_parts.1).1 tc_parts.1 uk_parts.2.2.1

theorem C2_le_CC : grpOf c2Gens ≤ grpOf cGens :=
  grpOf_le_of_gensIn (Enum.of_enumOK c2_parts.1).1 c_parts.1 c2_parts.2.2.1

theorem P3_le_C2 : grpOf p3Gens ≤ grpOf c2Gens :=
  grpOf_le_of_gensIn (Enum.of_enumOK p3_parts.1).1 c2_parts.1 p3_parts.2.2

theorem tbar_mem_TC : tbarG ∈ grpOf tGens := Subgroup.subset_closure ⟨0, by decide, rfl⟩

theorem b_mem_TC : bG ∈ grpOf tGens := Enum.mem_of_memK tc_parts.1 tc_parts.2.2.2.2.2.2 rep_b

theorem TC_pgroup : IsPGroup 2 (grpOf tGens) := IsPGroup.of_card (n := 8) card_TC

theorem TC_max (Y : Subgroup GL12) (hY : IsPGroup 2 Y) (hTY : grpOf tGens ≤ Y)
    (hYC : Y ≤ grpOf cGens) : Y = grpOf tGens := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hY.exists_card_eq
  have hdvd : Nat.card Y ∣ 80640 := card_CC ▸ Subgroup.card_dvd_of_le hYC
  have hk8 : k ≤ 8 := by
    by_contra hc
    have h9 : 2 ^ 9 ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega)
    rw [hk] at hdvd
    have := h9.trans hdvd
    omega
  refine (Subgroup.eq_of_le_of_card_ge hTY ?_).symm
  rw [hk, card_TC]
  calc 2 ^ k ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) hk8
    _ = 256 := by norm_num

theorem commute_tbar_CC {x : GL12} (hx : x ∈ grpOf cGens) : x * tbarG = tbarG * x :=
  (commute_of_commGens (Enum.of_enumOK c_parts.1).1 rep_tbar phi_parts.2.2.2.2.2.2.2.2 x hx).symm

theorem splitFacts : SplitFacts (splitModel .plus) where
  card_fixM_tbar := by
    show Nat.card (fixM (tbarG : Mat12)) = 2 ^ 6
    rw [← rep_tbar, card_fixM_eq, phi_parts.1]
    norm_num
  exists_of_fixM_tbar := by
    intro v hv
    change (tbarG : Mat12) *ᵥ v = v at hv
    show ∃ x : Vec12, (tbarG : Mat12) *ᵥ x + x = v
    rw [← rep_tbar] at hv ⊢
    exact exists_of_imgCheckW phi_parts.2.1 hv
  offender_m2 := by
    intro E hE hsq hne
    refine offender_bound tc_parts.1 (fun v hv hfix => ?_) m2_roots hE hsq hne
    refine List.mem_filter.2 ⟨List.mem_range.2 hv, ?_⟩
    have h1 : toVec 12 (mulVecK phiK v) = toVec 12 v := by
      rw [toVec_mulVecK, rep_tbar]
      exact hfix
    rw [toVec_injOn (mulVecK_lt _ _) hv h1, beq_self_eq_true]
  offender_TC := fun A hA hsq hne => offender_bound tc_parts.1
    (fun v hv _ => List.mem_range.2 hv) off_roots hA hsq hne
  card_TC := by
    show Nat.card (grpOf (splitTGens .plus)) = 2 ^ 8
    rw [← show tGens = splitTGens .plus from rfl, card_TC]
    norm_num
  TC_le_CC := TC_le_CC
  TC_max := TC_max

@[expose] def caseData : CaseData := ⟨bG, grpOf c2Gens, grpOf p3Gens⟩

theorem commute_tbar_TC {x : GL12} (hx : x ∈ grpOf tGens) : tbarG * x = x * tbarG :=
  commute_of_commGens (Enum.of_enumOK tc_parts.1).1 rep_tbar tc_parts.2.2.2.2.1 x hx

theorem commute_b_TC {x : GL12} (hx : x ∈ grpOf tGens) : bG * x = x * bG :=
  commute_of_commGens (Enum.of_enumOK tc_parts.1).1 rep_b tc_parts.2.2.2.2.2.1 x hx

theorem tbar_b_comm : bG * tbarG = tbarG * bG := commute_b_TC tbar_mem_TC

theorem caseFacts : SCaseFacts (splitModel .plus) caseData where
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
  C2_ge := fun c hc hcb => mem_of_centInCheck c_parts.1 c2_parts.1 c2_parts.2.2.2.2.2.1 hc rep_b hcb
  P3_le := P3_le_C2
  P3_pgroup := IsPGroup.of_card (n := 1) (show Nat.card (grpOf p3Gens) = 3 ^ 1 by
    rw [card_P3]; norm_num)
  P3_index := by
    have h := Subgroup.card_mul_index ((grpOf p3Gens).subgroupOf (grpOf c2Gens))
    have hc : Nat.card ((grpOf p3Gens).subgroupOf (grpOf c2Gens)) = 3 := by
      rw [← card_P3]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe P3_le_C2).toEquiv
    rw [hc, card_C2] at h
    have : ((grpOf p3Gens).subgroupOf (grpOf c2Gens)).index = 256 := by omega
    show ¬ 3 ∣ ((grpOf p3Gens).subgroupOf (grpOf c2Gens)).index
    rw [this]
    norm_num
  exp_C2 := by
    intro c hc
    obtain ⟨i, hi, hr⟩ := Enum.exists_key c2_parts.1 hc
    have h := c2_parts.2.2.2.2.2.2
    simp only [Array.all_eq_true, beq_iff_eq] at h
    have h1 := h i hi
    rw [← getD_mem hi] at h1
    have h2 := hr.fpow (n := 1152) (by norm_num)
    rw [h1] at h2
    exact h2.unique rep_one |>.symm.symm

theorem mem_CC_of_normalizes {y : GL12} (hy : ∀ c ∈ grpOf cGens, y * c * y⁻¹ ∈ grpOf cGens)
    (hyt : y * tbarG = tbarG * y) : y ∈ grpOf cGens := by
  have h := nc_check
  simp only [PlusW.ncChk, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hR, hρ⟩, htup⟩, hlin⟩, hspan⟩, hsq⟩, htC⟩ := h
  exact N3Split.mem_of_normalizes c_parts.1 hR hρ htup
    (fun hm hsol => forall_of_linCheckWith hlin hspan hm hsol) hsq phi_parts.2.2.1 htC
    (fun x hx => (commute_tbar_CC hx).symm) hy hyt

end CFSG.EvenSmallLie.OmegaEight.N3Split.Plus
