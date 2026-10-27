module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitPlus
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.N3SplitEnd

public section


namespace CFSG.EvenSmallLie.OmegaEight.N3Split.Plus

open CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Stage2
open CFSG.EvenSmallLie.UnitarySix.YamadaPar Subgroup Matrix

section Branches

variable {G : Type*} [Group G] {t : G} {TH W : Subgroup G}
  {φ : W ≃* Multiplicative (Fin 12 → ZMod 2)} {a : G}

theorem genG_append_left {xs ys : Array (ℕ × ℕ)} {j : ℕ} (hj : j < xs.size) :
    genG (xs ++ ys) j = genG xs j := by
  simp only [genG, genK, Array.getD_eq_getD_getElem?, Array.getElem?_append_left hj]

theorem genG_append_right {xs ys : Array (ℕ × ℕ)} {j : ℕ} (hj : xs.size ≤ j) :
    genG (xs ++ ys) j = genG ys (j - xs.size) := by
  simp only [genG, genK, Array.getD_eq_getD_getElem?, Array.getElem?_append_right hj]

theorem cGens_size : cGens.size = 8 := by
  simp [cGens, splitCGens]

theorem tGens_size : tGens.size = 8 := by
  simp [tGens, splitTGens]

theorem base_mem_X (h : Stage2Hyp (splitModel .plus) t TH W φ) {i : ℕ}
    (hr : glOf (reps.getD i (idK, idK)).1 (reps.getD i (idK, idK)).2 ∈ Xof W φ) :
    ∀ j < (base i).size, genG (base i) j ∈ Xof W φ := by
  intro j hj
  have hC : ∀ k < cGens.size, genG cGens k ∈ Xof W φ := fun k hk =>
    h.CC_le_X (genG_mem_grpOf hk)
  have hT : ∀ k < tGens.size, genG tGens k ∈ Xof W φ := fun k hk =>
    h.TC_le_X (genG_mem_grpOf hk)
  unfold base at hj ⊢
  by_cases h1 : j < (cGens ++ tGens).size
  · rw [genG_append_left h1]
    by_cases h2 : j < cGens.size
    · rw [genG_append_left h2]
      exact hC j h2
    · rw [genG_append_right (by omega)]
      exact hT _ (by simp only [Array.size_append] at h1; omega)
  · rw [genG_append_right (by omega)]
    have h3 : j - (cGens ++ tGens).size = 0 := by
      simp only [Array.size_append, cGens_size, tGens_size, List.size_toArray, List.length_cons,
        List.length_nil] at hj h1 ⊢
      omega
    rw [h3]
    exact hr

theorem false_of_bray (h : Stage2Hyp (splitModel .plus) t TH W φ) {i : ℕ}
    (hr : glOf (reps.getD i (idK, idK)).1 (reps.getD i (idK, idK)).2 ∈ Xof W φ)
    {prog : List (ℕ × ℕ × ℕ)} {out : ℕ} (hb : brayCheck (base i) prog out phiK cEnumW = true) :
    False := by
  obtain ⟨z, hzX, hzt, hzC⟩ := exists_of_brayCheck c_parts.1 hb (base_mem_X h hr) rep_tbar
  exact hzC (h.mem_CC_of_commute hzX hzt)

theorem relIndex_of_card {Y S : Subgroup GL12} (hYS : Y ≤ S) {n : ℕ} (hY : Nat.card Y = n)
    (hS : Nat.card S = 2 * n) (hn : 0 < n) : Y.relIndex S = 2 := by
  have h := Subgroup.relIndex_mul_card (H := Y) (K := S)
  rw [inf_of_le_left hYS, hY, hS] at h
  exact Nat.eq_of_mul_eq_mul_right hn h

theorem cand_classes {gs : Array (ℕ × ℕ)} {E : Enum} (hE : enumOK gs E = true) {rs : List ℕ}
    {B : ℕ → List ℕ} {R Y : ℕ → ℕ} (hcl : classCertW E rs [phiK, tauK] B R Y = true) {τ : GL12}
    (hτ : Rep tauK τ) :
    ∀ s ∈ grpOf gs, IsCand (grpOf gs) s →
      ∃ y ∈ grpOf gs, s = y * tbarG * y⁻¹ ∨ s = y * τ * y⁻¹ := by
  intro s hs hc
  obtain ⟨r, hr, rG, hrG, -, y, hy, e⟩ := cand_of_classCertW hE hcl hs hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with hr | hr
  · rw [hr] at hrG
    exact ⟨y, hy, Or.inl (by rw [e, hrG.unique rep_tbar])⟩
  · rw [hr] at hrG
    exact ⟨y, hy, Or.inr (by rw [e, hrG.unique hτ])⟩

theorem cand_classes1 {gs : Array (ℕ × ℕ)} {E : Enum} (hE : enumOK gs E = true) {rs : List ℕ}
    {B : ℕ → List ℕ} {R Y : ℕ → ℕ} (hcl : classCertW E rs [phiK] B R Y = true) :
    ∀ s ∈ grpOf gs, IsCand (grpOf gs) s → ∃ y ∈ grpOf gs, s = y * tbarG * y⁻¹ := by
  intro s hs hc
  obtain ⟨r, hr, rG, hrG, -, y, hy, e⟩ := cand_of_classCertW hE hcl hs hc
  rw [List.mem_singleton] at hr
  rw [hr] at hrG
  exact ⟨y, hy, by rw [e, hrG.unique rep_tbar]⟩

end Branches

section Branches2

variable {G : Type*} [Group G] {t : G} {TH W : Subgroup G}
  {φ : W ≃* Multiplicative (Fin 12 → ZMod 2)} {a : G}

theorem false_of_degenerate [Finite G] (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (h : Stage2Hyp (splitModel .plus) t TH W φ) (hX : SplitExtra t TH W a)
    (hdeg : ∀ Z : Subgroup GL12, Z ≤ Xof W φ → IsPGroup 2 Z → (splitModel .plus).TC ≤ Z →
      Z = (splitModel .plus).TC) : False :=
  false_of_offender_cand hG hnab h splitFacts hX (S := grpOf tGens) h.TC_le_X TC_pgroup le_rfl
    hdeg (fun A hA hsq hne => offender_bound tc_parts.1 (fun v hv _ => List.mem_range.2 hv)
      off_roots hA hsq hne)
    (relIndex_of_card UK_le_TC card_UK (by rw [card_TC]) (by norm_num))
    (fun s hs => not_isCand_of_avoidCheck tc_parts.1 uk_parts.1 uk_parts.2.2.2 hs)

theorem s_parts0 : gensOK (base 0) = true ∧ gensOK sGens0 = true ∧
    enumOK sGens0 sEnum0W = true ∧ sEnum0W.keys.size = 16384 ∧ gensIn tGens sEnum0W = true ∧
    classCertW sEnum0W sReps0 [phiK, tauK] wit.cls0.1 wit.cls0.2.1 wit.cls0.2.2 = true ∧
    enumOK mGens0 mEnum0W = true ∧ mEnum0W.keys.size = 8192 ∧ gensIn mGens0 sEnum0W = true ∧
    ([phiK, tauK].all fun r => !(memK mEnum0W.keys r) && decide (r < 2 ^ 144)) = true := by
  have h := s_check0
  simp only [PlusW.sChk0, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2,
    h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem s_parts1 : gensOK (base 1) = true ∧ gensOK sGens1 = true ∧
    enumOK sGens1 sEnum1W = true ∧ sEnum1W.keys.size = 16384 ∧ gensIn tGens sEnum1W = true ∧
    classCertW sEnum1W sReps1 [phiK, tauK] wit.cls1.1 wit.cls1.2.1 wit.cls1.2.2 = true ∧
    enumOK mGens1 mEnum1W = true ∧ mEnum1W.keys.size = 8192 ∧ gensIn mGens1 sEnum1W = true ∧
    ([phiK, tauK].all fun r => !(memK mEnum1W.keys r) && decide (r < 2 ^ 144)) = true := by
  have h := s_check1
  simp only [PlusW.sChk1, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2,
    h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem tau_parts0 : memK sEnum0W.keys tauK = true ∧ commCount sEnum0W tauK = 256 ∧
    fixCount tauK = 64 ∧ kerCount sEnum0W tauK = 2 ∧ invPair tauK tauK = true := by
  have h := tau_check0
  simp only [PlusW.tauChk0, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem tau_parts1 : memK sEnum1W.keys tauK = true ∧ commCount sEnum1W tauK = 256 ∧
    fixCount tauK = 64 ∧ kerCount sEnum1W tauK = 2 ∧ invPair tauK tauK = true := by
  have h := tau_check1
  simp only [PlusW.tauChk1, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

@[expose] def tauG : GL12 := glOf tauK tauK

theorem rep_tau : Rep tauK tauG := rep_glOf tau_parts0.2.2.2.2

theorem tau_data {gs : Array (ℕ × ℕ)} {E : Enum} (hE : enumOK gs E = true)
    (hc : commCount E tauK = 256) (hk : kerCount E tauK = 2) :
    Nat.card ↥(grpOf gs ⊓ centralizer ({tauG} : Set GL12)) = 2 ^ 8 ∧
      Nat.card (fixM (tauG : Mat12)) = 2 ^ 6 ∧ Nat.card (kerSet (grpOf gs) tauG) = 2 := by
  refine ⟨by rw [card_inf_centralizer_eq hE rep_tau, hc]; norm_num, ?_,
    by rw [card_kerSet_eq hE rep_tau, hk]⟩
  rw [← rep_tau, card_fixM_eq, tau_parts0.2.2.1]
  norm_num

theorem slp_le_X (h : Stage2Hyp (splitModel .plus) t TH W φ) {i : ℕ}
    (hr : glOf (reps.getD i (idK, idK)).1 (reps.getD i (idK, idK)).2 ∈ Xof W φ)
    (hb : gensOK (base i) = true) {prog : List (ℕ × ℕ × ℕ)} {outs : List ℕ}
    (hg : gensOK (slpGens (base i) prog outs) = true) :
    grpOf (slpGens (base i) prog outs) ≤ Xof W φ :=
  grpOf_slpGens_le hb (base_mem_X h hr) hg

end Branches2

section Branches3

variable {G : Type*} [Group G] {t : G} {TH W : Subgroup G}
  {φ : W ≃* Multiplicative (Fin 12 → ZMod 2)} {a : G}

theorem x0_parts : invPair x0K x0invK = true ∧ mulK (mulK x0K phiK) x0invK = tauK ∧
    gensOK (base 0) = true ∧ (baseK (base 0)).all (· < 2 ^ 144) = true ∧
    ((List.range 8).all fun j => (cGens.getD j (0, 0)).1 == idK ||
      (runK (baseK (base 0)) x0Prog).getD (x0Outs.getD j 0) idK ==
        mulK (mulK x0K (cGens.getD j (0, 0)).1) x0invK) = true := by
  have h := x0_check
  simp only [x0Chk, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

@[expose] def x0G : GL12 := glOf x0K x0invK

theorem rep_x0 : Rep x0K x0G := rep_glOf x0_parts.1

theorem rep_x0_inv : Rep x0invK x0G⁻¹ := rep_glOf_inv x0_parts.1

theorem tau_eq : tauG = x0G * tbarG * x0G⁻¹ :=
  rep_tau.unique (x0_parts.2.1 ▸ (rep_x0.mul rep_tbar).mul rep_x0_inv)

theorem x0_conj_mem_X (h : Stage2Hyp (splitModel .plus) t TH W φ)
    (hr : glOf (reps.getD 0 (idK, idK)).1 (reps.getD 0 (idK, idK)).2 ∈ Xof W φ) :
    ∀ c ∈ grpOf cGens, x0G * c * x0G⁻¹ ∈ Xof W φ := by
  obtain ⟨-, -, hb, hlt, hprog⟩ := x0_parts
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at hprog
  have hgen : ∀ j < cGens.size, x0G * genG cGens j * x0G⁻¹ ∈ Xof W φ := by
    intro j hj
    have hj8 : j < 8 := cGens_size ▸ hj
    have hrep := rep_genG (Enum.of_enumOK c_parts.1).1 j
    have hkey : (genK cGens j).1 = (cGens.getD j (0, 0)).1 := by
      simp [genK, Array.getD_eq_getD_getElem?, hj]
    rcases hprog j hj8 with h1 | h1
    · have e : genG cGens j = 1 := hrep.unique (by rw [hkey, h1]; exact rep_one)
      rw [e, mul_one, mul_inv_cancel]
      exact one_mem _
    · have hR := runK_rep x0Prog (baseK (base 0)) (baseG (base 0)) (baseK_size _)
        (rep_base hb) (x0Outs.getD j 0)
      rw [h1] at hR
      have hmem := runG_mem (Xof W φ) x0Prog (baseG (base 0)) (base_mem (base_mem_X h hr))
        (x0Outs.getD j 0)
      have e : (runG (baseG (base 0)) x0Prog).getD (x0Outs.getD j 0) 1 =
          x0G * genG cGens j * x0G⁻¹ :=
        hR.unique ((rep_x0.mul (hkey ▸ hrep)).mul rep_x0_inv)
      rw [← e]
      exact hmem
  intro c hc
  induction hc using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨j, hj, rfl⟩ := hz
    exact hgen j hj
  | one => rw [mul_one, mul_inv_cancel]; exact one_mem _
  | mul a b _ _ ha hb' =>
    have e : x0G * (a * b) * x0G⁻¹ = (x0G * a * x0G⁻¹) * (x0G * b * x0G⁻¹) := by group
    rw [e]
    exact mul_mem ha hb'
  | inv a _ ha =>
    have e : x0G * a⁻¹ * x0G⁻¹ = (x0G * a * x0G⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem ha

theorem s2_parts : gensOK s2Gens = true ∧ enumOK s2Gens s2EnumW = true ∧
    s2EnumW.keys.size = 32768 ∧ gensIn tGens s2EnumW = true ∧
    classCertW s2EnumW s2Reps [phiK] wit.cls2.1 wit.cls2.2.1 wit.cls2.2.2 = true ∧
    enumOK m2Gens m2EnumW = true ∧ m2EnumW.keys.size = 16384 ∧ gensIn m2Gens s2EnumW = true ∧
    ([phiK].all fun r => !(memK m2EnumW.keys r) && decide (r < 2 ^ 144)) = true := by
  have h := s2_check
  simp only [PlusW.s2Chk, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2,
    h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem false_of_wreath [Finite G] (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (h : Stage2Hyp (splitModel .plus) t TH W φ) (hX : SplitExtra t TH W a)
    (hr : glOf (reps.getD 0 (idK, idK)).1 (reps.getD 0 (idK, idK)).2 ∈ Xof W φ) : False := by
  obtain ⟨hb, hg, hsE, hsz, hTS, hcl, hmE, hmz, hMS, hav⟩ := s_parts0
  have hSX : grpOf sGens0 ≤ Xof W φ := slp_le_X h hr hb hg
  have hcardS : Nat.card (grpOf sGens0) = 16384 := by rw [Enum.card_eq hsE, hsz]
  have hS2 : IsPGroup 2 (grpOf sGens0) := IsPGroup.of_card (n := 14) (by rw [hcardS]; norm_num)
  have hTCS : grpOf tGens ≤ grpOf sGens0 :=
    grpOf_le_of_gensIn (Enum.of_enumOK tc_parts.1).1 hsE hTS
  by_cases hx0 : x0G ∈ Xof W φ
  ·
    obtain ⟨hg2, hs2E, hs2z, hTS2, hcl2, hm2E, hm2z, hMS2, hav2⟩ := s2_parts
    have hS2X : grpOf s2Gens ≤ Xof W φ := by
      rw [grpOf, Subgroup.closure_le]
      rintro _ ⟨j, hj, rfl⟩
      by_cases hj' : j < sGens0.size
      · rw [s2Gens, genG_append_left hj']
        exact hSX (genG_mem_grpOf hj')
      · have hs : s2Gens.size = sGens0.size + 1 := by simp [s2Gens]
        have hjj : j = sGens0.size := by omega
        rw [s2Gens, genG_append_right (by omega), hjj, Nat.sub_self]
        exact hx0
    have hcard2 : Nat.card (grpOf s2Gens) = 32768 := by rw [Enum.card_eq hs2E, hs2z]
    have hcardM2 : Nat.card (grpOf m2Gens) = 16384 := by rw [Enum.card_eq hm2E, hm2z]
    have hYS : grpOf m2Gens ≤ grpOf s2Gens := grpOf_le_of_gensIn (Enum.of_enumOK hm2E).1 hs2E hMS2
    have hidx := relIndex_of_card hYS hcardM2 (by rw [hcard2]) (by norm_num)
    exact false_of_cand1 hG hnab h splitFacts hX hS2X
      (IsPGroup.of_card (n := 15) (by rw [hcard2]; norm_num))
      (grpOf_le_of_gensIn (Enum.of_enumOK tc_parts.1).1 hs2E hTS2)
      (cand_classes1 hs2E hcl2) hidx
      (not_isCand_of_classCertW hs2E hcl2 hm2E (by rw [hm2z]; norm_num) hYS hidx hav2)
  ·
    obtain ⟨hτmem, hτc, -, hτk, -⟩ := tau_parts0
    obtain ⟨hcs, hfix, hker⟩ := tau_data hsE hτc hτk
    have hcardM : Nat.card (grpOf mGens0) = 8192 := by rw [Enum.card_eq hmE, hmz]
    have hYS : grpOf mGens0 ≤ grpOf sGens0 := grpOf_le_of_gensIn (Enum.of_enumOK hmE).1 hsE hMS
    have hτX : ∀ x ∈ Xof W φ, x * (splitModel .plus).tbar * x⁻¹ ≠ tauG := by
      intro x hx e
      apply hx0
      refine mem_X_of_conj h (fun y hy hyt => mem_CC_of_normalizes hy hyt)
        (fun c hc => commute_tbar_CC hc) (x0_conj_mem_X h hr) hx ?_
      rw [e, tau_eq]
      rfl
    have hidx := relIndex_of_card hYS hcardM (by rw [hcardS]) (by norm_num)
    exact false_of_cand2 hG hnab h splitFacts hX hSX hS2 hTCS (cand_classes hsE hcl rep_tau)
      hcs hfix hker hτX hidx
      (not_isCand_of_classCertW hsE hcl hmE (by rw [hmz]; norm_num) hYS hidx hav)

end Branches3

section Branches4

variable {G : Type*} [Group G] {t : G} {TH W : Subgroup G}
  {φ : W ≃* Multiplicative (Fin 12 → ZMod 2)} {a : G}

theorem z_facts (h : Stage2Hyp (splitModel .plus) t TH W φ) {i : ℕ}
    (hr : glOf (reps.getD i (idK, idK)).1 (reps.getD i (idK, idK)).2 ∈ Xof W φ)
    {prog : List (ℕ × ℕ × ℕ)} {out : ℕ}
    (hz : (gensOK (base i) && (baseK (base i)).all (· < 2 ^ 144) &&
      fpowK ((runK (baseK (base i)) prog).getD out idK) 9 == idK &&
      fpowK ((runK (baseK (base i)) prog).getD out idK) 3 != idK &&
      mulK ((runK (baseK (base i)) prog).getD out idK) tauK ==
        mulK tauK ((runK (baseK (base i)) prog).getD out idK)) = true) :
    ∃ z ∈ Xof W φ, z ^ 9 = 1 ∧ z ^ 3 ≠ 1 ∧ z * tauG = tauG * z := by
  generalize hk : (runK (baseK (base i)) prog).getD out idK = zK at hz
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hz
  obtain ⟨⟨⟨⟨hb', hlt⟩, hz9⟩, hz3⟩, hzτ⟩ := hz
  have hR := runK_rep prog (baseK (base i)) (baseG (base i)) (baseK_size _) (rep_base hb') out
  rw [hk] at hR
  have hτz := rep_tau.mul hR
  rw [← hzτ] at hτz
  have h9 := hR.fpow (n := 9) (by norm_num)
  rw [hz9] at h9
  refine ⟨(runG (baseG (base i)) prog).getD out 1,
    runG_mem (Xof W φ) prog (baseG (base i)) (base_mem (base_mem_X h hr)) out,
    h9.unique rep_one, fun e => hz3 ?_, (hR.mul rep_tau).unique hτz⟩
  have h3 : Rep idK (((runG (baseG (base i)) prog).getD out 1) ^ 3) := by
    rw [e]
    exact rep_one
  exact (hR.fpow (n := 3) (by norm_num)).key_unique h3 (fpowK_lt _ _) idK_lt

theorem false_of_l44 [Finite G] (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (h : Stage2Hyp (splitModel .plus) t TH W φ) (hX : SplitExtra t TH W a)
    (hr : glOf (reps.getD 1 (idK, idK)).1 (reps.getD 1 (idK, idK)).2 ∈ Xof W φ) : False := by
  obtain ⟨hb, hg, hsE, hsz, hTS, hcl, hmE, hmz, hMS, hav⟩ := s_parts1
  have hSX : grpOf sGens1 ≤ Xof W φ := slp_le_X h hr hb hg
  have hcardS : Nat.card (grpOf sGens1) = 16384 := by rw [Enum.card_eq hsE, hsz]
  have hS2 : IsPGroup 2 (grpOf sGens1) := IsPGroup.of_card (n := 14) (by rw [hcardS]; norm_num)
  have hTCS : grpOf tGens ≤ grpOf sGens1 :=
    grpOf_le_of_gensIn (Enum.of_enumOK tc_parts.1).1 hsE hTS
  obtain ⟨-, hτc, -, hτk, -⟩ := tau_parts1
  obtain ⟨hcs, hfix, hker⟩ := tau_data hsE hτc hτk
  have hcardM : Nat.card (grpOf mGens1) = 8192 := by rw [Enum.card_eq hmE, hmz]
  have hYS : grpOf mGens1 ≤ grpOf sGens1 := grpOf_le_of_gensIn (Enum.of_enumOK hmE).1 hsE hMS
  obtain ⟨z, hzX, hz9', hz3', hzτ'⟩ := z_facts h hr z_check
  have hno : ∀ c ∈ (splitModel .plus).CC, c ^ 9 = 1 → c ^ 3 = 1 := by
    intro c hc hc9
    obtain ⟨i, hi, hri⟩ := Enum.exists_key c_parts.1 hc
    have h1 : (cEnumW.keys.all fun c => fpowK c 9 != idK || fpowK c 3 == idK) = true := no_check
    simp only [Array.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h1
    rcases h1 i hi with h2 | h2
    · rw [← getD_mem hi] at h2
      have h3 : Rep idK (c ^ 9) := by
        rw [hc9]
        exact rep_one
      exact absurd ((hri.fpow (n := 9) (by norm_num)).key_unique h3 (fpowK_lt _ _) idK_lt) h2
    · rw [← getD_mem hi] at h2
      have h3 := hri.fpow (n := 3) (by norm_num)
      rw [h2] at h3
      exact h3.unique rep_one
  have hτX := not_conj_of_pow h hzX hzτ' hz9' hz3' hno
  have hidx := relIndex_of_card hYS hcardM (by rw [hcardS]) (by norm_num)
  exact false_of_cand2 hG hnab h splitFacts hX hSX hS2 hTCS (cand_classes hsE hcl rep_tau)
    hcs hfix hker hτX hidx
    (not_isCand_of_classCertW hsE hcl hmE (by rw [hmz]; norm_num) hYS hidx hav)

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
    (hcase : CaseI (splitModel .plus) caseData.b m ∨ CaseII (splitModel .plus) caseData.b m)
    (hP3 : ∀ y ∈ caseData.P3, m * y * m⁻¹ ∈ caseData.P3) (hm2 : m * m ∈ caseData.C2)
    (hm256 : m ^ 256 = 1) (hC2 : ∀ c ∈ caseData.C2, m * c * m⁻¹ ∈ caseData.C2) :
    ∃ r ∈ reps, (glOf r.1 r.2)⁻¹ * m ∈ grpOf cGens := by
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

theorem false_of_split [Finite G] (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (h : Stage2Hyp (splitModel .plus) t TH W φ) (hX : SplitExtra t TH W a) : False := by
  rcases SCaseFacts.degenerate_or_exists h caseFacts with
    hdeg | ⟨m, hmX, hcase, hP3, hm2, hm256, hC2⟩
  · exact false_of_degenerate hG hnab h hX hdeg
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
  have hlen : reps.length = 4 := rfl
  have hi4 : i < 4 := hlen ▸ hi
  interval_cases i
  · exact false_of_wreath hG hnab h hX hrX
  · exact false_of_l44 hG hnab h hX hrX
  · exact false_of_bray h hrX bray_check2
  · exact false_of_bray h hrX bray_check3

end Branches4

end CFSG.EvenSmallLie.OmegaEight.N3Split.Plus
