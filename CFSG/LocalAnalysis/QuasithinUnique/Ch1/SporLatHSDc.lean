module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHSDcInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatOfFacts
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatExport
public import CFSG.Certificates.Kernel.SporLatDcSound
public import CFSG.Certificates.Kernel.SporLatOmegaSound
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHS
import all CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHS
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 100000

public section

namespace CFSG.QuasithinUnique.Ch1.SporLat.HSK

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2
open CFSG.Sporadic.HS.Native (hsData)
open CFSG.QuasithinUnique.Ch1.SporLat.HS
open CFSG.KC.SLDc CFSG.KC.E64F CFSG.KC.SLOm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.Open (pCoreOf)

open CFSG.KD.HSDc (nodes L C D Om Ot Lm memOK)

theorem slp_size : ∀ (l : List (ℕ × ℕ)) (T : Array (Array ℕ)),
    (l.foldl slpStepA T).size = T.size + l.length
  | [], T => rfl
  | p :: l, T => by
    rw [List.foldl_cons, slp_size l, List.length_cons]
    simp only [slpStepA, Array.size_push]
    omega

theorem slp_get : ∀ (l : List (ℕ × ℕ)) (arr : Array (Array ℕ)) (i : ℕ), i < arr.size →
    (l.foldl slpStepA arr)[i]! = arr[i]!
  | [], _, _, _ => rfl
  | p :: l, arr, i, hi => by
    rw [List.foldl_cons, slp_get l _ i (by simp [slpStepA]; omega)]
    unfold slpStepA
    rw [getElem!_pos (arr.push _) i (by simp; omega), getElem!_pos arr i hi,
      Array.getElem_push_lt hi]

theorem slp0 : hsSLP[0]! = hsTa := by
  unfold hsSLP slpTabsA
  rw [slp_get hsProg _ 0 (by simp)]
  rfl

theorem slp1 : hsSLP[1]! = hsTb := by
  unfold hsSLP slpTabsA
  rw [slp_get hsProg _ 1 (by simp)]
  rfl

theorem sTabs_eq : hsSTabs = [hsSLP[172]!, hsSLP[185]!, hsSLP[200]!] := rfl

theorem sTabs_len : hsSTabs.length = 3 := rfl

section Group

theorem hs_facts : Facts hsData 3 := CFSG.Sporadic.HS.hsFacts

theorem hs_ta : (tab hsData.n (a hsData)).toArray = hsTa := by
  have : tab hsData.n (a hsData) = hsTa.toList := by
    rw [tab_eq_of_rep (n := hsData.n) _ (a hsData) (rep_a hs_facts.toBaseFacts)]
    simp [hsTa]
  rw [this, Array.toArray_toList]

theorem hs_tb : (tab hsData.n (b hsData)).toArray = hsTb := by
  have : tab hsData.n (b hsData) = hsTb.toList := by
    rw [tab_eq_of_rep (n := hsData.n) _ (b hsData) (rep_b hs_facts.toBaseFacts)]
    simp [hsTb]
  rw [this, Array.toArray_toList]

theorem hs_card : Nat.card (J hsData) = 2 ^ 9 * 86625 := by
  have hcard0 : Nat.card (J hsData) = 44352000 :=
    (Nat.card_congr (seedEquiv hs_facts.toBaseFacts).toEquiv).symm.trans CFSG.Sporadic.HS.card_HS
  rw [hcard0]; norm_num

theorem hs_cert' :
    BaseCertS hsData.n hsB
      (slpTabsA (tab hsData.n (a hsData)).toArray (tab hsData.n (b hsData)).toArray hsProg) hsQp
      164 202 206 204 208 hsEnum.1 hsEnum.2.1 hsEnum.2.2 9 := by
  rw [hs_ta, hs_tb]
  have : slpTabsA hsTa hsTb hsProg = hsSLP := by simp [hsSLP]
  rw [this]
  exact hs_cert

@[expose] noncomputable def hsSgK : List (J hsData) :=
  hsQp.map fun p => (slpElts (a hsData) (b hsData) hsProg).getD p.1 1

theorem hs_sGens :
    genTabs hsData.n hsSgK = hsSTabs ∧ Nat.card (Subgroup.closure {x | x ∈ hsSgK}) = 2 ^ 9 := by
  have := sGens_of_baseCertS (n := hsData.n) hsB (base_lt hs_facts) (base_property hs_facts)
    (a hsData) (b hsData) hsProg hs_valid hsQp 164 202 206 204 208 hsEnum.1 hsEnum.2.1 hsEnum.2.2
    9 hs_cert'
  refine ⟨?_, this.2⟩
  rw [hsSgK, this.1, hs_ta, hs_tb]
  have : slpTabsA hsTa hsTb hsProg = hsSLP := by simp [hsSLP]
  rw [this]
  rfl

@[irreducible] noncomputable def E (j : ℕ) : J hsData :=
  (slpElts (a hsData) (b hsData) hsProg).getD j 1

theorem hsSgK_eq : hsSgK = [E 172, E 185, E 200] := by
  simp only [hsSgK, hsQp, List.map_cons, List.map_nil, E]

theorem elts_get : ∀ (l : List (ℕ × ℕ)) (arr : Array (J hsData)) (i : ℕ), i < arr.size →
    (l.foldl eltStep arr).getD i 1 = arr.getD i 1
  | [], _, _, _ => rfl
  | p :: l, arr, i, hi => by
    rw [List.foldl_cons, elts_get l _ i (by simp [eltStep]; omega)]
    unfold eltStep
    exact getD_push_lt arr _ 1 hi

theorem E0 : E 0 = a hsData := by
  unfold E slpElts
  rw [elts_get hsProg _ 0 (by simp)]
  rfl

theorem E1 : E 1 = b hsData := by
  unfold E slpElts
  rw [elts_get hsProg _ 1 (by simp)]
  rfl

theorem tab_node {j : ℕ}
    (hj : j < hsProg.length + 2) : (tab hsData.n (E j)).toArray = hsSLP[j]! := by
  have hinv := slp_foldl_inv (n := hsData.n) hsProg #[a hsData, b hsData]
    #[(tab hsData.n (a hsData)).toArray, (tab hsData.n (b hsData)).toArray] (by simp)
    (by
      intro i hi
      have hi' : i < 2 := by simpa using hi
      interval_cases i <;> simp) (by simpa using hs_valid)
  have hs : j < (hsProg.foldl slpStepA
      #[(tab hsData.n (a hsData)).toArray, (tab hsData.n (b hsData)).toArray]).size := by
    rw [slp_size]
    simpa [Nat.add_comm] using hj
  have e := hinv.2 j hs
  have e2 : hsProg.foldl slpStepA
      #[(tab hsData.n (a hsData)).toArray, (tab hsData.n (b hsData)).toArray] = hsSLP := by
    rw [hs_ta, hs_tb]
    rfl
  rw [e2] at e
  unfold E slpElts
  rw [e, Array.toArray_toList]

noncomputable def sl : List (J hsData) := [E 172, E 185, E 200, E 212, E 217, E 218]

section Facts

variable (h : HSDcFacts)

include h in
theorem good_L {l : ℕ} (hl : l < 8) :
    Good hsData.n (tab hsData.n (E (nodes.getD l 0))).toArray (C.L l) := by
  have hj : nodes.getD l 0 < hsProg.length + 2 := by interval_cases l <;> decide
  refine ⟨?_, ?_⟩
  · simp [tab]
  · rw [tab_node hj]
    exact h.2.2.1 l hl

include h in
theorem hL : ∀ l < 2 + C.ns,
    Good hsData.n (tab hsData.n ((a hsData :: b hsData :: sl).getD l 1)).toArray (C.L l) := by
  intro l hl
  have hl' : l < 8 := hl
  have e : (a hsData :: b hsData :: sl).getD l 1 = E (nodes.getD l 0) := by
    interval_cases l
    · exact E0.symm
    · exact E1.symm
    all_goals rfl
  rw [e]
  exact good_L h hl'

theorem act_of_good {x : J hsData} {f : ℕ → ℕ} (hx : Good hsData.n (tab hsData.n x).toArray f)
    {p : ℕ} (hp : p < hsData.n) : act hsData.n x p = f p ∧ f p < hsData.n := by
  rw [← img_tab, img]
  exact hx.2 p hp

theorem eq_inv_of_maps {x y : J hsData} {f g : ℕ → ℕ}
    (hx : Good hsData.n (tab hsData.n x).toArray f) (hy : Good hsData.n (tab hsData.n y).toArray g)
    (hfg : ∀ p < hsData.n, f (g p) = p) : x = y⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  apply base_property hs_facts
  intro b hb
  have hb' := base_lt hs_facts b hb
  rw [act_mul _ _ hb', (act_of_good hy hb').1, (act_of_good hx (act_of_good hy hb').2).1]
  exact hfg b hb'

theorem htake : sl.take 3 = hsSgK := by
  rw [hsSgK_eq]
  rfl

include h in
theorem hinvL : ∀ i < 3, ∀ p < hsData.n, L (Nat.add 5 i) (L (Nat.add 2 i) p) = p := by
  intro i hi p hp
  have h0 := h.2.1
  unfold CFSG.KD.HSDc.invOK at h0
  exact beq_iff_eq.1 (all_range (all_range h0 i hi) p hp)

include h in
theorem hS :
    ∀ x ∈ sl, x ∈ Subgroup.closure {x | x ∈ sl.take C.ng} := by
  intro x hx
  change x ∈ Subgroup.closure {x | x ∈ sl.take 3}
  rw [htake]
  have hg : ∀ y ∈ [E 172, E 185, E 200], y ∈ Subgroup.closure {x | x ∈ hsSgK} :=
    fun y hy => Subgroup.subset_closure (by rw [hsSgK_eq]; exact hy)
  have hm : ∀ i < 3, ∀ j k : ℕ, Nat.add 2 i < 8 → Nat.add 5 i < 8 →
      nodes.getD (Nat.add 2 i) 0 = j → nodes.getD (Nat.add 5 i) 0 = k →
      E j ∈ [E 172, E 185, E 200] → E k ∈ Subgroup.closure {x | x ∈ hsSgK} := by
    intro i hi j k h1 h2 e1 e2 hmem
    have g1 := good_L h h1
    have g2 := good_L h h2
    rw [e1] at g1
    rw [e2] at g2
    rw [eq_inv_of_maps g2 g1 (hinvL h i hi)]
    exact Subgroup.inv_mem _ (hg _ hmem)
  simp only [sl, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hg _ (by simp)
  · exact hg _ (by simp)
  · exact hg _ (by simp)
  · exact hm 0 (by decide) 172 212 (by decide) (by decide) rfl rfl (by simp)
  · exact hm 1 (by decide) 185 217 (by decide) (by decide) rfl rfl (by simp)
  · exact hm 2 (by decide) 200 218 (by decide) (by decide) rfl rfl (by simp)

include h in
theorem hsep :
    ∀ g : J hsData, (∀ p ∈ D.sep, act hsData.n g p = p) → g = 1 := by
  intro g hg
  change ∀ p ∈ CFSG.KD.HSDc.J.sep, _ at hg
  rw [h.2.2.2.1] at hg
  exact base_property hs_facts g hg

theorem mw_get (j : ℕ) : hsLatK.mw[j]! = CFSG.KD.HSDc.J.mw.getD j [] := by
  change CFSG.KD.HSDc.J.mw.toArray[j]! = _
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getD_eq_getElem?_getD]
  rfl

theorem mw_size_eq : hsLatK.mw.size = CFSG.KD.HSDc.J.mw.length := by
  change CFSG.KD.HSDc.J.mw.toArray.size = _
  simp

include h in
theorem mw_size : hsLatK.mw.size = 5 := by rw [mw_size_eq, h.2.2.2.2.2.1]

include h in
theorem dc_facts :
    (∀ g : J hsData, lab hsData.n ptLab hsDelta g = hsDelta ↔
      g ∈ Subgroup.closure {x | x ∈ hsSgK}) ∧
    ∀ Z : Subgroup (J hsData), Subgroup.closure {x | x ∈ hsSgK} ≤ Z → ∃ j ≤ hsLatK.mw.size,
      Z = memberOrTop hsLatK.mw.size (fun j => Subgroup.closure {x | x ∈ hsSgK ++
        (hsLatK.mw[j]!).map (wordElt (a hsData) (b hsData))}) j := by
  have h0 := dcCheck_sound (Γ := J hsData) (n := hsData.n) C rfl D (a hsData) (b hsData)
    (closure_ab hsData) sl rfl (hL h) (hS h)
    (by change Nat.card (Subgroup.closure {x | x ∈ sl.take 3}) = 2 ^ 9
        rw [htake]; exact hs_sGens.2)
    (by change Nat.card (J hsData) = 86625 * 2 ^ 9; rw [hs_card, mul_comm]) (hsep h)
    (by decide) h.1
  change (∀ g : J hsData, lab hsData.n ptLab hsDelta g = hsDelta ↔
      g ∈ Subgroup.closure {x | x ∈ sl.take 3}) ∧
    ∀ Z : Subgroup (J hsData), Subgroup.closure {x | x ∈ sl.take 3} ≤ Z →
      ∃ j ≤ CFSG.KD.HSDc.J.mw.length, Z = memberOrTop CFSG.KD.HSDc.J.mw.length
        (fun j => Subgroup.closure {x | x ∈ sl.take 3 ++
          (CFSG.KD.HSDc.J.mw.getD j []).map (wordElt (a hsData) (b hsData))}) j at h0
  rw [htake] at h0
  refine ⟨h0.1, fun Z hZ => ?_⟩
  obtain ⟨j, hj, hZj⟩ := h0.2 Z hZ
  refine ⟨j, by rw [mw_size_eq]; exact hj, ?_⟩
  rw [hZj, mw_size_eq]
  simp only [mw_get]

end Facts

end Group

theorem labF_lt {f : ℕ → ℕ} (hf : ∀ p < 1100, f p < 1100) {x : List ℕ} (hx : ∀ p ∈ x, p < 1100) :
    ∀ p ∈ labF f x, p < 1100 := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (insN_mem hp)
  exact hf q (hx q hq)

theorem om_spec {letters : Array (Array ℕ)} {M : ℕ → ℕ → ℕ}
    (hG : ∀ l < letters.size, Good 1100 (letters.getD l #[]) (M l)) {x0 : List ℕ}
    (hx0 : ∀ p ∈ x0, p < 1100) {O : OmegaData (List ℕ)}
    (hO : omOKG (fun l x => labF (M l) x) x0 letters.size O = true) :
    OmegaSpec ptAct letters x0 O ∧ ∀ i < O.lbl.size, ∀ p ∈ O.lbl[i]!, p < 1100 :=
  omOKG_sound (fun x => ∀ p ∈ x, p < 1100) hx0 (fun l hl x hx =>
    ⟨labF_lt (fun p hp => ((hG l hl).2 p hp).2) hx, by
      rw [getElem!_eq_getD']; exact ptAct_good (hG l hl) hx⟩) hO

theorem ot_spec {letters : Array (Array ℕ)} {M : ℕ → ℕ → ℕ}
    (hG : ∀ l < letters.size, Good 1100 (letters.getD l #[]) (M l)) {X0 : List (List ℕ)}
    (hX0 : ∀ x ∈ X0, ∀ p ∈ x, p < 1100) {O : OmegaData (List (List ℕ))}
    (hO : omOKG (fun l X => X.map (labF (M l))) X0 letters.size O = true) :
    OmegaSpec (tupAct ptAct) letters X0 O :=
  (omOKG_sound (fun X => ∀ x ∈ X, ∀ p ∈ x, p < 1100) hX0 (fun l hl X hX => by
    refine ⟨fun y hy => ?_, ?_⟩
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      exact labF_lt (fun p hp => ((hG l hl).2 p hp).2) (hX x hx)
    · unfold tupAct
      refine List.map_congr_left fun x hx => ?_
      rw [getElem!_eq_getD']
      exact ptAct_good (hG l hl) (hX x hx)) hO).1

theorem Om_get {j : ℕ} (hj : j < 5) : hsLatK.Om[j]! = Om j := by
  interval_cases j <;> rfl

theorem Ot_get {j : ℕ} (hj : j < 5) : hsOtK[j]! = Ot j := by
  interval_cases j <;> rfl

theorem delta_lt : ∀ p ∈ hsDelta, p < 1100 := by decide

section Members

variable (h : HSDcFacts)

include h in
theorem mt_get {j : ℕ} (hj : j < 5) :
    hsLatK.mt[j]! = (hsLatK.mw[j]!).map (wordTabA #[hsTa, hsTb] hsData.n) := by
  have hl : CFSG.KD.HSDc.J.mw.length = 5 := h.2.2.2.2.2.1
  change (CFSG.KD.HSDc.J.mw.toArray.map _)[j]! = (CFSG.KD.HSDc.J.mw.toArray[j]!).map _
  rw [getElem!_pos _ j (by simp [hl, hj]),
    getElem!_pos CFSG.KD.HSDc.J.mw.toArray j (by simp [hl, hj])]
  simp

include h in
theorem mw_lt2 {j : ℕ} : ∀ w ∈ CFSG.KD.HSDc.J.mw.getD j [], ∀ l ∈ w, l < 2 := by
  intro w hw l hl
  have h1 := h.2.2.2.2.1
  unfold CFSG.KD.HSDc.mwOK at h1
  rcases Nat.lt_or_ge j CFSG.KD.HSDc.J.mw.length with hj | hj
  · rw [List.getD_eq_getElem _ _ hj] at hw
    have h2 := List.all_eq_true.1 h1 _ (List.getElem_mem hj)
    have h3 := List.all_eq_true.1 (List.all_eq_true.1 h2 w hw) l hl
    simpa using h3
  · rw [List.getD_eq_default _ _ hj] at hw
    simp at hw

include h in
theorem mems_ok' {j : ℕ} (hj : j < 5) :
    omOKG (fun l x => labF (Lm j l) x) CFSG.KD.HSDc.Δ
        (Nat.add 3 (CFSG.KD.HSDc.J.mw.getD j []).length) (Om j) = true ∧
      omOKG (fun l X => X.map (labF (L (Nat.add 2 l)))) (Om j).lbl.toList 3 (Ot j) = true := by
  have h1 := List.all_eq_true.1 h.2.2.2.2.2.2.2.2.1 j (List.mem_range.2 hj)
  unfold memOK at h1
  rwa [Bool.and_eq_true] at h1

include h in
theorem good_node {l : ℕ}
    (hl : l < 8) : Good hsData.n hsSLP[nodes.getD l 0]! (L l) := by
  have e := good_L h hl
  rwa [tab_node (j := nodes.getD l 0) (by interval_cases l <;> decide)] at e

include h in
theorem good_ab :
    ∀ l < (#[hsTa, hsTb] : Array (Array ℕ)).size,
      Good 1100 ((#[hsTa, hsTb] : Array (Array ℕ)).getD l #[]) (L l)
  | 0, _ => by
    have g := good_node h (l := 0) (by decide)
    change Good 1100 hsSLP[0]! (L 0) at g
    rw [slp0] at g
    exact g
  | 1, _ => by
    have g := good_node h (l := 1) (by decide)
    change Good 1100 hsSLP[1]! (L 1) at g
    rw [slp1] at g
    exact g
  | _ + 2, hl => absurd hl (by simp)

include h in
theorem good_s {l : ℕ}
    (hl : l < 3) : Good 1100 (hsSTabs.toArray.getD l #[]) (L (Nat.add 2 l)) := by
  rw [sTabs_eq]
  interval_cases l
  · exact good_node h (l := 2) (by decide)
  · exact good_node h (l := 3) (by decide)
  · exact good_node h (l := 4) (by decide)

include h in
theorem msize {j : ℕ} (hj : j < 5) :
    (hsLatK.sTabs ++ hsLatK.mt[j]!).toArray.size =
      Nat.add 3 (CFSG.KD.HSDc.J.mw.getD j []).length := by
  rw [mt_get h hj, mw_get]
  simp [hsLatK, sTabs_len]

include h in
theorem good_m {j : ℕ} (hj : j < 5) :
    ∀ l < (hsLatK.sTabs ++ hsLatK.mt[j]!).toArray.size,
      Good 1100 ((hsLatK.sTabs ++ hsLatK.mt[j]!).toArray.getD l #[]) (Lm j l) := by
  intro l hl
  have hs : hsLatK.sTabs = hsSTabs := rfl
  rw [hs, mt_get h hj, mw_get] at hl ⊢
  simp only [List.size_toArray, List.length_append, List.length_map, sTabs_len] at hl
  by_cases h3 : l < 3
  · have e : (hsSTabs ++ (CFSG.KD.HSDc.J.mw.getD j []).map
        (wordTabA #[hsTa, hsTb] hsData.n)).toArray.getD l #[] = hsSTabs.toArray.getD l #[] := by
      have hl3 : l < hsSTabs.length := by rw [sTabs_len]; exact h3
      simp [Array.getD_eq_getD_getElem?, List.getElem?_append_left hl3,
        List.getElem?_eq_getElem hl3]
    rw [e]
    have e2 : Lm j l = L (Nat.add 2 l) := by
      have hb : Nat.blt l 3 = true := by simpa using h3
      unfold Lm
      rw [hb]
      rfl
    rw [e2]
    exact good_s h h3
  · obtain ⟨i, rfl⟩ : ∃ i, l = 3 + i := ⟨l - 3, by omega⟩
    have hi : i < (CFSG.KD.HSDc.J.mw.getD j []).length := by omega
    have e : (hsSTabs ++ (CFSG.KD.HSDc.J.mw.getD j []).map
        (wordTabA #[hsTa, hsTb] hsData.n)).toArray.getD (3 + i) #[] =
        wordTabA #[hsTa, hsTb] hsData.n ((CFSG.KD.HSDc.J.mw.getD j []).getD i []) := by
      have hle : hsSTabs.length ≤ 3 + i := by rw [sTabs_len]; omega
      have hi' : i < (CFSG.KD.HSDc.J.mw[j]?.getD []).length := by
        simpa [List.getD_eq_getElem?_getD] using hi
      simp [Array.getD_eq_getD_getElem?, List.getElem?_append_right hle, sTabs_len,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
    rw [e]
    have e2 : Lm j (3 + i) = wordF L ((CFSG.KD.HSDc.J.mw.getD j []).getD i []) := by
      have hb : Nat.blt (3 + i) 3 = false := by
        cases hc : Nat.blt (3 + i) 3
        · rfl
        · exact absurd (Nat.blt_eq.mp hc) (by omega)
      have hs3 : Nat.sub (3 + i) 3 = i := by change 3 + i - 3 = i; omega
      unfold Lm
      rw [hb]
      change wordF L ((CFSG.KD.HSDc.J.mw.getD j []).getD (Nat.sub (3 + i) 3) []) = _
      rw [hs3]
    rw [e2]
    have hmem : (CFSG.KD.HSDc.J.mw.getD j []).getD i [] ∈ CFSG.KD.HSDc.J.mw.getD j [] := by
      rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
    exact good_word (good_ab h) (fun l hl => by simpa using mw_lt2 h _ hmem l hl)

include h in
theorem hsK_membersOK :
    MembersOK ptAct hsData.n hsTa hsTb hsDelta hsLatK := by
  refine ⟨by rw [mw_size h]; decide, by rw [mw_get]; exact h.2.2.2.2.2.2.1, by simp [hsLatK],
    by rw [mw_size h]; rfl, fun j hj => ?_⟩
  have hj' : j < 5 := by rw [mw_size h] at hj; exact hj
  refine ⟨by rw [mw_get]; exact mw_lt2 h, mt_get h hj', ?_⟩
  · rw [Om_get hj']
    have h1 := (mems_ok' h hj').1
    rw [← msize h hj'] at h1
    exact (om_spec (good_m h hj') delta_lt h1).1

end Members

end CFSG.QuasithinUnique.Ch1.SporLat.HSK

end
