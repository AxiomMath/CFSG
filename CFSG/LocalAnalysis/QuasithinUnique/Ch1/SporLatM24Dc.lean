module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24DcInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatOfFacts
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCode
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatExport
public import CFSG.Certificates.Kernel.SporLatDcPair
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicMathieu

set_option maxRecDepth 100000

public section

namespace CFSG.QuasithinUnique.Ch1.SporLat.M24K

open CFSG.KC.SLDc CFSG.KC.E64F CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat.M24
open CFSG.Sporadic.Mathieu (m24a m24b card_M24 m24_hyp)
open CFSG.KD.M24Dc
open CFSG.Open (pCoreOf)

abbrev G : Type := ↥CFSG.Blueprint.NativeSporadic.M24

theorem slp_size : ∀ (l : List (ℕ × ℕ)) (T : Array (Array ℕ)),
    (l.foldl slpStepA T).size = T.size + l.length
  | [], T => rfl
  | p :: l, T => by
    rw [List.foldl_cons, slp_size l, List.length_cons]
    simp only [slpStepA, Array.size_push]
    omega

theorem ta_eq : (tab 24 m24a).toArray = m24ta.toArray := by rw [m24_tab_a]

theorem tb_eq : (tab 24 m24b).toArray = m24tb.toArray := by rw [m24_tab_b]

@[irreducible] noncomputable def E (j : ℕ) : G := (slpElts m24a m24b m24Prog).getD j 1

theorem tab_node {j : ℕ} (hj : j < m24Prog.length + 2) :
    (tab 24 (E j)).toArray = m24SLP[j]! := by
  have hinv := slp_foldl_inv (n := 24) m24Prog #[m24a, m24b]
    #[(tab 24 m24a).toArray, (tab 24 m24b).toArray] (by simp)
    (by
      intro i hi
      have hi' : i < 2 := by simpa using hi
      interval_cases i <;> simp) (by simpa using m24_valid)
  have hs : j < (m24Prog.foldl slpStepA #[(tab 24 m24a).toArray, (tab 24 m24b).toArray]).size := by
    rw [slp_size]
    simpa [Nat.add_comm] using hj
  have e := hinv.2 j hs
  have e2 : m24Prog.foldl slpStepA #[(tab 24 m24a).toArray, (tab 24 m24b).toArray] = m24SLP := by
    rw [ta_eq, tb_eq]
    rfl
  rw [e2] at e
  unfold E slpElts
  rw [e, Array.toArray_toList]

@[expose] noncomputable def sl : List G :=
  [E 180, E 187, E 196, E 211, E 218, E 223, E 228, E 231]

@[expose] noncomputable def m24SgK : List G :=
  m24Qp.map fun p => (slpElts m24a m24b m24Prog).getD p.1 1

theorem m24SgK_eq : m24SgK = [E 180, E 187, E 196, E 211] := by
  simp only [m24SgK, m24Qp, List.map_cons, List.map_nil, E]

theorem htake : sl.take 4 = m24SgK := by
  rw [m24SgK_eq]
  rfl

theorem m24K_sGens : genTabs 24 m24SgK = m24STabs ∧
    Nat.card (Subgroup.closure {x | x ∈ m24SgK}) = 2 ^ 10 := by
  have hc : BaseCertS 24 (List.range 24)
      (slpTabsA (tab 24 m24a).toArray (tab 24 m24b).toArray m24Prog) m24Qp
      162 213 216 214 217 m24Enum.1 m24Enum.2.1 m24Enum.2.2 10 := by
    rw [ta_eq, tb_eq]
    exact m24_cert
  have := sGens_of_baseCertS (n := 24) (List.range 24) (fun b hb => List.mem_range.mp hb)
    base_of_faithful m24a m24b m24Prog m24_valid m24Qp 162 213 216 214 217 m24Enum.1
    m24Enum.2.1 m24Enum.2.2 10 hc
  refine ⟨?_, this.2⟩
  rw [m24SgK, this.1, ta_eq, tb_eq]
  rfl

theorem m24_delta_valid : CodeSetValid 24 m24Delta := by
  have h : ∀ l ∈ m24Sets, PtValid 24 l := by decide
  refine ⟨sortN_sorted _, fun c hc => ?_⟩
  rw [m24Delta, mem_sortN] at hc
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hc
  exact ⟨l, h l hl, rfl⟩

theorem delta_eq : m24Delta = Δc := by
  rw [m24Delta, CFSG.KC.E64F.sortN_eq]
  decide

section Facts

variable (h : M24DcFacts)

include h in
theorem tab_ok {l : ℕ} (hl : l < 10) :
    (J.tabs.getD l []).length = 24 ∧ ∀ p ∈ J.tabs.getD l [], p < 24 := by
  have h1 := h.2.2.1
  unfold CFSG.KD.M24Dc.tabsOK at h1
  rw [Bool.and_eq_true, List.all_eq_true] at h1
  have hl' : l < J.tabs.length := by rw [Nat.eq_of_beq_eq_true h1.1]; exact hl
  have hm : J.tabs.getD l [] ∈ J.tabs := by
    rw [List.getD_eq_getElem _ _ hl']; exact List.getElem_mem hl'
  have e := h1.2 _ hm
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at e
  exact e

theorem good_tabF {x : G} {t : List ℕ} (hx : (tab 24 x).toArray = t.toArray)
    (ht : t.length = 24 ∧ ∀ p ∈ t, p < 24) : Good 24 (tab 24 x).toArray (tabF t) := by
  rw [hx]
  refine ⟨by simp [ht.1], fun p hp => ⟨?_, ?_⟩⟩
  · simp [tabF, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  · have hp' : p < t.length := by rw [ht.1]; exact hp
    rw [tabF, List.getD_eq_getElem _ _ hp']
    exact ht.2 _ (List.getElem_mem hp')

include h in
theorem tab_letter {l : ℕ} (hl : l < 10) :
    (tab 24 ((m24a :: m24b :: sl).getD l 1)).toArray = (J.tabs.getD l []).toArray := by
  rw [h.2.1]
  interval_cases l
  · exact ta_eq
  · exact tb_eq
  all_goals
    change (tab 24 (E _)).toArray = _
    rw [tab_node (by decide)]
    simp

include h in
theorem good0 {l : ℕ} (hl : l < 10) :
    Good 24 (tab 24 ((m24a :: m24b :: sl).getD l 1)).toArray (L0 l) :=
  good_tabF (tab_letter h hl) (tab_ok h hl)

include h in
theorem hL : ∀ l < 2 + C.ns,
    Good (24 * 24) (@tab G _ (24 * 24) (pairAction G 24) ((m24a :: m24b :: sl).getD l 1)).toArray
      (C.L l) :=
  fun l hl => good_pair (good0 h (l := l) hl)

theorem act_of_good {x : G} {f : ℕ → ℕ} (hx : Good 24 (tab 24 x).toArray f) {p : ℕ}
    (hp : p < 24) : act 24 x p = f p ∧ f p < 24 := by
  rw [← img_tab, img]
  exact hx.2 p hp

theorem eq_inv_of_maps {x y : G} {f g : ℕ → ℕ} (hx : Good 24 (tab 24 x).toArray f)
    (hy : Good 24 (tab 24 y).toArray g) (hfg : ∀ p < 24, f (g p) = p) : x = y⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  apply base_of_faithful (n := 24)
  intro b hb
  have hb' := List.mem_range.1 hb
  rw [act_mul _ _ hb', (act_of_good hy hb').1, (act_of_good hx (act_of_good hy hb').2).1]
  exact hfg b hb'

include h in
theorem hinvL : ∀ i < 4, ∀ p < 24, L0 (Nat.add 6 i) (L0 (Nat.add 2 i) p) = p := by
  intro i hi p hp
  have h1 := h.2.2.2.1
  unfold CFSG.KD.M24Dc.invOK at h1
  exact beq_iff_eq.1 (List.all_eq_true.1 (List.all_eq_true.1 h1 i (List.mem_range.2 hi)) p
    (List.mem_range.2 hp))

include h in
theorem hS :
    ∀ x ∈ sl, x ∈ Subgroup.closure {x | x ∈ sl.take C.ng} := by
  intro x hx
  change x ∈ Subgroup.closure {x | x ∈ sl.take 4}
  rw [htake]
  have hg : ∀ y ∈ [E 180, E 187, E 196, E 211], y ∈ Subgroup.closure {x | x ∈ m24SgK} :=
    fun y hy => Subgroup.subset_closure (by rw [m24SgK_eq]; exact hy)
  have hm : ∀ i < 4, sl.getD (Nat.add 4 i) 1 =
      ((m24a :: m24b :: sl).getD (Nat.add 2 i) 1)⁻¹ := by
    intro i hi
    have e : sl.getD (Nat.add 4 i) 1 = (m24a :: m24b :: sl).getD (Nat.add 6 i) 1 := by
      have : Nat.add 6 i = Nat.add 4 i + 1 + 1 := by simp only [Nat.add_eq]; omega
      rw [this, List.getD_cons_succ, List.getD_cons_succ]
    rw [e]
    exact eq_inv_of_maps (f := L0 (Nat.add 6 i)) (g := L0 (Nat.add 2 i))
      (good0 h (l := Nat.add 6 i) (by simp only [Nat.add_eq]; omega))
      (good0 h (l := Nat.add 2 i) (by simp only [Nat.add_eq]; omega)) (hinvL h i hi)
  simp only [sl, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hg _ (by simp)
  · exact hg _ (by simp)
  · exact hg _ (by simp)
  · exact hg _ (by simp)
  · rw [show E 218 = ((m24a :: m24b :: sl).getD 2 1)⁻¹ from hm 0 (by decide)]
    exact Subgroup.inv_mem _ (hg _ (by simp [sl]))
  · rw [show E 223 = ((m24a :: m24b :: sl).getD 3 1)⁻¹ from hm 1 (by decide)]
    exact Subgroup.inv_mem _ (hg _ (by simp [sl]))
  · rw [show E 228 = ((m24a :: m24b :: sl).getD 4 1)⁻¹ from hm 2 (by decide)]
    exact Subgroup.inv_mem _ (hg _ (by simp [sl]))
  · rw [show E 231 = ((m24a :: m24b :: sl).getD 5 1)⁻¹ from hm 3 (by decide)]
    exact Subgroup.inv_mem _ (hg _ (by simp [sl]))

include h in
theorem hsep :
    ∀ g : G, (∀ p ∈ D.sep, @act G _ (24 * 24) (pairAction G 24) g p = p) → g = 1 := by
  intro g hg
  change ∀ p ∈ J.sep, _ at hg
  rw [h.2.2.2.2.1] at hg
  exact sep_pair base_of_faithful g hg

include h in
theorem dc_complete :
    ∀ Z : Subgroup G, Subgroup.closure {x | x ∈ m24SgK} ≤ Z →
      ∃ j ≤ J.mw.length, Z = memberOrTop J.mw.length
        (fun j => Subgroup.closure {x | x ∈ m24SgK ++ (J.mw.getD j []).map (wordElt m24a m24b)})
        j := by
  have h0 := @dcCheck_sound G _ _ (24 * 24) (pairAction G 24) C rfl D m24a m24b m24_hyp.gen sl
    rfl (hL h) (hS h)
    (by change Nat.card (Subgroup.closure {x | x ∈ sl.take 4}) = 2 ^ 10
        rw [htake]; exact m24K_sGens.2)
    (by change Nat.card G = 239085 * 2 ^ 10; rw [card_M24]; norm_num) (hsep h) (by decide) h.1
  have h0 := h0.2
  change ∀ Z : Subgroup G, Subgroup.closure {x | x ∈ sl.take 4} ≤ Z → ∃ j ≤ J.mw.length,
      Z = memberOrTop J.mw.length (fun j => Subgroup.closure
        {x | x ∈ sl.take 4 ++ (J.mw.getD j []).map (wordElt m24a m24b)}) j at h0
  rw [htake] at h0
  exact h0

theorem mw_size_eq : m24LatK.mw.size = J.mw.length := by
  change J.mw.toArray.size = _
  simp

include h in
theorem mw_size : m24LatK.mw.size = 13 := by rw [mw_size_eq, h.2.2.2.2.2.2.2.1]

theorem mw_get (j : ℕ) : m24LatK.mw[j]! = J.mw.getD j [] := by
  change J.mw.toArray[j]! = _
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getD_eq_getElem?_getD]
  rfl

include h in
theorem mt_get {j : ℕ} (hj : j < 13) :
    m24LatK.mt[j]! = (m24LatK.mw[j]!).map (wordTabA #[m24ta.toArray, m24tb.toArray] 24) := by
  have hl : J.mw.length = 13 := h.2.2.2.2.2.2.2.1
  rw [wordTabA_eq_L]
  change (J.mw.toArray.map _)[j]! = (J.mw.toArray[j]!).map _
  rw [getElem!_pos _ j (by simp [hl, hj]), getElem!_pos J.mw.toArray j (by simp [hl, hj])]
  simp

theorem Om_get {j : ℕ} (hj : j < 13) : m24LatK.Om[j]! = Om j := by
  interval_cases j <;> rfl

theorem Ot_get {j : ℕ} (hj : j < 13) : m24OtK[j]! = Ot j := by
  interval_cases j <;> rfl

include h in
theorem T_eq : T 0 = m24ta.toArray ∧ T 1 = m24tb.toArray ∧ sT = m24STabs := by
  simp [T, sT, h.2.1, m24STabs, m24Qp]

include h in
theorem mLet_eq {j : ℕ} (hj : j < 13) : (m24LatK.sTabs ++ m24LatK.mt[j]!).toArray = mLet j := by
  rw [mt_get h hj, mw_get, wordTabA_eq_L]
  unfold mLet
  rw [(T_eq h).1, (T_eq h).2.1, (T_eq h).2.2]
  rfl

include h in
theorem mw_lt2 {j : ℕ} : ∀ w ∈ J.mw.getD j [], ∀ l ∈ w, l < 2 := by
  intro w hw l hl
  have h1 := h.2.2.2.2.2.1
  unfold CFSG.KD.M24Dc.mwOK at h1
  rcases Nat.lt_or_ge j J.mw.length with hj | hj
  · rw [List.getD_eq_getElem _ _ hj] at hw
    have h2 := List.all_eq_true.1 h1 _ (List.getElem_mem hj)
    have h3 := List.all_eq_true.1 (List.all_eq_true.1 h2 w hw) l hl
    simpa using h3
  · rw [List.getD_eq_default _ _ hj] at hw
    simp at hw

include h in
theorem m24K_membersOK :
    MembersOK (codeSetAct 24) 24 m24ta.toArray m24tb.toArray m24Delta m24LatK := by
  refine ⟨by rw [mw_size h]; decide, by rw [mw_get]; exact h.2.2.2.2.2.2.1, by simp [m24LatK],
    by rw [mw_size h]; rfl, fun j hj => ?_⟩
  have hj' : j < 13 := by rw [mw_size h] at hj; exact hj
  refine ⟨by rw [mw_get]; exact mw_lt2 h, mt_get h hj', ?_⟩
  rw [mLet_eq h hj', delta_eq, Om_get hj']
  exact omCode_sound (List.all_eq_true.1 h.2.2.2.2.2.2.2.2.1 j (List.mem_range.2 hj'))

theorem size_of_map {A : Array (OmegaData (List ℕ))} {s : Array ℕ}
    (e : A.map (fun o => o.lbl.size) = s) {j : ℕ} (hj : j < s.size) : A[j]!.lbl.size = s[j]! := by
  subst e
  have hj' : j < A.size := by simpa using hj
  rw [getElem!_pos A j hj', getElem!_pos _ j hj, Array.getElem_map]

include h in
theorem om_size (j : ℕ) (hj : j < 13) :
    (Om j).lbl.size = #[1, 315, 63, 135, 21, 9, 21, 3, 3, 3, 9, 3, 9][j]! := by
  rw [← Om_get hj]
  exact size_of_map h.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by simpa using hj)

theorem size_of_mapT {A : Array (OmegaData (List (List ℕ)))} {s : Array ℕ}
    (e : A.map (fun o => o.lbl.size) = s) {j : ℕ} (hj : j < s.size) : A[j]!.lbl.size = s[j]! := by
  subst e
  have hj' : j < A.size := by simpa using hj
  rw [getElem!_pos A j hj', getElem!_pos _ j hj, Array.getElem_map]

include h in
theorem ot_size (j : ℕ) (hj : j < 13) :
    (Ot j).lbl.size = #[1, 64, 16, 16, 8, 4, 8, 2, 2, 2, 4, 2, 4][j]! := by
  rw [← Ot_get hj]
  exact size_of_mapT h.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (by simpa using hj)

include h in
theorem rows_eq : (List.range 13).map (defaultRow 10 m24LatK m24OtK) = m24Mems := by
  have e : ∀ j ∈ List.range 13, defaultRow 10 m24LatK m24OtK j =
      ⟨#[1, 315, 63, 135, 21, 9, 21, 3, 3, 3, 9, 3, 9][j]! * 2 ^ 10,
        2 ^ 10 / #[1, 64, 16, 16, 8, 4, 8, 2, 2, 2, 4, 2, 4][j]!,
        #[1, 315, 63, 135, 21, 9, 21, 3, 3, 3, 9, 3, 9][j]! * 2 ^ 10⟩ := by
    intro j hj
    have hj' := List.mem_range.1 hj
    unfold defaultRow
    rw [Om_get hj', om_size h j hj', Ot_get hj', ot_size h j hj']
  rw [List.map_congr_left e]
  rfl

include h in
theorem m24K_o2OK : O2OK (codeSetAct 24) m24LatK m24OtK := by
  refine ⟨by rw [mw_size h]; rfl, fun j hj => ?_⟩
  have hj' : j < 13 := by rw [mw_size h] at hj; exact hj
  have hodd : (Om j).lbl.size % 2 = 1 := by
    rw [om_size h j hj']
    interval_cases j <;> rfl
  rw [Om_get hj', Ot_get hj']
  refine ⟨hodd, ?_⟩
  have hs : m24LatK.sTabs.toArray = sT.toArray := by rw [(T_eq h).2.2]; rfl
  rw [hs]
  exact (omOKG_sound (act := tupAct (codeSetAct 24)) (letters := sT.toArray) (fun _ => True)
    trivial (fun l _ X _ => ⟨trivial, by
      unfold tupAct
      rw [codeSetAct_eq, Array.getElem!_eq_getD]
      rfl⟩)
    (List.all_eq_true.1 h.2.2.2.2.2.2.2.2.2.1 j (List.mem_range.2 hj'))).1

theorem hel : ∀ l < (#[m24a, m24b] : Array G).size,
    (#[m24ta.toArray, m24tb.toArray] : Array (Array ℕ)).getD l #[] =
      (tab 24 ((#[m24a, m24b] : Array G).getD l 1)).toArray
  | 0, _ => ta_eq.symm
  | 1, _ => tb_eq.symm
  | _ + 2, h => absurd h (by simp)

include h in
theorem lab_word {w : List ℕ} (hw : ∀ l ∈ w, l < 2) :
    lab 24 (codeSetLab 24) m24Delta (wordElt m24a m24b w) =
      codeSetT 24 (wordTabL #[T 0, T 1] 24 w) Δc := by
  change codeSetAct 24 (tab 24 (evalElt #[m24a, m24b] w)).toArray m24Delta = _
  rw [← wordTabA_eq #[m24a, m24b] _ hel w (by simpa using hw), codeSetAct_eq, delta_eq,
    wordTabA_eq_L, (T_eq h).1, (T_eq h).2.1]

include h in
theorem hfix :
    ∀ s ∈ m24SgK, lab 24 (codeSetLab 24) m24Delta s = m24Delta := by
  intro s hs
  have ht : (tab 24 s).toArray ∈ sT := by
    rw [(T_eq h).2.2, ← m24K_sGens.1]
    exact List.mem_map_of_mem hs
  change codeSetAct 24 (tab 24 s).toArray m24Delta = m24Delta
  rw [codeSetAct_eq, delta_eq]
  have h1 := h.2.2.2.2.2.2.2.2.2.2.1
  unfold CFSG.KD.M24Dc.fixOK at h1
  exact beq_iff_eq.1 (List.all_eq_true.1 h1 _ ht)

include h in
theorem hmove : ∀ j, 0 < j → j < J.mw.length → ∃ w ∈ J.mw.getD j [],
    lab 24 (codeSetLab 24) m24Delta (wordElt m24a m24b w) ≠ m24Delta := by
  intro j h0 hj
  rw [h.2.2.2.2.2.2.2.1] at hj
  have h1 := h.2.2.2.2.2.2.2.2.2.2.2.1
  unfold CFSG.KD.M24Dc.moveOK at h1
  obtain ⟨w, hw, hne⟩ := List.any_eq_true.1
    (List.all_eq_true.1 h1 j (List.mem_range'_1.2 ⟨h0, by omega⟩))
  refine ⟨w, hw, ?_⟩
  rw [lab_word h (mw_lt2 h w hw), delta_eq]
  simpa using hne

include h in
theorem htop : lab 24 (codeSetLab 24) m24Delta m24a ≠ m24Delta ∨
    lab 24 (codeSetLab 24) m24Delta m24b ≠ m24Delta := by
  change codeSetAct 24 (tab 24 m24a).toArray m24Delta ≠ m24Delta ∨
    codeSetAct 24 (tab 24 m24b).toArray m24Delta ≠ m24Delta
  rw [ta_eq, tb_eq, codeSetAct_eq, delta_eq, ← (T_eq h).1, ← (T_eq h).2.1]
  have h1 := h.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold CFSG.KD.M24Dc.topOK at h1
  simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at h1
  exact h1

include h in
theorem m24K_stab :
    ∀ g : G, lab 24 (codeSetLab 24) m24Delta g = m24Delta ↔
      g ∈ Subgroup.closure {x | x ∈ m24SgK} :=
  stab_of_complete codeSetLab_lawful m24_delta_valid m24a m24b m24SgK J.mw (dc_complete h)
    (hfix h) h.2.2.2.2.2.2.1 (hmove h) (htop h)

include h in
theorem m24K_comp :
    ∀ Z : Subgroup G, Subgroup.closure {x | x ∈ m24SgK} ≤ Z →
      ∃ j ≤ m24LatK.mw.size, Z = memberOrTop m24LatK.mw.size
        (fun j => Subgroup.closure {x | x ∈ m24SgK ++ (m24LatK.mw[j]!).map (wordElt m24a m24b)})
          j := by
  intro Z hZ
  obtain ⟨j, hj, e⟩ := dc_complete h Z hZ
  refine ⟨j, by rw [mw_size_eq]; exact hj, ?_⟩
  rw [e, mw_size_eq]
  simp only [mw_get]

end Facts

variable (h : M24DcFacts)

@[expose] noncomputable def m24CtxK : LatCtx G 24 (List ℕ) :=
  LatCtx.ofFacts (codeSetLab 24) (CodeSetValid 24) codeSetLab_lawful m24Delta m24_delta_valid
    m24a m24b m24ta.toArray m24tb.toArray ta_eq tb_eq m24_hyp.gen m24LatK m24SgK 10
    m24K_sGens.1 m24K_sGens.2 239085 (by rw [card_M24]; norm_num) (m24K_membersOK h)
    (m24K_stab h) (m24K_comp h)

theorem m24K_D_mw : (m24CtxK h).D.mw = m24LatK.mw := rfl

theorem m24K_J : (m24CtxK h).J = 13 := by
  unfold LatCtx.J
  rw [m24K_D_mw, mw_size h]

theorem m24K_complete : ∀ Z : Subgroup G, (m24CtxK h).S ≤ Z →
    ∃ j ≤ 13, Z = memberOrTop 13 (m24CtxK h).Y j := by
  intro Z hZ
  obtain ⟨j, hj, rfl⟩ := (m24CtxK h).complete Z hZ
  rw [m24K_J] at hj ⊢
  exact ⟨j, hj, rfl⟩

theorem m24K_rows : (List.range 13).map (defaultRow 10 (m24CtxK h).D m24OtK) = m24Mems :=
  rows_eq h

theorem m24K_row (j : ℕ) (hj : j < 13) : ∃ m ∈ m24Mems, MemStmt ((m24CtxK h).Y j) m := by
  have hk : (m24CtxK h).k = 10 := rfl
  refine (m24CtxK h).rows_of_default (Ot := m24OtK) (m24K_o2OK h) m24Mems ?_ j
    (by rw [m24K_J]; exact hj)
  rw [m24K_J, hk]
  exact m24K_rows h

theorem m24K_S_sylow : CFSG.QuasithinUnique.IsSylowTwoOf (m24CtxK h).S ⊤ := by
  refine CFSG.QuasithinUnique.K1.isSylowTwoOf_top_iff.mpr ⟨(m24CtxK h).S_isPGroup, ?_⟩
  have h1 := Subgroup.card_mul_index (m24CtxK h).S
  rw [(m24CtxK h).S_card, card_M24] at h1
  have h2 : (m24CtxK h).S.index = 239085 := by
    have : (m24CtxK h).k = 10 := rfl
    rw [this] at h1
    omega
  rw [h2]
  norm_num

open CFSG.Blueprint.NativeSporadic in
include h in
theorem m24K_overgroups {X : Type} [Group X] [Finite X] (hX : Nonempty (X ≃* Carrier .M24))
    {T Y : Subgroup X} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) (hTY : T ≤ Y) :
    Y = ⊤ ∨ ∃ m ∈ m24Mems, Nat.card Y = m.order ∧ Nat.card (pCoreOf 2 Y) = m.o2 ∧
      ∀ (N : Subgroup Y) [N.Normal], IsPGroup 2 (Y ⧸ N) → Nat.card (Y ⧸ N) ≤ m.quot2 := by
  obtain ⟨e⟩ := hX
  have hX' : Nonempty (X ≃* G) := ⟨e⟩
  exact overgroups_of_lattice (m24CtxK h).S (m24K_S_sylow h) 13 (m24CtxK h).Y m24Mems
    (m24K_complete h) (fun j hj => m24K_row h j hj) hX' hT hTY

end CFSG.QuasithinUnique.Ch1.SporLat.M24K

end
