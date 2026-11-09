module

public import CFSG.Certificates.Kernel.CosetBounds
import all CFSG.Certificates.Kernel.CosetBounds
public import CFSG.Certificates.Kernel.CosetBoundsFwd
public import Certificates.Data.Kernel.Bounds.TableE

public section

namespace CFSG.Certificates.KB

open CFSG.Certificates.KB.Sound

theorem tableOkE_lens {inv L eps nLab nT N RW RM nR nS nW nF : ℕ} {F D Wd Wd2 R S : ℕ → ℕ}
    {amap : ℕ} {rels words : List (List (ℕ × Bool))} {walk cov : List ℕ}
    (h : tableOkE inv L eps nLab nT N RW RM nR nS nW nF F D Wd Wd2 R S amap rels words walk cov =
      true) : (∀ r ∈ rels, r.length < 256) ∧ ∀ w ∈ words, w.length < 256 := by
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨hr, h⟩ := andB_true h
  obtain ⟨hw, -⟩ := andB_true h
  exact ⟨(lensLt_iff _ _).mp hr, (lensLt_iff _ _).mp hw⟩

theorem tableOkE_sound_alpha {G : Type*} [Group G] (gen : ℕ → G) {rels : List (List (ℕ × Bool))}
    {inv L eps nLab nT N RW RM nR nS nW nF : ℕ} {F D Wd Wd2 R S : ℕ → ℕ} {amap : ℕ}
    (hrels : ∀ r ∈ rels, (∀ x ∈ r, inAlpha amap x.1) → sword gen r = 1)
    {words : List (List (ℕ × Bool))} {walk cov : List ℕ}
    (h : tableOkE inv L eps nLab nT N RW RM nR nS nW nF F D Wd Wd2 R S amap rels words walk cov =
      true) :
    wordSub gen words ≤ alphaSub gen amap ∧ (wordSub gen words).relIndex (alphaSub gen amap) ≠ 0 ∧
      (wordSub gen words).relIndex (alphaSub gen amap) ≤ N := by
  obtain ⟨hlr, hlw⟩ := tableOkE_lens h
  unfold tableOkE at h
  simp only [andB_true_iff] at h
  obtain ⟨hL128, hN1, hNl, hlab, hlabbad, hFbad, hnRb, hnSb, -, -, hhdr, hrel, hsub, hwords, hw2,
    htree, hwalk, hcov⟩ := h
  have hL128' : L + 1 ≤ 128 := Nat.le_of_ble_eq_true hL128
  have hN1' : 1 ≤ N := Nat.le_of_ble_eq_true hN1
  have hNl' : N ≤ nLab := Nat.le_of_ble_eq_true hNl
  have hlab' : nLab = nT + 1 := Nat.eq_of_beq_eq_true hlab
  have hlabbad' : nLab + 1 ≤ bad := Nat.le_of_ble_eq_true hlabbad
  have hFbad' : nF + 1 ≤ bad := Nat.le_of_ble_eq_true hFbad
  have hnRb' : nR + 1 ≤ bad := Nat.le_of_ble_eq_true hnRb
  have hnSb' : nS + 1 ≤ bad := Nat.le_of_ble_eq_true hnSb
  have hwalk' := Nat.eq_of_beq_eq_true hwalk
  have hcov' := Nat.eq_of_beq_eq_true hcov
  obtain ⟨heps, hinvOk, halpha⟩ := hdrOk_spec hhdr
  obtain ⟨cnt, hL, hcard, hsurj⟩ := alphaOk_spec halpha
  obtain ⟨hle, hinj⟩ := alpha_struct hcard hsurj
  have hA : AlphaStruct amap cnt := ⟨hle, hinj, hsurj⟩
  obtain ⟨hinvL, hinvc⟩ := invOk_spec hinvOk
  have hLe : L % 2 = 0 := by omega
  have hLh : 2 * Nat.shiftRight L (nat_lit 1) = L := by
    change 2 * (L >>> 1) = L
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have hxor : ∀ c < L, letterVal gen amap L (Nat.xor c 1) = (letterVal gen amap L c)⁻¹ :=
    fun c hc => (letterVal_xor gen hLe hc).2
  have hvL : letterVal gen amap L L = 1 := by
    unfold letterVal
    rw [ite_eq_right_of_eq_false _ _ (eq_false (Nat.lt_irrefl L))]
  have hinvv : ∀ c ≤ L, letterVal gen amap L (byte inv c) = (letterVal gen amap L c)⁻¹ := by
    intro c hc
    rcases Nat.lt_or_eq_of_le hc with hc | rfl
    · rw [hinvc c hc]
      exact hxor c hc
    · rw [hinvL, hvL, inv_one]
  have hR : ∀ i < nR, wLetters (R i) = pkb 256 (wbytes (R i)) ∧
      lv (letterVal gen amap L) (wbytes (R i)) = 1 := by
    unfold relsOk at hrel
    have hfold := Nat.eq_of_beq_eq_true hrel
    have hg := (relsOk_run R amap rels 0).good (by rw [hfold]; omega)
    rw [hfold] at hg
    intro i hi
    obtain ⟨r, hr, hok, hRi⟩ := hg i (Nat.zero_le _) hi
    have hrlen := hlr r hr
    obtain ⟨hs1, hs2⟩ := sEnc_spec amap r (by omega)
    have hin : ∀ x ∈ r, inAlpha amap x.1 := fun x hx => sCode_lt (hs1.1 hok x hx)
    have hcodes : ∀ d ∈ r.map (sCode amap), d < 256 := by
      intro d hd
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
      exact hs1.1 hok x hx
    have hwb : wbytes (r.length + 2 ^ 24 * pkb 256 (r.map (sCode amap))) = r.map (sCode amap) := by
      rw [wbytes, entry_wN _ _ hrlen, entry_wLetters _ _ (by omega)]
      have := bytes_pkb _ hcodes
      rwa [List.length_map] at this
    rw [hRi, hs2 hok, hwb, entry_wLetters _ _ (by omega), lv_codes gen hA hL r hin]
    exact ⟨rfl, hrels r hr hin⟩
  obtain ⟨hnS, hS⟩ := subsOk_spec hsub (by omega)
  have hwords_in : ∀ w ∈ words, ∀ x ∈ w, inAlpha amap x.1 := by
    intro w hw x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hw
    have hwlen := hlw _ hw
    exact sCode_lt ((sEnc_spec amap _ (by omega)).1.1 (hS i hi).1 x hx)
  have hSv : ∀ i < nS, lv (letterVal gen amap L) (wbytes (S i)) ∈ wordSub gen words := by
    intro i hi
    rw [hnS] at hi
    obtain ⟨hok, hSi⟩ := hS i hi
    have hwmem : words[i] ∈ words := List.getElem_mem hi
    have hwlen := hlw _ hwmem
    obtain ⟨hs1, hs2⟩ := sEnc_spec amap words[i] (by omega)
    have hcodes : ∀ d ∈ words[i].map (sCode amap), d < 256 := by
      intro d hd
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
      exact hs1.1 hok x hx
    have hwb : wbytes ((words[i].length + 256) + 2 ^ 24 * pkb 256 (words[i].map (sCode amap))) =
        words[i].map (sCode amap) := by
      rw [wbytes, entry_wN_lor _ _ hwlen, entry_wLetters _ _ (by omega)]
      have := bytes_pkb _ hcodes
      rwa [List.length_map] at this
    rw [hSi, hs2 hok, entry_lor _ _ hwlen, hwb, lv_codes gen hA hL _ (hwords_in _ hwmem)]
    exact Subgroup.subset_closure ⟨_, hwmem, rfl⟩
  have hW : ∀ j < nW, (∀ q < wN (Wd j), letter (Wd j) q ≤ L) ∧
      (wKind (Wd j) = 0 → lv (letterVal gen amap L) (wbytes (Wd j)) = 1) ∧
      (wKind (Wd j) = 1 → lv (letterVal gen amap L) (wbytes (Wd j)) ∈ wordSub gen words) := by
    intro j hj
    unfold wordsOkB at hwords
    obtain ⟨h1, h2⟩ := natrec_all2 (fun i => wordOkB R S inv eps nR nS (Wd i))
      (fun i => lettersLe eps (Wd i)) nW hwords j hj
    have := word_sem (wordSub gen words) (letterVal gen amap L) (by omega : eps < 128)
      (by rw [heps]; exact hvL) (fun c hc => hinvv c (by omega)) hR hSv h1 h2
    rwa [heps] at this
  have hcl := cover_closedE (wordSub gen words) (letterVal gen amap L) hLh hNl' hlab' hlabbad'
    hFbad' hxor hinvv hW hw2 htree hwalk' hcov'
  have hHA : wordSub gen words ≤ alphaSub gen amap := by
    rw [wordSub, Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    exact sword_mem gen w (hwords_in w hw)
  obtain ⟨h0, hle'⟩ := index_le_even (letterVal gen amap L) (rep (letterVal gen amap L) F D nT)
    (alphaSub_le_closure gen hA hL) (rep_mem _ F D nT _ (letterVal_mem gen hA hL))
    (rep_zero _ F D nT) hN1' (fun c hc => letterVal_xor gen hLe hc) hcl
  exact ⟨hHA, h0, hle'⟩

end CFSG.Certificates.KB

end
