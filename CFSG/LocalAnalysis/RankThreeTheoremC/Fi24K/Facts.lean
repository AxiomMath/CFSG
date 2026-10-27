module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.Fi7Gen
public import Certificates.Certificate753522

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K

open CFSG.Sporadic.Fi24 CFSG.Sporadic.Fi24.Native CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Dickson.I271.Fi7 CFSG.Perm
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24SevenNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Seven
  CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube


@[expose] def WK : Array (List ℤ) := fi24SevenData.words ++ fi24kExtra ()

@[expose] noncomputable def sK (j : ℕ) : CFSG.Sporadic.Fi24.J := CFSG.Sporadic.Fi23.slpG genG WK j


structure Fi24KFacts : Prop where
  slp : CFSG.Sporadic.Fi23.Native.slpOK WK = true
  size_words : fi24SevenData.words.size = 1087
  size_extra : (fi24kExtra ()).size = 2733
  w0 : fi24SevenData.words[0]! = [1]
  w1 : fi24SevenData.words[1]! = [2]
  header : headerOK (fi24kExtra ()) = true
  comm85 : eqRows 781 (mulW (mLetters WK)[2 * 1085]! (mLetters WK)[2 * 67]!)
    (mulW (mLetters WK)[2 * 67]! (mLetters WK)[2 * 1085]!) = true
  comm86 : eqRows 781 (mulW (mLetters WK)[2 * 1086]! (mLetters WK)[2 * 67]!)
    (mulW (mLetters WK)[2 * 67]! (mLetters WK)[2 * 1086]!) = true
  comm82 : eqRows 781 (mulW (mLetters WK)[2 * 1082]! (mLetters WK)[2 * 66]!)
    (mulW (mLetters WK)[2 * 66]! (mLetters WK)[2 * 1082]!) = true
  comm83 : eqRows 781 (mulW (mLetters WK)[2 * 1083]! (mLetters WK)[2 * 66]!)
    (mulW (mLetters WK)[2 * 66]! (mLetters WK)[2 * 1083]!) = true
  comm84 : eqRows 781 (mulW (mLetters WK)[2 * 1084]! (mLetters WK)[2 * 66]!)
    (mulW (mLetters WK)[2 * 66]! (mLetters WK)[2 * 1084]!) = true
  mixed : ∀ m ∈ mixedSecs, mixedOK WK (mLetters WK) m = true
  pure : ∀ q ∈ pureSecs,
    pureOK WK (mLetters WK) TauCeti.Sporadic.hePresentation.relatorLetters q = true

theorem fi24k_parts : Fi24KFacts := by
  have h := Certificates.certificate753522
  unfold fi24kOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

structure Fi24KHeader : Prop where
  c3 : (fi24SevenData.conj[3]!).1 = 1
  e0 : (fi24kExtra ())[0]! = (fi24SevenData.conj[3]!).2.map lt2w
  c49 : (fi24SevenData.conj[49]!).1 = 0
  e1 : (fi24kExtra ())[1]! = (fi24SevenData.conj[49]!).2.map lt2w
  line : ∀ i < 6, (fi24SevenData.conj[56 + 7 * i]!).1 = 1 ∧
    (fi24kExtra ())[2 + i]! = (fi24SevenData.conj[56 + 7 * i]!).2.map lt2w
  even : ∀ i < 6, (fi24kExtra ())[8 + 2 * i]! =
    [-((1092 + i : ℕ) : ℤ), 1088, ((1092 + i : ℕ) : ℤ)]
  odd : ∀ i < 6, (fi24kExtra ())[9 + 2 * i]! =
    [-((1092 + i : ℕ) : ℤ), 1089, ((1092 + i : ℕ) : ℤ)]
  e20 : (fi24kExtra ())[20]! = [-1091, 1085, 1091]
  e21 : (fi24kExtra ())[21]! = [-1091, 1086, 1091]
  e22 : (fi24kExtra ())[22]! = [-1091, 1087, 1091]

theorem headerOK_parts (h : headerOK (fi24kExtra ()) = true) : Fi24KHeader := by
  unfold headerOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, fun i hi => (h6 i hi).1, fun i hi => (h6 i hi).2, h7, h8, h9⟩

theorem WK_size : WK.size = 3820 := by
  have := fi24k_parts
  simp only [WK, Array.size_append, this.size_words, this.size_extra]

theorem WK_get_left {j : ℕ} (hj : j < 1087) : WK[j]! = fi24SevenData.words[j]! := by
  rw [WK, arr_getElem!_append_left _ _ (by rw [fi24k_parts.size_words]; exact hj)]

theorem WK_get_right {k : ℕ} (hk : k < 2733) : WK[1087 + k]! = (fi24kExtra ())[k]! := by
  have hs := fi24k_parts.size_words
  have hs2 := fi24k_parts.size_extra
  have h1 : fi24SevenData.words.size ≤ 1087 + k := by omega
  have h2 : 1087 + k - fi24SevenData.words.size < (fi24kExtra ()).size := by omega
  have h3 := arr_getElem!_append_right fi24SevenData.words (fi24kExtra ()) h1 h2
  have h4 : 1087 + k - fi24SevenData.words.size = k := by omega
  rwa [h4] at h3

theorem sK_prefix {j : ℕ} (hj : j < 1087) : sK j = g7 j := by
  unfold sK g7 WK
  exact slpG_append_prefix genG _ _ j (by rw [fi24k_parts.size_words]; exact hj)

@[expose] noncomputable def letterK (j : ℕ) (z : ℤ) : CFSG.Sporadic.Fi24.J :=
  if z.natAbs ≤ 2 then genG z else if z.natAbs - 3 < j then
    (if 0 < z then sK (z.natAbs - 3) else (sK (z.natAbs - 3))⁻¹) else 1

theorem sK_eq (j : ℕ) : sK j = wordG (letterK j) WK[j]! :=
  CFSG.Sporadic.Fi23.slpG_eq genG WK j

theorem letterK_pos {j k : ℕ} (hk : k < j) : letterK j ((k + 3 : ℕ) : ℤ) = sK k := by
  have h3 : ¬ k + 3 ≤ 2 := by omega
  have h0 : (0 : ℤ) < ((k + 3 : ℕ) : ℤ) := by positivity
  simp only [letterK, Int.natAbs_natCast, h3, if_false, Nat.add_sub_cancel, hk, if_true, h0]

theorem letterK_neg {j k : ℕ} (hk : k < j) : letterK j (-((k + 3 : ℕ) : ℤ)) = (sK k)⁻¹ := by
  have h3 : ¬ k + 3 ≤ 2 := by omega
  have h0 : ¬ (0 : ℤ) < -((k + 3 : ℕ) : ℤ) := by omega
  simp only [letterK, Int.natAbs_neg, Int.natAbs_natCast, h3, if_false, Nat.add_sub_cancel, hk,
    if_true, h0]

theorem sim_sK {j : ℕ} (hj : j < 3820) : Fi24Sim (mLetters WK)[2 * j]! (sK j) :=
  ((sim_mLetters fi24k_parts.slp).2 j (by rw [WK_size]; exact hj)).1

theorem sK_zero : sK 0 = CFSG.Sporadic.Fi24.a := by
  rw [sK_eq, WK_get_left (by norm_num), fi24k_parts.w0]
  simp [wordG, letterK, genG]

theorem sK_one : sK 1 = CFSG.Sporadic.Fi24.b := by
  rw [sK_eq, WK_get_left (by norm_num), fi24k_parts.w1]
  simp [wordG, letterK, genG]

theorem sK_X7 : X7 = sK 64 := (sK_prefix (j := 64) (by norm_num)).symm

theorem sK_Y7 : Y7 = sK 66 := (sK_prefix (j := 66) (by norm_num)).symm

theorem sK_C7 : C7 = sK 67 := (sK_prefix (j := 67) (by norm_num)).symm

theorem conjLine_mem {lam : ℕ} (h1 : 1 ≤ lam) (h6 : lam ≤ 6) : 49 + 7 * lam ∈ conjTs := by
  interval_cases lam <;> decide

theorem sK_eq_M7 {j t : ℕ} (hj : 1087 ≤ j) (ht : t ∈ conjTs)
    (hw : WK[j]! = (fi24SevenData.conj[t]!).2.map lt2w) : sK j = M7 t := by
  rw [sK_eq, hw, M7]
  unfold wordG
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro l hl
  have hl' : l < 2 * 1087 := conj_letters_lt ht l hl
  have hl2 : l / 2 < 1087 := by omega
  simp only [Function.comp]
  by_cases hev : l % 2 = 0
  · have : lt2w l = ((l / 2 + 3 : ℕ) : ℤ) := by simp [lt2w, hev]
    rw [this, letterK_pos (by omega), sK_prefix hl2]
    simp [pairG, hev]
  · have : lt2w l = -((l / 2 + 3 : ℕ) : ℤ) := by simp [lt2w, hev]
    rw [this, letterK_neg (by omega), sK_prefix hl2]
    simp [pairG, hev]

theorem sK_1087 : sK 1087 = M7 3 := by
  refine sK_eq_M7 le_rfl (by decide) ?_
  have h := (headerOK_parts fi24k_parts.header).e0
  rw [← WK_get_right (k := 0) (by norm_num)] at h
  exact h

theorem sK_1088 : sK 1088 = M7 49 := by
  refine sK_eq_M7 (by norm_num) (by decide) ?_
  have h := (headerOK_parts fi24k_parts.header).e1
  rw [← WK_get_right (k := 1) (by norm_num)] at h
  exact h

theorem sK_conjLine {lam : ℕ} (h1 : 1 ≤ lam) (h6 : lam ≤ 6) :
    sK (1088 + lam) = M7 (49 + 7 * lam) := by
  refine sK_eq_M7 (by omega) (conjLine_mem h1 h6) ?_
  have h := (headerOK_parts fi24k_parts.header).line (lam - 1) (by omega)
  have e1 : 2 + (lam - 1) = 1 + lam := by omega
  have e2 : 56 + 7 * (lam - 1) = 49 + 7 * lam := by omega
  rw [e1, e2] at h
  have e : 1088 + lam = 1087 + (1 + lam) := by omega
  rw [e, WK_get_right (by omega)]
  exact h.2

theorem sK_1087_conj : sK 1087 * C7 ^ 3 = C7 * sK 1087 := by
  have hrel := fi7_conj_rel (t := 3) (by decide)
  have hc : (fi24SevenData.conj[3]!).1 = 1 := (headerOK_parts fi24k_parts.header).c3
  have hif : (if (fi24SevenData.conj[3]!).1 == 0 then Y7 else C7) = C7 := by simp [hc]
  rw [hif] at hrel
  have hcube : cube7 3 = C7 ^ 3 := by norm_num [cube7]
  rw [hcube] at hrel
  rw [sK_1087]
  exact hrel

theorem sK_1088_conj : sK 1088 * X7 = Y7 * sK 1088 := by
  have hrel := fi7_conj_rel (t := 49) (by decide)
  have hc : (fi24SevenData.conj[49]!).1 = 0 := (headerOK_parts fi24k_parts.header).c49
  have hif : (if (fi24SevenData.conj[49]!).1 == 0 then Y7 else C7) = Y7 := by simp [hc]
  rw [hif] at hrel
  have hcube : cube7 49 = X7 := by norm_num [cube7]
  rw [hcube] at hrel
  rw [sK_1088]
  exact hrel

theorem sK_conjLine_conj {lam : ℕ} (h1 : 1 ≤ lam) (h6 : lam ≤ 6) :
    sK (1088 + lam) * (X7 * Y7 ^ lam) = C7 * sK (1088 + lam) := by
  have hlab := (headerOK_parts fi24k_parts.header).line (lam - 1) (by omega)
  have e2 : 56 + 7 * (lam - 1) = 49 + 7 * lam := by omega
  rw [e2] at hlab
  have hrel := fi7_conj_rel (t := 49 + 7 * lam) (conjLine_mem h1 h6)
  have hif : (if (fi24SevenData.conj[49 + 7 * lam]!).1 == 0 then Y7 else C7) = C7 := by
    simp [hlab.1]
  rw [hif] at hrel
  have hcube : cube7 (49 + 7 * lam) = X7 * Y7 ^ lam := by
    simp only [cube7]
    have e1 : (49 + 7 * lam) / 49 = 1 := by omega
    have e2 : (49 + 7 * lam) / 7 % 7 = lam := by omega
    have e3 : (49 + 7 * lam) % 7 = 0 := by omega
    rw [e1, e2, e3]
    simp
  rw [hcube] at hrel
  rw [sK_conjLine h1 h6]
  exact hrel

theorem sK_cent85 {lam : ℕ} (h1 : 1 ≤ lam) (h6 : lam ≤ 6) :
    sK (1093 + 2 * lam) = (sK (1088 + lam))⁻¹ * sK 1085 * sK (1088 + lam) := by
  have hE := (headerOK_parts fi24k_parts.header).even (lam - 1) (by omega)
  have e8 : 8 + 2 * (lam - 1) = 6 + 2 * lam := by omega
  have e1092 : 1092 + (lam - 1) = 1091 + lam := by omega
  rw [e8, e1092] at hE
  have hW : WK[1093 + 2 * lam]! =
      [-((1091 + lam : ℕ) : ℤ), 1088, ((1091 + lam : ℕ) : ℤ)] := by
    rw [show 1093 + 2 * lam = 1087 + (6 + 2 * lam) by omega, WK_get_right (by omega)]
    exact hE
  rw [sK_eq, hW]
  have h1' : letterK (1093 + 2 * lam) (-((1091 + lam : ℕ) : ℤ)) =
      (sK (1088 + lam))⁻¹ := by
    have := letterK_neg (j := 1093 + 2 * lam) (k := 1088 + lam) (by omega)
    rwa [show ((1088 + lam + 3 : ℕ) : ℤ) = ((1091 + lam : ℕ) : ℤ) by congr 1; omega] at this
  have h2' : letterK (1093 + 2 * lam) (1088 : ℤ) = sK 1085 := by
    have := letterK_pos (j := 1093 + 2 * lam) (k := 1085) (by omega)
    rwa [show ((1085 + 3 : ℕ) : ℤ) = (1088 : ℤ) by norm_num] at this
  have h3' : letterK (1093 + 2 * lam) ((1091 + lam : ℕ) : ℤ) = sK (1088 + lam) := by
    have := letterK_pos (j := 1093 + 2 * lam) (k := 1088 + lam) (by omega)
    rwa [show ((1088 + lam + 3 : ℕ) : ℤ) = ((1091 + lam : ℕ) : ℤ) by congr 1; omega] at this
  simp only [wordG, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, h1', h2', h3']
  simp [mul_assoc]

theorem sK_cent86 {lam : ℕ} (h1 : 1 ≤ lam) (h6 : lam ≤ 6) :
    sK (1094 + 2 * lam) = (sK (1088 + lam))⁻¹ * sK 1086 * sK (1088 + lam) := by
  have hE := (headerOK_parts fi24k_parts.header).odd (lam - 1) (by omega)
  have e8 : 9 + 2 * (lam - 1) = 7 + 2 * lam := by omega
  have e1092 : 1092 + (lam - 1) = 1091 + lam := by omega
  rw [e8, e1092] at hE
  have hW : WK[1094 + 2 * lam]! =
      [-((1091 + lam : ℕ) : ℤ), 1089, ((1091 + lam : ℕ) : ℤ)] := by
    rw [show 1094 + 2 * lam = 1087 + (7 + 2 * lam) by omega, WK_get_right (by omega)]
    exact hE
  rw [sK_eq, hW]
  have h1' : letterK (1094 + 2 * lam) (-((1091 + lam : ℕ) : ℤ)) =
      (sK (1088 + lam))⁻¹ := by
    have := letterK_neg (j := 1094 + 2 * lam) (k := 1088 + lam) (by omega)
    rwa [show ((1088 + lam + 3 : ℕ) : ℤ) = ((1091 + lam : ℕ) : ℤ) by congr 1; omega] at this
  have h2' : letterK (1094 + 2 * lam) (1089 : ℤ) = sK 1086 := by
    have := letterK_pos (j := 1094 + 2 * lam) (k := 1086) (by omega)
    rwa [show ((1086 + 3 : ℕ) : ℤ) = (1089 : ℤ) by norm_num] at this
  have h3' : letterK (1094 + 2 * lam) ((1091 + lam : ℕ) : ℤ) = sK (1088 + lam) := by
    have := letterK_pos (j := 1094 + 2 * lam) (k := 1088 + lam) (by omega)
    rwa [show ((1088 + lam + 3 : ℕ) : ℤ) = ((1091 + lam : ℕ) : ℤ) by congr 1; omega] at this
  simp only [wordG, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, h1', h2', h3']
  simp [mul_assoc]

theorem sK_centX {k : ℕ} (hk : k < 3) :
    sK (1107 + k) = (sK 1088)⁻¹ * sK (1082 + k) * sK 1088 := by
  have hd := headerOK_parts fi24k_parts.header
  interval_cases k
  · rw [sK_eq, show WK[1107]! = (fi24kExtra ())[20]! by
      rw [show 1107 = 1087 + 20 by norm_num, WK_get_right (by norm_num)], hd.e20]
    simp [wordG, letterK, mul_assoc]
  · rw [sK_eq, show WK[1108]! = (fi24kExtra ())[21]! by
      rw [show 1108 = 1087 + 21 by norm_num, WK_get_right (by norm_num)], hd.e21]
    simp [wordG, letterK, mul_assoc]
  · rw [sK_eq, show WK[1109]! = (fi24kExtra ())[22]! by
      rw [show 1109 = 1087 + 22 by norm_num, WK_get_right (by norm_num)], hd.e22]
    simp [wordG, letterK, mul_assoc]

theorem sK_comm {i k : ℕ} (hi : i < 3820) (hk : k < 3820)
    (e : eqRows 781 (mulW (mLetters WK)[2 * i]! (mLetters WK)[2 * k]!)
      (mulW (mLetters WK)[2 * k]! (mLetters WK)[2 * i]!) = true) :
    sK i * sK k = sK k * sK i :=
  sim_eq (sim_mul (sim_sK hi) (sim_sK hk)) (sim_mul (sim_sK hk) (sim_sK hi)) e

theorem sK_1085_comm : sK 1085 * C7 = C7 * sK 1085 := by
  rw [sK_C7]
  exact sK_comm (by norm_num) (by norm_num) fi24k_parts.comm85

theorem sK_1086_comm : sK 1086 * C7 = C7 * sK 1086 := by
  rw [sK_C7]
  exact sK_comm (by norm_num) (by norm_num) fi24k_parts.comm86

theorem sK_comm_Y7 {k : ℕ} (hk : k < 3) : sK (1082 + k) * Y7 = Y7 * sK (1082 + k) := by
  interval_cases k
  · rw [sK_Y7]
    exact sK_comm (by norm_num) (by norm_num) fi24k_parts.comm82
  · rw [sK_Y7]
    exact sK_comm (by norm_num) (by norm_num) fi24k_parts.comm83
  · rw [sK_Y7]
    exact sK_comm (by norm_num) (by norm_num) fi24k_parts.comm84

theorem secOK_mem_closure {gs : List ℕ} {lo hi : ℕ} (h : secOK WK gs lo hi = true) :
    ∀ j, lo ≤ j → j < hi → sK j ∈ Subgroup.closure (sK '' {k | k ∈ gs}) := by
  have hall : ∀ r < hi - lo, ∀ z ∈ WK[lo + r]!, 3 ≤ z.natAbs ∧
      (gs.contains (z.natAbs - 3) = true ∨
        (lo ≤ z.natAbs - 3 ∧ z.natAbs - 3 < lo + r)) := by
    unfold secOK at h
    rw [List.all_eq_true] at h
    intro r hr z hz
    have h1 := h r (List.mem_range.2 hr)
    rw [List.all_eq_true] at h1
    simpa only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] using h1 z hz
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj1 hj2
    have hr : ∀ z ∈ WK[j]!, 3 ≤ z.natAbs ∧
        (gs.contains (z.natAbs - 3) = true ∨
          (lo ≤ z.natAbs - 3 ∧ z.natAbs - 3 < j)) := by
      intro z hz
      have h1 := hall (j - lo) (by omega) z (by rwa [show lo + (j - lo) = j by omega])
      simpa [show lo + (j - lo) = j by omega] using h1
    rw [sK_eq]
    unfold wordG
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
    obtain ⟨hz3, hcase⟩ := hr z hz
    unfold letterK
    rw [if_neg (by omega)]
    rcases hcase with hg | ⟨hlo, hlt⟩
    · have hmem : z.natAbs - 3 ∈ gs := List.contains_iff_mem.1 hg
      by_cases hlt : z.natAbs - 3 < j
      · rw [if_pos hlt]
        split_ifs
        · exact Subgroup.subset_closure ⟨_, hmem, rfl⟩
        · exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨_, hmem, rfl⟩)
      · rw [if_neg hlt]
        exact Subgroup.one_mem _
    · rw [if_pos hlt]
      have hm := ih _ hlt hlo (by omega)
      split_ifs
      · exact hm
      · exact Subgroup.inv_mem _ hm

theorem mixedOK_parts {m : MixedSec} (hm : m ∈ mixedSecs) :
    secOK WK m.gs m.lo m.hi = true ∧ m.lo ≤ m.ia ∧ m.ia < m.hi ∧
      m.lo ≤ m.ib ∧ m.ib < m.hi ∧
      eqRows 781 (mLetters WK)[2 * m.ia]! (mLetters WK)[0]! = true ∧
      eqRows 781 (mLetters WK)[2 * m.ib]! (mLetters WK)[2]! = true := by
  have h := fi24k_parts.mixed m hm
  unfold mixedOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem mixed_sec_mem {m : MixedSec} (hm : m ∈ mixedSecs) (hh : m.hi ≤ 3820) :
    CFSG.Sporadic.Fi24.a ∈ Subgroup.closure (sK '' {k | k ∈ m.gs}) ∧
      CFSG.Sporadic.Fi24.b ∈ Subgroup.closure (sK '' {k | k ∈ m.gs}) := by
  obtain ⟨hsec, hlo, hia, hlib, hib, heqa, heqb⟩ := mixedOK_parts hm
  have ha : sK m.ia = a := by
    have h := sim_eq (sim_sK (j := m.ia) (by omega)) (sim_sK (j := 0) (by norm_num)) heqa
    rw [h, sK_zero]
  have hb : sK m.ib = b := by
    have h := sim_eq (sim_sK (j := m.ib) (by omega)) (sim_sK (j := 1) (by norm_num)) heqb
    rw [h, sK_one]
  exact ⟨by rw [← ha]; exact secOK_mem_closure hsec m.ia hlo hia,
    by rw [← hb]; exact secOK_mem_closure hsec m.ib hlib hib⟩

theorem mixed_facts : ∀ m ∈ mixedSecs,
    CFSG.Sporadic.Fi24.a ∈ Subgroup.closure (sK '' {k | k ∈ m.gs}) ∧ CFSG.Sporadic.Fi24.b ∈ Subgroup.closure (sK '' {k | k ∈ m.gs}) := by
  intro m hm
  have hm' : m = ⟨[1085, 1086, 64, 66, 1087, 1082, 1083, 1084], 1110, 1657, 1655, 1656⟩ ∨
      m = ⟨[1085, 1086, 64, 66, 1087, 1107, 1108, 1109], 1657, 2208, 2206, 2207⟩ := by
    simpa only [mixedSecs, List.mem_cons, List.not_mem_nil, or_false] using hm
  have hh : m.hi ≤ 3820 := by rcases hm' with rfl | rfl <;> norm_num
  exact mixed_sec_mem hm hh


structure PureOKFacts (q : PureSec) : Prop where
  sec1 : secOK WK (pureGens q.lam) q.lo q.hi = true
  sec2 : secOK WK [q.ix, q.iy] q.hi q.hi2 = true
  lo_ix : q.lo ≤ q.ix
  ix_hi : q.ix < q.hi
  lo_iy : q.lo ≤ q.iy
  iy_hi : q.iy < q.hi
  hi_oX : q.hi ≤ q.oX
  oX_hi2 : q.oX < q.hi2
  hi_oY : q.hi ≤ q.oY
  oY_hi2 : q.oY < q.hi2
  hi_oh : q.hi ≤ q.oh
  oh_hi2 : q.oh < q.hi2
  rels : ∀ v ∈ TauCeti.Sporadic.hePresentation.relatorLetters,
    eqRows 781 (mWord (mLetters WK) (v.map (heLetter q.ix q.iy))) (idW 781) = true
  ne : eqRows 781 (mLetters WK)[2 * q.ix]! (idW 781) = false
  eqX : eqRows 781 (mLetters WK)[2 * q.oX]! (mLetters WK)[2 * 64]! = true
  eqY : eqRows 781 (mLetters WK)[2 * q.oY]! (mLetters WK)[2 * 66]! = true
  conj : eqRows 781 (mulW (mLetters WK)[2 * q.oh]!
      (mulW (mLetters WK)[2 * 64]! (powW 781 (mLetters WK)[2 * 66]! q.lam)))
    (mulW (mLetters WK)[2 * 67]! (mLetters WK)[2 * q.oh]!) = true

theorem pureOK_parts {q : PureSec} (hq : q ∈ pureSecs) : PureOKFacts q := by
  have h := fi24k_parts.pure q hq
  unfold pureOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩,
    h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

theorem sK_image_pair (x y : ℕ) :
    sK '' {k | k ∈ [x, y]} = ({sK x, sK y} : Set CFSG.Sporadic.Fi24.J) := by
  ext g
  constructor
  · rintro ⟨k, hk, rfl⟩
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl <;> simp
  · rintro (rfl | rfl)
    · exact ⟨x, by simp, rfl⟩
    · exact ⟨y, by simp, rfl⟩

theorem heLetter_F {x y : ℕ} (hx : x < 3820) (hy : y < 3820) (l : ℕ × Bool) :
    (if 0 < heLetter x y l then sK ((heLetter x y l).natAbs - 3)
      else (sK ((heLetter x y l).natAbs - 3))⁻¹) =
    (if l.2 then img2 (sK x) (sK y) l.1 else (img2 (sK x) (sK y) l.1)⁻¹) := by
  obtain ⟨i, b⟩ := l
  cases b
  · simp only [heLetter, Bool.false_eq_true, if_false, Int.natAbs_neg, Int.natAbs_natCast]
    rw [if_neg (by omega : ¬ (0 : ℤ) < -(((if i = 0 then x else y) + 3 : ℕ) : ℤ))]
    by_cases hi : i = 0 <;> simp [img2, hi, Nat.add_sub_cancel]
  · simp only [heLetter, if_true, Int.natAbs_natCast]
    rw [if_pos (by omega : (0 : ℤ) < (((if i = 0 then x else y) + 3 : ℕ) : ℤ))]
    by_cases hi : i = 0 <;> simp [img2, hi, Nat.add_sub_cancel]

theorem wordG_heLetter {x y : ℕ} (hx : x < 3820) (hy : y < 3820) (v : List (ℕ × Bool)) :
    wordG (fun z : ℤ => if 0 < z then sK (z.natAbs - 3) else (sK (z.natAbs - 3))⁻¹)
      (v.map (heLetter x y)) = wordProd (img2 (sK x) (sK y)) v := by
  have hm := List.map_congr_left (l := v)
    (f := fun l => (fun z : ℤ => if 0 < z then sK (z.natAbs - 3)
      else (sK (z.natAbs - 3))⁻¹) (heLetter x y l))
    (g := fun l => if l.2 then img2 (sK x) (sK y) l.1
      else (img2 (sK x) (sK y) l.1)⁻¹)
    (fun l _ => heLetter_F hx hy l)
  rw [wordG, wordProd, List.map_map]
  exact congrArg List.prod hm

theorem sim_heLetter {x y : ℕ} (hx : x < 3820) (hy : y < 3820) (l : ℕ × Bool) :
    Fi24Sim (mLetter (mLetters WK) (heLetter x y l))
      (if l.2 then img2 (sK x) (sK y) l.1 else (img2 (sK x) (sK y) l.1)⁻¹) := by
  obtain ⟨i, b⟩ := l
  have hL : ∀ k < 3820,
      Fi24Sim (mLetters WK)[2 * k]! (CFSG.Sporadic.Fi23.slpG genG WK k) ∧
      Fi24Sim (mLetters WK)[2 * k + 1]! (CFSG.Sporadic.Fi23.slpG genG WK k)⁻¹ :=
    fun k hk => (sim_mLetters fi24k_parts.slp).2 k (by rw [WK_size]; exact hk)
  cases b
  · have hz0 : heLetter x y (i, false) ≠ 0 := by
      simp only [heLetter, Bool.false_eq_true, if_false]
      omega
    have hz : (heLetter x y (i, false)).natAbs ≤ 2 ∨
        (heLetter x y (i, false)).natAbs < 3820 + 3 := by
      simp only [heLetter, Bool.false_eq_true, if_false, Int.natAbs_neg, Int.natAbs_natCast]
      right
      split_ifs <;> omega
    have hmain := (sim_mLetter (L := mLetters WK) hL hz0 hz).1
    rw [show letterG genG WK 3820 (heLetter x y (i, false)) =
      letterK 3820 (heLetter x y (i, false)) from rfl] at hmain
    have h : letterK 3820 (heLetter x y (i, false)) = (img2 (sK x) (sK y) i)⁻¹ := by
      rw [show heLetter x y (i, false) = -(((if i = 0 then x else y) + 3 : ℕ) : ℤ) from rfl]
      rw [letterK_neg (by split_ifs <;> omega)]
      by_cases hi : i = 0 <;> simp [img2, hi]
    rw [h] at hmain
    simpa only [Bool.false_eq_true, if_false] using hmain
  · have hz0 : heLetter x y (i, true) ≠ 0 := by
      simp only [heLetter, if_true]
      omega
    have hz : (heLetter x y (i, true)).natAbs ≤ 2 ∨
        (heLetter x y (i, true)).natAbs < 3820 + 3 := by
      simp only [heLetter, if_true, Int.natAbs_natCast]
      right
      split_ifs <;> omega
    have hmain := (sim_mLetter (L := mLetters WK) hL hz0 hz).1
    rw [show letterG genG WK 3820 (heLetter x y (i, true)) =
      letterK 3820 (heLetter x y (i, true)) from rfl] at hmain
    have h : letterK 3820 (heLetter x y (i, true)) = img2 (sK x) (sK y) i := by
      rw [show heLetter x y (i, true) = (((if i = 0 then x else y) + 3 : ℕ) : ℤ) from rfl]
      rw [letterK_pos (by split_ifs <;> omega)]
      by_cases hi : i = 0 <;> simp [img2, hi]
    rw [h] at hmain
    simpa only [if_true] using hmain

theorem sim_heWord {x y : ℕ} (hx : x < 3820) (hy : y < 3820) (v : List (ℕ × Bool)) :
    Fi24Sim (mWord (mLetters WK) (v.map (heLetter x y)))
      (wordProd (img2 (sK x) (sK y)) v) := by
  rw [mWord]
  have hf : ∀ z ∈ v.map (heLetter x y), Fi24Sim (mLetter (mLetters WK) z)
      ((fun z : ℤ => if 0 < z then sK (z.natAbs - 3) else (sK (z.natAbs - 3))⁻¹) z) := by
    intro z hz
    obtain ⟨l, hl, hfl⟩ := List.mem_map.1 hz
    rw [← hfl]
    change Fi24Sim (mLetter (mLetters WK) (heLetter x y l))
      (if 0 < heLetter x y l then sK ((heLetter x y l).natAbs - 3)
        else (sK ((heLetter x y l).natAbs - 3))⁻¹)
    rw [heLetter_F hx hy l]
    exact sim_heLetter hx hy l
  have h := sim_mProd (f := mLetter (mLetters WK))
    (F := fun z : ℤ => if 0 < z then sK (z.natAbs - 3) else (sK (z.natAbs - 3))⁻¹)
    (w := v.map (heLetter x y)) hf
  rwa [wordG_heLetter hx hy v] at h

theorem pure_sec_facts {q : PureSec} (hb : q.hi2 ≤ 3820) (hp : PureOKFacts q) :
    sK q.ix ∈ Subgroup.closure (sK '' {k | k ∈ pureGens q.lam}) ∧
    sK q.iy ∈ Subgroup.closure (sK '' {k | k ∈ pureGens q.lam}) ∧
    (∀ v ∈ TauCeti.Sporadic.hePresentation.relatorLetters,
      wordProd (img2 (sK q.ix) (sK q.iy)) v = 1) ∧
    sK q.ix ≠ 1 ∧
    X7 ∈ Subgroup.closure {sK q.ix, sK q.iy} ∧ Y7 ∈ Subgroup.closure {sK q.ix, sK q.iy} ∧
    sK q.oh ∈ Subgroup.closure {sK q.ix, sK q.iy} ∧
    sK q.oh * (X7 * Y7 ^ q.lam) = C7 * sK q.oh := by
  obtain ⟨hsec1, hsec2, hlo_ix, hix_hi, hlo_iy, hiy_hi, hhi_oX, hoX_hi2, hhi_oY, hoY_hi2,
    hhi_oh, hoh_hi2, hrels, hne, heqX, heqY, hconj⟩ := hp
  have hix : q.ix < 3820 := by omega
  have hiy : q.iy < 3820 := by omega
  have hoX : q.oX < 3820 := by omega
  have hoY : q.oY < 3820 := by omega
  have hoh : q.oh < 3820 := by omega
  have hmem1 := secOK_mem_closure hsec1 q.ix hlo_ix hix_hi
  have hmem2 := secOK_mem_closure hsec1 q.iy hlo_iy hiy_hi
  have hoXmem := secOK_mem_closure hsec2 q.oX hhi_oX hoX_hi2
  have hoYmem := secOK_mem_closure hsec2 q.oY hhi_oY hoY_hi2
  have hohmem := secOK_mem_closure hsec2 q.oh hhi_oh hoh_hi2
  rw [sK_image_pair] at hoXmem hoYmem hohmem
  have hX : sK q.oX = X7 := by
    have h := sim_eq (sim_sK (j := q.oX) hoX) (sim_sK (j := 64) (by norm_num)) heqX
    exact h.trans sK_X7.symm
  have hY : sK q.oY = Y7 := by
    have h := sim_eq (sim_sK (j := q.oY) hoY) (sim_sK (j := 66) (by norm_num)) heqY
    exact h.trans sK_Y7.symm
  have hrel : ∀ v ∈ TauCeti.Sporadic.hePresentation.relatorLetters,
      wordProd (img2 (sK q.ix) (sK q.iy)) v = 1 :=
    fun v hv => sim_eq (sim_heWord hix hiy v) sim_idW (hrels v hv)
  have hne' : sK q.ix ≠ 1 := sim_ne (sim_sK (j := q.ix) hix) sim_idW hne
  have hj : sK q.oh * (X7 * Y7 ^ q.lam) = C7 * sK q.oh := by
    have h := sim_eq
      (sim_mul (sim_sK (j := q.oh) hoh)
        (sim_mul (sim_sK (j := 64) (by norm_num))
          (sim_pow q.lam (sim_sK (j := 66) (by norm_num)))))
      (sim_mul (sim_sK (j := 67) (by norm_num)) (sim_sK (j := q.oh) hoh)) hconj
    rwa [← sK_X7, ← sK_Y7, ← sK_C7] at h
  exact ⟨hmem1, hmem2, hrel, hne', by rw [← hX]; exact hoXmem,
    by rw [← hY]; exact hoYmem, hohmem, hj⟩

theorem pure_facts : ∀ q ∈ pureSecs,
    sK q.ix ∈ Subgroup.closure (sK '' {k | k ∈ pureGens q.lam}) ∧
    sK q.iy ∈ Subgroup.closure (sK '' {k | k ∈ pureGens q.lam}) ∧
    (∀ v ∈ TauCeti.Sporadic.hePresentation.relatorLetters,
      wordProd (img2 (sK q.ix) (sK q.iy)) v = 1) ∧
    sK q.ix ≠ 1 ∧
    X7 ∈ Subgroup.closure {sK q.ix, sK q.iy} ∧ Y7 ∈ Subgroup.closure {sK q.ix, sK q.iy} ∧
    sK q.oh ∈ Subgroup.closure {sK q.ix, sK q.iy} ∧
    sK q.oh * (X7 * Y7 ^ q.lam) = C7 * sK q.oh := by
  intro q hq
  have hb : q.hi2 ≤ 3820 := by
    have hq' := hq
    simp only [pureSecs, List.mem_cons, List.not_mem_nil, or_false] at hq'
    rcases hq' with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  exact pure_sec_facts hb (pureOK_parts hq)

end CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K
