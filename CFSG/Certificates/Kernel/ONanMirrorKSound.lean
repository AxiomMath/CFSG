module

public import Certificates.Data.Kernel.ONanMirrorK
public import CFSG.Certificates.Kernel.ONanB2KSound
public import CFSG.LocalAnalysis.OddStandard.ONanB2MirrorFacts

public section

namespace CFSG.OddStandard.ONanRec.MirK

open CFSG.OddStandard.ONanRec.CM CFSG.OddStandard.ONanRec.CMK CFSG.OddStandard.ONanRec.B2K

theorem lt12_s1W : ∀ c ∈ s1W, c < 12 := lt12_append (lt12_append lt12_r1W lt12_r2W) lt12_r2W

theorem lt12_s2W : ∀ c ∈ s2W, c < 12 := lt12_append lt12_r1W lt12_r2W

theorem lt12_x5W : ∀ c ∈ x5W, c < 12 := lt12_append (lt12_append lt12_yW lt12_bW) lt12_cW

theorem mirrorFactsP_of (H : Hyp) (h : mSmallK = true) : MirrorFactsP := by
  have hl := cmLettersOK_of H.letters
  simp only [mSmallK, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hy, hc1⟩, hc2⟩, hyz⟩, hyd⟩, h5⟩, h5n⟩, hgz⟩, hgd⟩, -⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e := eqB_eq H (lt12_append lt12_yW lt12_yW) lt12_aW hy
    rw [wordPerm_append] at e
    exact e
  · have e := eqB_eq H (lt12_append (lt12_append (lt12_append lt12_yW lt12_s1W)
      (invWord_lt lt12_yW)) (invWord_lt lt12_s1W)) lt12_r1W hc1
    rw [wordPerm_append, wordPerm_append, wordPerm_append, wordPerm_inv hl lt12_yW,
      wordPerm_inv hl lt12_s1W, s1W, wordPerm_append, wordPerm_append] at e
    exact e
  · have e := eqB_eq H (lt12_append (lt12_append (lt12_append lt12_yW lt12_s2W)
      (invWord_lt lt12_yW)) (invWord_lt lt12_s2W)) lt12_r2W hc2
    rw [wordPerm_append, wordPerm_append, wordPerm_append, wordPerm_inv hl lt12_yW,
      wordPerm_inv hl lt12_s2W, s2W, wordPerm_append] at e
    exact e
  · have e := eqB_eq H (lt12_append lt12_yW lt12_zW) (lt12_append lt12_zW lt12_yW) hyz
    rw [wordPerm_append, wordPerm_append] at e
    exact e
  · have e := eqB_eq H (lt12_append lt12_yW lt12_dW) (lt12_append lt12_dW lt12_yW) hyd
    rw [wordPerm_append, wordPerm_append] at e
    exact e
  · have e := eqB_eq H (lt12_wpow lt12_x5W 5) lt12_nil h5
    rw [wordPerm_wpow, wordPerm_nil, x5W, wordPerm_append, wordPerm_append] at e
    exact e
  · intro he
    refine eqB_ne H lt12_x5W lt12_nil h5n ?_
    rw [x5W, wordPerm_append, wordPerm_append, wordPerm_nil]
    exact he
  · have e := eqB_eq H (lt12_append (lt12_append (invWord_lt lt12_gW) lt12_zW) lt12_gW)
      (lt12_wpow lt12_zW 3) hgz
    rw [wordPerm_append, wordPerm_append, wordPerm_inv hl lt12_gW, wordPerm_wpow] at e
    exact e
  · have e := eqB_eq H (lt12_append (lt12_append (invWord_lt lt12_gW) lt12_dW) lt12_gW)
      (lt12_append lt12_zW lt12_dW) hgd
    rw [wordPerm_append, wordPerm_append, wordPerm_inv hl lt12_gW, wordPerm_append] at e
    exact e

theorem relsP_of (H : Hyp) (h : mSmallK = true) :
    ∀ r ∈ relsM, FreeGroup.lift gen2Perm r = 1 := by
  have hl := cmLettersOK_of H.letters
  simp only [mSmallK, Bool.and_eq_true] at h
  have hrel := h.2
  rw [relsM_eq]
  rintro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  rw [lift_mk_gen2 hl]
  have hw' := List.all_eq_true.1 hrel (w.map code) (List.mem_map_of_mem (f := fun w =>
    w.map fun l => 2 * l.1.val + (if l.2 then 0 else 1)) hw)
  have hlt : ∀ c ∈ (w.map code).flatMap substG2, c < 12 := by
    intro c hc
    obtain ⟨d, hd, hc⟩ := List.mem_flatMap.1 hc
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hd
    exact lt12_substG2 _ (code_lt l) c hc
  rw [eqB_eq H hlt lt12_nil hw', wordPerm_nil]

theorem conj_inv_of_mul {G : Type*} [Group G] {m y f : G} (hmf : m * f = f * m)
    (hyf : y * f = f * y) (hff : f * f = 1) (hmm : m * m = 1)
    (h : m * (y * f) * m = (y * f)⁻¹) : m * y * m⁻¹ = y⁻¹ := by
  have hmi : m⁻¹ = m := inv_eq_of_mul_eq_one_right hmm
  have hfi : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
  rw [hmi]
  have e1 : m * (y * f) * m = m * y * m * f := by
    simp only [mul_assoc, ← hmf]
  have e2 : (y * f)⁻¹ = y⁻¹ * f := by
    rw [mul_inv_rev, hfi]
    exact (Commute.inv_left (hyf : Commute y f)).eq.symm
  exact mul_right_cancel (e1.symm.trans (h.trans e2))

theorem inv_mul_comm_of_inv {G : Type*} [Group G] {a b y : G} (ha : a * y * a⁻¹ = y⁻¹)
    (hb : b * y * b⁻¹ = y⁻¹) : a⁻¹ * b * y = y * (a⁻¹ * b) := by
  have hb' : b * y = y⁻¹ * b := by
    rw [← hb]
    group
  have ha' : a⁻¹ * y⁻¹ = y * a⁻¹ := by
    rw [← ha]
    group
  calc a⁻¹ * b * y = a⁻¹ * (b * y) := mul_assoc _ _ _
    _ = a⁻¹ * y⁻¹ * b := by rw [hb', mul_assoc]
    _ = y * a⁻¹ * b := by rw [ha']
    _ = y * (a⁻¹ * b) := mul_assoc _ _ _

theorem lt12_mEvalW {uW t : List ℕ} (hu : ∀ c ∈ uW, c < 12) (ht : ∀ c ∈ t, c < 12)
    (w : List ℕ) : ∀ c ∈ mEvalW uW t w, c < 12 := by
  intro c hc
  obtain ⟨k, -, hc⟩ := List.mem_flatMap.1 hc
  split_ifs at hc
  · exact lt12_r1W c hc
  · exact lt12_r2W c hc
  · exact hu c hc
  · exact ht c hc

theorem wordPerm_mEvalW (uW t w : List ℕ) :
    wordPerm (mEvalW uW t w) = evalP (wordPerm uW) (wordPerm t) w := by
  unfold mEvalW evalP
  rw [wordPerm_flatMap]
  refine congrArg List.prod (List.map_congr_left fun k _ => ?_)
  split_ifs <;> rfl

theorem mOrd68K_sound (H : Hyp) {W : List ℕ} (hW : ∀ c ∈ W, c < 12) (h : mOrd68K W = true) :
    (wordPerm W ^ 6 = 1 ∧ wordPerm W ^ 2 ≠ 1 ∧ wordPerm W ^ 3 ≠ 1) ∨
      (wordPerm W ^ 8 = 1 ∧ wordPerm W ^ 4 ≠ 1) := by
  have one : ∀ n, eqB (wpow W n) [] = true → wordPerm W ^ n = 1 := fun n hn => by
    have e := eqB_eq H (lt12_wpow hW n) lt12_nil hn
    rwa [wordPerm_wpow, wordPerm_nil] at e
  have ne : ∀ n, eqB (wpow W n) [] = false → wordPerm W ^ n ≠ 1 := fun n hn he =>
    eqB_ne H (lt12_wpow hW n) lt12_nil hn (by rw [wordPerm_wpow, wordPerm_nil]; exact he)
  simp only [mOrd68K, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  rcases h with ⟨⟨h6, h2⟩, h3⟩ | ⟨h8, h4⟩
  · exact Or.inl ⟨one 6 h6, ne 2 h2, ne 3 h3⟩
  · exact Or.inr ⟨one 8 h8, ne 4 h4⟩

theorem mLeafK_sound (H : Hyp) {uW t : List ℕ} {l h : ℕ} (hu : ∀ c ∈ uW, c < 12)
    (ht : ∀ c ∈ t, c < 12) (hleaf : mLeafK uW l t h = true)
    (h1 : wordPerm t * wordPerm t = 1) :
    (l = 0 ∧ ∃ k < 4, wordPerm t * wordPerm uW ^ k = cP ∨
        wordPerm t * wordPerm uW ^ k = dP * cP * dP) ∨
      ∃ w ∈ badWords,
        ((evalP (wordPerm uW) (wordPerm t) w) ^ 6 = 1 ∧
          (evalP (wordPerm uW) (wordPerm t) w) ^ 2 ≠ 1 ∧
          (evalP (wordPerm uW) (wordPerm t) w) ^ 3 ≠ 1) ∨
        ((evalP (wordPerm uW) (wordPerm t) w) ^ 8 = 1 ∧
          (evalP (wordPerm uW) (wordPerm t) w) ^ 4 ≠ 1) := by
  unfold mLeafK at hleaf
  split_ifs at hleaf with ha hb hc
  · exfalso
    rw [Bool.not_eq_true'] at hleaf
    exact eqB_ne H (lt12_append ht ht) lt12_nil hleaf (by rw [wordPerm_append, wordPerm_nil, h1])
  · rw [Bool.and_eq_true, beq_iff_eq] at hleaf
    obtain ⟨hl0, he⟩ := hleaf
    have e := eqB_eq H (lt12_append ht (lt12_wpow hu _)) lt12_cW he
    rw [wordPerm_append, wordPerm_wpow] at e
    exact Or.inl ⟨hl0, h - 1, by omega, Or.inl e⟩
  · rw [Bool.and_eq_true, beq_iff_eq] at hleaf
    obtain ⟨hl0, he⟩ := hleaf
    have e := eqB_eq H (lt12_append ht (lt12_wpow hu _))
      (lt12_append (lt12_append lt12_dW lt12_cW) lt12_dW) he
    rw [wordPerm_append, wordPerm_wpow, wordPerm_append, wordPerm_append] at e
    exact Or.inl ⟨hl0, h - 5, by omega, Or.inr e⟩
  · rw [Bool.and_eq_true, Nat.blt_eq] at hleaf
    obtain ⟨hj, ho⟩ := hleaf
    have hlen : h - 9 < badWords.length := hj
    rw [List.getD_eq_getElem _ _ hlen] at ho
    have h68 := mOrd68K_sound H (lt12_mEvalW hu ht _) ho
    rw [wordPerm_mEvalW] at h68
    exact Or.inr ⟨_, List.getElem_mem hlen, h68⟩

theorem mChainK_sound {uW t0 : List ℕ} {l : ℕ} :
    ∀ (cw : List (List ℕ)) (hs : List ℕ), mChainK uW l t0 cw hs = true →
      ∀ c ∈ cw, ∃ h, mLeafK uW l (t0 ++ c) h = true
  | [], _, _, c, hc => absurd hc List.not_mem_nil
  | c :: cs, h :: hs, hch, c', hc' => by
    rw [mChainK, Bool.and_eq_true] at hch
    rcases List.mem_cons.1 hc' with rfl | hc'
    · exact ⟨h, hch.1⟩
    · exact mChainK_sound cs hs hch.2 c' hc'
  | _ :: _, [], hch, _, _ => by
    rw [mChainK] at hch
    exact absurd hch Bool.false_ne_true

theorem fP_central (H : Hyp) (hfz : fzK = true) {m : Equiv.Perm (Fin 480)} (hm : m ∈ M480) :
    m * fP = fP * m := by
  have hl := cmLettersOK_of H.letters
  simp only [fzK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hfz
  obtain ⟨⟨hf, -⟩, -⟩ := hfz
  refine comm_of_gens (fun i => ?_) hm
  have e := eqB_eq H (lt12_append (lt12_gen i i.2) lt12_fW)
    (lt12_append lt12_fW (lt12_gen i i.2)) (hf i i.2)
  rwa [wordPerm_append, wordPerm_append, (wordPerm_genCode hl i).1] at e

theorem mirrorChainP_of (H : Hyp) (hfz : fzK = true) (hff : eqB (fW ++ fW) [] = true)
    (horb : ∃ ws, orbK [yW, zW] ptsM 2520 ws = true) {cw : List (List ℕ)} {t0 : List ℕ}
    {hs0 hs1 : List ℕ} (hC : mCentK cw = true) (hT : mT0K t0 = true)
    (h0 : mChainK (yW ++ wpow fW 0) 0 t0 cw hs0 = true)
    (h1 : mChainK (yW ++ wpow fW 1) 1 t0 cw hs1 = true) : MirrorChainP := by
  have hl := cmLettersOK_of H.letters
  intro l hl2 m hm hmm hm1 hmz hmu
  have hff' : fP * fP = 1 := by
    have e := eqB_eq H (lt12_append lt12_fW lt12_fW) lt12_nil hff
    rwa [wordPerm_append, wordPerm_nil] at e
  have hyM : yP ∈ M480 := mem_M480_wordPerm hl lt12_yW
  have hmy : m * yP * m⁻¹ = yP⁻¹ := by
    refine conj_inv_of_mul (f := fP ^ l) (Commute.pow_right (fP_central H hfz hm) l).eq
      (Commute.pow_right (fP_central H hfz hyM) l).eq ?_ hmm hmu
    rw [← (Commute.refl fP).mul_pow, hff', one_pow]
  simp only [mT0K, Bool.and_eq_true, List.all_eq_true, Nat.blt_eq] at hT
  obtain ⟨⟨ht12, hty⟩, htz⟩ := hT
  have hT0y : wordPerm t0 * yP * (wordPerm t0)⁻¹ = yP⁻¹ := by
    have e := eqB_eq H (lt12_append (lt12_append ht12 lt12_yW) (invWord_lt ht12))
      (invWord_lt lt12_yW) hty
    rwa [wordPerm_append, wordPerm_append, wordPerm_inv hl ht12, wordPerm_inv hl lt12_yW] at e
  have hT0z : wordPerm t0 * zP = zP * wordPerm t0 := by
    have e := eqB_eq H (lt12_append ht12 lt12_zW) (lt12_append lt12_zW ht12) htz
    rwa [wordPerm_append, wordPerm_append] at e
  simp only [mCentK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Nat.blt_eq] at hC
  obtain ⟨⟨⟨hlen, hc12⟩, hnd⟩, hcc⟩ := hC
  have hcard : Nat.card (centW [yW, zW]) ≤ 64 := by
    obtain ⟨ws, hws⟩ := horb
    have := orbK_card H (rs := [yW, zW]) (by decide) (by decide) hws
    omega
  have hx : (wordPerm t0)⁻¹ * m ∈ centW [yW, zW] := by
    refine mem_centW.2 ⟨mul_mem (inv_mem (mem_M480_wordPerm hl ht12)) hm, fun r hr => ?_⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl
    · exact inv_mul_comm_of_inv hT0y hmy
    · exact ((Commute.inv_left (hT0z : Commute (wordPerm t0) zP)).mul_left
        (hmz : Commute m zP)).eq
  have hmem := mem_of_card_le (C := centW [yW, zW]) (allNeB_sound H cw hc12 hnd)
    (fun x hx => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
      have hcw := hcc w hw
      refine mem_centW.2 ⟨wordPerm_mem hl w (hc12 w hw), fun r hr => ?_⟩
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl
      · have e := eqB_eq H (lt12_append (hc12 w hw) lt12_yW) (lt12_append lt12_yW (hc12 w hw))
          hcw.1
        rwa [wordPerm_append, wordPerm_append] at e
      · have e := eqB_eq H (lt12_append (hc12 w hw) lt12_zW) (lt12_append lt12_zW (hc12 w hw))
          hcw.2
        rwa [wordPerm_append, wordPerm_append] at e)
    (by rw [List.length_map, hlen]; exact hcard) hx
  obtain ⟨c, hc, hce⟩ := List.mem_map.1 hmem
  have hmt : m = wordPerm (t0 ++ c) := by
    rw [wordPerm_append, hce, mul_inv_cancel_left]
  have hch : ∃ hs, mChainK (yW ++ wpow fW l) l t0 cw hs = true := by
    interval_cases l
    · exact ⟨_, h0⟩
    · exact ⟨_, h1⟩
  obtain ⟨hs, hchain⟩ := hch
  obtain ⟨h, hleaf⟩ := mChainK_sound cw hs hchain c hc
  have hu12 : ∀ x ∈ yW ++ wpow fW l, x < 12 := lt12_append lt12_yW (lt12_wpow lt12_fW l)
  have hup : wordPerm (yW ++ wpow fW l) = yP * fP ^ l := by
    rw [wordPerm_append, wordPerm_wpow]
    rfl
  have key := mLeafK_sound H hu12 (lt12_append ht12 (hc12 c hc)) hleaf
    (by rw [← hmt]; exact hmm)
  rw [← hmt, hup] at key
  exact key

end CFSG.OddStandard.ONanRec.MirK
