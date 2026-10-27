module

public import Certificates.Data.Kernel.J4Aff2A
public import CFSG.Certificates.Kernel.J4TreeNode.Sound
public import CFSG.Milestones.ASVolI.C31.J4NP.Is2A

public section

namespace CFSG.KC.J4Aff2A

open CFSG.KC.J4Tree CFSG.KC.J4TreeN CFSG.J4Tree.Native CFSG.ASVolI CFSG.Sporadic.J4
open CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2
open CFSG.Quasithin.J4Loc (z0)

theorem clsOK_sound {T : Tabs} (hT : tabsOK T = true)
    (hsx : ∀ t < 2048, T.sx.testBit t = (burnsideJ4NP_sextArr ())[t]?.getD false) {e : ℕ}
    (he : e < 1024) {y : ℕ × ℕ × ℕ × ℕ} {w : ℕ} (h : clsOK T (T.kel e) y w = true) :
    burnsideJ4NP_treeTest (etaCode y.1 * kelCode e) =
      burnsideJ4NP_treeTest (etaCode y.2.2.1) := by
  unfold clsOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨hr, hn⟩, h⟩ := h
  unfold tabsOK at hT
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hT
  have her : T.eta y.1 = etaCK UK y.1 := Nat.eq_of_beq_eq_true (hT.1.1 _ hr)
  have hen : T.eta y.2.2.1 = etaCK UK y.2.2.1 := Nat.eq_of_beq_eq_true (hT.1.1 _ hn)
  have hk : T.kel e = kelCK e := Nat.eq_of_beq_eq_true (hT.1.2 _ he)
  have hX : RC (etaCode y.1 * kelCode e) (M (T.eta y.1) (T.kel e)) := by
    rw [her, hk]
    exact rc_mul (rc_etaCode u_wf _) (rc_kel e)
  have hN : RC (etaCode y.2.2.1) (T.eta y.2.2.1) := by
    rw [hen]
    exact rc_etaCode u_wf _
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [is2AK_spec h2 hX hsx, is2AK_spec h1 hN hsx]
  · rw [non2AK_spec h2 hX hsx, non2AK_spec h1 hN hsx]

theorem clsAll_sound {T : Tabs} (hT : tabsOK T = true)
    (hsx : ∀ t < 2048, T.sx.testBit t = (burnsideJ4NP_sextArr ())[t]?.getD false) {e : ℕ}
    (he : e < 1024) :
    ∀ {ys : List (ℕ × ℕ × ℕ × ℕ)} {ws : ℕ}, clsAll T (T.kel e) ys ws = true →
      ∀ y ∈ ys, burnsideJ4NP_treeTest (etaCode y.1 * kelCode e) =
        burnsideJ4NP_treeTest (etaCode y.2.2.1)
  | [], _, _ => by simp
  | y :: ys, ws, h => by
    simp only [clsAll, Bool.and_eq_true] at h
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact clsOK_sound hT hsx he h.1
    · exact clsAll_sound hT hsx he h.2 z hz

theorem entOK_sound {T : Tabs} (hT : tabsOK T = true)
    (hsx : ∀ t < 2048, T.sx.testBit t = (burnsideJ4NP_sextArr ())[t]?.getD false)
    {W : ℕ → ℕ} :
    ∀ {D : List (ℕ × ℕ × List (ℕ × ℕ × ℕ × ℕ))} {j : ℕ}, entOK T W j D = true →
      ∀ x ∈ D, x.1 < 1024 ∧ ∀ y ∈ x.2.2, burnsideJ4NP_treeTest (etaCode y.1 * kelCode x.1) =
        burnsideJ4NP_treeTest (etaCode y.2.2.1)
  | [], _, _ => by simp
  | x :: D, j, h => by
    simp only [entOK, Bool.and_eq_true, Nat.blt_eq] at h
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact ⟨h.1.1, clsAll_sound hT hsx h.1.1 h.1.2⟩
    · exact entOK_sound hT hsx h.2 z hz

theorem allOK_sound {T : Tabs} (hT : tabsOK T = true)
    (hsx : ∀ t < 2048, T.sx.testBit t = (burnsideJ4NP_sextArr ())[t]?.getD false)
    {D : List (ℕ × ℕ × List (ℕ × ℕ × ℕ × ℕ))} {W : ℕ → ℕ} (h : allOK T D W = true) :
    ∀ x ∈ D, x.1 < 1024 ∧ ∀ y ∈ x.2.2, burnsideJ4NP_treeTest (etaCode y.1 * kelCode x.1) =
      burnsideJ4NP_treeTest (etaCode y.2.2.1) :=
  entOK_sound hT hsx h

theorem eta_mod (d : ℕ) : eta uJ 11 d = eta uJ 11 (d % 2 ^ 11) := by
  unfold eta
  refine List.foldl_ext _ _ _ fun acc j hj => ?_
  rw [Nat.testBit_mod_two_pow, decide_eq_true (List.mem_range.1 hj), Bool.true_and]

theorem etaCode_mod (d : ℕ) : etaCode d = etaCode (d % 2 ^ 11) := by
  unfold etaCode
  refine List.foldl_ext _ _ _ fun acc j hj => ?_
  rw [Nat.testBit_mod_two_pow, decide_eq_true (List.mem_range.1 hj), Bool.true_and]

theorem testBit_sxFold (t : ℕ) : ∀ (l : List ℕ) (a : ℕ),
    (l.foldl (fun acc c => acc ||| 2 ^ ((etaCK UK c) % 2 ^ 12 / 2)) a).testBit t =
      (a.testBit t || l.any fun c => (etaCK UK c) % 2 ^ 12 / 2 == t)
  | [], a => by simp
  | c :: l, a => by
    rw [List.foldl_cons, testBit_sxFold t l, Nat.testBit_or, Nat.testBit_two_pow, List.any_cons]
    simp only [Bool.or_assoc, beq_eq_decide]

theorem etaCode_row0
    (c : ℕ) : (etaCode c).rows[0]?.getD 0 % 2 = 1 := by
  have h00 := burnsideJ4NP_rho_col0 (Eg_le_Hj (eta_mem_Eg 11 le_rfl c)) 0
  rw [if_pos rfl, burnsideJ4NP_rho_eta, burnsideJ4NP_codeMat,
    CFSG.Sporadic.SmallF2.rowsMatrix_apply, CFSG.Sporadic.SmallF2.toVecD_apply, Fin.val_zero] at h00
  by_contra hc
  have h0 : ((etaCode c).rows[0]?.getD 0).testBit 0 = false := by
    rw [Nat.testBit_zero]
    simpa using hc
  rw [h0] at h00
  simp at h00

theorem etaCode_transl_inj
    {c d : ℕ} (hc : c < 2048) (hd : d < 2048)
    (h : (etaCode c).transl = (etaCode d).transl) : c = d := by
  have hE := burnsideJ4NP_affChecks_parts.2.2.2.1
  unfold etaInEOK at hE
  simp only [List.all_eq_true, List.mem_range] at hE
  have hic := hE c hc
  have hid := hE d hd
  unfold Code.inE at hic hid
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hic hid
  have h0 : (etaCode c).rows[0]?.getD 0 = (etaCode d).rows[0]?.getD 0 := by
    have oc := etaCode_row0 c
    have od := etaCode_row0 d
    unfold Code.transl at h
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.pow_one] at h
    omega
  have hwc := burnsideJ4NP_codeWF_etaCode c
  have hwd := burnsideJ4NP_codeWF_etaCode d
  have hrows : (etaCode c).rows = (etaCode d).rows := by
    refine Array.ext (by rw [hwc.1, hwd.1]) fun i h1 h2 => ?_
    have hi12 : i < 12 := by
      rw [hwc.1] at h1
      exact h1
    have key : (etaCode c).rows[i]?.getD 0 = (etaCode d).rows[i]?.getD 0 := by
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · exact h0
      · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
        rw [hic k (by omega), hid k (by omega)]
    rwa [Array.getElem?_eq_getElem h1, Array.getElem?_eq_getElem h2, Option.getD_some,
      Option.getD_some] at key
  have hcode : etaCode c = etaCode d := by
    calc etaCode c = ⟨(etaCode c).rows⟩ := rfl
      _ = ⟨(etaCode d).rows⟩ := by rw [hrows]
      _ = etaCode d := rfl
  refine eta_inj j4Facts.mat c (by simpa using hc) d (by simpa using hd) ?_
  exact burnsideJ4NP_rho_injOn (Eg_le_Hj (eta_mem_Eg 11 le_rfl c))
    (Eg_le_Hj (eta_mem_Eg 11 le_rfl d)) (by rw [burnsideJ4NP_rho_eta, burnsideJ4NP_rho_eta, hcode])

theorem treeTest_etaCode_iff
    {c : ℕ} (hc : c < 2048)
    (hc0 : c ≠ 0) : burnsideJ4NP_treeTest (etaCode c) = true ↔ IsConj (eta uJ 11 c) z0 := by
  have hF := j4Facts
  have hE := burnsideJ4NP_affChecks_parts.2.2.2.1
  unfold etaInEOK at hE
  simp only [List.all_eq_true, List.mem_range] at hE
  have hin : (etaCode c).inE = true := hE c hc
  have htr : (etaCode c).transl < 2048 := by
    rw [transl_etaCode]
    have := Nat.mod_lt (etaCK UK c) (by norm_num : 0 < 2 ^ 12)
    omega
  have hbit : burnsideJ4NP_treeTest (etaCode c) = (sxOf zMasks).testBit (etaCode c).transl := by
    unfold burnsideJ4NP_treeTest burnsideJ4NP_affine2AWith
    rw [hin, if_pos rfl, sxOf_testBit zMasks _ htr]
    rfl
  rw [hbit, sxOf, testBit_sxFold, Nat.zero_testBit, Bool.false_or, List.any_eq_true]
  simp only [beq_iff_eq]
  constructor
  · rintro ⟨d, hd, hdt⟩
    rw [← transl_etaCode, etaCode_mod d] at hdt
    have hdc : d % 2 ^ 11 = c := etaCode_transl_inj (Nat.mod_lt _ (by norm_num)) hc hdt
    rw [← hdc, ← eta_mod d]
    exact (burnsideJ4NP_isConj_eta_three hF hd).symm.trans
      (burnsideJ4NP_isConj_eta_three hF burnsideJ4NP_mem_zMasks_1131)
  · intro h
    exact ⟨c, (burnsideJ4NP_isConj_z0_iff hc hc0).1 h, (transl_etaCode c).symm⟩

theorem is2A_iff_treeTest_H
    {T : Tabs} {W : ℕ → ℕ} (hT : tabsOK T = true)
    (hsx : ∀ t < 2048, T.sx.testBit t = (burnsideJ4NP_sextArr ())[t]?.getD false)
    (h : allOK T invData W = true) {x : J} (hx : x ∈ Hj) (hsq : x * x = 1) (hne : x ≠ 1) :
    IsConj x z0 ↔ burnsideJ4NP_treeTest (burnsideJ4NP_encJ x) = true := by
  have hF := j4Facts
  have hM := hF.mat
  rw [burnsideJ4NP_encJ_of_mem hx]
  by_cases hxE : x ∈ Eg uJ 11
  · obtain ⟨c, hc, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hxE
    have hc' : c < 2048 := by simpa using hc
    have hc0 : c ≠ 0 := fun h0 => hne (by rw [h0, eta_zero])
    rw [burnsideJ4NP_enc_eta c]
    exact (treeTest_etaCode_iff hc' hc0).symm
  have key : ∀ {y : J} (hy : y ∈ Hj), y ∉ Eg uJ 11 →
      (burnsideJ4NP_treeTest (burnsideJ4NP_enc ⟨y, hy⟩) = true ↔
        burnsideJ4NP_HasFix (burnsideJ4NP_rho y)) :=
    fun hy hyE => burnsideJ4NP_affine2A_iff_hasFix hy hyE
  obtain ⟨g, hg, hyP⟩ := burnsideJ4NP_exists_conj_mem_P0 hx hsq
  have hyE : g⁻¹ * x * g ∉ Eg uJ 11 := by
    intro h'
    apply hxE
    have h'' := Hj_normalizes_Eg hM g hg _ h'
    rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h''
  have hysq : (g⁻¹ * x * g) * (g⁻¹ * x * g) = 1 := by
    calc (g⁻¹ * x * g) * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
      _ = 1 := by rw [hsq]; group
  have hxy : IsConj x (g⁻¹ * x * g) := isConj_iff.2 ⟨g⁻¹, by group⟩
  obtain ⟨c, hc, e, he, hyce⟩ := exists_eta_mul_Kel hM hF hyP
  rw [hyce] at hyE hysq hxy
  have hc' : c < 2048 := by simpa using hc
  have he0 : e ≠ 0 := by
    rintro rfl
    apply hyE
    rw [burnsideJ4NP_Kel_zero, mul_one]
    exact eta_mem_Eg 11 le_rfl c
  obtain ⟨yc, hyc⟩ := burnsideJ4NP_classOf_isSome hF hc' he he0 hysq
  obtain ⟨xd, hxd, hxde, hycx, m, hm, hmy⟩ := burnsideJ4NP_classOf_spec hyc
  obtain ⟨hconj, hn0, hn⟩ := burnsideJ4NP_isConj_of_class hF he hysq hxd hxde hycx hm hmy
  have hrep := burnsideJ4NP_conj_class_rep hF he hm hmy
  have hsound := (allOK_sound hT hsx h xd hxd).2 yc hycx
  rw [hxde] at hsound
  have hmH : eta uJ 11 m ∈ Hj := Eg_le_Hj (eta_mem_Eg 11 le_rfl m)
  have hyH : eta uJ 11 c * Kel e ∈ Hj := P0_le_Hj (eta_mul_Kel_mem he)
  have hzH : eta uJ 11 yc.1 * Kel e ∈ Hj := P0_le_Hj (eta_mul_Kel_mem he)
  have hzE : eta uJ 11 yc.1 * Kel e ∉ Eg uJ 11 := by
    rw [← hrep]
    intro h'
    apply hyE
    have h'' := Hj_normalizes_Eg hM (eta uJ 11 m)⁻¹ (Hj.inv_mem hmH) _ h'
    rwa [show (eta uJ 11 m)⁻¹ * (eta uJ 11 m * (eta uJ 11 c * Kel e) * (eta uJ 11 m)⁻¹) *
      (eta uJ 11 m)⁻¹⁻¹ = eta uJ 11 c * Kel e by group] at h''
  have hfix : burnsideJ4NP_HasFix (burnsideJ4NP_rho (eta uJ 11 c * Kel e)) ↔
      burnsideJ4NP_HasFix (burnsideJ4NP_rho (eta uJ 11 yc.1 * Kel e)) := by
    rw [← hrep]
    have h' := burnsideJ4NP_HasFix_conj (Hj.inv_mem hmH) hyH
    rw [inv_inv] at h'
    exact h'.symm
  rw [key hx hxE, ← burnsideJ4NP_HasFix_conj hg hx, hyce, hfix, ← key hzH hzE,
    burnsideJ4NP_enc_eta_mul_Kel yc.1 he, codeOfCoord, hsound,
    treeTest_etaCode_iff hn (by omega)]
  exact ⟨fun h1 => hconj.trans (hxy.symm.trans h1), fun h1 => hxy.trans (hconj.symm.trans h1)⟩

end CFSG.KC.J4Aff2A
