module

public import CFSG.Certificates.Kernel.O8DickProved

public section

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.OmegaEight
  CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Chain

theorem oCount_eq {q : ℕ → Bool} {Q : Nat} {L : List ℕ} (hq : QBind q Q)
    (h : ∀ c < 64, walkFrom Q (fun _ => 1) c = L.getD c 0) (hl : L.length ≤ 64) :
    (oColsG q).length = L.sum :=
  OrthPf.oCount_eq_proved hq h hl

theorem inv_sound {q : ℕ → Bool} {Q : Nat} (hq : QBind q Q)
    (h : ∀ c < 64, walkFrom Q invBadK c = 0) : invCheckG q = true :=
  OrthPf.inv_sound_proved hq h

theorem gen_sound {q : ℕ → Bool} {G GI : ℕ → Array ℕ} {Q GP GIP : Nat} (hq : QBind q Q)
    (hG : ∀ s < 6, G s = decR (mat GP s)) (hGI : ∀ s < 6, GI s = decR (mat GIP s))
    (h : genOK Q GP GIP = true) : genCheckG q G GI = true :=
  OrthPf.gen_sound_proved hq hG hGI h

theorem orbit_sound {q : ℕ → Bool} {G : ℕ → Array ℕ} {OW : Array (List ℕ)} {Q GP n : Nat}
    {OWl : List (List ℕ)} (hq : QBind q Q) (hG : ∀ s < 6, G s = decR (mat GP s))
    (hOW : OW = OWl.toArray) (hl : ∀ w ∈ OWl, ∀ s ∈ w, s < 6) (h : orbitOK Q GP n OWl = true) :
    orbitCheckG q G OW n = true :=
  OrthPf.orbit_sound_proved hq hG hOW hl h

theorem dick_sound {q : ℕ → Bool} {G GI : ℕ → Array ℕ} {Q GP GIP : Nat} (hq : QBind q Q)
    (hf : formOK Q = true) (hG : ∀ s < 6, G s = decR (mat GP s))
    (hGI : ∀ s < 6, GI s = decR (mat GIP s)) (hgen : genCheckG q G GI = true)
    (h : genDickOK GP GIP = true) : dickCheckG q G GI = true :=
  DickPf.dick_sound_proved hq hf hG hGI hgen h

theorem cone_sound {q : ℕ → Bool} {X Xi Y Yi : Array ℕ × ℕ} {C : List ℕ}
    {Q XP XiP YP YiP CC : Nat} (hq : QBind q Q)
    (hX : X = (decR (Nat.land XP (maskN 36)), Nat.shiftRight XP 36))
    (hXi : Xi = (decR (Nat.land XiP (maskN 36)), Nat.shiftRight XiP 36))
    (hY : Y = (decR (Nat.land YP (maskN 36)), Nat.shiftRight YP 36))
    (hYi : Yi = (decR (Nat.land YiP (maskN 36)), Nat.shiftRight YiP 36))
    (hw : ∀ D ∈ [XP, XiP, YP, YiP], Nat.shiftRight D 36 < 64)
    (hC : C = (List.range 6).map fun j => colAt CC j)
    (h : coneOK Q XP XiP YP YiP CC = true) : coneCheckG q X Xi Y Yi C = true :=
  OrthPf.cone_sound_proved hq hX hXi hY hYi hw hC h

section InvBad

open Matrix Module DickPf OrthPf

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem toVec_colsActAux_o8 (C : List ℕ) (z : ℕ) : ∀ n,
    toVec 6 (colsActAux C z n) = ∑ j ∈ Finset.range n, bz (z.testBit j) • toVec 6 (C.getD j 0)
  | 0 => by rw [colsActAux, dtoVec_zero, Finset.sum_range_zero]
  | n + 1 => by
    rw [colsActAux, dtoVec_xor, toVec_colsActAux_o8 C z n, Finset.sum_range_succ]
    congr 1
    by_cases h : z.testBit n <;> simp [h, bz, dtoVec_zero]

theorem colsAct_mulVec_o8 (L : List ℕ) (z : ℕ) :
    toVec 6 (colsAct L z) = colMat L *ᵥ toVec 6 z := by
  rw [colsAct, toVec_colsActAux_o8,
    Finset.sum_range fun j => bz (z.testBit j) • toVec 6 (L.getD j 0)]
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, colMat,
    Matrix.of_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem colsActAux_lt_o8 {L : List ℕ} (hL : ∀ j < 6, L.getD j 0 < 64) (z : ℕ) :
    ∀ n ≤ 6, colsActAux L z n < 64
  | 0, _ => by simp [colsActAux]
  | n + 1, hn => by
    rw [colsActAux]
    refine Nat.xor_lt_two_pow (n := 6) (colsActAux_lt_o8 hL z n (by omega)) ?_
    split_ifs
    · exact hL n (by omega)
    · norm_num

theorem fixCount_ker_o8 {L : List ℕ} (hL : ∀ j < 6, L.getD j 0 < 64) :
    fixCount L = 2 ^ finrank (ZMod 2) (LinearMap.ker (mulVecLin (colMat L) - 1)) := by
  classical
  have h1 : fixCount L = ((Finset.range 64).filter fun x => (colsAct L x == x) = true).card := by
    rw [fixCount, Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range,
      Multiset.filter_coe, Multiset.coe_card]
    congr 2
  have hT : ∀ z < 64, (colsAct L z == z) = true ↔
      (mulVecLin (colMat L) - 1) (toVec 6 z) = 0 := by
    intro z hz
    rw [beq_iff_eq, LinearMap.sub_apply, mulVecLin_apply, Module.End.one_apply, sub_eq_zero,
      ← colsAct_mulVec_o8]
    exact ⟨congrArg (toVec 6), dtoVec_inj (colsActAux_lt_o8 hL z 6 le_rfl) hz⟩
  have h2 : ((Finset.range 64).filter fun x => (colsAct L x == x) = true).card =
      (Finset.univ.filter fun v : Vd => (mulVecLin (colMat L) - 1) v = 0).card := by
    refine Finset.card_nbij' (toVec 6) ofVec ?_ ?_ ?_ ?_
    · intro z hz
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hz
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (hT z hz.1).1 hz.2⟩
    · intro v hv
      rw [Finset.mem_coe, Finset.mem_filter] at hv
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      refine ⟨ofVec_lt v, (hT _ (ofVec_lt v)).2 ?_⟩
      rw [dtoVec_ofVec]
      exact hv.2
    · intro z hz
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hz
      exact ofVec_toVec hz.1
    · intro v _
      exact dtoVec_ofVec v
  have e : ((Finset.univ.filter fun v : Vd => (mulVecLin (colMat L) - 1) v = 0 : Finset Vd) :
      Set Vd) = (LinearMap.ker (mulVecLin (colMat L) - 1) : Set Vd) := by
    ext v
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, SetLike.mem_coe,
      LinearMap.mem_ker]
  rw [h1, h2, ← Set.ncard_coe_finset, e, ← Nat.card_coe_set_eq]
  change Nat.card (LinearMap.ker (mulVecLin (colMat L) - 1)) = _
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

theorem invol_fix16 {L : List ℕ} (hl : L.length = 6) (hc : ∀ x ∈ L, x < 64)
    (hd : dickC L = false) (hi : isInvol L = true) : fixCount L = 16 := by
  have hL : ∀ j < 6, L.getD j 0 < 64 := fun j _ => getD_lt hc j
  rw [isInvol, Bool.and_eq_true, List.all_eq_true] at hi
  have hj : ∀ j : Fin 6, colMat L *ᵥ (colMat L *ᵥ Pi.single j 1) = Pi.single j 1 := by
    intro j
    have h1 := congrArg (toVec 6) (beq_iff_eq.1 (hi.1 j (List.mem_range.2 j.isLt)))
    rw [colsAct_mulVec_o8, dtoVec_two_pow] at h1
    rw [colMat_mulVec_single]
    exact h1
  have hM2 : colMat L * colMat L = 1 := by
    ext i j
    have := congrFun (hj j) i
    rw [mulVec_mulVec, mulVec_single_one] at this
    change (colMat L * colMat L) i j = _ at this
    rw [this, Pi.single_apply, one_apply]
  have h2 : ∀ a : Vd, a + a = 0 := fun a => by
    funext i
    exact CharTwo.add_self_eq_zero (a i)
  have hle : LinearMap.range (mulVecLin (colMat L) - 1) ≤
      LinearMap.ker (mulVecLin (colMat L) - 1) := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker]
    simp only [LinearMap.sub_apply, mulVecLin_apply, Module.End.one_apply, mulVec_sub,
      mulVec_mulVec, hM2, one_mulVec]
    rw [sub_eq_add_d, sub_eq_add_d, sub_eq_add_d, add_comm (colMat L *ᵥ v) v]
    exact h2 _
  have hrn := LinearMap.finrank_range_add_finrank_ker (mulVecLin (colMat L) - 1)
  rw [Module.finrank_fin_fun] at hrn
  have hmono := Submodule.finrank_mono hle
  obtain ⟨c, hc1, hc2⟩ := dickC_spec hL
  rw [card_spanF_eq hL] at hc2
  have hcr : finrank (ZMod 2) (LinearMap.range (mulVecLin (colMat L) - 1)) = c :=
    Nat.pow_right_injective (le_refl 2) hc2
  rw [hd] at hc1
  have hpar : c % 2 = 0 := by
    have := hc1.symm
    rw [decide_eq_false_iff_not] at this
    omega
  have hr0 : c ≠ 0 := by
    intro h0
    rw [h0, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at hcr
    have hid : L = (List.range 6).map (2 ^ ·) := by
      apply List.ext_getElem (by rw [hl, List.length_map, List.length_range])
      intro j h1 _
      rw [List.getElem_map, List.getElem_range, ← List.getD_eq_getElem L 0 h1]
      have hz := LinearMap.congr_fun hcr (Pi.single ⟨j, by omega⟩ 1)
      rw [LinearMap.sub_apply, mulVecLin_apply, Module.End.one_apply, LinearMap.zero_apply,
        sub_eq_zero, colMat_mulVec_single] at hz
      exact dtoVec_inj (hL j (by omega)) (pow_lt64 ⟨j, by omega⟩)
        (hz.trans (dtoVec_two_pow ⟨j, by omega⟩).symm)
    have := hi.2
    rw [hid, bne_self_eq_false] at this
    exact Bool.false_ne_true this
  rw [fixCount_ker_o8 hL, show finrank (ZMod 2) (LinearMap.ker (mulVecLin (colMat L) - 1)) = 4 by
    omega]
  rfl

theorem invBadK_packL {L : List ℕ} (hl : L.length = 6) (hc : ∀ x ∈ L, x < 64) :
    invBadK (packL L) = 0 := by
  have hC : ∀ d < 6, colAt (packL L) d = L.getD d 0 := fun d _ => colAt_packL hc d
  unfold invBadK
  rw [dickK_eq_dickC (X := packL L) (L := L) (fun j hj => (hC j hj).symm), involK_eq hl hc,
    fixK_eq hC, nIf_eq, nIf_eq, nIf_eq]
  cases hd : dickC L
  · cases hi : isInvol L
    · simp
    · rw [invol_fix16 hl hc hd hi]
      simp
  · simp

theorem walkFrom_invBadK {q : ℕ → Bool} {Q : ℕ} (hq : QBind q Q) :
    ∀ c < 64, walkFrom Q invBadK c = 0 := by
  intro c hc
  rw [walkFrom_eq hq invBadK hc]
  split
  · apply List.sum_eq_zero
    intro x hx
    obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hx
    obtain ⟨hl, hcs⟩ := mem_oColsAuxG 5 [c] C hC (by simpa using hc)
    exact invBadK_packL (by simpa using hl) hcs
  · rfl

end InvBad

end CFSG.KC.O8

end
