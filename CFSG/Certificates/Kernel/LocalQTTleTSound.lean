module

public import Certificates.Data.Kernel.LocalQT.LatT
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermLat
public import CFSG.Certificates.Kernel.LocalQTChainGSound

public section

namespace CFSG.KC.LQT.CM

open Equiv CFSG.KC.LQT.L CFSG.KC.LQT.S CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.QuasithinUnique.Unc25K1.Six

variable {n : ℕ}

theorem testBit_lorFold (f : List ℕ → ℕ) (i : ℕ) : ∀ T : List (List ℕ),
    (List.rec (motive := fun _ => ℕ) 0
      (fun w _ acc => Nat.lor (Nat.shiftLeft 1 (f w)) acc) T).testBit i = true →
      ∃ w ∈ T, f w = i
  | [], h => by simp at h
  | w :: T, h => by
    change (Nat.shiftLeft 1 (f w) ||| List.rec (motive := fun _ => ℕ) 0
      (fun w _ acc => Nat.lor (Nat.shiftLeft 1 (f w)) acc) T).testBit i = true at h
    rw [Nat.testBit_lor, Bool.or_eq_true] at h
    rcases h with h | h
    · change (1 <<< f w).testBit i = true at h
      rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_iff] at h
      exact ⟨w, List.mem_cons_self .., h⟩
    · obtain ⟨w', hw', e⟩ := testBit_lorFold f i T h
      exact ⟨w', List.mem_cons_of_mem _ hw', e⟩

theorem tab_sound (hn : n ≤ 32) (G : List (Perm (Fin n))) {D : List Lvl}
    (hD : ∀ lv ∈ D, LvOK n lv) {T : List (List ℕ)} {L : ℕ}
    (h : tabOK n D (G.map P.code) T L = true) (σ : Perm (Fin n)) (hσ : InC n D σ) :
    ∃ w ∈ T, w.length ≤ L ∧ evalW G w = σ := by
  unfold tabOK at h
  rw [P.andB_iff, allA_eq_true, P.beq_iff] at h
  obtain ⟨hlen, hmask⟩ := h
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 hσ
  have hilt : i < chainF D := sift_lt hn D hD (fc_code hn σ) hi
  have hbit := testBit_lorFold
    (fun w => idxM n D (chainF D) (CFSG.KC.LQT.W.evalWK n (G.map P.code) w)) i T (by
      rw [hmask]
      change (1 <<< chainF D - 1).testBit i = true
      rw [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one, decide_eq_true_iff]
      exact hilt)
  obtain ⟨w, hw, e⟩ := hbit
  rw [LK.evalWK_code hn, idxM_sift] at e
  refine ⟨w, hw, ?_, ?_⟩
  · have := hlen w hw
    rw [Nat.ble_eq, LK.lenA_eq] at this
    exact this
  · cases hs : sift n D (P.code (evalW G w)) with
    | none =>
      rw [hs] at e
      simp only [Option.elim_none] at e
      omega
    | some k =>
      rw [hs] at e
      simp only [Option.elim_some, id] at e
      subst e
      exact P.code_inj hn (sift_inj hn D hD (fc_code hn _) (fc_code hn _) hs hi)

@[expose] noncomputable def wordsTGo (n : ℕ) (G : List ℕ) (T : List (List ℕ)) (L : ℕ)
    (C : List Lvl) : List (List (List ℕ)) → ℕ → ℕ → Bool :=
  List.rec (motive := fun _ => List (List (List ℕ)) → ℕ → ℕ → Bool) (fun _ _ _ => true)
    (fun lv C' ih W budget k => Bool.rec (motive := fun _ => Bool)
      (List.rec (motive := fun _ => Bool) false
        (fun ws W' _ => CFSG.KC.Ord.andB
          (P.allN n fun j => P.impB (CFSG.KC.Ord.notB (Nat.beq (getK lv.2.1 j) 0))
            (Nat.beq (CFSG.KC.LQT.W.evalWK n G (CFSG.KC.LQT.M.getW ws j)) (getK lv.2.1 j)))
          (P.letB (maxLen n ws) fun len =>
            CFSG.KC.Ord.andB (Nat.ble len budget) (ih W' (Nat.sub budget len) (Nat.sub k 1))))
        W)
      (CFSG.KC.Ord.andB (Nat.ble L budget) (tabOK n (List.cons lv C') G T L))
      (Nat.beq k 0)) C

theorem wordsT_eq (n : ℕ) (C : List Lvl) (G : List ℕ) (W : List (List (List ℕ))) (k : ℕ)
    (T : List (List ℕ)) (L d : ℕ) : wordsT n C G W k T L d = wordsTGo n G T L C W d k := rfl

theorem words_of_inCT (hn : n ≤ 32) (G : List (Perm (Fin n))) (T : List (List ℕ)) (L : ℕ) :
    ∀ (C : List Lvl) (W : List (List (List ℕ))) (budget k : ℕ),
    wordsTGo n (G.map P.code) T L C W budget k = true →
    (∀ lv ∈ C, LvOK n lv) → ∀ σ, InC n C σ →
      ∃ l : List (Perm (Fin n)), (∀ g ∈ l, g ∈ G) ∧ l.length ≤ budget ∧ l.prod = σ
  | [], _, _, _, _, _, σ, hσ => by
    refine ⟨[], by simp, by simp, ?_⟩
    simp only [InC, sift] at hσ
    split_ifs at hσ with e
    · rw [P.code_one] at e
      exact (P.code_inj hn e).symm
    · exact absurd hσ (by simp)
  | lv :: C, W, budget, 0, h, hC, σ, hσ => by
    change CFSG.KC.Ord.andB (Nat.ble L budget) (tabOK n (lv :: C) (G.map P.code) T L) = true at h
    rw [P.andB_iff, Nat.ble_eq] at h
    obtain ⟨w, -, hwL, hw⟩ := tab_sound hn G hC h.2 σ hσ
    refine ⟨w.filterMap (fun i => G[i]?), fun g hg => ?_, ?_, ?_⟩
    · obtain ⟨i, -, hi⟩ := List.mem_filterMap.1 hg
      exact List.mem_of_getElem? hi
    · have := List.length_filterMap_le (fun i => G[i]?) w
      omega
    · rw [← evalW_eq, hw]
  | _ :: _, [], _, _ + 1, h, _, _, _ => by
    change (false : Bool) = true at h
    exact absurd h Bool.false_ne_true
  | lv :: C, ws :: W, budget, k + 1, h, hC, σ, hσ => by
    change CFSG.KC.Ord.andB (P.allN n fun j => P.impB
        (CFSG.KC.Ord.notB (Nat.beq (getK lv.2.1 j) 0))
        (Nat.beq (CFSG.KC.LQT.W.evalWK n (G.map P.code) (CFSG.KC.LQT.M.getW ws j)) (getK lv.2.1 j)))
      (P.letB (maxLen n ws) fun len => CFSG.KC.Ord.andB (Nat.ble len budget)
        (wordsTGo n (G.map P.code) T L C W (Nat.sub budget len) (Nat.sub (k + 1) 1))) = true at h
    rw [P.andB_iff, P.letB_eq, P.andB_iff, P.allN_iff, Nat.ble_eq] at h
    obtain ⟨hw, hle, hrest⟩ := h
    obtain ⟨k0, hk⟩ := Option.isSome_iff_exists.1 hσ
    obtain ⟨j, hj, τ, hτ, e, -, k', h', -⟩ :=
      sift_cons_code hn (hC lv (List.mem_cons_self ..)) σ hk
    have hwj := hw j hj
    rw [P.impB_iff, P.notB_iff, P.beq_iff, P.beq_iff, LK.evalWK_code hn, ← hτ] at hwj
    have hτ' : evalW G (CFSG.KC.LQT.M.getW ws j) = τ := P.code_inj hn (hwj (by rwa [hτ]))
    obtain ⟨l', hl'G, hl'len, hl'⟩ := words_of_inCT hn G T L C W _ _ hrest
      (fun l hl => hC l (List.mem_cons_of_mem _ hl)) (τ⁻¹ * σ) (by rw [InC, h']; rfl)
    have hlen := maxLen_ge ws n j hj
    rw [LK.lenA_eq] at hlen
    refine ⟨(CFSG.KC.LQT.M.getW ws j).filterMap (fun i => G[i]?) ++ l', fun g hg => ?_, ?_, ?_⟩
    · rcases List.mem_append.1 hg with hg | hg
      · obtain ⟨i, -, hi⟩ := List.mem_filterMap.1 hg
        exact List.mem_of_getElem? hi
      · exact hl'G g hg
    · rw [List.length_append]
      have := List.length_filterMap_le (fun i => G[i]?) (CFSG.KC.LQT.M.getW ws j)
      change _ ≤ budget - maxLen n ws at hl'len
      omega
    · rw [List.prod_append, ← evalW_eq, hτ', hl', mul_inv_cancel_left]

theorem tleT_sound (hn : n ≤ 32) (C : List Lvl) (hI : chainInj n C = true)
    (MW : List (List (List ℕ))) (k : ℕ) (T : List (List ℕ)) (L : ℕ)
    (c : LatCert (Perm (Fin n)))
    (h : tleT n C c.depth (c.mGens.map P.code) MW k T L (c.tGens.map P.code) = true) :
    c.tleOK RN.enc = true := by
  unfold tleT at h
  rw [P.andB_iff, P.andB_iff] at h
  obtain ⟨hok, hM, h6⟩ := h
  have hC := chainP_lvOK (chainP_of_ok hok hI)
  unfold grpT at hM
  rw [P.andB_iff, P.andB_iff, wordsT_eq] at hM
  have hw := words_of_inCT hn c.mGens T L C MW c.depth k hM.2.1 hC
  unfold tleC at h6
  rw [P.allL_map] at h6
  unfold LatCert.tleOK
  rw [List.all_eq_true]
  intro g hg
  obtain ⟨l, hl, hlen, rfl⟩ := hw g ((inC_iff hn hC g).1 (h6 g hg))
  exact Std.HashSet.contains_iff_mem.2 (mem_bfsSet_prod RN.enc_mul RN.enc_one c.mGens c.depth l hl hlen)

end CFSG.KC.LQT.CM

end
