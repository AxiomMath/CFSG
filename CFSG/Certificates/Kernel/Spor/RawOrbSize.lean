module

public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import Certificates.Data.Kernel.Spor.RawOrb
public import CFSG.Certificates.Kernel.Spor.RawOrbBfs
public import CFSG.Certificates.NativeValidSchreier

public section

namespace CFSG.KS.Raw.Orb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2
  CFSG.Certificates.Native CFSG.Certificates.ChainArrays CFSG.KS.Raw

@[expose] def enc : List Nat → Nat
  | [] => 0
  | x :: L => x + 256 * enc L

theorem enc_append (L : List Nat) (x : Nat) : enc (L ++ [x]) = enc L + x * 256 ^ L.length := by
  induction L with
  | nil => simp [enc]
  | cons y L ih =>
    simp only [List.cons_append, enc, ih, List.length_cons, Nat.pow_succ]
    ring

theorem enc_digit : ∀ (L : List Nat), (∀ x ∈ L, x < 256) → ∀ j (hj : j < L.length),
    enc L / 256 ^ j % 256 = L[j]
  | [], _, j, hj => absurd hj (by simp)
  | x :: L, hL, 0, _ => by
    simp only [enc, Nat.pow_zero, Nat.div_one, List.getElem_cons_zero]
    have := hL x List.mem_cons_self
    omega
  | x :: L, hL, j + 1, hj => by
    simp only [enc, List.getElem_cons_succ]
    rw [Nat.pow_succ, Nat.mul_comm (256 ^ j) 256, ← Nat.div_div_eq_div_mul]
    have hx := hL x List.mem_cons_self
    have e : (x + 256 * enc L) / 256 = enc L := by omega
    rw [e]
    exact enc_digit L (fun y hy => hL y (List.mem_cons_of_mem _ hy)) j
      (by simpa using hj)

theorem shl_eq' (a b : Nat) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b

@[expose] noncomputable def tabP (kS M l : Nat) : Bool :=
  hasBit M (if l < kS then l else Nat.sub l kS)

theorem stepTab_fold {kS M : Nat} (hk : kS + kS < 256) : ∀ k ≤ kS + kS,
    (List.range k).foldl (fun s l => strictN (Nat.land s (nat_lit 255)) (fun c =>
      nIf(hasBit M (nIf(Nat.blt l kS, l, Nat.sub l kS)),
        Nat.add (Nat.succ s) (Nat.shiftLeft l (Nat.add (nat_lit 8) (Nat.mul (nat_lit 8) c))), s)))
      0 = ((List.range k).filter (tabP kS M)).length +
        256 * enc ((List.range k).filter (tabP kS M)) := by
  intro k
  induction k with
  | zero => intro _; simp [enc]
  | succ k ih =>
    intro hk1
    rw [List.range_succ, List.foldl_append, ih (by omega), List.filter_append]
    set L := (List.range k).filter (tabP kS M) with hL
    have hlen : L.length ≤ k := by
      rw [hL]
      exact (List.length_filter_le _ _).trans (by simp)
    simp only [List.foldl_cons, List.foldl_nil, List.filter_cons, List.filter_nil]
    rw [strictN_eq]
    have e1 : Nat.land (L.length + 256 * enc L) 255 = L.length := by
      change (L.length + 256 * enc L) &&& (2 ^ 8 - 1) = L.length
      rw [Nat.and_two_pow_sub_one_eq_mod]
      omega
    rw [e1, nIf_eq, nIf_eq, blt_dec]
    have hp : hasBit M (if decide (k < kS) = true then k else Nat.sub k kS) = tabP kS M k := by
      simp [tabP]
    rw [hp]
    cases htk : tabP kS M k
    · simp
    · simp only [↓reduceIte, List.length_append, List.length_cons, List.length_nil,
        enc_append]
      have e2 : Nat.shiftLeft k (Nat.add 8 (Nat.mul 8 L.length)) =
          256 * (k * 256 ^ L.length) := by
        rw [shl_eq', Nat.add_eq, Nat.mul_eq, Nat.pow_add, Nat.pow_mul]
        ring
      rw [e2, Nat.add_eq, Nat.succ_eq_add_one]
      ring

theorem stepTab_eq {kS M : Nat} (hk : kS + kS < 256) :
    stepTab kS M = ((List.range (kS + kS)).filter (tabP kS M)).length +
      256 * enc ((List.range (kS + kS)).filter (tabP kS M)) := by
  unfold stepTab
  rw [foldUp_eq]
  exact stepTab_fold hk _ le_rfl

theorem stCnt_eq {kS M : Nat} (hk : kS + kS < 256) :
    stCnt (stepTab kS M) = ((List.range (kS + kS)).filter (tabP kS M)).length := by
  have hlen : ((List.range (kS + kS)).filter (tabP kS M)).length < 256 :=
    lt_of_le_of_lt ((List.length_filter_le _ _).trans (by simp)) hk
  unfold stCnt
  rw [stepTab_eq hk]
  change (_ + 256 * _) &&& (2 ^ 8 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem digit_eq {L : List Nat} (hlt : ∀ x ∈ L, x < 256) (hlen : L.length < 256) {j : Nat}
    (hj : j < L.length) :
    Nat.land (Nat.shiftRight (L.length + 256 * enc L) (Nat.add 8 (Nat.mul 8 j))) 255 = L[j] := by
  change (Nat.shiftRight (L.length + 256 * enc L) (8 + 8 * j)) &&& (2 ^ 8 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, shr_eq, Nat.pow_add, ← Nat.div_div_eq_div_mul,
    Nat.pow_mul]
  have e : (L.length + 256 * enc L) / 2 ^ 8 = enc L := by
    change (L.length + 256 * enc L) / 256 = enc L
    omega
  rw [e]
  exact enc_digit L hlt j hj

theorem stAt_eq {kS M j : Nat} (hk : kS + kS < 256)
    (hj : j < ((List.range (kS + kS)).filter (tabP kS M)).length) :
    stAt (stepTab kS M) j = ((List.range (kS + kS)).filter (tabP kS M))[j] := by
  have hlen : ((List.range (kS + kS)).filter (tabP kS M)).length < 256 :=
    lt_of_le_of_lt ((List.length_filter_le _ _).trans (by simp)) hk
  have hlt : ∀ x ∈ (List.range (kS + kS)).filter (tabP kS M), x < 256 := fun x hx => by
    rw [List.mem_filter, List.mem_range] at hx
    omega
  unfold stAt
  rw [stepTab_eq hk]
  exact digit_eq hlt hlen hj

@[expose] noncomputable def fxK (w : Nat) (PS : Nat → Nat) (BP i j : Nat) : Bool :=
  allN i (fun t => strictB (pg w (mask w) BP t) (fun b =>
    Nat.beq (pg w (mask w) (PS j) b) b))

theorem fixMask_testBit {w : Nat} {PS : Nat → Nat} {kS BP i : Nat} (l : Nat) :
    (fixMaskK w (mask w) PS kS BP i).testBit l = (decide (l < kS) && fxK w PS BP i l) := by
  unfold fixMaskK
  rw [foldUp_eq]
  have key : ∀ k, ((List.range k).foldl (fun s j => nIf(allN i (fun t =>
      strictB (pg w (mask w) BP t) (fun b => Nat.beq (pg w (mask w) (PS j) b) b)),
      Nat.lor s (Nat.shiftLeft (nat_lit 1) j), s)) 0).testBit l =
      (decide (l < k) && fxK w PS BP i l) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, nIf_eq]
      have e1 : Nat.shiftLeft 1 k = 2 ^ k := Nat.one_shiftLeft k
      by_cases hl : l = k
      · subst hl
        cases hf : fxK w PS BP i l
        · have hf' : allN i (fun t => strictB (pg w (mask w) BP t) (fun b =>
              Nat.beq (pg w (mask w) (PS l) b) b)) = false := hf
          rw [hf']
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [ih, hf]
          simp
        · have hf' : allN i (fun t => strictB (pg w (mask w) BP t) (fun b =>
              Nat.beq (pg w (mask w) (PS l) b) b)) = true := hf
          rw [hf']
          simp only [↓reduceIte]
          change (_ ||| Nat.shiftLeft 1 l).testBit l = _
          rw [Nat.testBit_or, e1, Nat.testBit_two_pow]
          simp
      · split
        · change (_ ||| Nat.shiftLeft 1 k).testBit l = _
          rw [Nat.testBit_or, e1, Nat.testBit_two_pow, ih]
          have : (k = l) = False := by simp; omega
          simp only [this, decide_false, Bool.or_false]
          congr 1
          simp
          omega
        · rw [ih]
          congr 1
          simp
          omega
  exact key kS

theorem tab_split {kS M : Nat} {f : Nat → Bool} (hM : ∀ l, M.testBit l = (decide (l < kS) && f l)) :
    (List.range (kS + kS)).filter (tabP kS M) =
      (List.range kS).filter f ++ ((List.range kS).filter f).map (kS + ·) := by
  rw [List.range_add, List.filter_append, List.filter_map]
  congr 1
  · apply List.filter_congr
    intro l hl
    rw [List.mem_range] at hl
    simp [tabP, hasBit_eq, hM, hl]
  · congr 1
    apply List.filter_congr
    intro l hl
    rw [List.mem_range] at hl
    simp only [Function.comp_apply, tabP, hasBit_eq]
    have e : Nat.sub (kS + l) kS = l := Nat.add_sub_cancel_left kS l
    rw [ite_eq_right (by omega), e, hM]
    simp [hl]

section Steps

variable {n w kS nb BP : Nat} {PS PSI : Nat → Nat} {S : Array (Array Nat)} {base : Array Nat}
  (hb : Binds n w PS kS nb BP S base)
  (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
include hb hp

theorem rep_S_of : ∀ j < S.size, Rep n S[j]! (permOfArr n S[j]!) := fun j hj => by
  have hS : S.size = kS := hb.2.2.2.1
  have e := hb.2.2.2.2.1 j (hS ▸ hj)
  have := rep_unpack (prep_PS hb hp (hS ▸ hj)).1
  rwa [← e] at this

theorem rep_Si_of : ∀ j < S.size, Rep n (rawInvs n S)[j]! (permOfArr n S[j]!)⁻¹ := fun j hj => by
  rw [rawInvs_get hj]
  exact rep_invCand (rep_S_of hb hp j hj)

theorem isInv_of : ∀ j < S.size, isInvA n S[j]! (rawInvs n S)[j]! = true := fun j hj =>
  isInvA_of_rep (rep_S_of hb hp j hj) (rep_Si_of hb hp j hj)

theorem steps_eq (hk : kS < 128) {i : Nat} (hi : i ≤ nb) (hbl : ∀ t < nb, base[t]! < n) :
    stCnt (stepsAt n w PS kS BP i) = (rawSteps n S base i).size ∧
      ∀ j < (rawSteps n S base i).size, ∀ p < n,
        pg w (mask w) (letterK PS PSI kS (stAt (stepsAt n w PS kS BP i) j)) p =
          ((rawSteps n S base i)[j]!)[p]! := by
  have hb0 := hb
  obtain ⟨_, _, _, hS, hSj, _, hbt⟩ := hb0
  have hk2 : kS + kS < 256 := by omega
  have hsplit := tab_split (M := fixMaskK w (mask w) PS kS BP i) (f := fxK w PS BP i)
    fixMask_testBit
  set idx := (List.range kS).filter (fxK w PS BP i) with hidx
  have hlev : levelIdx S base i = idx := by
    unfold levelIdx
    rw [hS, hidx]
    apply List.filter_congr
    intro j hj
    rw [List.mem_range] at hj
    rw [Bool.eq_iff_iff, fixesFirst, allLt_iff, fxK, allN_iff]
    refine forall_congr' fun t => imp_congr_right fun ht => ?_
    have htn : t < nb := by omega
    have hbn : pg w (mask w) BP t < n := hbt t htn ▸ hbl t htn
    rw [strictB_eq, beq_iff_eq, hbt t htn, hSj j hj, unpack_get hbn, beq_dec, decide_eq_true_iff]
  have hidx_lt : ∀ x ∈ idx, x < kS := fun x hx => by
    rw [hidx, List.mem_filter, List.mem_range] at hx
    exact hx.1
  have hsz : (rawSteps n S base i).size = idx.length + idx.length := by
    simp [rawSteps, levelSteps, hlev]
  have hcnt : stCnt (stepsAt n w PS kS BP i) = idx.length + idx.length := by
    unfold stepsAt
    rw [stCnt_eq hk2, hsplit]
    simp
  refine ⟨by rw [hcnt, hsz], fun j hj p hpn => ?_⟩
  rw [hsz] at hj
  have hjL : j < ((List.range (kS + kS)).filter (tabP kS (fixMaskK w (mask w) PS kS BP i))).length := by
    rw [hsplit]
    simp
    omega
  have hst : stAt (stepsAt n w PS kS BP i) j = (idx ++ idx.map (kS + ·))[j]'(by simp; omega) := by
    unfold stepsAt
    rw [stAt_eq hk2 hjL]
    simp only [hsplit]
  have hget : (rawSteps n S base i)[j]! = (rawSteps n S base i)[j]'(by rw [hsz]; exact hj) :=
    getElem!_pos _ j _
  by_cases hlt : j < idx.length
  · rw [List.getElem_append_left hlt] at hst
    have hx := hidx_lt _ (List.getElem_mem hlt)
    have hL : letterK PS PSI kS (stAt (stepsAt n w PS kS BP i) j) = PS idx[j] := by
      unfold letterK
      rw [hst, nIf_eq, blt_dec]
      simp [hx]
    have hR : (rawSteps n S base i)[j]! = S[idx[j]]! := by
      rw [hget]
      simp only [rawSteps, levelSteps, hlev]
      rw [Array.getElem_append_left (by simpa using hlt)]
      simp
    rw [hL, hR, hSj _ hx, unpack_get hpn]
  · have hle : idx.length ≤ j := by omega
    rw [List.getElem_append_right hle] at hst
    simp only [List.getElem_map] at hst
    have hk' : j - idx.length < idx.length := by omega
    have hx := hidx_lt _ (List.getElem_mem hk')
    have hL : letterK PS PSI kS (stAt (stepsAt n w PS kS BP i) j) = PSI idx[j - idx.length] := by
      unfold letterK
      rw [hst, nIf_eq, blt_dec]
      have e : Nat.sub (kS + idx[j - idx.length]) kS = idx[j - idx.length] :=
        Nat.add_sub_cancel_left _ _
      simp only [e]
      simp
    have hR : (rawSteps n S base i)[j]! = (rawInvs n S)[idx[j - idx.length]]! := by
      rw [hget]
      simp only [rawSteps, levelSteps, hlev]
      rw [Array.getElem_append_right (by simpa using hle)]
      simp
    rw [hL, hR, (rep_Si_of hb hp _ (hS ▸ hx)).apply hpn,
      ← (prep_PS hb hp hx).2 ⟨p, hpn⟩]

end Steps

structure RecFacts (n w : Nat) (PS PSI : Nat → Nat) (kS root T R : Nat) : Prop where
  sz : n < 16777216 ∧ n + 1 < 2 ^ w
  kS_lt : kS < 128
  c_pos : 0 < rcnt R
  c_le : rcnt R ≤ n
  root : rpt w (mask w) R 0 = root
  pt : ∀ k < rcnt R, rpt w (mask w) R k < n ∧ rpos w (mask w) (n * w) R (rpt w (mask w) R k) = k
  pos : ∀ z < n, rpos w (mask w) (n * w) R z < rcnt R →
    rpt w (mask w) R (rpos w (mask w) (n * w) R z) = z
  edge : ∀ k < rcnt R, 0 < k → rpar w (mask w) (n * w) R k < k ∧ rlab n (n * w) R k < stCnt T ∧
    pg w (mask w) (letterK PS PSI kS (stAt T (rlab n (n * w) R k)))
      (rpt w (mask w) R (rpar w (mask w) (n * w) R k)) = rpt w (mask w) R k
  closed : ∀ k < rcnt R, ∀ j < stCnt T, rpos w (mask w) (n * w) R
    (pg w (mask w) (letterK PS PSI kS (stAt T j)) (rpt w (mask w) R k)) < rcnt R

theorem recFacts_of {n w kS root T R NS CH : Nat} {PS PSI : Nat → Nat}
    (hh : lvOrbHdK n w (mask w) kS root T R = true)
    (hs : ∀ s < NS, lvOrbSlK n w (mask w) (n * w) PS PSI kS T R (s * CH) CH = true)
    (hN : n ≤ NS * CH) : RecFacts n w PS PSI kS root T R := by
  have hpt : ∀ k < n, lvOrbPtK n w (mask w) (n * w) PS PSI kS T R (rcnt R) (stCnt T) k = true := by
    intro k hk
    obtain ⟨hCH, hsk, e⟩ := slice_cover hN hk
    have h1 := allN_iff.1 (hs (k / CH) hsk) (k % CH) (Nat.mod_lt _ hCH)
    rwa [e] at h1
  unfold lvOrbHdK szOK at hh
  simp only [strictB_eq, bAnd_eq, Bool.and_eq_true, blt_dec, ble_dec, beq_dec,
    decide_eq_true_eq] at hh
  obtain ⟨⟨hn, hw⟩, hkS, hc0, hcn, _, hroot⟩ := hh
  have hw' : n + 1 < 2 ^ w := by
    rw [shl_eq', Nat.one_mul] at hw
    exact hw
  have hpos : ∀ z < n, lvPosK w (mask w) (n * w) R (rcnt R) z = true := fun z hz => by
    have := hpt z hz
    unfold lvOrbPtK at this
    rw [bAnd_eq, Bool.and_eq_true, bIf_eq, blt_dec] at this
    simpa [hz] using this.1
  have hkk : ∀ k < rcnt R, lvOrbKK n w (mask w) (n * w) PS PSI kS T R (rcnt R) (stCnt T) k =
      true := fun k hk => by
    have := hpt k (by omega)
    unfold lvOrbPtK at this
    rw [bAnd_eq, Bool.and_eq_true, bIf_eq, bIf_eq, blt_dec, blt_dec] at this
    simpa [hk] using this.2
  refine ⟨⟨hn, hw'⟩, hkS, hc0, hcn, hroot, fun k hk => ?_, fun z hz hzc => ?_,
    fun k hk hk0 => ?_, fun k hk j hj => ?_⟩
  · have := hkk k hk
    unfold lvOrbKK at this
    simp only [strictB_eq, bAnd_eq, Bool.and_eq_true, blt_dec, beq_dec, decide_eq_true_eq] at this
    exact this.1
  · have := hpos z hz
    unfold lvPosK at this
    rw [strictB_eq, bIf_eq, blt_dec] at this
    simpa [hzc, beq_dec] using this
  · have := hkk k hk
    unfold lvOrbKK at this
    simp only [strictB_eq, bAnd_eq] at this
    simp only [Bool.and_eq_true] at this
    have h2 := this.2.1
    have hk0' : k ≠ 0 := by omega
    simp only [beq_dec, hk0', decide_false, Bool.and_eq_true, blt_dec, decide_eq_true_eq] at h2
    exact ⟨h2.1, h2.2.1, h2.2.2⟩
  · have := hkk k hk
    unfold lvOrbKK at this
    simp only [strictB_eq, bAnd_eq] at this
    simp only [Bool.and_eq_true, allN_iff] at this
    have h4 := this.2.2.2 j hj
    simp only [blt_dec, decide_eq_true_eq] at h4
    exact h4.1

theorem len_eq_of_orbit {m c r : Nat} {P Q : Nat → Nat} {F : Nat → Nat → Nat}
    (hm : 0 < m) (hc : 0 < c) (h0 : P 0 = Q 0)
    (hPi : ∀ a < m, ∀ b < m, P a = P b → a = b) (hQi : ∀ a < c, ∀ b < c, Q a = Q b → a = b)
    (hPe : ∀ k < m, 0 < k → ∃ h < k, ∃ j < r, F j (P h) = P k)
    (hQe : ∀ k < c, 0 < k → ∃ h < k, ∃ j < r, F j (Q h) = Q k)
    (hPc : ∀ h < m, ∀ j < r, ∃ k < m, P k = F j (P h))
    (hQc : ∀ h < c, ∀ j < r, ∃ k < c, Q k = F j (Q h)) : m = c := by
  have sub : ∀ {m c : Nat} {P Q : Nat → Nat}, 0 < c → P 0 = Q 0 →
      (∀ k < m, 0 < k → ∃ h < k, ∃ j < r, F j (P h) = P k) →
      (∀ h < c, ∀ j < r, ∃ k < c, Q k = F j (Q h)) → ∀ k < m, ∃ k' < c, Q k' = P k := by
    intro m c P Q hc h0 hPe hQc k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · exact ⟨0, hc, h0.symm⟩
      · obtain ⟨h, hh, j, hj, e⟩ := hPe k hk hk0
        obtain ⟨k₁, hk₁, e₁⟩ := ih h hh (by omega)
        obtain ⟨k', hk', e'⟩ := hQc k₁ hk₁ j hj
        exact ⟨k', hk', by rw [e', e₁, e]⟩
  have hPQ := sub hc h0 hPe hQc
  have hQP := sub hm h0.symm hQe hPc
  have hset : (Finset.range m).image P = (Finset.range c).image Q := by
    ext x
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨k', hk', e⟩ := hPQ k hk
      exact ⟨k', hk', e⟩
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨k', hk', e⟩ := hQP k hk
      exact ⟨k', hk', e⟩
  have e1 := Finset.card_image_of_injOn (s := Finset.range m) (f := P)
    (fun a ha b hb e => hPi a (by simpa using ha) b (by simpa using hb) e)
  have e2 := Finset.card_image_of_injOn (s := Finset.range c) (f := Q)
    (fun a ha b hb e => hQi a (by simpa using ha) b (by simpa using hb) e)
  rw [hset, e2, Finset.card_range, Finset.card_range] at e1
  exact e1.symm

section Sizes

variable {n w kS nb BP NS CH : Nat} {PS PSI LR : Nat → Nat} {S : Array (Array Nat)}
  {base : Array Nat} (hb : Binds n w PS kS nb BP S base)
  (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
  (hh : ∀ i < nb, lvOrbHdK n w (mask w) kS (pg w (mask w) BP i) (stepsAt n w PS kS BP i)
    (LR i) = true)
  (hs : ∀ i < nb, ∀ s < NS, lvOrbSlK n w (mask w) (n * w) PS PSI kS (stepsAt n w PS kS BP i)
    (LR i) (s * CH) CH = true)
  (hN : n ≤ NS * CH)
include hb hp hh hs hN

omit hp in
theorem base_lt_of : ∀ t < nb, base[t]! < n := fun t ht => by
  have R := recFacts_of (hh t ht) (hs t ht) hN
  rw [hb.2.2.2.2.2.2 t ht, ← R.root]
  exact (R.pt 0 R.c_pos).1

theorem size_eq_rcnt {i : Nat} (hi : i < nb) :
    (CFSG.Monster.B.Co2.Native.bfs n base[i]! (rawSteps n S base i)).pts.size = rcnt (LR i) := by
  have R := recFacts_of (hh i hi) (hs i hi) hN
  have hbl := base_lt_of hb hh hs hN
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  have hroot : base[i]! < n := hbl i hi
  have hrep : ∀ j < (rawSteps n S base i).size, ∃ g : Equiv.Perm (Fin n),
      Rep n (rawSteps n S base i)[j]! g := fun j hj =>
    rep_of_mem_levelSteps (isInv_of hb hp) (by rw [getElem!_pos _ j hj]; exact Array.getElem_mem hj)
  have hlt : ∀ j < (rawSteps n S base i).size, ∀ x < n, ((rawSteps n S base i)[j]!)[x]! < n :=
    fun j hj x hx => (hrep j hj).choose_spec.lt hx
  have F := levelFacts_of_levelOK (levelOK_of (levelOKT_bfs hroot hlt) (levelTrOK_bfs hrep))
  obtain ⟨hcnt, hstep⟩ := steps_eq hb hp R.kS_lt (Nat.le_of_lt hi) hbl
  set L := CFSG.Monster.B.Co2.Native.bfs n base[i]! (rawSteps n S base i)
  set T := stepsAt n w PS kS BP i
  refine len_eq_of_orbit (r := (rawSteps n S base i).size)
    (P := fun k => L.pts[k]!) (Q := fun k => rpt w (mask w) (LR i) k)
    (F := fun j p => ((rawSteps n S base i)[j]!)[p]!) F.pos R.c_pos ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [F.root, R.root, hb.2.2.2.2.2.2 i hi]
  · intro a ha b hb' e
    rw [← F.pos_pts a ha, ← F.pos_pts b hb']
    exact congrArg _ e
  · intro a ha b hb' e
    rw [← (R.pt a ha).2, ← (R.pt b hb').2]
    exact congrArg _ e
  · intro k hk hk0
    exact ⟨_, F.par_lt k hk hk0, _, F.lab_lt k hk hk0, F.edge k hk hk0⟩
  · intro k hk hk0
    obtain ⟨e1, e2, e3⟩ := R.edge k hk hk0
    refine ⟨_, e1, _, by rw [← hcnt]; exact e2, ?_⟩
    rw [← hstep _ (by rw [← hcnt]; exact e2) _ (R.pt _ (by omega)).1]
    exact e3
  · intro h hh' j hj
    obtain ⟨hk, _⟩ := F.closed h hh' j hj
    exact ⟨_, hk, F.pts_pos _ (hlt j hj _ (F.pts_lt h hh')) hk⟩
  · intro h hh' j hj
    have hj' : j < stCnt T := by rw [hcnt]; exact hj
    have hpn := (R.pt h hh').1
    have hc := R.closed h hh' j hj'
    rw [hstep j hj _ hpn] at hc
    exact ⟨_, hc, R.pos _ (hlt j hj _ hpn) hc⟩

theorem rawOrbitSizes_orb :
    rawOrbitSizes n S base = (List.range nb).map fun i => rcnt (LR i) := by
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  rw [rawOrbitSizes]
  apply List.ext_getElem
  · simp [rawLevels, hbs]
  · intro k _ h2
    have hk : k < nb := by simpa using h2
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
    have e := rawLevels_get (n := n) (S := S) (hbs ▸ hk : k < base.size)
    rw [getElem!_pos _ k (by simpa [rawLevels, hbs] using hk)] at e
    rw [e]
    exact size_eq_rcnt hb hp hh hs hN hk

end Sizes

end CFSG.KS.Raw.Orb

end
