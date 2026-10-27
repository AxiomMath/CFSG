module

public import CFSG.Certificates.Kernel.O8ModelDefs
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.F2WordSound

public section

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.EvenSmallLie CFSG.EvenSmallLie.OmegaEight.Stage1.Model
open CFSG.KC.Enum (pidn pg permOK)
open CFSG.Monster.B.Co2 PA

private theorem perm_head {n w kS kO nb BP : ℕ} {PS PSI : ℕ → ℕ} {D : List (List Int)}
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true) :
    CFSG.KC.Enum.allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true := by
  unfold headK at hh
  simp only [Orb.bAnd_eq, Bool.and_eq_true] at hh
  exact hh.2.2.2.2.1

private theorem strictN_eq' (y : ℕ) (k : ℕ → ℕ) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

private theorem one_nIf (c : Bool) :
    Nat.beq (nat_lit 1) (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) c) = c := by
  cases c <;> rfl

private theorem bit_eq' (X i : ℕ) : bit X i = X.testBit i := by
  unfold bit
  change ((X >>> i) &&& 1 == 1) = _
  rw [Nat.and_one_is_mod, Nat.testBit, Nat.one_and_eq_mod_two]
  cases h : X >>> i % 2 == 1 <;> simp_all

private theorem testBit_orN {n : ℕ} {f : ℕ → ℕ} {j : ℕ} :
    (orN n f).testBit j = true ↔ ∃ i < n, (f i).testBit j = true := by
  induction n with
  | zero => simp [orN]
  | succ n ih =>
    rw [F2W.orN_succ, Nat.testBit_or, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨n, by omega, h⟩
      · exact ⟨i, by omega, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_or_ge i n with h' | h'
      · exact Or.inr ⟨i, h', h⟩
      · have e : i = n := by omega
        rw [e] at h
        exact Or.inl h

private theorem get_of_toList {a : Array ℕ} {n w P : ℕ}
    (h : a.toList = (List.range n).map fun i => fget P i w) {z : ℕ} (hz : z < n) :
    a[z]! = pg w (mask w) P z := by
  rw [unpack_of_toList h, Orb.unpack_get hz]

private theorem cond_iff {n w : ℕ} {PT : ℕ → Array ℕ} {PSI : ℕ → ℕ}
    (hPT : ∀ y < 64, (PT y).toList = (List.range n).map fun i => fget (PSI y) i w) {z : ℕ}
    (hz : z < n) :
    CFSG.KLie.CT.allN (nat_lit 63) (fun y => notB (Nat.beq (pg w (mask w) (PSI (Nat.succ y)) z) z)) =
      inOG PT z := by
  rw [Bool.eq_iff_iff, ctAllN_iff, inOG, allLt_iff]
  refine forall_congr' fun y => imp_congr_right fun hy => ?_
  have hy' : y < 63 := hy
  rw [get_of_toList (hPT (y + 1) (by omega)) hz, ctNotB_eq, bne_iff_ne, Bool.not_eq_true']
  constructor
  · intro h e
    change Nat.beq (pg w (mask w) (PSI (y + 1)) z) z = false at h
    rw [e, Nat.beq_refl] at h
    exact absurd h (by decide)
  · intro h
    cases e : Nat.beq (pg w (mask w) (PSI (Nat.succ y)) z) z
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) h

private theorem oMask_bit {n w : ℕ} {PSI : ℕ → ℕ} (z : ℕ) :
    (oMaskK n w PSI).testBit z = (decide (z < n) && CFSG.KLie.CT.allN (nat_lit 63)
      (fun y => notB (Nat.beq (pg w (mask w) (PSI (Nat.succ y)) z) z))) := by
  rw [Bool.eq_iff_iff]
  unfold oMaskK
  rw [testBit_orN, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    revert h
    cases hc : CFSG.KLie.CT.allN (nat_lit 63)
        (fun y => notB (Nat.beq (pg w (mask w) (PSI (Nat.succ y)) i) i)) with
    | false => intro h; simp at h
    | true =>
      intro h
      change (pw2 i).testBit z = true at h
      rw [pw2_eq, Nat.testBit_two_pow] at h
      have e : i = z := of_decide_eq_true h
      subst e
      exact ⟨hi, hc⟩
  · rintro ⟨hz, hc⟩
    refine ⟨z, hz, ?_⟩
    rw [hc]
    change (pw2 z).testBit z = true
    rw [pw2_eq, Nat.testBit_two_pow_self]

private theorem bitN_eq (x i : ℕ) : bitN x i = if x.testBit i then 1 else 0 := by
  unfold bitN
  change (x >>> i) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.testBit, Nat.one_and_eq_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (x >>> i) with h | h <;> simp [h]

private theorem img_bit {n w O G : ℕ} (z : ℕ) :
    (imgMask n w O G).testBit z = (decide (z < n) && O.testBit (pg w (mask w) G z)) := by
  rw [Bool.eq_iff_iff]
  unfold imgMask
  rw [testBit_orN, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    change (bitN O (pg w (mask w) G i) <<< i).testBit z = true at h
    rw [Nat.testBit_shiftLeft, bitN_eq] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hzi, h⟩ := h
    split at h
    · rename_i hb
      have e : z - i = 0 := by
        by_contra hne
        rw [Nat.testBit_one_eq_true_iff_self_eq_zero] at h
        exact hne h
      have : i = z := by omega
      subst this
      exact ⟨hi, hb⟩
    · simp at h
  · rintro ⟨hz, hb⟩
    refine ⟨z, hz, ?_⟩
    change (bitN O (pg w (mask w) G z) <<< z).testBit z = true
    rw [Nat.testBit_shiftLeft, bitN_eq, if_pos hb]
    simp

private theorem img_lt {n w O G : ℕ} : imgMask n w O G < 2 ^ n := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [img_bit]
  simp [show ¬ i < n by omega]

private theorem fget_bit (X i n k : ℕ) :
    (fget X i n).testBit k = (decide (k < n) && X.testBit (i * n + k)) := by
  unfold fget
  change ((X >>> (i * n)) &&& maskN n).testBit k = _
  rw [F2W.maskN_eq, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
    Bool.and_comm]

private theorem fget_imgTab {n w O TI m i : ℕ} (hn : 0 < n) (hi : i < m) (k : ℕ) :
    (fget (imgTab n w O TI m) i n).testBit k = (imgMask n w O (perAt n w TI i)).testBit k := by
  have e : imgTab n w O TI m = orN m fun i => imgMask n w O (perAt n w TI i) <<< (n * i) := rfl
  rw [fget_bit, e, F2W.testBit_orN_fields (fun _ _ => img_lt)]
  by_cases hk : k < n
  · have h1 : (i * n + k) / n = i := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hk, Nat.zero_add]
    have h2 : (i * n + k) % n = k := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
    have h3 : i * n + k < n * m := by
      have : (i + 1) * n ≤ m * n := Nat.mul_le_mul_right n hi
      rw [Nat.succ_mul] at this
      rw [Nat.mul_comm n m]
      omega
    simp [hk, h1, h2, h3]
  · have : (imgMask n w O (perAt n w TI i)).testBit k = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le img_lt (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [hk, this]

private theorem getD_ofFn_lt {α : Type} {m : ℕ} (f : Fin m → α) (x : α) {i : ℕ} (hi : i < m) :
    (Array.ofFn f).getD i x = f ⟨i, hi⟩ := by
  simp [Array.getD, hi]

private theorem getD_ofFn_ge {α : Type} {m : ℕ} (f : Fin m → α) (x : α) {i : ℕ} (hi : ¬ i < m) :
    (Array.ofFn f).getD i x = x := by
  simp [Array.getD, hi]

private theorem inOTG_lt {n : ℕ} {PT : ℕ → Array ℕ} {z : ℕ} (hz : z < n) :
    inOTG n PT z = inOG PT z :=
  getD_ofFn_lt _ _ hz

private theorem maskOfG_lt {n : ℕ} {PT : ℕ → Array ℕ} {g : Array ℕ} {j : ℕ} (hj : j < n) :
    (maskOfG n PT g).getD j false = inOTG n PT (invCand n g)[j]! :=
  getD_ofFn_lt _ _ hj

private theorem mask_key {n w m TL TI : ℕ} {PT : ℕ → Array ℕ} {PSI : ℕ → ℕ}
    {T : Array (Array ℕ)}
    (hPT : ∀ y < 64, (PT y).toList = (List.range n).map fun i => fget (PSI y) i w)
    (hT : ListBind n w T TL m) (hn : 0 < n) {i : ℕ} (hi : i < m)
    (hI : permOK n w (mask w) (n * w) (perAt n w TL i) (perAt n w TI i) = true) (j : ℕ) :
    (maskOfG n PT T[i]!).getD j false =
      (fget (imgTab n w (oMaskK n w PSI) TI m) i n).testBit j := by
  have hr := rep_permOfArr (Orb.isInvA_unpack hI)
  have hTi : T[i]! = unpack n w (perAt n w TL i) := hT.2 i hi
  have hinv : ∀ j < n, (invCand n T[i]!)[j]! = pg w (mask w) (perAt n w TI i) j := by
    intro j hj
    rw [hTi, (rep_invCand hr.1).apply hj, ← hr.2.apply hj, Orb.unpack_get hj]
  rw [fget_imgTab hn hi, img_bit]
  by_cases hj : j < n
  · have hlt : pg w (mask w) (perAt n w TI i) j < n := by
      rw [← hinv j hj, hTi]
      exact (rep_invCand hr.1).lt hj
    rw [maskOfG_lt hj, hinv j hj, oMask_bit, inOTG_lt hlt]
    simp only [hlt, hj, decide_true, Bool.true_and]
    exact (cond_iff hPT hlt).symm
  · rw [maskOfG, getD_ofFn_ge _ _ hj]
    simp [hj]

private theorem map_getElem!' {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (a : Array α)
    {i : ℕ} (hi : i < a.size) : (a.map f)[i]! = f a[i]! := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_map, getElem!_pos a i hi]

private theorem inOTG_eq {n w : ℕ} {PT : ℕ → Array ℕ} {PSI : ℕ → ℕ}
    (hPT : ∀ y < 64, (PT y).toList = (List.range n).map fun i => fget (PSI y) i w) (z : ℕ) :
    inOTG n PT z = (oMaskK n w PSI).testBit z := by
  rw [oMask_bit]
  by_cases hz : z < n
  · rw [inOTG_lt hz]
    simp only [hz, decide_true, Bool.true_and]
    exact (cond_iff hPT hz).symm
  · rw [inOTG, getD_ofFn_ge _ _ hz]
    simp [hz]

theorem oSet_sound {n w : Nat} {PT : ℕ → Array ℕ} {LS : Array (Array ℕ)} {LB PB : Array ℕ}
    {nO : ℕ} {T : Array (Array ℕ)} {PSI SL SIL LRL TRL TRIL : Nat → Nat}
    {kSL kOL nbL BPL PBP pnb TL TI m : Nat} {DL : List (List Int)}
    (hPT : ∀ y < 64, (PT y).toList = (List.range n).map fun i => fget (PSI y) i w)
    (hL : LevelsK n w SL SIL LRL TRL TRIL kSL kOL nbL BPL DL LS LB)
    (hPB : PB.size = pnb ∧ ∀ t < pnb, PB[t]! = pg w (mask w) PBP t) (hT : ListBind n w T TL m)
    (h : oSetOK n w PSI ⟨LRL, TRIL, BPL, nbL⟩ PBP pnb nO TL TI m = true) :
    oSetCheckG n PT LS LB PB nO T = true := by
  obtain ⟨hb, hh, hl⟩ := hL
  have hn : 0 < n := hb.1
  unfold oSetOK at h
  simp only [strictN_eq', one_nIf, ctAndB_eq, ctOrB_eq, ctNotB_eq, Bool.and_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', ctAllN_iff, ctAnyN_iff] at h
  obtain ⟨hA, hB, hC, hD, hE⟩ := h
  have hm : m = nO := Nat.eq_of_beq_eq_true hC
  have hsz : T.size = m := hT.1
  unfold oSetCheckG
  simp only [Bool.and_eq_true, allLt_iff, beq_iff_eq, Array.all_eq_true]
  refine ⟨⟨⟨⟨⟨fun z hz => ?_, fun t ht => ?_⟩, fun z hz => ?_⟩, by omega⟩, fun i hi => ?_⟩,
    fun i hi j hj => ?_⟩
  · rw [inOTG_lt hz]
  · have ht' : t < pnb := by rw [← hPB.1]; exact ht
    rw [← getElem!_pos PB t ht, hPB.2 t ht', inOTG_eq hPT, ← bit_eq']
    exact hA t ht'
  · simp only [Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true, List.mem_range, beq_iff_eq]
    rcases hB z hz with h0 | ⟨y, hy, e⟩
    · left
      rw [inOTG_eq hPT, ← bit_eq']
      exact h0
    · right
      refine ⟨y, hy, ?_⟩
      rw [get_of_toList (hPT y hy) hn]
      exact Nat.eq_of_beq_eq_true e
  · have hi' : i < m := by omega
    obtain ⟨hp, hs⟩ := hD i hi'
    have hr := rep_permOfArr (Orb.isInvA_unpack hp)
    rw [hT.2 i hi']
    refine ⟨isInvA_of_rep hr.1 (rep_invCand hr.1), ?_⟩
    exact siftK_sound hb (perm_head hh) hl rfl (range_of_permOK hp) hs
  · have hi' : i < m := by omega
    have hj' : j < m := by omega
    simp only [List.any_eq_true, List.mem_range, bne_iff_ne, ne_eq]
    have hne := hE i hi' j hj
    by_contra hall
    push Not at hall
    have key : fget (imgTab n w (oMaskK n w PSI) TI m) i n =
        fget (imgTab n w (oMaskK n w PSI) TI m) j n := by
      apply Nat.eq_of_testBit_eq
      intro k
      rw [← mask_key hPT hT hn hi' (hD i hi').1, ← mask_key hPT hT hn hj' (hD j hj').1]
      by_cases hk : k < n
      · have e := hall k hk
        rw [map_getElem!' _ _ hi, map_getElem!' _ _ (by omega)] at e
        have hs : ∀ g : Array ℕ, (maskOfG n PT g)[k]! = (maskOfG n PT g).getD k false :=
          fun g => by
            rw [maskOfG_lt hk, maskOfG, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
        rw [← hs, ← hs, e]
      · rw [maskOfG, getD_ofFn_ge _ _ hk, maskOfG, getD_ofFn_ge _ _ hk]
    rw [key, Nat.beq_refl] at hne
    exact absurd hne (by decide)

theorem r3_sound {PT : ℕ → Array ℕ} {US T : Array (Array ℕ)} {PSI UP : Nat → Nat} {TL TI m kU : Nat}
    (hPT : ∀ y < 64, (PT y).toList = (List.range 120).map fun i => fget (PSI y) i 9)
    (hU : US.size = kU ∧ ∀ s < kU, US[s]! = unpack 120 9 (UP s)) (hT : ListBind 120 9 T TL m)
    (hm : 0 < m)
    (hI : allN m (fun i => permOK 120 9 (mask 9) (120 * 9) (perAt 120 9 TL i) (perAt 120 9 TI i)) =
      true)
    (h : r3OK 120 9 PSI UP kU TL TI m = true) : r3CheckG PT US T = true := by
  unfold r3OK at h
  simp only [strictN_eq', one_nIf, ctAndB_eq, ctOrB_eq, ctNotB_eq, Bool.and_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', ctAllN_iff] at h
  obtain ⟨h0, hE⟩ := h
  rw [ctAllN_iff] at hI
  have hsz : T.size = m := hT.1
  unfold r3CheckG
  simp only [Bool.and_eq_true, allLt_iff, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq]
  refine ⟨?_, fun i hi => ?_⟩
  · rw [hT.2 0 hm, Nat.eq_of_beq_eq_true h0]
    exact (eqA_iff (Orb.rep_unpack (Orb.prep_pidn (by decide) (by decide))) rep_idA).2 rfl
  · have hi' : i < m := by omega
    rcases hE i hi' with hn | h0'
    · left
      rw [Bool.eq_false_iff]
      intro hall
      rw [Array.all_eq_true] at hall
      have : CFSG.KLie.CT.allN kU (fun s =>
          stabK 120 9 (UP s) (fget (imgTab 120 9 (oMaskK 120 9 PSI) TI m) i 120)) = true := by
        rw [ctAllN_iff]
        intro s hs
        have hs' : s < US.size := by rw [hU.1]; exact hs
        have hst := hall s hs'
        rw [← getElem!_pos US s hs', hU.2 s hs] at hst
        unfold stabB at hst
        rw [allLt_iff] at hst
        unfold stabK
        rw [ctAllN_iff]
        intro z hz
        have := hst z hz
        rw [ctOrB_eq, ctNotB_eq, bit_eq', bit_eq', Bool.or_eq_true, Bool.not_eq_true']
        rw [Bool.or_eq_true, Bool.not_eq_true', mask_key hPT hT (by decide) hi' (hI i hi'),
          mask_key hPT hT (by decide) hi' (hI i hi'), Orb.unpack_get hz] at this
        cases hb : (fget (imgTab 120 9 (oMaskK 120 9 PSI) TI m) i 120).testBit z
        · exact Or.inl rfl
        · rcases this with h' | h'
          · rw [hb] at h'; exact absurd h' (by decide)
          · exact Or.inr h'
      rw [this] at hn
      exact absurd hn (by decide)
    · exact Or.inr (Nat.eq_of_beq_eq_true h0')

end CFSG.KC.O8

end
