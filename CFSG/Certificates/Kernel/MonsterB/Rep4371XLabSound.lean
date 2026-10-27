module

public import Certificates.Data.Kernel.MonsterB.Rep4371XLab
public import CFSG.Certificates.Kernel.MonsterB.Rep4371XNf
public import Certificates.Data.CFSGNative.MonsterB.PacketCheck

public section

namespace CFSG.KC.Rep4371X

open CFSG.KC CFSG.KC.KDense CFSG.KC.Loop CFSG.KC.Rep4371Row CFSG.KC.BM.Pkt CFSG.KC.BM.B64
open CFSG.KC.YModel CFSG.Monster.B

theorem hexD_tab : ∀ c < 256, CFSG.Monster.B.Native.hexDigit (UInt8.ofNat c) = hexD c := by
  decide +kernel

theorem text_get {CH : List (Nat × Nat)} (hc : piecesOK CH = true) {n : Nat} (hn : CH.length ≤ n)
    (ha : ∀ k < (joinP CH 0 n).2, chAt (joinP CH 0 n).1 k < 128) {o : Nat} (ho : o < (joinP CH 0 n).2) :
    (String.ofList (charsOf CH)).toUTF8.get! o = UInt8.ofNat (chAt (joinP CH 0 n).1 o) := by
  have hj : joinP CH 0 n = joinR CH n (0, 0) := by
    rw [joinP_eq]
    rfl
  have hb := (joinR_bytes CH (fun q hq => piecesOK_mem hc q hq) n 0 0 (by decide)).2
  rw [← hj, List.take_of_length_le hn, ← bytesOf_eq] at hb
  have hp0 : pieceBytes (0, 0) = [] := rfl
  rw [hp0, List.nil_append] at hb
  have hL : (String.ofList (charsOf CH)).toUTF8.data.toList =
      (pieceBytes (joinP CH 0 n)).map UInt8.ofNat := by
    rw [text_bytes, ← hb, flatMap_encB]
    intro b hb'
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hb'
    exact ha k (List.mem_range.1 hk)
  have hs : o < (String.ofList (charsOf CH)).toUTF8.data.size := by
    rw [← Array.length_toList, hL, List.length_map]
    unfold pieceBytes
    rw [List.length_map, List.length_range]
    exact ho
  change (String.ofList (charsOf CH)).toUTF8.data[o]! = _
  rw [getElem!_pos _ o hs, ← Array.getElem_toList, List.getElem_of_eq hL]
  simp [pieceBytes]

theorem hexNum_eq {b : ByteArray} {N M : Nat} (hb : ∀ k < M, b.get! k = UInt8.ofNat (chAt N k)) :
    ∀ (o w : Nat), o + w ≤ M → CFSG.Monster.B.Native.hexNum b o w = hexT N o w
  | _, 0, _ => by
    rw [CFSG.Monster.B.Native.hexNum]
    rfl
  | o, w + 1, h => by
    rw [CFSG.Monster.B.Native.hexNum, hexNum_eq hb o w (by omega), hb (o + w) (by omega),
      hexD_tab _ (chAt_lt _ _)]
    rfl

theorem labT_spec {N t c c' : Nat} (h : labT N t c c' = true) :
    kt c = 1 ∧ kt c' = 1 ∧ hexT N (14 * t) 1 = 0 ∧ hexT N (14 * t + 1) 3 = kx c ∧
      hexT N (14 * t + 4) 3 = ky c ∧ hexT N (14 * t + 7) 1 = 0 ∧
      hexT N (14 * t + 8) 3 = kx c' ∧ hexT N (14 * t + 11) 3 = ky c' := by
  unfold labT at h
  dsimp only at h
  obtain ⟨h1, h⟩ := bAnd_true h
  obtain ⟨h2, h⟩ := bAnd_true h
  obtain ⟨h3, h⟩ := bAnd_true h
  obtain ⟨h4, h⟩ := bAnd_true h
  obtain ⟨h5, h⟩ := bAnd_true h
  obtain ⟨h6, h⟩ := bAnd_true h
  obtain ⟨h7, h8⟩ := bAnd_true h
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
    Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5, Nat.eq_of_beq_eq_true h6,
    Nat.eq_of_beq_eq_true h7, Nat.eq_of_beq_eq_true h8⟩

theorem packetLabels_get {t : Nat} (ht : t < 2300) : (CFSG.Monster.B.Native.packetLabels ())[t]! =
    (CFSG.Monster.B.Native.pauliAt CFSG.Monster.B.Native.packetLabelsText.toUTF8 (14 * t),
      CFSG.Monster.B.Native.pauliAt CFSG.Monster.B.Native.packetLabelsText.toUTF8 (14 * t + 7)) := by
  simp only [CFSG.Monster.B.Native.packetLabels]
  rw [getElem!_pos _ t (by simp [ht]), Array.getElem_ofFn]

theorem packetSpin_get {t : Nat} (ht : t < 2048) : (CFSG.Monster.B.Native.packetSpinIndices ())[t]! =
    CFSG.Monster.B.Native.hexNum CFSG.Monster.B.Native.packetLabelsText.toUTF8 (2300 * 14 + 1 + 3 * t) 3 := by
  simp only [CFSG.Monster.B.Native.packetSpinIndices]
  rw [getElem!_pos _ t (by simp [ht]), Array.getElem_ofFn]

theorem labels_true {CH : List (Nat × Nat)}
    (heq : CFSG.Monster.B.Native.packetLabelsText = String.ofList (charsOf CH))
    (hc : piecesOK CH = true) (hn : CH.length ≤ 151) {TH : Nat} (hTH : thOK TH = true)
    (hT : labText TH (joinP CH 0 151) = true) :
    CFSG.Monster.B.Rep4371.Native.labelsCheck = true ∧
      CFSG.Monster.B.Rep4371.Native.spinIndexCheck = true := by
  unfold labText at hT
  obtain ⟨hlen, hT⟩ := bAnd_true hT
  obtain ⟨hasc, hT⟩ := bAnd_true hT
  obtain ⟨hlab, hspin⟩ := bAnd_true hT
  have hlen' : (joinP CH 0 151).2 = 38346 := Nat.eq_of_beq_eq_true hlen
  have ha : ∀ k < (joinP CH 0 151).2, chAt (joinP CH 0 151).1 k < 128 := by
    intro k hk
    have e := allBelow_spec hasc (by decide) k (lt_of_lt_of_eq hk hlen')
    rwa [Nat.blt_eq] at e
  have hget : ∀ o < 38346, CFSG.Monster.B.Native.packetLabelsText.toUTF8.get! o =
      UInt8.ofNat (chAt (joinP CH 0 151).1 o) := by
    intro o ho
    rw [heq]
    exact text_get hc hn ha (lt_of_lt_of_eq ho hlen'.symm)
  have hhex := hexNum_eq hget
  generalize joinP CH 0 151 = T at hlab hspin hhex
  refine ⟨?_, ?_⟩
  · unfold CFSG.Monster.B.Rep4371.Native.labelsCheck
    rw [List.all_eq_true]
    intro t ht
    have ht' := List.mem_range.1 ht
    have hl := allBelow_spec hlab (by decide) t ht'
    change lab2 T.1 t (rawT TH (23 + t)) = true at hl
    rw [CFSG.Monster.B.Rep4371.native_rawModel, rawModel_eq hTH]
    generalize rawT TH (23 + t) = R at hl ⊢
    rcases R with _ | ⟨e, _ | ⟨e', r⟩⟩
    · change false = true at hl
      exact Bool.noConfusion hl
    · change false = true at hl
      exact Bool.noConfusion hl
    · change bAnd(nilB r, labT T.1 t e.1 e'.1) = true at hl
      obtain ⟨hr, hl⟩ := bAnd_true hl
      obtain rfl := nilB_eq hr
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := labT_spec hl
      have hpl : (CFSG.Monster.B.Native.packetLabels ())[t]! =
          ((0, kx e.1, ky e.1), (0, kx e'.1, ky e'.1)) := by
        rw [packetLabels_get ht']
        unfold CFSG.Monster.B.Native.pauliAt
        simp only [Nat.add_assoc, Nat.reduceAdd]
        rw [hhex _ _ (by omega), hhex _ _ (by omega), hhex _ _ (by omega), hhex _ _ (by omega),
          hhex _ _ (by omega), hhex _ _ (by omega), h3, h4, h5, h6, h7, h8]
      rw [kt_eq] at h1 h2
      simp only [List.map_cons, List.map_nil, td]
      rw [hpl, kx_eq, kx_eq, ky_eq, ky_eq]
      simp [kd, h1, h2]
  · unfold CFSG.Monster.B.Rep4371.Native.spinIndexCheck
    rw [List.all_eq_true]
    intro t ht
    have ht' := List.mem_range.1 ht
    have hs := Nat.eq_of_beq_eq_true (allBelow_spec hspin (by decide) t ht')
    have hif : nIf(Nat.ble 1024 t, 2048, 0) = (if 1024 ≤ t then 2048 else 0) := by
      by_cases h : 1024 ≤ t
      · rw [if_pos h, Nat.ble_eq_true_of_le h]
      · rw [if_neg h, ble_false h]
    rw [packetSpin_get ht', hhex _ _ (by omega), CFSG.Monster.B.Rep4371.native_oddCodes,
      oddCodes_get (Nat.mod_lt _ (by decide)), beq_iff_eq, ← hif,
      show 2300 * 14 + 1 + 3 * t = 32201 + 3 * t by omega]
    exact hs

end CFSG.KC.Rep4371X

end
