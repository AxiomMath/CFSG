module

public import Certificates.Data.Kernel.McL5Pairs
public import CFSG.Certificates.Kernel.MaxD2.Sound
public import CFSG.Certificates.Kernel.Spor.RawCongr
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.KS.McL5P

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.PSL3Four.Native
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open Certificates.McLFivePairs Certificates.MaxD2Heis

set_option maxRecDepth 4000

theorem getD_get {α : Type} [Inhabited α] {a : Array α} {i : Nat} {d : α} (h : i < a.size) :
    a.getD i d = a[i]! := by
  rw [getElem!_pos a i h]
  simp [Array.getD, h]

theorem map_get! {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) {a : Array α} {i : Nat}
    (h : i < a.size) : (a.map f)[i]! = f a[i]! := by
  rw [getElem!_pos _ i (by simpa using h), Array.getElem_map, getElem!_pos a i h]

theorem perm_of {p q : Nat} (h : perm275 p q = true) :
    permOK 275 9 (mask 9) (275 * 9) p q = true := h

theorem pc1 (hn : szOK 275 9 = true) {p q : Nat} (h : perm275 p q = true) : Cn 275 9 p :=
  (perm_canon (perm_of h) hn).1

theorem pc2 (hn : szOK 275 9 = true) {p q : Nat} (h : perm275 p q = true) : Cn 275 9 q :=
  (perm_canon (perm_of h) hn).2

theorem conjBy_u (hn : szOK 275 9 = true) {r ri x : Nat} (hr : perm275 r ri = true)
    (hx : Cn 275 9 x) : conjBy (unpack 275 9 r) (unpack 275 9 x) = unpack 275 9 (cj r ri x) := by
  unfold conjBy cj
  rw [inv_u (perm_of hr), comp_u (pc2 hn hr) hx, comp_u (cc (pc2 hn hr) hx) (pc1 hn hr)]

theorem hasInv_u {r ri : Nat} (hr : perm275 r ri = true) : hasInv (unpack 275 9 r) = true := by
  unfold hasInv
  rw [inv_u (perm_of hr), inv_comp (perm_of hr)]
  simp [size_u]

theorem gensOK_u {gs : Array Tab} {k : Nat} {PS PSI : Nat → Nat} (hs : gs.size = k)
    (hS : ∀ j < k, gs[j]! = unpack 275 9 (PS j)) (hp : ∀ j < k, perm275 (PS j) (PSI j) = true) :
    gensOK gs = true := by
  unfold gensOK invsOK
  simp only [Bool.and_eq_true, beq_iff_eq, Array.size_map, true_and]
  rw [allBelow_iff']
  intro j hj
  rw [map_get! _ hj, hS j (by omega), inv_u (perm_of (hp j (by omega))),
    inv_comp (perm_of (hp j (by omega)))]
  simp [size_u]

theorem wordIn_u {gs : Array Tab} {k r : Nat} {PS PSI : Nat → Nat} {wd : List Int}
    (hs : gs.size = k) (hS : ∀ j < k, gs[j]! = unpack 275 9 (PS j))
    (hp : ∀ j < k, perm275 (PS j) (PSI j) = true) (h : wEq PS PSI k wd r = true) :
    wordIn gs wd = unpack 275 9 r := by
  unfold wordIn
  exact wordT_u ⟨hs, hS⟩ (PK.allN_iff.2 fun j hj => perm_of (hp j hj)) h

theorem l4_0 (a b c d : Nat) : l4 a b c d 0 = a := rfl
theorem l4_1 (a b c d : Nat) : l4 a b c d 1 = b := rfl
theorem l4_2 (a b c d : Nat) : l4 a b c d 2 = c := rfl
theorem l4_3 (a b c d : Nat) : l4 a b c d 3 = d := rfl

theorem beq_u {a b : Tab} (h : a = b) : (a == b) = true := by
  rw [h]
  exact beq_self_eq_true _

theorem blkK_spec {HK HKI B0 BK BKI : Nat → Nat} (h : blkK HK HKI B0 BK BKI = true) :
    ∀ k < 3, ∀ l < 4, BK (4 * k + l) = cj (HK k) (HKI k) (B0 l) ∧
      perm275 (BK (4 * k + l)) (BKI (4 * k + l)) = true := by
  intro k hk l hl
  unfold blkK at h
  have h' := band_e ((PK.allN_iff.1 ((PK.allN_iff.1 h) k hk)) l hl)
  exact ⟨Nat.eq_of_beq_eq_true h'.1, h'.2⟩

theorem pairOK_of (hn : szOK 275 9 = true) {GA GB U V UI VI : Nat} {REP REPI : Nat → Nat}
    {reps : Array Tab} (hU : perm275 U UI = true) (hV : perm275 V VI = true)
    (hrep : ∀ i < 114, reps.getD i (idTab 275) = unpack 275 9 (REP i))
    (hR : ∀ i < 114, perm275 (REP i) (REPI i) = true)
    (hA : mclTabA = unpack 275 9 GA) (hB : mclTabB = unpack 275 9 GB)
    {e : Nat × List Int × List Int} (h : pairK1 GA GB U V UI VI REP REPI e = true) :
    Certificates.McLFivePairs.pairOK (unpack 275 9 U) (unpack 275 9 V) reps e = true := by
  unfold pairK1 at h
  simp only [PK.strictB_eq] at h
  obtain ⟨hi, h⟩ := band_e h
  have hi' : e.1 < 114 := Nat.blt_eq.mp hi
  have hRp := hR _ hi'
  set c1 := cj (REP e.1) (REPI e.1) U with ec1
  set c2 := cj (REP e.1) (REPI e.1) V with ec2
  set d1 := cj (REP e.1) (REPI e.1) UI with ed1
  set d2 := cj (REP e.1) (REPI e.1) VI with ed2
  obtain ⟨h1, h⟩ := band_e h
  obtain ⟨h2, h⟩ := band_e h
  obtain ⟨ha, hb⟩ := band_e h
  have hs4 : (#[unpack 275 9 U, unpack 275 9 V, unpack 275 9 c1, unpack 275 9 c2] :
      Array Tab).size = 4 := rfl
  have hS : ∀ j < 4, (#[unpack 275 9 U, unpack 275 9 V, unpack 275 9 c1, unpack 275 9 c2] :
      Array Tab)[j]! = unpack 275 9 (l4 U V c1 c2 j) := by
    intro j hj
    interval_cases j <;> rfl
  have hp : ∀ j < 4, perm275 (l4 U V c1 c2 j) (l4 UI VI d1 d2 j) = true := by
    intro j hj
    interval_cases j
    exacts [hU, hV, h1, h2]
  unfold Certificates.McLFivePairs.pairOK pairGens
  simp only [hrep _ hi', conjBy_u hn hRp (pc1 hn hU), conjBy_u hn hRp (pc1 hn hV),
    Bool.and_eq_true]
  exact ⟨⟨⟨hasInv_u hRp, gensOK_u hs4 hS hp⟩, beq_u ((wordIn_u hs4 hS hp ha).trans hA.symm)⟩,
    beq_u ((wordIn_u hs4 hS hp hb).trans hB.symm)⟩

theorem actOK_of (hn : szOK 275 9 = true) {NG NGI BK BKI : Nat → Nat}
    {blocks : Array (Array Tab)} {ns : Array Tab}
    (hblk : ∀ k < 3, (blocks.getD k #[]).size = 4 ∧
      ∀ l < 4, (blocks.getD k #[])[l]! = unpack 275 9 (BK (4 * k + l)))
    (hbp : ∀ q < 12, perm275 (BK q) (BKI q) = true)
    (hns : ∀ j < 4, ns.getD j (idTab 275) = unpack 275 9 (NG j))
    (hnp : ∀ j < 4, perm275 (NG j) (NGI j) = true)
    {e : Nat × Nat × Nat × List (List Int)} (h : actK NG NGI BK BKI e = true) :
    actOK blocks ns e = true := by
  unfold actK at h
  obtain ⟨hi, h⟩ := band_e h
  obtain ⟨hj, h⟩ := band_e h
  obtain ⟨hk, h⟩ := band_e h
  obtain ⟨hl, h⟩ := band_e h
  have hi' : e.1 < 3 := Nat.blt_eq.mp hi
  have hj' : e.2.1 < 4 := Nat.blt_eq.mp hj
  have hk' : e.2.2.1 < 3 := Nat.blt_eq.mp hk
  unfold actOK
  simp only [hns _ hj', Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨⟨hk', hasInv_u (hnp _ hj')⟩, Nat.eq_of_beq_eq_true hl⟩, ?_⟩
  rw [allBelow_iff']
  intro l hl4
  have hw := (PK.allN_iff.1 h) l hl4
  rw [getD_get (a := blocks.getD e.1 #[]) (by rw [(hblk _ hi').1]; exact hl4),
    (hblk _ hi').2 l hl4,
    conjBy_u hn (hnp _ hj') (pc1 hn (hbp _ (by omega)))]
  exact beq_u (wordIn_u (hblk _ hk').1 (fun t ht => (hblk _ hk').2 t ht)
    (fun t ht => hbp _ (by omega)) hw)

theorem append_get4 {a b : Array Tab} (ha : a.size = 4) (hb : b.size = 4) {t : Nat} (ht : t < 8) :
    (a ++ b)[t]! = if t < 4 then a[t]! else b[t - 4]! := by
  rw [getElem!_pos (a ++ b) t (by simp [ha, hb]; omega)]
  split_ifs with h4
  · rw [Array.getElem_append_left (by omega), getElem!_pos a t (by omega)]
  · rw [Array.getElem_append_right (by omega), getElem!_pos b (t - 4) (by omega)]
    simp [ha]

theorem l8_lt {B : Nat → Nat} {i j t : Nat} (h : t < 4) : l8 B i j t = B (4 * i + t) := by
  unfold l8
  rw [Nat.blt_eq.mpr h]
  try rfl

theorem l8_ge {B : Nat → Nat} {i j t : Nat} (h : ¬ t < 4) : l8 B i j t = B (4 * j + (t - 4)) := by
  unfold l8
  rw [Bool.eq_false_iff.2 (fun h' => h (Nat.blt_eq.mp h'))]
  try rfl

theorem joinOK_of {GA GB : Nat} {BK BKI : Nat → Nat} {blocks : Array (Array Tab)}
    (hblk : ∀ k < 3, (blocks.getD k #[]).size = 4 ∧
      ∀ l < 4, (blocks.getD k #[])[l]! = unpack 275 9 (BK (4 * k + l)))
    (hbp : ∀ q < 12, perm275 (BK q) (BKI q) = true)
    (hA : mclTabA = unpack 275 9 GA) (hB : mclTabB = unpack 275 9 GB)
    {e : Nat × Nat × List Int × List Int} (h : joinK GA GB BK BKI e = true) :
    joinOK blocks e = true := by
  unfold joinK at h
  obtain ⟨hi, h⟩ := band_e h
  obtain ⟨hj, h⟩ := band_e h
  obtain ⟨ha, hb⟩ := band_e h
  have hi' : e.1 < 3 := Nat.blt_eq.mp hi
  have hj' : e.2.1 < 3 := Nat.blt_eq.mp hj
  have hs : (blocks.getD e.1 #[] ++ blocks.getD e.2.1 #[]).size = 8 := by
    rw [Array.size_append, (hblk _ hi').1, (hblk _ hj').1]
  have hS : ∀ t < 8, (blocks.getD e.1 #[] ++ blocks.getD e.2.1 #[])[t]! =
      unpack 275 9 (l8 BK e.1 e.2.1 t) := by
    intro t ht
    rw [append_get4 (hblk _ hi').1 (hblk _ hj').1 ht]
    by_cases h4 : t < 4
    · rw [if_pos h4, (hblk _ hi').2 t h4, l8_lt h4]
    · rw [if_neg h4, (hblk _ hj').2 (t - 4) (by omega), l8_ge h4]
  have hp : ∀ t < 8, perm275 (l8 BK e.1 e.2.1 t) (l8 BKI e.1 e.2.1 t) = true := by
    intro t ht
    by_cases h4 : t < 4
    · rw [l8_lt h4, l8_lt h4]
      exact hbp _ (by omega)
    · rw [l8_ge h4, l8_ge h4]
      exact hbp _ (by omega)
  unfold joinOK
  simp only [Bool.and_eq_true]
  exact ⟨⟨gensOK_u hs hS hp, beq_u ((wordIn_u hs hS hp ha).trans hA.symm)⟩,
    beq_u ((wordIn_u hs hS hp hb).trans hB.symm)⟩

theorem rawChainOK_congrW {n : Nat} {O S : Array (Array Nat)} {base : Array Nat}
    {W W' : Array (List Int)} {chunks : Nat} (hs : W.size = W'.size)
    (he : ∀ j < S.size, O.size ≤ j → W[j]! = W'[j]!) :
    rawChainOK n O S base W chunks = rawChainOK n O S base W' chunks := by
  have key : ∀ j < S.size, (decide (j < O.size) ||
      (lettersOK j W[j]! && eqA n S[j]! (wordA n S (rawInvs n S) W[j]!))) =
      (decide (j < O.size) ||
      (lettersOK j W'[j]! && eqA n S[j]! (wordA n S (rawInvs n S) W'[j]!))) := by
    intro j hj
    by_cases h : j < O.size
    · simp [h]
    · rw [he j hj (by omega)]
  simp only [rawChainOK]
  rw [hs, Raw.allLt_congr key]

end CFSG.KS.McL5P

end
