module

public import CFSG.Certificates.Kernel.Q47KSound
public import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.HexaKGlue
import CFSG.Certificates.Kernel.PackSetSound

public section

namespace CFSG.KC.Q47K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.HexaK
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.KLie.CT (sumN notB)

noncomputable def pl (SZ : Nat → Nat) (TR : Nat → Nat → Nat) : Nat → Nat → Nat → List Nat
  | 0, _, p => [p]
  | r + 1, k, p => (List.range (SZ k)).flatMap fun j => pl SZ TR r (k + 1) (HexaK.mul 64 7 p (TR k j))

def plen (SZ : Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 1
  | r + 1, k => SZ k * plen SZ r (k + 1)

theorem len_flatMap {g : Nat → List Nat} {m : Nat} (hg : ∀ j, (g j).length = m) :
    ∀ L : List Nat, (L.flatMap g).length = L.length * m
  | [] => by simp
  | j :: L => by
    rw [List.flatMap_cons, List.length_append, hg j, len_flatMap hg L, List.length_cons,
      Nat.succ_mul, Nat.add_comm]

theorem pl_length (SZ : Nat → Nat) (TR : Nat → Nat → Nat) :
    ∀ r k p, (pl SZ TR r k p).length = plen SZ r k
  | 0, _, _ => rfl
  | r + 1, k, p => by
    rw [pl, plen, len_flatMap (m := plen SZ r (k + 1)) fun j => pl_length SZ TR r (k + 1) _,
      List.length_range]

theorem foldr_add (f : Nat → Nat) : ∀ (L : List Nat) (st : Nat),
    L.foldr (fun j s => s + f j) st = st + (L.map f).sum
  | [], st => by simp
  | j :: L, st => by
    rw [List.foldr_cons, foldr_add f L st, List.map_cons, List.sum_cons]
    omega

theorem sum_flatMap_map (g : Nat → List Nat) (c : Nat → Nat) : ∀ L : List Nat,
    ((L.flatMap g).map c).sum = (L.map fun j => ((g j).map c).sum).sum
  | [] => rfl
  | j :: L => by
    rw [List.flatMap_cons, List.map_append, List.sum_append, sum_flatMap_map g c L, List.map_cons,
      List.sum_cons]

theorem filter_flatMap_length (g : Nat → List Nat) (q : Nat → Bool) : ∀ L : List Nat,
    ((L.flatMap g).filter q).length = (L.map fun j => ((g j).filter q).length).sum
  | [] => rfl
  | j :: L => by
    rw [List.flatMap_cons, List.filter_append, List.length_append, filter_flatMap_length g q L,
      List.map_cons, List.sum_cons]

theorem oFold_sum (SZ : Nat → Nat) (TR : Nat → Nat → Nat) {F : Nat → Nat → Nat} (c : Nat → Nat)
    (hF : ∀ p st, F p st = st + c p) : ∀ r k p st,
    oFold SZ TR F r k p st = st + ((pl SZ TR r k p).map c).sum
  | 0, k, p, st => by
    change F p st = _
    rw [hF, pl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  | r + 1, k, p, st => by
    change foldN (SZ k) (fun j st' => strictN (HexaK.mul 64 7 p (TR k j)) fun q =>
      oFold SZ TR F r (k + 1) q st') st = _
    rw [CFSG.KC.Pack.foldN_eq]
    simp only [strictN_eq', oFold_sum SZ TR c hF r]
    rw [foldr_add, pl, sum_flatMap_map]

theorem sum_bn (f : Nat → Bool) : ∀ L : List Nat, (L.map fun t => bn (f t)).sum = (L.filter f).length
  | [] => rfl
  | j :: L => by
    rw [List.map_cons, List.sum_cons, sum_bn f L, List.filter_cons]
    cases f j
    · change 0 + _ = _
      simp
    · change 1 + _ = _
      simp only [ite_true, List.length_cons]
      omega

theorem sumN_list (f : Nat → Nat) : ∀ N, sumN N f = ((List.range N).map f).sum
  | 0 => rfl
  | N + 1 => by
    change Nat.add (f N) (sumN N f) = _
    rw [sumN_list f N, List.range_succ, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, Nat.add_eq]
    omega

noncomputable def incT (W1 W2 : Array Nat) (L30 : List (Array Nat)) (cs : List Cls) (t : Nat) :
    Nat :=
  bn (mapsK t W1 (maskOf W1)) + 65536 * bn (mapsK t W2 (maskOf W2)) +
    4294967296 * bn (swapK W1 W2 t) + 281474976710656 * bn (CFSG.KLie.CT.notB (okT W1 W2 L30 cs t))

theorem oStep_eq (W1 W2 : Array Nat) (L30 : List (Array Nat)) (cs : List Cls) (t st : Nat) :
    oStep W1 W2 L30 cs t st = st + incT W1 W2 L30 cs t := by
  unfold oStep incT
  rw [strictN_eq']
  simp only [Nat.add_eq, Nat.mul_eq]
  omega

theorem sum_incT (W1 W2 : Array Nat) (L30 : List (Array Nat)) (cs : List Cls) : ∀ L : List Nat,
    (L.map (incT W1 W2 L30 cs)).sum = (L.filter fun t => mapsK t W1 (maskOf W1)).length +
      65536 * (L.filter fun t => mapsK t W2 (maskOf W2)).length +
      4294967296 * (L.filter (swapK W1 W2)).length +
      281474976710656 * (L.filter fun t => CFSG.KLie.CT.notB (okT W1 W2 L30 cs t)).length := by
  intro L
  rw [← sum_bn, ← sum_bn, ← sum_bn, ← sum_bn]
  induction L with
  | nil => rfl
  | cons j L ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    unfold incT
    omega

def Bd (a : Array Nat) : Prop := ∀ i < 64, a[i]! < 64

theorem compA_get {n : Nat} (a b : Array Nat) {i : Nat} (hi : i < n) :
    (compA n a b)[i]! = a[b[i]!]! := by
  unfold compA
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem compA_assoc {n : Nat} (a b e : Array Nat) (hc : ∀ i < n, e[i]! < n) :
    compA n a (compA n b e) = compA n (compA n a b) e := by
  have hs : ∀ x y : Array Nat, (compA n x y).size = n := fun x y => by simp [compA]
  apply Array.ext (by rw [hs, hs])
  intro i h1 h2
  have hi : i < n := by rwa [hs] at h1
  rw [← getElem!_pos (compA n a (compA n b e)) i h1, ← getElem!_pos (compA n (compA n a b) e) i h2,
    compA_get _ _ hi, compA_get _ _ hi, compA_get _ _ hi, compA_get _ _ (hc i hi)]

theorem idA_get {n i : Nat} (hi : i < n) : (idA n)[i]! = i := by
  unfold idA
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem compA_idA {n : Nat} {a : Array Nat} (ha : a.size = n) : compA n a (idA n) = a := by
  have hs : (compA n a (idA n)).size = n := by simp [compA]
  apply Array.ext (by rw [hs, ha])
  intro i h1 h2
  have hi : i < n := by rwa [hs] at h1
  rw [← getElem!_pos (compA n a (idA n)) i h1, compA_get _ _ hi, idA_get hi, getElem!_pos a i h2]

theorem Bd_compA {a b : Array Nat} (ha : Bd a) (hb : Bd b) : Bd (compA 64 a b) := fun i hi => by
  rw [compA_get _ _ hi]
  exact ha _ (hb i hi)

theorem Bd_idA : Bd (idA 64) := fun i hi => by
  rw [idA_get hi]
  exact hi

theorem Bd_unpack {t : Nat} (ht : PP 64 7 t) : Bd (unpack 64 7 t) := fun i hi => by
  rw [unpack_getElem!, ite_eq_left hi]
  exact ht.2.1 i hi

theorem size_unpack (n w t : Nat) : (unpack n w t).size = n := by simp [unpack]

abbrev oF (T : List (Array Nat)) (acc : List (Array Nat)) : List (Array Nat) :=
  T.flatMap fun t => acc.map fun a => compA 64 t a

theorem foldr_Bd : ∀ (Ts : List (List (Array Nat))), (∀ T ∈ Ts, ∀ t ∈ T, Bd t) →
    ∀ a ∈ Ts.foldr oF [idA 64], Bd a
  | [], _, a, ha => by
    rw [List.foldr_nil, List.mem_singleton] at ha
    rw [ha]
    exact Bd_idA
  | T :: Ts, h, a, ha => by
    rw [List.foldr_cons] at ha
    obtain ⟨t, ht, ha⟩ := List.mem_flatMap.1 ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
    exact Bd_compA (h T List.mem_cons_self t ht)
      (foldr_Bd Ts (fun T' hT' => h T' (List.mem_cons_of_mem T hT')) b hb)

theorem flatMap_congr_mem {α β : Type} {f g : α → List β} : ∀ {l : List α},
    (∀ a ∈ l, f a = g a) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
      flatMap_congr_mem fun b hb => h b (List.mem_cons_of_mem a hb)]

theorem list_of_bound {n w : Nat} {gs : List (Array Nat)} {G : Nat → Nat} (h : Bound n w gs G) :
    gs = (List.range gs.length).map fun k => unpack n w (G k) := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  rw [List.getElem_map, List.getElem_range, ← (h k h1).1, getElem!_pos gs k h1]

section Prods

variable {SZ : Nat → Nat} {TR : Nat → Nat → Nat} {Ts : List (List (Array Nat))}
  (hl : Ts.length = 6)
  (hTk : ∀ k < 6, Ts[k]! = (List.range (SZ k)).map fun j => unpack 64 7 (TR k j))
  (hT : ∀ k < 6, ∀ j < SZ k, PP 64 7 (TR k j))

include hT in
theorem pl_PP : ∀ r k p, k + r ≤ 6 → PP 64 7 p → ∀ t ∈ pl SZ TR r k p, PP 64 7 t
  | 0, k, p, _, hp, t, ht => by
    rw [pl, List.mem_singleton] at ht
    rw [ht]
    exact hp
  | r + 1, k, p, hk, hp, t, ht => by
    rw [pl] at ht
    obtain ⟨j, hj, ht⟩ := List.mem_flatMap.1 ht
    exact pl_PP r (k + 1) _ (by omega) (hp.mul (hT k (by omega) j (List.mem_range.1 hj))) t ht

include hl hTk hT in
theorem pl_unpack : ∀ r k p, k + r = 6 → PP 64 7 p →
    (pl SZ TR r k p).map (unpack 64 7) = ((Ts.drop k).foldr oF [idA 64]).map (compA 64 (unpack 64 7 p))
  | 0, k, p, hk, hp => by
    have e : Ts.drop k = [] := List.drop_eq_nil_of_le (by omega)
    rw [e, pl, List.foldr_nil, List.map_cons, List.map_nil, List.map_cons, List.map_nil,
      compA_idA (size_unpack 64 7 p)]
  | r + 1, k, p, hk, hp => by
    have hk6 : k < Ts.length := by omega
    have hBd : ∀ a ∈ (Ts.drop (k + 1)).foldr oF [idA 64], Bd a := by
      refine foldr_Bd _ fun T hT' t ht => ?_
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (List.mem_of_mem_drop hT')
      rw [← getElem!_pos Ts i hi, hTk i (by omega)] at ht
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ht
      exact Bd_unpack (hT i (by omega) j (List.mem_range.1 hj))
    rw [List.drop_eq_getElem_cons hk6, List.foldr_cons, ← getElem!_pos Ts k hk6, hTk k (by omega),
      pl, List.map_flatMap, oF, List.map_flatMap, List.flatMap_map]
    refine flatMap_congr_mem fun j hj => ?_
    have pj := hT k (by omega) j (List.mem_range.1 hj)
    have e : HexaK.mul 64 7 p (TR k j) = pcomp 64 7 (mask 7) p (TR k j) := rfl
    rw [pl_unpack r (k + 1) (HexaK.mul 64 7 p (TR k j)) (by omega) (hp.mul pj), List.map_map, e,
      ← compA_PP hp pj]
    refine List.map_congr_left fun a ha => ?_
    exact (compA_assoc _ _ _ (hBd a ha)).symm

include hl hTk hT in
theorem oAll_eq (hSZ : SZ 0 = 35) :
    ((List.range 35).flatMap fun s => pl SZ TR 5 1 (TR 0 s)).map (unpack 64 7) = oAllG Ts := by
  have h0 : 0 < Ts.length := by omega
  unfold oAllG
  rw [← List.drop_zero (l := Ts), List.drop_eq_getElem_cons h0, List.foldr_cons,
    ← getElem!_pos Ts 0 h0, hTk 0 (by omega), hSZ, List.map_flatMap, List.flatMap_map]
  refine flatMap_congr_mem fun s hs => ?_
  exact pl_unpack hl hTk hT 5 1 _ rfl (hT 0 (by omega) s (by rw [hSZ]; exact List.mem_range.1 hs))

end Prods

theorem fields {x A B C D : Nat} (h : x = A + 65536 * B + 4294967296 * C + 281474976710656 * D)
    (hA : A < 65536) (hB : B < 65536) (hC : C < 65536) :
    Nat.land x 65535 = A ∧ Nat.land (Nat.shiftRight x 16) 65535 = B ∧
      Nat.land (Nat.shiftRight x 32) 65535 = C ∧ Nat.shiftRight x 48 = D := by
  have m : ∀ y : Nat, Nat.land y 65535 = y % 65536 := fun y => Nat.and_two_pow_sub_one_eq_mod y 16
  have s : ∀ y k : Nat, Nat.shiftRight y k = y / 2 ^ k := fun y k => Nat.shiftRight_eq_div_pow y k
  rw [m, m, m, s, s, s]
  norm_num
  omega

theorem o_sound {SZ : Nat → Nat} {TR : Nat → Nat → Nat} {Ts : List (List (Array Nat))}
    {W1 W2 : Array Nat} {L30 : List (Array Nat)} {cs : List Cls} {BC : Nat → Nat}
    (hl : Ts.length = 6) (bT : ∀ k < 6, (Ts[k]!).length = SZ k ∧ Bound 64 7 Ts[k]! (TR k))
    (hSZ : SZ 0 = 35) (hSZb : Nat.blt (SZ 1 * SZ 2 * SZ 3 * SZ 4 * SZ 5) 65536 = true)
    (hO : ∀ s < 35, Nat.beq (oBlock SZ TR W1 W2 L30 cs s) (BC s) = true) (hBC : bcK BC = true) :
    ∃ OP : List Nat, oAllG Ts = OP.map (unpack 64 7) ∧ (∀ t ∈ OP, PP 64 7 t) ∧
      (∀ t ∈ OP, okT W1 W2 L30 cs t = true) ∧
      (OP.filter fun t => mapsK t W1 (maskOf W1)).length = 1344 ∧
      (OP.filter fun t => mapsK t W2 (maskOf W2)).length = 1344 ∧
      (OP.filter (swapK W1 W2)).length = 336 := by
  have hsz : szOK 64 7 = true := by decide
  have hTk : ∀ k < 6, Ts[k]! = (List.range (SZ k)).map fun j => unpack 64 7 (TR k j) := by
    intro k hk
    have e := list_of_bound (bT k hk).2
    rwa [(bT k hk).1] at e
  have hT : ∀ k < 6, ∀ j < SZ k, PP 64 7 (TR k j) := by
    intro k hk j hj
    exact PP_of_permOK hsz ((bT k hk).2 j (by rw [(bT k hk).1]; exact hj)).2
  let blk : Nat → List Nat := fun s => pl SZ TR 5 1 (TR 0 s)
  have hlen : ∀ s, (blk s).length < 65536 := by
    intro s
    have e : plen SZ 5 1 = SZ 1 * SZ 2 * SZ 3 * SZ 4 * SZ 5 := by
      simp only [plen]
      ring
    have := Nat.blt_eq.mp hSZb
    change (pl SZ TR 5 1 (TR 0 s)).length < 65536
    rw [pl_length, e]
    exact this
  have hblk : ∀ s < 35, Nat.land (BC s) 65535 = (( blk s).filter fun t => mapsK t W1 (maskOf W1)).length ∧
      Nat.land (Nat.shiftRight (BC s) 16) 65535 = ((blk s).filter fun t => mapsK t W2 (maskOf W2)).length ∧
      Nat.land (Nat.shiftRight (BC s) 32) 65535 = ((blk s).filter (swapK W1 W2)).length ∧
      Nat.shiftRight (BC s) 48 = ((blk s).filter fun t => CFSG.KLie.CT.notB (okT W1 W2 L30 cs t)).length := by
    intro s hs
    have e := Nat.eq_of_beq_eq_true (hO s hs)
    unfold oBlock at e
    rw [oFold_sum SZ TR (incT W1 W2 L30 cs) (oStep_eq W1 W2 L30 cs), Nat.zero_add, sum_incT] at e
    exact fields e.symm (lt_of_le_of_lt (List.length_filter_le _ _) (hlen s))
      (lt_of_le_of_lt (List.length_filter_le _ _) (hlen s))
      (lt_of_le_of_lt (List.length_filter_le _ _) (hlen s))
  unfold bcK at hBC
  simp only [andB_eq, Bool.and_eq_true] at hBC
  obtain ⟨c1, c2, c3, c4⟩ := hBC
  rw [sumN_list] at c1 c2 c3
  rw [allN_eq', List.all_eq_true] at c4
  replace c1 := Nat.eq_of_beq_eq_true c1
  replace c2 := Nat.eq_of_beq_eq_true c2
  replace c3 := Nat.eq_of_beq_eq_true c3
  refine ⟨(List.range 35).flatMap blk, (oAll_eq hl hTk hT hSZ).symm, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨s, hs, ht⟩ := List.mem_flatMap.1 ht
    exact pl_PP hT 5 1 _ (by omega) (hT 0 (by omega) s (by rw [hSZ]; exact List.mem_range.1 hs)) t ht
  · intro t ht
    obtain ⟨s, hs, ht⟩ := List.mem_flatMap.1 ht
    have hs' := List.mem_range.1 hs
    have h0 := Nat.eq_of_beq_eq_true (c4 s hs)
    rw [(hblk s hs').2.2.2, List.length_eq_zero_iff, List.filter_eq_nil_iff] at h0
    have := h0 t ht
    rw [notB_eq] at this
    simpa using this
  · rw [filter_flatMap_length, ← c1]
    exact congrArg List.sum
      (List.map_congr_left fun s hs => ((hblk s (List.mem_range.1 hs)).1).symm)
  · rw [filter_flatMap_length, ← c2]
    exact congrArg List.sum
      (List.map_congr_left fun s hs => ((hblk s (List.mem_range.1 hs)).2.1).symm)
  · rw [filter_flatMap_length, ← c3]
    exact congrArg List.sum
      (List.map_congr_left fun s hs => ((hblk s (List.mem_range.1 hs)).2.2.1).symm)

end CFSG.KC.Q47K

end
