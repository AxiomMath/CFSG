module

public import CFSG.Certificates.Kernel.Q47KSound
public import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.HexaKGlue
import CFSG.Certificates.Kernel.PackSetSound
import CFSG.Certificates.Kernel.HeSylKSound

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

@[expose] noncomputable def subK47 (x m : Nat) : Bool := Nat.beq (Nat.lor x m) m

@[expose] noncomputable def imgM47 (t : Nat) (A : Array Nat) : Nat :=
  A.toList.foldr (fun a acc => Nat.lor acc (Nat.shiftLeft 1 (pg 7 (mask 7) t a))) 0

@[expose] noncomputable def ord3F47 (t : Nat) : Bool :=
  CFSG.KLie.CT.andB
    (allN 64 fun x => Nat.beq (pg 7 (mask 7) t (pg 7 (mask 7) t (pg 7 (mask 7) t x))) x)
    (CFSG.KLie.CT.notB (Nat.beq t (pidn 64 7)))

@[expose] noncomputable def okF47 (LM : List Nat) (cs : List Cls) (t i1 i2 : Nat) : Bool :=
  CFSG.KLie.CT.andB (CFSG.KLie.CT.andB (LM.any fun m => subK47 i1 m) (LM.any fun m => subK47 i2 m))
    (CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (ord3F47 t)) (cs.all fun c => clsC c t))

@[expose] noncomputable def oStepF (m1 m2 : Nat) (W1 W2 : Array Nat) (LM : List Nat) (cs : List Cls)
    (t st : Nat) : Nat :=
  strictN t fun t => strictN (imgM47 t W1) fun i1 => strictN (imgM47 t W2) fun i2 =>
    Nat.add st (Nat.add (bn (subK47 i1 m1)) (Nat.add (Nat.mul 65536 (bn (subK47 i2 m2)))
      (Nat.add (Nat.mul 4294967296 (bn (CFSG.KLie.CT.orB
          (CFSG.KLie.CT.andB (subK47 i1 m1) (subK47 i2 m2)) (CFSG.KLie.CT.andB (subK47 i1 m2) (subK47 i2 m1)))))
        (Nat.mul 281474976710656 (bn (CFSG.KLie.CT.notB (okF47 LM cs t i1 i2)))))))

@[expose] noncomputable def oBlockF (SZ : Nat → Nat) (TR : Nat → Nat → Nat) (m1 m2 : Nat)
    (W1 W2 : Array Nat) (LM : List Nat) (cs : List Cls) (s : Nat) : Nat :=
  oFold SZ TR (oStepF m1 m2 W1 W2 LM cs) 5 1 (TR 0 s) 0

theorem subK47_iff {x m : Nat} : subK47 x m = true ↔ ∀ i, x.testBit i = true → m.testBit i = true := by
  unfold subK47
  rw [Nat.beq_eq]
  constructor
  · intro h i hi
    rw [← h]
    change (x ||| m).testBit i = true
    rw [Nat.testBit_or, hi, Bool.true_or]
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    change (x ||| m).testBit i = _
    rw [Nat.testBit_or]
    cases hx : x.testBit i
    · simp
    · simp [h i hx]

theorem bitK47_iff {m b : Nat} : HeAutK.bitK m b = true ↔ m.testBit b = true := by
  unfold HeAutK.bitK
  rw [Nat.beq_eq]
  change (m >>> b) &&& 1 = 1 ↔ _
  rw [Nat.testBit, Nat.and_comm 1, Nat.and_one_is_mod]
  have := Nat.mod_two_eq_zero_or_one (m >>> b)
  simp only [bne_iff_ne, ne_eq]
  omega

theorem subK47_lor (x y m : Nat) : subK47 (Nat.lor x y) m = (subK47 x m && subK47 y m) := by
  apply Bool.eq_iff_iff.2
  rw [Bool.and_eq_true, subK47_iff, subK47_iff, subK47_iff]
  constructor
  · intro h
    refine ⟨fun i hi => h i ?_, fun i hi => h i ?_⟩
    · change (x ||| y).testBit i = true
      rw [Nat.testBit_or, hi, Bool.true_or]
    · change (x ||| y).testBit i = true
      rw [Nat.testBit_or, hi, Bool.or_true]
  · intro h i hi
    change (x ||| y).testBit i = true at hi
    rw [Nat.testBit_or, Bool.or_eq_true] at hi
    rcases hi with hi | hi
    · exact h.1 i hi
    · exact h.2 i hi

theorem subK47_one (b m : Nat) : subK47 (Nat.shiftLeft 1 b) m = HeAutK.bitK m b := by
  apply Bool.eq_iff_iff.2
  rw [subK47_iff, bitK47_iff]
  have e : Nat.shiftLeft 1 b = 2 ^ b := by
    change 1 <<< b = 2 ^ b
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [e]
  constructor
  · intro h
    exact h b (by rw [Nat.testBit_two_pow_self])
  · intro h i hi
    rw [Nat.testBit_two_pow] at hi
    have : b = i := of_decide_eq_true hi
    rw [← this]
    exact h

theorem all_bitK (m : Nat) (f : Nat → Nat) : ∀ L : List Nat,
    (L.all fun a => HeAutK.bitK m (f a)) =
      subK47 (L.foldr (fun a acc => Nat.lor acc (Nat.shiftLeft 1 (f a))) 0) m
  | [] => by
    change true = Nat.beq (0 ||| m) m
    rw [Nat.zero_or, Nat.beq_refl]
  | a :: L => by
    rw [List.all_cons, List.foldr_cons, subK47_lor, ← all_bitK m f L, subK47_one, Bool.and_comm]

theorem mapsK_eq (t : Nat) (A : Array Nat) (m : Nat) : mapsK t A m = subK47 (imgM47 t A) m :=
  all_bitK m _ A.toList

theorem ord3F47_eq {t : Nat} (ht : PP 64 7 t) : ord3F47 t = ord3 t := by
  unfold ord3F47 ord3
  congr 1
  rw [← eqA_id_PP (HeAutK.pw_PP ht 3), ← HeAutK.powN_PP ht 3, allN_eq']
  apply Bool.eq_iff_iff.2
  rw [List.all_eq_true, eqA, CFSG.Monster.B.Co2.allLt_iff]
  have hu : ∀ x < 64, (unpack 64 7 t)[x]! = pg 7 (mask 7) t x ∧ pg 7 (mask 7) t x < 64 :=
    fun x hx => ⟨by simp only [unpack_getElem!, hx, ite_true], ht.2.1 x hx⟩
  have hp : ∀ x < 64, (ComponentClassification.AS81.HeSylow.powN 64 (unpack 64 7 t) 3)[x]! =
      pg 7 (mask 7) t (pg 7 (mask 7) t (pg 7 (mask 7) t x)) := by
    intro x hx
    change (compA 64 (unpack 64 7 t) (compA 64 (unpack 64 7 t) (compA 64 (unpack 64 7 t)
      (idA 64))))[x]! = _
    have h1 := hu x hx
    have h2 := hu _ h1.2
    have h3 := hu _ h2.2
    rw [compA_get _ _ hx, compA_get _ _ hx, compA_get _ _ hx, idA_get hx, h1.1, h2.1, h3.1]
  constructor
  · intro h x hx
    rw [hp x hx, idA_get hx]
    simpa using h x (List.mem_range.2 hx)
  · intro h x hx
    have hx' := List.mem_range.1 hx
    have := h x hx'
    rw [hp x hx', idA_get hx'] at this
    simpa using this

noncomputable def incF47 (W1 W2 : Array Nat) (LM : List Nat) (cs : List Cls) (t : Nat) : Nat :=
  bn (mapsK t W1 (maskOf W1)) + 65536 * bn (mapsK t W2 (maskOf W2)) +
    4294967296 * bn (swapK W1 W2 t) +
      281474976710656 * bn (CFSG.KLie.CT.notB (okF47 LM cs t (imgM47 t W1) (imgM47 t W2)))

theorem oStepF_eq {m1 m2 : Nat} {W1 W2 : Array Nat} (hm1 : maskOf W1 = m1) (hm2 : maskOf W2 = m2)
    (LM : List Nat) (cs : List Cls) (t st : Nat) :
    oStepF m1 m2 W1 W2 LM cs t st = st + incF47 W1 W2 LM cs t := by
  unfold oStepF incF47 swapK
  rw [strictN_eq', strictN_eq', strictN_eq']
  simp only [mapsK_eq, hm1, hm2, Nat.add_eq, Nat.mul_eq]
  omega

theorem sum_incF47 (W1 W2 : Array Nat) (LM : List Nat) (cs : List Cls) : ∀ L : List Nat,
    (L.map (incF47 W1 W2 LM cs)).sum = (L.filter fun t => mapsK t W1 (maskOf W1)).length +
      65536 * (L.filter fun t => mapsK t W2 (maskOf W2)).length +
      4294967296 * (L.filter (swapK W1 W2)).length +
      281474976710656 *
        (L.filter fun t => CFSG.KLie.CT.notB (okF47 LM cs t (imgM47 t W1) (imgM47 t W2))).length := by
  intro L
  rw [← sum_bn, ← sum_bn, ← sum_bn, ← sum_bn]
  induction L with
  | nil => rfl
  | cons j L ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    unfold incF47
    omega

theorem okT_of_okF47 {W1 W2 : Array Nat} {L30 : List (Array Nat)} {LM : List Nat} {cs : List Cls}
    {t : Nat} (hLM : (List.range 30).map (fun j => maskOf (L30.getD j #[])) = LM) (ht : PP 64 7 t)
    (h : okF47 LM cs t (imgM47 t W1) (imgM47 t W2) = true) : okT W1 W2 L30 cs t = true := by
  rw [← hLM] at h
  unfold okF47 at h
  unfold okT
  rw [ord3F47_eq ht] at h
  simpa only [List.any_map, Function.comp_def, mapsK_eq] using h

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
    {m1 m2 : Nat} {LM : List Nat} (hm1 : maskOf W1 = m1) (hm2 : maskOf W2 = m2)
    (hLM : (List.range 30).map (fun j => maskOf (L30.getD j #[])) = LM)
    (hO : ∀ s < 35, Nat.beq (oBlockF SZ TR m1 m2 W1 W2 LM cs s) (BC s) = true)
    (hBC : bcK BC = true) :
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
      Nat.shiftRight (BC s) 48 = ((blk s).filter fun t =>
        CFSG.KLie.CT.notB (okF47 LM cs t (imgM47 t W1) (imgM47 t W2))).length := by
    intro s hs
    have e := Nat.eq_of_beq_eq_true (hO s hs)
    unfold oBlockF at e
    rw [oFold_sum SZ TR (incF47 W1 W2 LM cs) (oStepF_eq hm1 hm2 LM cs), Nat.zero_add, sum_incF47] at e
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
    have hok : okF47 LM cs t (imgM47 t W1) (imgM47 t W2) = true := by simpa using this
    exact okT_of_okF47 hLM
      (pl_PP hT 5 1 _ (by omega) (hT 0 (by omega) s (by rw [hSZ]; exact hs')) t ht) hok
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
