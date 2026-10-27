module

public import Certificates.Data.Kernel.WeylE8.Frame
public import CFSG.Certificates.Kernel.LocalCompCoordSound
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylAGLData
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.Spor.SiftEq

public section

namespace CFSG.KLC.E8

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def frameMaskOfL (L : List (List ℤ)) (K : List ℕ) (x : Array ℕ) : ℕ :=
  ((List.range 8).filter fun i => x[K.getD i 0]! == (negArrL L)[K.getD i 0]!).foldl
    (fun m i => m + 2 ^ i) 0 % 256

@[expose] def memE1L (L : List (List ℤ)) (K : List ℕ) (FA : Array (Array ℕ)) (x : Array ℕ) :
    Bool :=
  eqA 240 x FA[frameMaskOfL L K x]!

@[expose] def negSetL (L : List (List ℤ)) (x : Array ℕ) : List ℕ :=
  (List.range 240).filter fun r => x[r]! == (negArrL L)[r]!

@[expose] def frame16CheckWithL (L : List (List ℤ)) (K : List ℕ) (RA FA : Array (Array ℕ)) : Bool :=
  allLt 240 (fun r => !memE1L L K FA RA[r]! || (List.range 8).any fun i =>
    r == K.getD i 0 || r == (negArrL L)[K.getD i 0]!) &&
  allLt 8 (fun i => allLt 8 fun j => i == j ||
    (K.getD i 0 != K.getD j 0 && K.getD i 0 != (negArrL L)[K.getD j 0]!))

@[expose] def frameCheckWithL (L : List (List ℤ)) (K F : List ℕ) (RA FA : Array (Array ℕ)) :
    Bool :=
  allLt 240 (fun r => memE1L L K FA RA[r]! == F.contains r) &&
    allLt 256 (fun m => frameMaskOfL L K FA[m]! == m) &&
    allLt 256 (fun m => allLt 8 fun i =>
      (FA[m]!)[K.getD i 0]! ==
        if m.testBit i then (negArrL L)[K.getD i 0]! else K.getD i 0) &&
    allLt 8 (fun i => negSetL L RA[K.getD i 0]! ==
      [K.getD i 0, (negArrL L)[K.getD i 0]!].mergeSort (fun a b => decide (a ≤ b))) &&
    allLt 8 (fun i => allLt 8 fun j => i == j || negSetL L FA[2 ^ i + 2 ^ j]! ==
      [K.getD i 0, (negArrL L)[K.getD i 0]!, K.getD j 0,
        (negArrL L)[K.getD j 0]!].mergeSort (fun a b => decide (a ≤ b))) &&
    allLt 256 (fun m => framePop m != 4 || ((fixCount 240 FA[m]! == 24) == frameIsPlane m))

@[expose] def singerCheckWithL (L : List (List ℤ)) (G : List ℕ) (B : List (Fin 240)) (K : List ℕ)
    (X : Array ℕ) (SL FL : List ℕ) : Bool :=
  isInvA 240 X (invCand 240 X) && siftWL L G B X && isId (powArr' X 7) &&
    allLt 8 (fun i => X[K.getD i 0]! == K.getD (SL.getD i 0) 0) &&
    allLt 8 (fun i => ((signArrsL L)[5]!)[K.getD i 0]! ==
      if i < 4 then (negArrL L)[K.getD (FL.getD i 0) 0]! else K.getD i 0)

theorem frame16Check_eq :
    frame16Check = frame16CheckWithL rootList keyPts (reflArrsL rootList) (frameArrsL rootList) :=
  rfl

theorem frameCheck_eq :
    frameCheck = frameCheckWithL rootList keyPts frame16 (reflArrsL rootList) (frameArrsL rootList) :=
  rfl

theorem equivCheck_eq : equivCheck = equivCheckWith (reflArrsL rootList) := rfl

theorem singerCheck_eq :
    singerCheck = singerCheckWithL rootList sgsRoots wBase keyPts singerArr singerList flipList :=
  rfl

end CFSG.KLC.E8

end

namespace CFSG.KLC.E8

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem e8_eq (P i : ℕ) : e8 P i = pg 8 (mask 8) P i := rfl

theorem ne_of_beq_false {a b : ℕ} (h : Nat.beq a b = false) : a ≠ b := Nat.ne_of_beq_eq_false h

theorem notB'_true {b : Bool} (h : notB' b = true) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

theorem allN_false {n : ℕ} {f : ℕ → Bool} (h : allN n f = false) : ∃ i < n, f i = false := by
  by_contra hc
  have : allN n f = true := Orb.allN_iff.2 fun i hi => by
    cases hf : f i
    · exact absurd ⟨i, hi, hf⟩ hc
    · rfl
  rw [this] at h
  exact absurd h (by decide)

theorem low_of_eqA {X Y : ℕ} (h : eqA 240 (unpack 240 8 X) (unpack 240 8 Y) = true) :
    low X = low Y := by
  apply PF.eq_of_fields (n := 240) (w := 8) (by norm_num) (low_shr X) (low_shr Y)
  intro i hi
  have := eqA_spec h i hi
  rw [Orb.unpack_get hi, Orb.unpack_get hi] at this
  change pg 8 (mask 8) (Nat.land X (mask (nat_lit 1920))) i =
    pg 8 (mask 8) (Nat.land Y (mask (nat_lit 1920))) i
  rw [pg_low8 hi, pg_low8 hi, this]

theorem refl_c (r x : Fin 8 → ℤ) (c : ℤ) (h : ∑ j, x j * r j = 4 * c) :
    reflVec (List.ofFn r) (List.ofFn x) = List.ofFn (fun k => x k - c * r k) := by
  rw [reflVec_ofFn, h, Int.mul_ediv_cancel_left _ (by norm_num : (4 : ℤ) ≠ 0)]

theorem lin_l (u v w : Fin 8 → ℤ) (c : ℤ) :
    ∑ j, (u j - c * v j) * w j = ∑ j, u j * w j - c * ∑ j, v j * w j := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  congr 1
  funext j
  ring

theorem lin_r (u v w : Fin 8 → ℤ) (c : ℤ) :
    ∑ j, u j * (v j - c * w j) = ∑ j, u j * v j - c * ∑ j, u j * w j := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  congr 1
  funext j
  ring

theorem dcomm (u v : Fin 8 → ℤ) : ∑ j, u j * v j = ∑ j, v j * u j := by
  congr 1
  funext j
  ring

theorem equiv_vec (x a r : Fin 8 → ℤ) (haa : ∑ j, a j * a j = 8) {c1 c4 c6 : ℤ}
    (h1 : ∑ j, x j * a j = 4 * c1) (h4 : ∑ j, r j * a j = 4 * c4) (h6 : ∑ j, x j * r j = 4 * c6) :
    reflVec (List.ofFn a) (reflVec (List.ofFn r) (reflVec (List.ofFn a) (List.ofFn x))) =
      reflVec (reflVec (List.ofFn a) (List.ofFn r)) (List.ofFn x) := by
  have hy : reflVec (List.ofFn a) (List.ofFn x) = List.ofFn (fun k => x k - c1 * a k) :=
    refl_c a x c1 h1
  have hra : reflVec (List.ofFn a) (List.ofFn r) = List.ofFn (fun k => r k - c4 * a k) :=
    refl_c a r c4 h4
  have hz : reflVec (List.ofFn r) (List.ofFn (fun k => x k - c1 * a k)) =
      List.ofFn (fun k => (x k - c1 * a k) - (c6 - c1 * c4) * r k) :=
    refl_c r _ (c6 - c1 * c4) (by rw [lin_l, h6, dcomm a r, h4]; ring)
  have hw : reflVec (List.ofFn a) (List.ofFn (fun k => (x k - c1 * a k) - (c6 - c1 * c4) * r k)) =
      List.ofFn (fun k => ((x k - c1 * a k) - (c6 - c1 * c4) * r k) -
        (-c1 - (c6 - c1 * c4) * c4) * a k) :=
    refl_c a _ (-c1 - (c6 - c1 * c4) * c4) (by
      rw [lin_l (fun k => x k - c1 * a k), lin_l x, h1, haa, h4]
      ring)
  have hv : reflVec (List.ofFn (fun k => r k - c4 * a k)) (List.ofFn x) =
      List.ofFn (fun k => x k - (c6 - c1 * c4) * (r k - c4 * a k)) :=
    refl_c _ x (c6 - c1 * c4) (by rw [lin_r, h6, h1]; ring)
  rw [hy, hz, hw, hra, hv]
  congr 1
  funext k
  ring

theorem refl_dvd {x r e : ℕ} (he : e < 4294967296) (hk : e = reflKey x r) :
    ∃ c : ℤ, dotZ (vecOf x) (vecOf r) = 4 * c := by
  have hdot := dot_eq x r
  have he2 := he
  unfold reflKey at hk
  beta_reduce at hk
  generalize hP : Nat.add (sumN (nat_lit 8) fun k => Nat.mul (cf x k) (cf r k)) (nat_lit 32) = P
    at hk
  generalize hN : Nat.mul (nat_lit 2) (Nat.add (sumN (nat_lit 8) fun k => cf x k)
    (sumN (nat_lit 8) fun k => cf r k)) = N at hk
  have hd : dotZ (vecOf x) (vecOf r) = (P : ℤ) - N := by
    rw [← hP, ← hN]
    exact hdot
  rw [hd]
  cases h1 : Nat.beq P N
  · simp only [h1] at hk
    cases h2 : Nat.beq P (Nat.add N (nat_lit 4))
    · simp only [h2] at hk
      cases h3 : Nat.beq N (Nat.add P (nat_lit 4))
      · simp only [h3] at hk
        cases h4 : Nat.beq P (Nat.add N (nat_lit 8))
        · simp only [h4] at hk
          cases h5 : Nat.beq N (Nat.add P (nat_lit 8))
          · simp only [h5] at hk
            rw [hk] at he2
            exact absurd he2 (lt_irrefl _)
          · have h5' : N = P + 8 := Nat.eq_of_beq_eq_true h5
            exact ⟨-2, by omega⟩
        · have h4' : P = N + 8 := Nat.eq_of_beq_eq_true h4
          exact ⟨2, by omega⟩
      · have h3' : N = P + 4 := Nat.eq_of_beq_eq_true h3
        exact ⟨-1, by omega⟩
    · have h2' : P = N + 4 := Nat.eq_of_beq_eq_true h2
      exact ⟨1, by omega⟩
  · have h1' : P = N := Nat.eq_of_beq_eq_true h1
    exact ⟨0, by omega⟩

noncomputable def cv (RK : ℕ → ℕ) (i : ℕ) : Fin 8 → ℤ := fun k => (cf (RK i) k : ℤ) - 2

theorem dots4 {L : List (List ℤ)} {RK RT : Nat → Nat} (hb : bindRoots RK L = true)
    (hr : ∀ r < 240, reflRowOK RK r (RT r) = true) {i j : ℕ}
    (hi : i < 240) (hj : j < 240) : ∃ c : ℤ, ∑ k, cv RK i k * cv RK j k = 4 * c := by
  obtain ⟨-, hf⟩ := bind_facts hb
  have h := hr j hj
  unfold reflRowOK at h
  rw [Orb.strictB_eq, Orb.allN_iff] at h
  have h1 := h i hi
  rw [Orb.strictB_eq] at h1
  obtain ⟨e1, e2⟩ := band_true h1
  obtain ⟨c, hc⟩ := refl_dvd (x := RK i) (r := RK j)
    (e := RK (pg (nat_lit 8) (nat_lit 255) (RT j) i)) (hf _ (blt_true e1)).1
    (Nat.eq_of_beq_eq_true e2)
  refine ⟨c, ?_⟩
  rw [← hc, vecOf, vecOf, dotZ_ofFn]
  rfl

theorem norm8 {RK : Nat → Nat} (hn8 : norm8K RK = true) {i : ℕ} (hi : i < 240) :
    ∑ k, cv RK i k * cv RK i k = 8 := by
  unfold norm8K at hn8
  rw [Orb.allN_iff] at hn8
  have h := hn8 i hi
  rw [Orb.strictB_eq] at h
  have e : sumN 8 (fun k => cf (RK i) k * cf (RK i) k) + 32 =
      4 * sumN 8 (fun k => cf (RK i) k) + 8 := Nat.eq_of_beq_eq_true h
  have hd := dot_eq (RK i) (RK i)
  have : dotZ (vecOf (RK i)) (vecOf (RK i)) = 8 := by
    rw [hd]
    push_cast
    omega
  rw [← this, vecOf, dotZ_ofFn]
  rfl

theorem bindArr {A : Array ℕ} {n P : Nat} (h : bindList A.toList n P = true) :
    A.size = n ∧ ∀ i < n, A[i]! = e8 P i ∧ e8 P i < 240 := by
  obtain ⟨h1, h2⟩ := bindList_go8 (n := n) (P := P) A.toList 0 h
  have hs : A.size = n := by rw [← Array.length_toList]; omega
  refine ⟨hs, fun i hi => ?_⟩
  have := h2 i (by rw [Array.length_toList]; omega)
  rw [Array.getElem_toList, Nat.zero_add] at this
  have h3 := this.1
  rw [this.2] at h3
  rw [getElem!_pos A i (by omega), this.2]
  exact ⟨rfl, h3⟩

theorem invCand_foldl (n : ℕ) (t : Array ℕ) :
    invCand n t = (List.range n).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0) := by
  unfold invCand
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure, List.range_eq_range']
  rfl

theorem invCand_get {n : ℕ} {t : Array ℕ} (hlt : ∀ i < n, t[i]! < n)
    (hinj : ∀ i < n, ∀ j < n, t[i]! = t[j]! → i = j) : ∀ i < n, (invCand n t)[t[i]!]! = i := by
  have key : ∀ k ≤ n, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0)).size = n ∧ ∀ i < k, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0))[t[i]!]! = i := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      obtain ⟨hs, hi⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      refine ⟨by rw [Array.size_set!, hs], fun i hik => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hik with hlt' | rfl
      · have hne : t[i]! ≠ t[k]! := fun e => by
          have := hinj i (by omega) k (by omega) e
          omega
        rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hne)]
        exact hi i hlt'
      · rw [Array.getElem!_set!_self _ _ _ (by rw [hs]; exact hlt i (by omega))]
  intro i hi
  rw [invCand_foldl]
  exact (key n le_rfl).2 i hi

theorem unpack_pcomp' {P Q : Nat} (hQ : ∀ i < 240, pg 8 (mask 8) Q i < 240) :
    unpack 240 8 (pcomp 240 8 (mask 8) P Q) = compA 240 (unpack 240 8 P) (unpack 240 8 Q) := by
  apply arr_ext8 (n := 240) (by simp [unpack]) (by simp [compA])
  intro i hi
  rw [Orb.unpack_get hi, PF.pg_pcomp (by norm_num) hi, compA_get hi, Orb.unpack_get hi,
    Orb.unpack_get (hQ i hi)]

theorem unpack_pidn' : unpack 240 8 (pidn 240 8) = idA 240 := by
  apply arr_ext8 (n := 240) (by simp [unpack]) (by simp [idA])
  intro i hi
  rw [Orb.unpack_get hi, PF.pg_pidn (by norm_num) (by norm_num) hi, idA, getElem!_ofFn_nat _ hi]

theorem powArr_eq {SG : ℕ} (hS : ∀ i < 240, pg 8 (mask 8) SG i < 240) :
    ∀ k, powArr' (unpack 240 8 SG) k = unpack 240 8 (ppow SG k) ∧
      ∀ i < 240, pg 8 (mask 8) (ppow SG k) i < 240
  | 0 => by
    refine ⟨unpack_pidn'.symm, fun i hi => ?_⟩
    change pg 8 (mask 8) (pidn 240 8) i < 240
    rw [PF.pg_pidn (by norm_num) (by norm_num) hi]
    exact hi
  | k + 1 => by
    obtain ⟨ih1, ih2⟩ := powArr_eq hS k
    have e : ppow SG (k + 1) = pcomp 240 8 (mask 8) SG (ppow SG k) := by
      change strictN (ppow SG k) (fun q => pcomp (nat_lit 240) (nat_lit 8) (nat_lit 255) SG q) = _
      rw [Orb.strictN_eq]
      rfl
    refine ⟨?_, fun i hi => ?_⟩
    · rw [powArr', ih1, e, unpack_pcomp' ih2]
    · rw [e, PF.pg_pcomp (by norm_num) hi]
      exact hS _ (ih2 i hi)

theorem beqB_true {a b : Bool} (h : beqB a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem sumN_congr' {f g : ℕ → ℕ} : ∀ {n : ℕ}, (∀ i < n, f i = g i) → sumN n f = sumN n g
  | 0, _ => rfl
  | n + 1, h => by
    change f n + sumN n f = g n + sumN n g
    rw [h n (by omega), sumN_congr' (fun i hi => h i (by omega))]

theorem foldl_pow_acc (l : List ℕ) : ∀ acc, l.foldl (fun m i => m + 2 ^ i) acc =
    acc + l.foldl (fun m i => m + 2 ^ i) 0 := by
  induction l with
  | nil => intro acc; rfl
  | cons a l ih =>
    intro acc
    simp only [List.foldl_cons]
    rw [ih (acc + 2 ^ a), ih (0 + 2 ^ a)]
    omega

theorem foldl_filter_pow (c : ℕ → Bool) : ∀ n,
    ((List.range n).filter c).foldl (fun m i => m + 2 ^ i) 0 =
      sumN n (fun i => if c i = true then 2 ^ i else 0)
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.filter_append, List.foldl_append, foldl_pow_acc, foldl_filter_pow c n]
    have hs : sumN (n + 1) (fun i => if c i = true then 2 ^ i else 0) =
        (if c n = true then 2 ^ n else 0) + sumN n (fun i => if c i = true then 2 ^ i else 0) := rfl
    rw [hs]
    cases h : c n
    · simp [h]
    · simp [h]
      omega

theorem sumN_pow_lt (c : ℕ → Bool) : ∀ n, sumN n (fun i => if c i = true then 2 ^ i else 0) < 2 ^ n
  | 0 => Nat.zero_lt_one
  | n + 1 => by
    change (if c n = true then 2 ^ n else 0) + sumN n _ < 2 ^ (n + 1)
    have := sumN_pow_lt c n
    rw [pow_succ]
    split_ifs <;> omega

theorem inList_iff {P n r : ℕ} : inList P n r = true ↔ ∃ j < n, r = e8 P j := by
  unfold inList
  rw [notB'_eq, Bool.not_eq_true']
  constructor
  · intro h
    obtain ⟨j, hj, hf⟩ := allN_false h
    refine ⟨j, hj, ?_⟩
    cases h2 : Nat.beq r (e8 P j)
    · rw [h2] at hf
      exact absurd hf (by decide)
    · exact Nat.eq_of_beq_eq_true h2
  · rintro ⟨j, hj, rfl⟩
    cases h : allN n (fun k => notB' (Nat.beq (e8 P j) (e8 P k)))
    · rfl
    · have := Orb.allN_iff.1 h j hj
      rw [Nat.beq_refl] at this
      exact absurd this (by decide)

theorem sorted_mergeSort_le' (l : List ℕ) :
    (l.mergeSort fun a b => decide (a ≤ b)).Pairwise (· ≤ ·) := by
  have := List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) l
  exact this.imp fun h => by simpa using h

theorem mergeSort_perm_eq {l₁ l₂ : List ℕ} (h : l₁.Perm l₂) :
    (l₁.mergeSort fun a b => decide (a ≤ b)) = l₂.mergeSort fun a b => decide (a ≤ b) :=
  List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (sorted_mergeSort_le' l₁) (sorted_mergeSort_le' l₂)
    ((List.mergeSort_perm _ _).trans (h.trans (List.mergeSort_perm _ _).symm))

theorem filter_sort {q : ℕ → Bool} {l : List ℕ} (hnd : l.Nodup) (hm : ∀ r ∈ l, r < 240)
    (hq : ∀ r < 240, q r = true ↔ r ∈ l) :
    (List.range 240).filter q = l.mergeSort (fun a b => decide (a ≤ b)) := by
  have hp : ((List.range 240).filter q).Perm l := by
    rw [List.perm_ext_iff_of_nodup ((List.nodup_range).filter _) hnd]
    intro x
    rw [List.mem_filter, List.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      exact (hq x h1).1 h2
    · intro h
      exact ⟨hm x h, (hq x (hm x h)).2 h⟩
  refine List.Perm.eq_of_pairwise' (r := (· ≤ ·)) ?_ (sorted_mergeSort_le' l)
    (hp.trans (List.mergeSort_perm _ _).symm)
  exact ((List.pairwise_lt_range (n := 240)).filter q).imp (fun h => le_of_lt h)

theorem e8_two {p a : ℕ} (hp : p < 256) (ha : a < 256) :
    e8 (Nat.add p (Nat.shiftLeft a (nat_lit 8))) 0 = p ∧
      e8 (Nat.add p (Nat.shiftLeft a (nat_lit 8))) 1 = a := by
  rw [e8_eq, e8_eq, Orb.pg_eq, Orb.pg_eq]
  have e : Nat.add p (Nat.shiftLeft a (nat_lit 8)) = p + a * 256 := by
    rw [Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq]
  rw [e]
  norm_num
  omega

theorem e8_four {p a b c : ℕ} (hp : p < 256) (ha : a < 256) (hb : b < 256) (hc : c < 256) :
    let X := Nat.add (Nat.add p (Nat.shiftLeft a (nat_lit 8)))
      (Nat.add (Nat.shiftLeft b (nat_lit 16)) (Nat.shiftLeft c (nat_lit 24)))
    e8 X 0 = p ∧ e8 X 1 = a ∧ e8 X 2 = b ∧ e8 X 3 = c := by
  intro X
  rw [e8_eq, e8_eq, e8_eq, e8_eq, Orb.pg_eq, Orb.pg_eq, Orb.pg_eq, Orb.pg_eq]
  have e : X = p + a * 256 + b * 65536 + c * 16777216 := by
    simp only [X, Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq]
    norm_num
    ring
  rw [e]
  norm_num
  omega

theorem negSet_facts {NEG T P n : ℕ} (h : negSetK NEG T P n = true) :
    (∀ r < 240, (e8 T r = e8 NEG r ↔ ∃ j < n, r = e8 P j)) ∧
      ∀ j < n, ∀ k < j, e8 P j ≠ e8 P k := by
  unfold negSetK at h
  obtain ⟨h1, h2⟩ := band_true h
  rw [Orb.allN_iff] at h1 h2
  refine ⟨fun r hr => ?_, fun j hj k hk => ?_⟩
  · have := beqB_true (h1 r hr)
    rw [← inList_iff, ← this, Nat.beq_eq]
  · have h3 := h2 j hj
    rw [Orb.allN_iff] at h3
    exact ne_of_beq_false (notB'_true (h3 k hk))

theorem planeK_eq : ∀ m < 256, planeK m = frameIsPlane m := by decide +kernel

theorem frame_pts {L : List (List ℤ)} {K : List ℕ} {RK RT : Nat → Nat} {SO NEG KP : Nat}
    (hb : bindRoots RK L = true) (hs : sortedOK RK SO = true)
    (hr : ∀ r < 240, reflRowOK RK r (RT r) = true) (hn : negTabOK RK NEG = true)
    (hK : bindList K 8 KP = true) {i : ℕ} (hi : i < 8) :
    K.getD i 0 = e8 KP i ∧ e8 KP i < 240 ∧ (negArrL L)[K.getD i 0]! = e8 NEG (e8 KP i) ∧
      e8 NEG (e8 KP i) < 240 := by
  obtain ⟨h1, h2⟩ := bindList_get hK hi
  have hneg := (tables_sound hb hs hr hn).2
  have hn' : ∀ j < 240, e8 NEG j < 240 := fun j hj => by
    unfold negTabOK at hn
    rw [Orb.allN_iff] at hn
    have := hn j hj
    rw [Orb.strictB_eq] at this
    exact blt_true (band_true this).1
  refine ⟨h1, h2, ?_, hn' _ h2⟩
  rw [hneg, h1, Orb.unpack_get h2]
  rfl

theorem mask_eq {L : List (List ℤ)} {K : List ℕ} {RK RT : Nat → Nat} {SO NEG KP T : Nat}
    (hb : bindRoots RK L = true) (hs : sortedOK RK SO = true)
    (hr : ∀ r < 240, reflRowOK RK r (RT r) = true) (hn : negTabOK RK NEG = true)
    (hK : bindList K 8 KP = true) :
    frameMaskOfL L K (unpack 240 8 T) = maskK NEG KP T := by
  unfold frameMaskOfL maskK
  rw [foldl_filter_pow, Nat.mod_eq_of_lt (lt_of_lt_of_eq (sumN_pow_lt _ 8) (by norm_num))]
  apply sumN_congr'
  intro i hi
  obtain ⟨k1, k2, k3, -⟩ := frame_pts hb hs hr hn hK hi
  rw [Orb.strictN_eq, Orb.nIf_eq, k3, k1, Orb.unpack_get k2]
  have e : Nat.shiftLeft (nat_lit 1) i = 2 ^ i := by
    rw [Nat.shiftLeft_eq', Nat.one_shiftLeft]
  rw [e]
  by_cases h : pg 8 (mask 8) T (e8 KP i) = e8 NEG (e8 KP i)
  · have h' : Nat.beq (e8 T (e8 KP i)) (e8 NEG (e8 KP i)) = true := by rw [Nat.beq_eq]; exact h
    rw [ite_eq_left (beq_iff_eq.2 h), ite_eq_left h']
  · have h' : ¬ Nat.beq (e8 T (e8 KP i)) (e8 NEG (e8 KP i)) = true := by
      rw [Nat.beq_eq]
      exact h
    have h'' : ¬ (pg 8 (mask 8) T (e8 KP i) == e8 NEG (e8 KP i)) = true := by
      rw [beq_iff_eq]
      exact h
    rw [ite_eq_right h'', ite_eq_right h']

theorem beq_nat (a b : ℕ) : (a == b) = Nat.beq a b :=
  Bool.eq_iff_iff.2 (by rw [beq_iff_eq, Nat.beq_eq])

theorem eqA_lowB (X Y : ℕ) :
    eqA 240 (unpack 240 8 X) (unpack 240 8 Y) = Nat.beq (low X) (low Y) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq]
  refine ⟨low_of_eqA, fun h => eqA_of fun i hi => ?_⟩
  rw [Orb.unpack_get hi, Orb.unpack_get hi, ← pg_low8 hi, ← pg_low8 (X := Y) hi]
  exact congrArg (fun Z => pg 8 (mask 8) Z i) h

theorem nodup4 {a b c d : ℕ} (h10 : b ≠ a) (h20 : c ≠ a) (h21 : c ≠ b) (h30 : d ≠ a) (h31 : d ≠ b)
    (h32 : d ≠ c) : [a, b, c, d].Nodup := by
  refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_,
    List.nodup_singleton d⟩⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨Ne.symm h10, Ne.symm h20, Ne.symm h30⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨Ne.symm h21, Ne.symm h31⟩
  · simp only [List.mem_singleton]
    exact Ne.symm h32

end CFSG.KLC.E8

public section

namespace CFSG.KLC.E8

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem equiv_sound {L : List (List ℤ)} {RK RT : Nat → Nat} {SO : Nat}
    (hb : bindRoots RK L = true) (hs : sortedOK RK SO = true)
    (hr : ∀ r < 240, reflRowOK RK r (RT r) = true) (hn8 : norm8K RK = true) :
    equivCheckWith (reflArrsL L) = true := by
  obtain ⟨hl, hf⟩ := bind_facts hb
  have hrefl := refl_sound hb hs hr
  have RA_get : ∀ r < 240, ∀ i < 240, ((reflArrsL L)[r]!)[i]! = pg 8 (mask 8) (RT r) i :=
    fun r hr' i hi => by rw [reflArrs_get hr', hrefl r hr', Orb.unpack_get hi]
  have hvec : ∀ j < 240, L.getD j [] = List.ofFn (cv RK j) := fun j hj => (hf j hj).2.2
  have hent : ∀ r < 240, ∀ i < 240, L.getD (pg 8 (mask 8) (RT r) i) [] =
      reflVec (L.getD r []) (L.getD i []) := fun r hr' i hi => by
    have e := congrArg (fun A => A[i]!) (hrefl r hr')
    simp only [reflArrL, getElem!_ofFn_nat _ hi, Orb.unpack_get hi] at e
    have hlt := rt_lt8 hr hr' hi
    rw [← e] at hlt ⊢
    rw [getD_eq (by omega)]
    exact List.getElem_idxOf (by omega)
  unfold equivCheckWith
  rw [allLt_iff]
  intro a ha
  rw [allLt_iff]
  intro r hr'
  have he := rt_lt8 hr ha hr'
  rw [RA_get a ha r hr']
  apply eqA_of
  intro i hi
  have h1 := rt_lt8 hr ha hi
  have h2 := rt_lt8 hr hr' h1
  have h3 := rt_lt8 hr ha h2
  have h1' : ((reflArrsL L)[a]!)[i]! < 240 := by rw [RA_get a ha i hi]; exact h1
  rw [compA_get hi, compA_get h1', RA_get a ha i hi, RA_get r hr' _ h1, RA_get a ha _ h2,
    RA_get _ he i hi]
  rw [← idxOf_root hb hs h3, ← idxOf_root hb hs (rt_lt8 hr he hi)]
  congr 1
  rw [hent a ha _ h2, hent r hr' _ h1, hent a ha i hi, hent _ he i hi, hent a ha r hr', hvec a ha,
    hvec r hr', hvec i hi]
  obtain ⟨c1, hc1⟩ := dots4 hb hr hi ha
  obtain ⟨c4, hc4⟩ := dots4 hb hr hr' ha
  obtain ⟨c6, hc6⟩ := dots4 hb hr hi hr'
  exact equiv_vec _ _ _ (norm8 hn8 ha) hc1 hc4 hc6

theorem frame16_sound {L : List (List ℤ)} {K : List ℕ} {RK RT FT : Nat → Nat} {SO NEG FR KP : Nat}
    (hb : bindRoots RK L = true) (hs : sortedOK RK SO = true)
    (hr : ∀ r < 240, reflRowOK RK r (RT r) = true) (hn : negTabOK RK NEG = true)
    (hfr : frameRootsOK RK FR = true) (hf0 : frameRowOK RK FR 0 (FT 0) = true)
    (hft : ∀ k < 8, frameRowOK RK FR (1 <<< k) (FT (1 <<< k)) = true)
    (hK : bindList K 8 KP = true) (kHF : homF FT = true) (k16 : f16K RT FT NEG KP = true) :
    frame16CheckWithL L K (reflArrsL L) (frameArrsL L) = true := by
  obtain ⟨hFA, -, -⟩ := frame_tabs hb hs hfr hf0 hft kHF
  have hrefl := refl_sound hb hs hr
  unfold f16K at k16
  obtain ⟨f1, f2⟩ := band_true k16
  rw [Orb.allN_iff] at f1
  unfold frame16CheckWithL
  rw [Bool.and_eq_true, allLt_iff, allLt_iff]
  refine ⟨fun r hr' => ?_, fun i hi => ?_⟩
  · have h1 := f1 r hr'
    cases hin : inFrame NEG KP r
    · rw [hin] at h1
      change strictB (low (RT r)) _ = true at h1
      rw [Orb.strictB_eq, Orb.allN_iff] at h1
      have hne : memE1L L K (frameArrsL L) (reflArrsL L)[r]! = false := by
        unfold memE1L
        generalize hmk : frameMaskOfL L K (reflArrsL L)[r]! = mk
        have hm : mk < 256 := by rw [← hmk]; exact Nat.mod_lt _ (by norm_num)
        rw [hFA _ hm, reflArrs_get hr', hrefl r hr', Bool.eq_false_iff]
        intro h
        exact ne_of_beq_false (notB'_true (h1 _ hm)) (low_of_eqA h)
      rw [hne]
      rfl
    · unfold inFrame at hin
      rw [notB'_eq, Bool.not_eq_true'] at hin
      obtain ⟨j, hj, hjf⟩ := allN_false hin
      rw [Orb.strictB_eq, Orb.bAnd_eq, notB'_eq, notB'_eq] at hjf
      have hjf' : r = e8 KP j ∨ r = e8 NEG (e8 KP j) := by
        cases h1 : Nat.beq r (e8 KP j)
        · cases h2 : Nat.beq r (e8 NEG (e8 KP j))
          · rw [h1, h2] at hjf
            exact absurd hjf (by decide)
          · exact Or.inr (Nat.eq_of_beq_eq_true h2)
        · exact Or.inl (Nat.eq_of_beq_eq_true h1)
      obtain ⟨k1, -, k3, -⟩ := frame_pts hb hs hr hn hK hj
      rw [Bool.or_eq_true, List.any_eq_true]
      right
      refine ⟨j, List.mem_range.2 hj, ?_⟩
      rw [k3, k1]
      rcases hjf' with e | e
      · simp [e]
      · simp [e]
  · rw [allLt_iff]
    intro j hj
    obtain ⟨k1, -, -, -⟩ := frame_pts hb hs hr hn hK hi
    obtain ⟨k1', -, k3', -⟩ := frame_pts hb hs hr hn hK hj
    by_cases hij : i = j
    · simp [hij]
    unfold distFr at f2
    rw [Orb.allN_iff] at f2
    have h2 := f2 i hi
    rw [Orb.allN_iff] at h2
    have h3 := h2 j hj
    have hb' : Nat.beq i j = false := by
      cases h : Nat.beq i j
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hij
    rw [hb'] at h3
    change bAnd(notB' _, notB' _) = true at h3
    obtain ⟨h4, h5⟩ := band_true h3
    rw [k3', k1, k1']
    simp [hij, ne_of_beq_false (notB'_true h4), ne_of_beq_false (notB'_true h5)]

theorem frame_sound {L : List (List ℤ)} {K F : List ℕ} {RK RT FT : Nat → Nat} {SO NEG FR KP FP : Nat}
    (hb : bindRoots RK L = true) (hs : sortedOK RK SO = true)
    (hr : ∀ r < 240, reflRowOK RK r (RT r) = true) (hn : negTabOK RK NEG = true)
    (hfr : frameRootsOK RK FR = true) (hf0 : frameRowOK RK FR 0 (FT 0) = true)
    (hft : ∀ k < 8, frameRowOK RK FR (1 <<< k) (FT (1 <<< k)) = true)
    (hK : bindList K 8 KP = true) (hF : bindList F 16 FP = true) (kHF : homF FT = true)
    (kfr : frameK RT FT NEG KP FP = true) :
    frameCheckWithL L K F (reflArrsL L) (frameArrsL L) = true := by
  obtain ⟨hFA, hFlt, -⟩ := frame_tabs hb hs hfr hf0 hft kHF
  have hrefl := refl_sound hb hs hr
  have hneg := (tables_sound hb hs hr hn).2
  have hneg_get : ∀ r < 240, (negArrL L)[r]! = e8 NEG r := fun r hr' => by
    rw [hneg, Orb.unpack_get hr']
    rfl
  have hRA : ∀ r < 240, (reflArrsL L)[r]! = unpack 240 8 (RT r) := fun r hr' => by
    rw [reflArrs_get hr', hrefl r hr']
  unfold frameK at kfr
  obtain ⟨F1, F2⟩ := band_true kfr
  obtain ⟨F2, F3⟩ := band_true F2
  obtain ⟨F3, F4⟩ := band_true F3
  obtain ⟨F4, F5⟩ := band_true F4
  rw [Orb.allN_iff] at F1 F2 F3 F4 F5
  have hmask : ∀ T, maskK NEG KP T < 256 := fun T => by
    rw [← mask_eq (T := T) hb hs hr hn hK]
    exact Nat.mod_lt _ (by norm_num)
  have F2' : ∀ m < 256, maskK NEG KP (FT m) = m ∧ ∀ i < 8,
      pg 8 (mask 8) (FT m) (e8 KP i) =
        if m.testBit i = true then e8 NEG (e8 KP i) else e8 KP i := fun m hm => by
    have h := F2 m hm
    rw [Orb.strictB_eq] at h
    obtain ⟨h1, h2⟩ := band_true h
    rw [Orb.allN_iff] at h2
    refine ⟨Nat.eq_of_beq_eq_true h1, fun i hi => ?_⟩
    have h3 := h2 i hi
    rw [Orb.strictB_eq] at h3
    change e8 (FT m) (e8 KP i) = _
    rw [Nat.eq_of_beq_eq_true h3, Orb.nIf_eq]
    have : (Nat.beq (Nat.land (Nat.shiftRight m i) (nat_lit 1)) (nat_lit 1) = true) =
        (m.testBit i = true) := by
      rw [Nat.beq_eq, eq_iff_iff]
      exact bit_testBit m i
    simp only [this]
  have negq : ∀ {T P n : ℕ} {l : List ℕ}, negSetK NEG T P n = true →
      (∀ j < n, e8 P j < 240) → l.Nodup → (∀ r, r ∈ l ↔ ∃ j < n, r = e8 P j) →
      negSetL L (unpack 240 8 T) = l.mergeSort (fun a b => decide (a ≤ b)) := by
    intro T P n l h hlt hnd hmem
    obtain ⟨g1, -⟩ := negSet_facts h
    unfold negSetL
    apply filter_sort hnd
    · intro r hr'
      obtain ⟨j, hj, rfl⟩ := (hmem r).1 hr'
      exact hlt j hj
    · intro r hr'
      rw [Orb.unpack_get hr', hneg_get r hr', beq_iff_eq, hmem]
      exact g1 r hr'
  have five : ∀ i < 8, ∀ j < i, negSetL L (frameArrsL L)[2 ^ i + 2 ^ j]! =
      [K.getD i 0, (negArrL L)[K.getD i 0]!, K.getD j 0, (negArrL L)[K.getD j 0]!].mergeSort
        (fun a b => decide (a ≤ b)) := by
    intro i hi j hj
    obtain ⟨k1, k2, k3, k4⟩ := frame_pts hb hs hr hn hK hi
    obtain ⟨k1', k2', k3', k4'⟩ := frame_pts hb hs hr hn hK (by omega : j < 8)
    have hij : 2 ^ i + 2 ^ j < 256 := by
      have : 2 ^ i ≤ 128 := by
        calc 2 ^ i ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 128 := by norm_num
      have : 2 ^ j < 2 ^ i := Nat.pow_lt_pow_right (by norm_num) hj
      omega
    have h := F4 i hi
    rw [Orb.allN_iff] at h
    have h' := h j hj
    rw [Orb.strictB_eq, Orb.strictB_eq] at h'
    have hm : Nat.add (Nat.shiftLeft (nat_lit 1) i) (Nat.shiftLeft (nat_lit 1) j) = 2 ^ i + 2 ^ j := by
      rw [Nat.add_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq', Nat.one_shiftLeft, Nat.one_shiftLeft]
    rw [hm] at h'
    obtain ⟨d0, d1, d2, d3⟩ := e8_four (p := e8 KP i) (a := e8 NEG (e8 KP i)) (b := e8 KP j)
      (c := e8 NEG (e8 KP j)) (by omega) (by omega) (by omega) (by omega)
    obtain ⟨-, g2⟩ := negSet_facts h'
    rw [hFA _ hij, k3, k1, k3', k1']
    refine negq h' (fun t ht => ?_) ?_ ?_
    · interval_cases t
      · rw [d0]; exact k2
      · rw [d1]; exact k4
      · rw [d2]; exact k2'
      · rw [d3]; exact k4'
    · have e10 := g2 1 (by norm_num) 0 (by norm_num)
      have e20 := g2 2 (by norm_num) 0 (by norm_num)
      have e21 := g2 2 (by norm_num) 1 (by norm_num)
      have e30 := g2 3 (by norm_num) 0 (by norm_num)
      have e31 := g2 3 (by norm_num) 1 (by norm_num)
      have e32 := g2 3 (by norm_num) 2 (by norm_num)
      rw [d0, d1, d2, d3] at *
      exact nodup4 e10 e20 e21 e30 e31 e32
    · intro r
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro (rfl | rfl | rfl | rfl)
        · exact ⟨0, by norm_num, d0.symm⟩
        · exact ⟨1, by norm_num, d1.symm⟩
        · exact ⟨2, by norm_num, d2.symm⟩
        · exact ⟨3, by norm_num, d3.symm⟩
      · rintro ⟨t, ht, rfl⟩
        interval_cases t
        · exact Or.inl d0
        · exact Or.inr (Or.inl d1)
        · exact Or.inr (Or.inr (Or.inl d2))
        · exact Or.inr (Or.inr (Or.inr d3))
  obtain ⟨Fl, Fg⟩ := bindList_go8 (n := 16) (P := FP) F 0 hF
  unfold frameCheckWithL
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [allLt_iff]
    intro r hr'
    have h := F1 r hr'
    rw [Orb.strictB_eq] at h
    have e := beqB_true h
    unfold memE1L
    rw [hRA r hr', mask_eq hb hs hr hn hK, hFA _ (hmask _), eqA_lowB, e]
    have hc : F.contains r = inList FP 16 r := by
      rw [Bool.eq_iff_iff, inList_iff, List.contains_iff_mem, List.mem_iff_getElem]
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨j, by omega, by rw [(Fg j hj).2, Nat.zero_add]; rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨j, by omega, by rw [(Fg j (by omega)).2, Nat.zero_add]; rfl⟩
    rw [hc]
    exact beq_self_eq_true _
  · rw [allLt_iff]
    intro m hm
    rw [hFA m hm, mask_eq hb hs hr hn hK, (F2' m hm).1]
    exact beq_self_eq_true _
  · rw [allLt_iff]
    intro m hm
    rw [allLt_iff]
    intro i hi
    obtain ⟨k1, k2, k3, -⟩ := frame_pts hb hs hr hn hK hi
    rw [hFA m hm, k3, k1, Orb.unpack_get k2, (F2' m hm).2 i hi]
    exact beq_self_eq_true _
  · rw [allLt_iff]
    intro i hi
    obtain ⟨k1, k2, k3, k4⟩ := frame_pts hb hs hr hn hK hi
    have h := F3 i hi
    rw [Orb.strictB_eq] at h
    obtain ⟨d0, d1⟩ := e8_two (p := e8 KP i) (a := e8 NEG (e8 KP i)) (by omega) (by omega)
    obtain ⟨-, g2⟩ := negSet_facts h
    rw [k3, k1, hRA _ k2]
    have hlt2 : ∀ t < 2, e8 (Nat.add (e8 KP i) (Nat.shiftLeft (e8 NEG (e8 KP i)) (nat_lit 8))) t <
        240 := by
      intro t ht
      interval_cases t
      · rw [d0]; exact k2
      · rw [d1]; exact k4
    have hnd2 : [e8 KP i, e8 NEG (e8 KP i)].Nodup := by
      have e10 := g2 1 (by norm_num) 0 (by norm_num)
      rw [d0, d1] at e10
      refine List.nodup_cons.2 ⟨?_, List.nodup_singleton _⟩
      simp only [List.mem_singleton]
      exact Ne.symm e10
    have hmem2 : ∀ r, r ∈ [e8 KP i, e8 NEG (e8 KP i)] ↔ ∃ j < 2,
        r = e8 (Nat.add (e8 KP i) (Nat.shiftLeft (e8 NEG (e8 KP i)) (nat_lit 8))) j := by
      intro r
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro (rfl | rfl)
        · exact ⟨0, by norm_num, d0.symm⟩
        · exact ⟨1, by norm_num, d1.symm⟩
      · rintro ⟨t, ht, rfl⟩
        interval_cases t
        · exact Or.inl d0
        · exact Or.inr d1
    rw [negq h hlt2 hnd2 hmem2]
    exact beq_self_eq_true _
  · rw [allLt_iff]
    intro i hi
    rw [allLt_iff]
    intro j hj
    rcases Nat.lt_trichotomy i j with h | rfl | h
    · have hperm : [K.getD j 0, (negArrL L)[K.getD j 0]!, K.getD i 0, (negArrL L)[K.getD i 0]!].Perm
          [K.getD i 0, (negArrL L)[K.getD i 0]!, K.getD j 0, (negArrL L)[K.getD j 0]!] :=
        List.perm_append_comm (l₁ := [K.getD j 0, (negArrL L)[K.getD j 0]!])
          (l₂ := [K.getD i 0, (negArrL L)[K.getD i 0]!])
      rw [Nat.add_comm (2 ^ i) (2 ^ j), five j hj i h, mergeSort_perm_eq hperm]
      simp
    · simp
    · rw [five i hi j h]
      simp
  · rw [allLt_iff]
    intro m hm
    by_cases h4 : framePop m = 4
    · have h := F5 m hm
      have hp : Nat.beq (pop8 m) (nat_lit 4) = true := by rw [Nat.beq_eq, pop8_eq]; exact h4
      rw [hp] at h
      change beqB _ _ = true at h
      have e := beqB_true h
      rw [hFA m hm, fixCntK_sound, beq_nat, e, planeK_eq m hm]
      simp
    · simp [h4]

theorem singer_sound {L : List (List ℤ)} {G : List ℕ} {B : List (Fin 240)} {K SL FL : List ℕ}
    {X : Array ℕ} {RK RT ST PS PSI LR TR TRI : Nat → Nat} {SO NEG KP BP SG SGI SLP FLP : Nat}
    (hb : bindRoots RK L = true) (hs : sortedOK RK SO = true)
    (hr : ∀ r < 240, reflRowOK RK r (RT r) = true) (hn : negTabOK RK NEG = true)
    (hst : ∀ m < 256, signRowOK RK m (ST m) = true) (hK : bindList K 8 KP = true)
    (hX : bindList X.toList 240 SG = true) (hSL : bindList SL 8 SLP = true)
    (hFL : bindList FL 8 FLP = true)
    (hcb : Binds 240 8 PS 13 8 BP (wSL L G) (B.map Fin.val).toArray)
    (hcp : allN 13 (fun j => permOK 240 8 (mask 8) (240 * 8) (PS j) (PSI j)) = true)
    (hcl : LevelsOK 240 8 PS PSI LR TR TRI 13 8 BP)
    (ks : singerK ST LR TRI BP NEG KP SG SGI SLP FLP = true) :
    singerCheckWithL L G B K X SL FL = true := by
  unfold singerK at ks
  obtain ⟨s1, s2⟩ := band_true ks
  obtain ⟨s2, s3⟩ := band_true s2
  obtain ⟨s3, s4⟩ := band_true s3
  obtain ⟨s4, s5⟩ := band_true s4
  obtain ⟨s5, s6⟩ := band_true s5
  rw [Orb.allN_iff] at s5 s6
  have hp := Orb.permOK_facts (n := 240) (w := 8) s1
  have hS : ∀ i < 240, pg 8 (mask 8) SG i < 240 := fun i hi => (hp.2.2 i hi).1
  obtain ⟨hXs, hXg⟩ := bindArr hX
  have hXe : X = unpack 240 8 SG := by
    apply arr_ext8 (n := 240) hXs (by simp [unpack])
    intro i hi
    rw [(hXg i hi).1, Orb.unpack_get hi]
    rfl
  have hsign := signs_sound hb hs hst
  have hneg := (tables_sound hb hs hr hn).2
  subst hXe
  unfold singerCheckWithL
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · unfold isInvA
    rw [allLt_iff]
    intro i hi
    have hlt : ∀ j < 240, (unpack 240 8 SG)[j]! < 240 := fun j hj => by
      rw [Orb.unpack_get hj]
      exact hS j hj
    have hinj : ∀ a < 240, ∀ b < 240, (unpack 240 8 SG)[a]! = (unpack 240 8 SG)[b]! → a = b :=
      fun a ha b hb2 e => by
        rw [Orb.unpack_get ha, Orb.unpack_get hb2] at e
        rw [← (hp.2.2 a ha).2, ← (hp.2.2 b hb2).2, e]
    rw [invCand_get hlt hinj i hi]
    simp [hlt i hi]
  · unfold siftWL
    rw [CFSG.KS.Raw.siftK_eq hcb hcp hcl rfl (Nat.eq_of_beq_eq_true s2) ?_]
    · exact s3
    · rw [Orb.allN_iff]
      intro i hi
      rw [Nat.blt_eq]
      exact hS i hi
  · have e : ppow SG 7 = pidn 240 8 := Nat.eq_of_beq_eq_true s4
    unfold isId
    rw [(powArr_eq hS 7).1, e, unpack_pidn']
    exact eqA_of fun _ _ => rfl
  · rw [allLt_iff]
    intro i hi
    obtain ⟨b1, b2⟩ := band_true (s5 i hi)
    obtain ⟨k1, k2, -, -⟩ := frame_pts hb hs hr hn hK hi
    obtain ⟨l1, -⟩ := bindList_get hSL hi
    obtain ⟨k1', -, -, -⟩ := frame_pts hb hs hr hn hK (blt_true b1)
    rw [k1, Orb.unpack_get k2, l1]
    change (pg 8 (mask 8) SG (e8 KP i) == K.getD (e8 SLP i) 0) = true
    rw [k1']
    exact beq_iff_eq.2 (Nat.eq_of_beq_eq_true b2)
  · rw [allLt_iff]
    intro i hi
    obtain ⟨k1, k2, -, -⟩ := frame_pts hb hs hr hn hK hi
    have h6 := s6 i hi
    rw [Orb.strictB_eq] at h6
    rw [signArrs_get (by norm_num), hsign 5 (by norm_num) (by decide), k1, Orb.unpack_get k2]
    by_cases hi4 : i < 4
    · have h4 : Nat.blt i (nat_lit 4) = true := by rw [Nat.blt_eq]; exact hi4
      rw [h4] at h6
      change bAnd(_, _) = true at h6
      obtain ⟨b1, b2⟩ := band_true h6
      obtain ⟨l1, -⟩ := bindList_get hFL hi
      obtain ⟨k1', k2', k3', -⟩ := frame_pts hb hs hr hn hK (blt_true b1)
      rw [ite_eq_left hi4, l1]
      change (pg 8 (mask 8) (ST 5) (e8 KP i) == (negArrL L)[K.getD (e8 FLP i) 0]!) = true
      rw [k3']
      exact beq_iff_eq.2 (Nat.eq_of_beq_eq_true b2)
    · have h4 : Nat.blt i (nat_lit 4) = false := by
        cases h : Nat.blt i (nat_lit 4)
        · rfl
        · exact absurd (blt_true h) hi4
      rw [h4] at h6
      change Nat.beq _ _ = true at h6
      rw [ite_eq_right hi4]
      exact beq_iff_eq.2 (Nat.eq_of_beq_eq_true h6)

end CFSG.KLC.E8

end
