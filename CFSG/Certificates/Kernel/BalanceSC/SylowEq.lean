module

public import Certificates.Data.Kernel.BalanceSC.Sylow
public import CFSG.Certificates.Kernel.Misc.ArrEnumUnpack
public import CFSG.LocalAnalysis.OddStandard.Solomon75AhatDataPerm
import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

namespace CFSG.KC.BalanceSC.SylowEq

open CFSG.KC.BalanceSC
open CFSG.KC.Enum (pg pcomp pidn strictB)
open CFSG.KS (mask)
open CFSG.KS.Raw (unpack szOK)
open CFSG.KC.BfsPin (PP)
open CFSG.KC.LQT.P (allN anyN)
open CFSG.KC.Misc.ArrEnum (allNP_iff anyNP_eq)
open CFSG.OddStandard.Solomon75

theorem strictB_eq (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by cases y <;> rfl

theorem strictL_eq (y : ℕ) (k : ℕ → List ℕ) : strictL y k = k y := by cases y <;> rfl

theorem bAnd_eq (a b : Bool) : bAnd(a, b) = (a && b) := by cases a <;> rfl

theorem bIf_true_eq (c e : Bool) : bIf(c, true, e) = (c || e) := by cases c <;> rfl

theorem bIf_eq_true (c t : Bool) : bIf(c, t, true) = (!c || t) := by cases c <;> rfl

theorem notB_eq (a : Bool) : notB a = !a := by cases a <;> rfl

theorem allL_eq (L : List ℕ) (f : ℕ → Bool) : allL L f = L.all f := by
  induction L with
  | nil => rfl
  | cons d L ih =>
    change bAnd(f d, allL L f) = _
    rw [ih, List.all_cons, bAnd_eq]

theorem anyL_eq (L : List ℕ) (f : ℕ → Bool) : anyL L f = L.any f := by
  induction L with
  | nil => rfl
  | cons d L ih =>
    change bIf(f d, true, anyL L f) = _
    rw [ih, List.any_cons]
    cases f d <;> rfl

theorem memL_iff (c : ℕ) (L : List ℕ) : memL c L = true ↔ c ∈ L := by
  induction L with
  | nil => simp [memL]
  | cons d L ih =>
    change bIf(Nat.beq c d, true, memL c L) = true ↔ _
    rw [List.mem_cons, ← ih]
    cases h : Nat.beq c d
    · simp [Nat.ne_of_beq_eq_false h]
    · simp [Nat.eq_of_beq_eq_true h]

theorem getL_eq (L : List ℕ) (i : ℕ) : getL 0 L i = L[i]! := by
  induction L generalizing i with
  | nil => rfl
  | cons d L ih =>
    cases i with
    | zero => rfl
    | succ i =>
      change getL 0 L i = _
      rw [ih, List.getElem!_cons_succ]

theorem allN_eq (m : ℕ) (f : ℕ → Bool) : allN m f = Nat.all m fun i _ => f i := by
  apply Bool.eq_iff_iff.2
  rw [allNP_iff, AhatData.nat_all_iff]

theorem anyN_eq (m : ℕ) (f : ℕ → Bool) : anyN m f = Nat.any m fun i _ => f i := by
  apply Bool.eq_iff_iff.2
  rw [anyNP_eq, AhatData.nat_any_iff, List.any_eq_true]
  simp only [List.mem_range]
  exact ⟨fun ⟨i, hi, h⟩ => ⟨i, hi, h⟩, fun ⟨i, hi, h⟩ => ⟨i, hi, h⟩⟩

theorem all_congr' {L : List ℕ} {f g : ℕ → Bool} (h : ∀ x ∈ L, f x = g x) :
    L.all f = L.all g := by
  induction L with
  | nil => rfl
  | cons d L ih =>
    rw [List.all_cons, List.all_cons, h d List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem d hx)]

theorem any_congr' {L : List ℕ} {f g : ℕ → Bool} (h : ∀ x ∈ L, f x = g x) :
    L.any f = L.any g := by
  induction L with
  | nil => rfl
  | cons d L ih =>
    rw [List.any_cons, List.any_cons, h d List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem d hx)]

theorem natAll_congr {m : ℕ} {f g : ℕ → Bool} (h : ∀ i < m, f i = g i) :
    (Nat.all m fun i _ => f i) = Nat.all m fun i _ => g i := by
  apply Bool.eq_iff_iff.2
  rw [AhatData.nat_all_iff, AhatData.nat_all_iff]
  exact ⟨fun H i hi => (h i hi) ▸ H i hi, fun H i hi => (h i hi) ▸ H i hi⟩

theorem natAny_congr {m : ℕ} {f g : ℕ → Bool} (h : ∀ i < m, f i = g i) :
    (Nat.any m fun i _ => f i) = Nat.any m fun i _ => g i := by
  apply Bool.eq_iff_iff.2
  rw [AhatData.nat_any_iff, AhatData.nat_any_iff]
  exact ⟨fun ⟨i, hi, H⟩ => ⟨i, hi, (h i hi) ▸ H⟩, fun ⟨i, hi, H⟩ => ⟨i, hi, (h i hi).symm ▸ H⟩⟩

variable {n : ℕ}

theorem mulA_u {a b : ℕ} (ha : PP n 4 a) (hb : PP n 4 b) :
    AhatData.mulA n (unpack n 4 a) (unpack n 4 b) = unpack n 4 (pcomp n 4 15 a b) :=
  CFSG.KC.BfsPin.compA_PP ha hb

theorem eqA_u {a b : ℕ} (ha : PP n 4 a) (hb : PP n 4 b) :
    AhatData.eqA n (unpack n 4 a) (unpack n 4 b) = Nat.beq a b :=
  CFSG.KC.BfsPin.eqA_PP ha hb

theorem pp_mul {a b : ℕ} (ha : PP n 4 a) (hb : PP n 4 b) : PP n 4 (pcomp n 4 15 a b) :=
  ha.mul hb

theorem idA_u (hw : szOK n 4 = true) : AhatData.idA n = unpack n 4 (pidn n 4) :=
  CFSG.KC.BfsPin.idA_eq hw

theorem suppA_u (a : ℕ) : AhatData.suppA n (unpack n 4 a) = movK n a := by
  have key : ∀ k ≤ n, AhatData.suppAux (unpack n 4 a) k = movK k a := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      change AhatData.suppAux (unpack n 4 a) k +
          (if (unpack n 4 a)[k]! == k then 0 else 1) =
        Nat.add (movK k a) (nIf(Nat.beq (pg 4 15 a k) k, 0, 1))
      rw [ih (by omega), CFSG.KS.Raw.Orb.unpack_get (by omega : k < n)]
      change _ + (if pg 4 15 a k == k then 0 else 1) = _
      cases h : Nat.beq (pg 4 15 a k) k
      · have := Nat.ne_of_beq_eq_false h
        simp [this]
      · have := Nat.eq_of_beq_eq_true h
        simp [this]
  exact key n le_rfl

theorem invA_u (hw : szOK n 4 = true) {a : ℕ} (ha : PP n 4 a) (m : ℕ) :
    (AhatData.eqA n (AhatData.mulA n (unpack n 4 a) (unpack n 4 a)) (AhatData.idA n) &&
      AhatData.suppA n (unpack n 4 a) == m) = invK n m (pidn n 4) a := by
  rw [mulA_u ha ha, idA_u hw, eqA_u (pp_mul ha ha) (CFSG.KC.BfsPin.PP.id hw), suppA_u, invK,
    strictB_eq, bAnd_eq]
  rfl

theorem isoA_u (hw : szOK n 4 = true) {a : ℕ} (ha : PP n 4 a) :
    AhatData.isoA n (unpack n 4 a) = isoK n (pidn n 4) a :=
  invA_u hw ha 8

theorem dblA_u (hw : szOK n 4 = true) {a : ℕ} (ha : PP n 4 a) :
    AhatData.dblA n (unpack n 4 a) = dblK n (pidn n 4) a :=
  invA_u hw ha 4

theorem commA_u {a b : ℕ} (ha : PP n 4 a) (hb : PP n 4 b) :
    AhatData.commA n (unpack n 4 a) (unpack n 4 b) = commK n a b := by
  rw [AhatData.commA, mulA_u ha hb, mulA_u hb ha, eqA_u (pp_mul ha hb) (pp_mul hb ha)]
  rfl

theorem adjA_u (hw : szOK n 4 = true) {a b : ℕ} (ha : PP n 4 a) (hb : PP n 4 b) :
    AhatData.adjA n (unpack n 4 a) (unpack n 4 b) = adjK n (pidn n 4) a b := by
  rw [AhatData.adjA, eqA_u ha hb, commA_u ha hb, mulA_u ha hb, isoA_u hw (pp_mul ha hb), adjK,
    bAnd_eq, bAnd_eq, notB_eq, Bool.and_assoc]

variable {N : ℕ} {PT : ℕ → ℕ} {tab : Array (Array ℕ)}

structure Bind (n N : ℕ) (PT : ℕ → ℕ) (tab : Array (Array ℕ)) : Prop where
  sz : szOK n 4 = true
  pos : 0 < N
  size : tab.size = N
  get : ∀ i < N, tab[i]! = unpack n 4 (PT i)
  pp : ∀ i < N, PP n 4 (PT i)

theorem isoIdx_eq (B : Bind n N PT tab) : (AhatData.isoIdx n tab).toList = isoIdxK n N PT := by
  rw [AhatData.isoIdx, Array.toList_filter, Array.toList_range, isoIdxK, strictL_eq, B.size]
  refine List.filter_congr fun k hk => ?_
  have hk' := List.mem_range.1 hk
  rw [B.get k hk', isoA_u B.sz (B.pp k hk')]

theorem lt_of_mem_iso {I : List ℕ} (B : Bind n N PT tab) (hI : (AhatData.isoIdx n tab).toList = I)
    {k : ℕ} (hk : k ∈ I) : k < N := by
  rw [← hI, Array.mem_toList_iff, AhatData.mem_isoIdx, B.size] at hk
  exact hk.1

theorem isoArr_eq {I : List ℕ} (B : Bind n N PT tab) (hI : (AhatData.isoIdx n tab).toList = I) :
    ((AhatData.isoIdx n tab).map fun k => tab[k]!).toList = (I.map PT).map (unpack n 4) := by
  rw [Array.toList_map, hI, List.map_map]
  exact List.map_congr_left fun k hk => B.get k (lt_of_mem_iso B hI hk)

theorem nbrOK_eq {I : List ℕ} (B : Bind n N PT tab) (hI : (AhatData.isoIdx n tab).toList = I) :
    AhatData.nbrOK n tab = nbrK n PT I := by
  rw [AhatData.nbrOK, ← Array.all_toList, hI, nbrK, strictB_eq, allL_eq]
  refine all_congr' fun k hk => ?_
  have hk' := lt_of_mem_iso B hI hk
  rw [strictB_eq, anyL_eq, ← Array.any_toList, hI]
  refine any_congr' fun l hl => ?_
  have hl' := lt_of_mem_iso B hI hl
  rw [strictB_eq, B.get k hk', B.get l hl', adjA_u B.sz (B.pp k hk') (B.pp l hl')]

theorem connOK_eq {I : List ℕ} (B : Bind n N PT tab) (hI : (AhatData.isoIdx n tab).toList = I)
    (ORD : List ℕ) : AhatData.connOK n tab ORD.toArray = connK n PT I ORD := by
  have hA : AhatData.isoIdx n tab = I.toArray := by rw [← hI, Array.toArray_toList]
  have hget : ∀ x : ℕ, tab[I.toArray[x]!]! = unpack n 4 (PT I[x]!) ∧ PP n 4 (PT I[x]!) := by
    intro x
    have hx : I[x]! < N := by
      by_cases h : x < I.length
      · rw [getElem!_pos I x h]
        exact lt_of_mem_iso B hI (List.getElem_mem h)
      · rw [getElem!_neg I x h]
        exact B.pos
    rw [List.getElem!_toArray (xs := I)]
    exact ⟨B.get _ hx, B.pp _ hx⟩
  unfold AhatData.connOK
  rw [hA]
  dsimp only
  rw [connK, strictB_eq, strictB_eq, bAnd_eq, bAnd_eq, bAnd_eq, allN_eq, allN_eq,
    List.size_toArray, getL_eq, List.getElem!_toArray (xs := ORD), Bool.and_assoc,
    Bool.and_assoc]
  refine congrArg₂ (· && ·) (Bool.eq_iff_iff.2 (by simp [Nat.blt_eq])) ?_
  refine congrArg₂ (· && ·) (Bool.eq_iff_iff.2 (by simp [Nat.beq_eq])) ?_
  refine congrArg₂ (· && ·) ?_ ?_
  · refine natAll_congr fun i _ => ?_
    apply Bool.eq_iff_iff.2
    rw [Array.contains_iff_mem, List.mem_toArray, memL_iff]
  · refine natAll_congr fun k _ => ?_
    rw [bAnd_eq, bIf_true_eq, getL_eq, List.getElem!_toArray (xs := ORD)]
    refine congrArg₂ (· && ·) (Bool.eq_iff_iff.2 (by simp [Nat.blt_eq]))
      (congrArg₂ (· || ·) (Bool.eq_iff_iff.2 (by simp [Nat.beq_eq])) ?_)
    rw [anyN_eq]
    refine natAny_congr fun j _ => ?_
    simp only [strictB_eq, getL_eq]
    rw [List.getElem!_toArray (xs := ORD), (hget _).1, (hget _).1,
      adjA_u B.sz (hget _).2 (hget _).2]

theorem c2_u (hw : szOK n 4 = true) {a b : ℕ} (ha : PP n 4 a) (hb : PP n 4 b) :
    (AhatData.commA n (unpack n 4 a) (unpack n 4 b) &&
      AhatData.isoA n (AhatData.mulA n (unpack n 4 a) (unpack n 4 b))) =
      c2K n (pidn n 4) a b (pcomp n 4 15 a b) := by
  rw [commA_u ha hb, mulA_u ha hb, isoA_u hw (pp_mul ha hb), c2K, bAnd_eq]

theorem c3_u (hw : szOK n 4 = true) {a b c : ℕ} (ha : PP n 4 a) (hb : PP n 4 b)
    (hc : PP n 4 c) :
    (AhatData.commA n (unpack n 4 a) (unpack n 4 c) &&
      AhatData.commA n (unpack n 4 b) (unpack n 4 c) &&
      AhatData.isoA n (AhatData.mulA n (unpack n 4 a) (unpack n 4 c)) &&
      AhatData.isoA n (AhatData.mulA n (unpack n 4 b) (unpack n 4 c)) &&
      AhatData.isoA n (AhatData.mulA n (AhatData.mulA n (unpack n 4 a) (unpack n 4 b))
        (unpack n 4 c))) = c3K n (pidn n 4) a b (pcomp n 4 15 a b) c := by
  rw [commA_u ha hc, commA_u hb hc, mulA_u ha hc, mulA_u hb hc, mulA_u ha hb,
    mulA_u (pp_mul ha hb) hc, isoA_u hw (pp_mul ha hc), isoA_u hw (pp_mul hb hc),
    isoA_u hw (pp_mul (pp_mul ha hb) hc), c3K, bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq]
  simp only [Bool.and_assoc]

theorem c4_u (hw : szOK n 4 = true) {a b c d : ℕ} (ha : PP n 4 a) (hb : PP n 4 b)
    (hc : PP n 4 c) (hd : PP n 4 d) :
    (AhatData.commA n (unpack n 4 a) (unpack n 4 d) &&
      AhatData.commA n (unpack n 4 b) (unpack n 4 d) &&
      AhatData.commA n (unpack n 4 c) (unpack n 4 d) &&
      AhatData.isoA n (AhatData.mulA n (unpack n 4 a) (unpack n 4 d)) &&
      AhatData.isoA n (AhatData.mulA n (unpack n 4 b) (unpack n 4 d)) &&
      AhatData.isoA n (AhatData.mulA n (unpack n 4 c) (unpack n 4 d)) &&
      AhatData.isoA n (AhatData.mulA n (AhatData.mulA n (unpack n 4 a) (unpack n 4 b))
        (unpack n 4 d)) &&
      AhatData.isoA n (AhatData.mulA n (AhatData.mulA n (unpack n 4 a) (unpack n 4 c))
        (unpack n 4 d)) &&
      AhatData.isoA n (AhatData.mulA n (AhatData.mulA n (unpack n 4 b) (unpack n 4 c))
        (unpack n 4 d)) &&
      AhatData.isoA n (AhatData.mulA n (AhatData.mulA n (AhatData.mulA n (unpack n 4 a)
        (unpack n 4 b)) (unpack n 4 c)) (unpack n 4 d))) =
      c4K n (pidn n 4) a b c (pcomp n 4 15 a b) (pcomp n 4 15 a c) (pcomp n 4 15 b c)
        (pcomp n 4 15 (pcomp n 4 15 a b) c) d := by
  have hab := pp_mul ha hb
  have hac := pp_mul ha hc
  have hbc := pp_mul hb hc
  have habc := pp_mul hab hc
  rw [commA_u ha hd, commA_u hb hd, commA_u hc hd, mulA_u ha hb, mulA_u ha hc, mulA_u hb hc,
    mulA_u hab hc, mulA_u ha hd, mulA_u hb hd, mulA_u hc hd, mulA_u hab hd, mulA_u hac hd,
    mulA_u hbc hd, mulA_u habc hd, isoA_u hw (pp_mul ha hd), isoA_u hw (pp_mul hb hd),
    isoA_u hw (pp_mul hc hd), isoA_u hw (pp_mul hab hd), isoA_u hw (pp_mul hac hd),
    isoA_u hw (pp_mul hbc hd), isoA_u hw (pp_mul habc hd), c4K]
  simp only [bAnd_eq, Bool.and_assoc]

theorem rankOK_eq {I : List ℕ} (B : Bind n N PT tab) (hI : (AhatData.isoIdx n tab).toList = I) :
    AhatData.rankOK n tab = rankK n PT I := by
  have hpp : ∀ k ∈ I, PP n 4 (PT k) := fun k hk => B.pp k (lt_of_mem_iso B hI hk)
  unfold AhatData.rankOK
  simp only [← Array.all_toList, isoArr_eq B hI, List.all_map, Function.comp_def]
  rw [rankK, strictB_eq, allL_eq]
  refine all_congr' fun ka ha => ?_
  rw [strictB_eq, allL_eq]
  refine all_congr' fun kb hb => ?_
  rw [strictB_eq, strictB_eq, c2_u B.sz (hpp ka ha) (hpp kb hb), bIf_eq_true, allL_eq]
  congr 1
  refine all_congr' fun kc hc => ?_
  rw [strictB_eq, c3_u B.sz (hpp ka ha) (hpp kb hb) (hpp kc hc), bIf_eq_true, strictB_eq,
    strictB_eq, strictB_eq, allL_eq]
  congr 1
  refine all_congr' fun kd hd => ?_
  rw [strictB_eq, notB_eq, c4_u B.sz (hpp ka ha) (hpp kb hb) (hpp kc hc) (hpp kd hd)]

theorem eightE_u {L : List ℕ} (hlen : L.length = 8) (hp : ∀ x ∈ L, PP n 4 x) :
    ((Nat.all 8 fun i _ => Nat.all 8 fun j _ => (L.map (unpack n 4)).toArray.any fun z =>
        AhatData.eqA n (AhatData.mulA n (L.map (unpack n 4)).toArray[i]!
          (L.map (unpack n 4)).toArray[j]!) z) &&
      Nat.all 8 fun i _ => Nat.all i fun j _ =>
        !(AhatData.eqA n (L.map (unpack n 4)).toArray[i]! (L.map (unpack n 4)).toArray[j]!)) =
      eightE n L := by
  have hget : ∀ i < 8, (L.map (unpack n 4)).toArray[i]! = unpack n 4 (getL 0 L i) ∧
      PP n 4 (getL 0 L i) := by
    intro i hi
    have hi' : i < L.length := by omega
    rw [List.getElem!_toArray (xs := L.map (unpack n 4)), getL_eq,
      getElem!_pos _ i (by simpa using hi'),
      getElem!_pos L i hi', List.getElem_map]
    exact ⟨rfl, hp _ (List.getElem_mem hi')⟩
  rw [eightE, bAnd_eq]
  simp only [allN_eq]
  congr 1
  · refine natAll_congr fun i hi => natAll_congr fun j hj => ?_
    rw [(hget i hi).1, (hget j hj).1, mulA_u (hget i hi).2 (hget j hj).2, strictB_eq,
      ← Array.any_toList, List.toList_toArray, List.any_map]
    apply Bool.eq_iff_iff.2
    rw [memL_iff, List.any_eq_true]
    constructor
    · rintro ⟨x, hx, h⟩
      rw [Function.comp_apply, eqA_u (pp_mul (hget i hi).2 (hget j hj).2) (hp x hx)] at h
      rwa [Nat.eq_of_beq_eq_true h]
    · intro h
      refine ⟨_, h, ?_⟩
      rw [Function.comp_apply, eqA_u (pp_mul (hget i hi).2 (hget j hj).2) (hp _ h)]
      exact Nat.beq_refl _
  · refine natAll_congr fun i hi => natAll_congr fun j hj => ?_
    rw [(hget i hi).1, (hget j (by omega)).1, eqA_u (hget i hi).2 (hget j (by omega)).2, notB_eq]

theorem eightSub_u (hw : szOK n 4 = true) {a b c : ℕ} (ha : PP n 4 a) (hb : PP n 4 b)
    (hc : PP n 4 c) :
    AhatData.eightSubOK n (unpack n 4 a) (unpack n 4 b) (unpack n 4 c) =
      eightSubK n (pidn n 4) a b c (pcomp n 4 15 a b) := by
  have hab := pp_mul ha hb
  have hE : AhatData.eightArr n (unpack n 4 a) (unpack n 4 b) (unpack n 4 c) =
      (([pidn n 4, a, b, pcomp n 4 15 a b, c, pcomp n 4 15 a c, pcomp n 4 15 b c,
        pcomp n 4 15 (pcomp n 4 15 a b) c]).map (unpack n 4)).toArray := by
    rw [AhatData.eightArr, idA_u hw, mulA_u ha hb, mulA_u ha hc, mulA_u hb hc, mulA_u hab hc]
    rfl
  have hEp : ∀ x ∈ [pidn n 4, a, b, pcomp n 4 15 a b, c, pcomp n 4 15 a c, pcomp n 4 15 b c,
      pcomp n 4 15 (pcomp n 4 15 a b) c], PP n 4 x := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [CFSG.KC.BfsPin.PP.id hw, ha, hb, hab, hc, pp_mul ha hc, pp_mul hb hc, pp_mul hab hc]
  unfold AhatData.eightSubOK
  rw [hE, eightE_u rfl hEp, eightSubK, strictB_eq, strictB_eq, strictB_eq]

theorem eightOK_eq {I : List ℕ} (B : Bind n N PT tab) (hI : (AhatData.isoIdx n tab).toList = I) :
    AhatData.eightOK n tab = eightK n PT I := by
  have hpp : ∀ k ∈ I, PP n 4 (PT k) := fun k hk => B.pp k (lt_of_mem_iso B hI hk)
  unfold AhatData.eightOK
  simp only [← Array.any_toList, isoArr_eq B hI, List.any_map, Function.comp_def]
  rw [eightK, strictB_eq, anyL_eq]
  refine any_congr' fun ka ha => ?_
  rw [strictB_eq, anyL_eq]
  refine any_congr' fun kb hb => ?_
  rw [strictB_eq, strictB_eq, bAnd_eq, ← c2_u B.sz (hpp ka ha) (hpp kb hb), anyL_eq]
  congr 1
  refine any_congr' fun kc hc => ?_
  rw [strictB_eq, bAnd_eq, ← c3_u B.sz (hpp ka ha) (hpp kb hb) (hpp kc hc),
    eightSub_u B.sz (hpp ka ha) (hpp kb hb) (hpp kc hc)]

theorem halfOK_eq {I : List ℕ} (B : Bind n N PT tab) (hI : (AhatData.isoIdx n tab).toList = I) :
    AhatData.halfOK n tab = halfK n N PT I := by
  have htl : tab.toList = (List.range N).map fun i => unpack n 4 (PT i) := by
    apply List.ext_getElem
    · simp [B.size]
    · intro i h1 h2
      rw [Array.getElem_toList, List.getElem_map, List.getElem_range,
        ← B.get i (by simpa [B.size] using h1), getElem!_pos tab i (by simpa using h1)]
  unfold AhatData.halfOK
  rw [← Array.any_toList, hI, halfK, strictB_eq, anyL_eq]
  refine any_congr' fun k hk => ?_
  have hk' := lt_of_mem_iso B hI hk
  rw [strictB_eq, bAnd_eq, allN_eq, anyNP_eq, ← Array.any_toList, htl, List.any_map, B.size,
    B.get k hk']
  congr 1
  · refine natAll_congr fun j hj => ?_
    rw [strictB_eq, B.get j hj, commA_u (B.pp k hk') (B.pp j hj)]
  · refine any_congr' fun s hs => ?_
    have hs := List.mem_range.1 hs
    rw [Function.comp_apply, strictB_eq, bAnd_eq, bAnd_eq, dblA_u B.sz (B.pp s hs),
      commA_u (B.pp s hs) (B.pp k hk'), mulA_u (B.pp s hs) (B.pp k hk'),
      isoA_u B.sz (pp_mul (B.pp s hs) (B.pp k hk')), Bool.and_assoc]

end CFSG.KC.BalanceSC.SylowEq

end
