module

public import Certificates.Data.Kernel.Misc.SuzOut
public import Certificates.Data.SuzOutComp
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Certificates.Kernel.PermToolSound
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Certificates.Kernel.BfsPinUnpack
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Misc.TitsPrimSound
import CFSG.Certificates.Kernel.MonsterB.Co2PermSound
import CFSG.Certificates.Kernel.LocalQTCovTPrim
import CFSG.Certificates.Kernel.Spor.Co2ChainSound
import CFSG.Certificates.Kernel.LocalQTCovParse
import CFSG.Certificates.Kernel.Common.StrSplit
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

namespace CFSG.KC.SuzOut

open CFSG.KC.Enum CFSG.KS CFSG.KC.IntLines CFSG.KC.LQT.Cov CFSG.KC.TitsPrim
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.ComponentClassification.SuzOutComp.Native
open CFSG.KS.Raw (unpack)

private theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

private theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

private theorem bAnd_eq (a b : Bool) : bAnd(a, b) = (a && b) := by cases a <;> rfl

private theorem bIf_eq (c t e : Bool) : bIf(c, t, e) = if c = true then t else e := by
  cases c <;> rfl

private theorem nIf_eq (c : Bool) (t e : Nat) : nIf(c, t, e) = if c = true then t else e := by
  cases c <;> rfl

private theorem beq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem blocksOK_of_K {n m : Nat} {L R : Nat → Nat} {lab rep : Array Nat}
    (hL : ∀ x < n, lab[x]! = L x) (hR : ∀ j < m, rep[j]! = R j) (h : repsK n m L R = true) :
    blocksOK n m lab rep = true := by
  unfold blocksOK
  rw [allLt_iff]
  intro j hj
  have hj' := allN_spec h j hj
  rw [strictB_eq, bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hj'
  rw [hR j hj, hL _ hj'.1]
  simp [hj'.1, hj'.2]

theorem blockPt_spec {n w m wT G T x : Nat} {L : Nat → Nat} (h : blockPt n w m wT G T L x = true) :
    pg w (mask w) G x < n ∧ (L x < m → L (pg w (mask w) G x) < m ∧
      L (pg w (mask w) G x) = pg wT (mask wT) T (L x)) ∧
      (¬ L x < m → ¬ L (pg w (mask w) G x) < m) := by
  rw [blockPt, strictB_eq, bAnd_eq, Bool.and_eq_true, Nat.blt_eq, strictB_eq, bIf_eq] at h
  obtain ⟨hy, h⟩ := h
  refine ⟨hy, fun hl => ?_, fun hl => ?_⟩
  · rw [if_pos (by rw [Nat.blt_eq]; exact hl), bAnd_eq, Bool.and_eq_true, Nat.blt_eq,
      Nat.beq_eq] at h
    exact h
  · rw [if_neg (by rw [Nat.blt_eq]; exact hl), bIf_eq] at h
    intro hl'
    rw [if_pos (by rw [Nat.blt_eq]; exact hl')] at h
    exact absurd h Bool.false_ne_true

theorem blockArr_eq {n w m wT G T : Nat} {L R : Nat → Nat} {lab rep : Array Nat}
    (hL : ∀ x < n, lab[x]! = L x) (hR : ∀ j < m, rep[j]! = R j)
    (h1 : ∀ x < n, blockPt n w m wT G T L x = true)
    (h2 : ∀ j < m, blockRep n w wT G T L R j = true) :
    blockArr lab rep m (unpack n w G) = unpack m wT T := by
  unfold blockArr
  change _ = Array.ofFn (n := m) fun i => pg wT (mask wT) T i.val
  congr 1
  funext j
  have hj := h2 j j.2
  rw [blockRep, strictB_eq, bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hj
  obtain ⟨hr, he⟩ := hj
  have hy := h1 _ hr
  rw [blockPt, strictB_eq, bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at hy
  rw [hR j j.2, Raw.Orb.unpack_get hr, hL _ hy.1, he]

theorem blockOK_of_K {n w m wT G T TI : Nat} {L R : Nat → Nat} {lab rep : Array Nat}
    (hL : ∀ x < n, lab[x]! = L x) (hR : ∀ j < m, rep[j]! = R j)
    (h : blockK n w m wT G T TI L R = true) : blockOK n m lab rep (unpack n w G) = true := by
  unfold blockK at h
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  have h1' := allN_spec h1
  have hB := blockArr_eq hL hR h1' (allN_spec h2)
  unfold blockOK
  rw [hB]
  simp only [Bool.and_eq_true, allLt_iff]
  refine ⟨⟨fun x hx => ?_, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨hy, hin, hout⟩ := blockPt_spec (h1' x hx)
    rw [Raw.Orb.unpack_get hx, hL x hx, hL _ hy]
    by_cases hl : L x < m
    · simp [hl, (hin hl).1]
    · simp [hl, hout hl]
  · obtain ⟨hy, hin, -⟩ := blockPt_spec (h1' x hx)
    rw [Raw.Orb.unpack_get hx, hL x hx, hL _ hy]
    by_cases hl : L x < m
    · rw [Raw.Orb.unpack_get hl, (hin hl).2]
      simp
    · simp [hl]
  · rw [CFSG.KC.LQT.Cov.T.invCand_unpack h3]
    exact Raw.Orb.isInvA_unpack h3

private theorem pair_facts {n w p r : Nat} (h : permOK n w (mask w) (n * w) p r = true) {u : Nat}
    (hu : u < n) : pg w (mask w) p u < n ∧ pg w (mask w) r u < n ∧
      pg w (mask w) r (pg w (mask w) p u) = u ∧ pg w (mask w) p (pg w (mask w) r u) = u := by
  obtain ⟨hpr, hs⟩ := CFSG.KC.LQT.Cov.T.perm_facts h
  obtain ⟨v, hv, e⟩ := hs u hu
  have hrv : pg w (mask w) r u = v := by rw [← e, (hpr v hv).2]
  exact ⟨(hpr u hu).1, by rw [hrv]; exact hv, (hpr u hu).2, by rw [hrv, e]⟩

section Words

variable {n w kS : Nat} {PS PSI : Nat → Nat} {S : Array (Array Nat)}

theorem letter_inv (hp : ∀ j < kS, permOK n w (mask w) (n * w) (PS j) (PSI j) = true)
    {z : Int} (hz0 : z ≠ 0) (hzk : z.natAbs ≤ kS) {u : Nat} (hu : u < n) :
    pg w (mask w) (letP PS PSI z) u < n ∧ pg w (mask w) (letInv PS PSI z) u < n ∧
      pg w (mask w) (letInv PS PSI z) (pg w (mask w) (letP PS PSI z) u) = u ∧
      pg w (mask w) (letP PS PSI z) (pg w (mask w) (letInv PS PSI z) u) = u := by
  cases z with
  | ofNat k =>
    have hk0 : k ≠ 0 := fun h => hz0 (by rw [h]; rfl)
    have hkk : k ≤ kS := hzk
    exact pair_facts (hp (k - 1) (by omega)) hu
  | negSucc k =>
    have hkk : k < kS := by
      have : (Int.negSucc k).natAbs = k + 1 := rfl
      omega
    obtain ⟨a, b, c, d⟩ := pair_facts (hp k hkk) hu
    exact ⟨b, a, d, c⟩

theorem ptK_ptKI (hp : ∀ j < kS, permOK n w (mask w) (n * w) (PS j) (PSI j) = true) :
    ∀ wd : List Int, lettersOK kS wd = true → ∀ y < n,
      ptK w PS PSI wd y < n ∧ ptKI w PS PSI wd y < n ∧
        ptKI w PS PSI wd (ptK w PS PSI wd y) = y ∧ ptK w PS PSI wd (ptKI w PS PSI wd y) = y
  | [], _, y, hy => ⟨hy, hy, rfl, rfl⟩
  | z :: wd, hl, y, hy => by
    simp only [CFSG.Monster.B.Co2.Native.lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne,
      ne_eq, decide_eq_true_eq] at hl
    obtain ⟨⟨hz0, hzk⟩, hl⟩ := hl
    have e1 : ∀ u, ptK w PS PSI (z :: wd) u = pg w (mask w) (letP PS PSI z) (ptK w PS PSI wd u) :=
      fun u => strictN_eq _ _
    have e2 : ∀ u, ptKI w PS PSI (z :: wd) u =
        ptKI w PS PSI wd (pg w (mask w) (letInv PS PSI z) u) := fun u => strictN_eq _ _
    obtain ⟨a1, a2, a3, a4⟩ := ptK_ptKI hp wd hl y hy
    obtain ⟨b1, -, b3, -⟩ := letter_inv hp hz0 hzk a1
    obtain ⟨-, c2, -, c4⟩ := letter_inv hp hz0 hzk hy
    obtain ⟨-, d2, -, d4⟩ := ptK_ptKI hp wd hl _ c2
    refine ⟨by rw [e1]; exact b1, by rw [e2]; exact d2, ?_, ?_⟩
    · rw [e1, e2, b3, a3]
    · rw [e2, e1, d4, c4]

private theorem push_get_lt {T : Array (Array Nat)} {g : Array Nat} {i : Nat} (hi : i < T.size) :
    (T.push g)[i]! = T[i]! := by
  rw [getElem!_pos (T.push g) i (by simp; omega), getElem!_pos T i hi, Array.getElem_push_lt]

private theorem push_get_last {T : Array (Array Nat)} {g : Array Nat} {i : Nat} (hi : i = T.size) :
    (T.push g)[i]! = g := by
  subst hi
  rw [getElem!_pos (T.push g) T.size (by simp), Array.getElem_push_eq]

variable (hS : S.size = kS) (hb : ∀ j < kS, S[j]! = unpack n w (PS j))
  (hp : ∀ j < kS, permOK n w (mask w) (n * w) (PS j) (PSI j) = true)
include hS hb hp

theorem isInvA_wordA {gw : List Int} (hgl : lettersOK kS gw = true) :
    isInvA n (wordA n S (rawInvs n S) gw) (invCand n (wordA n S (rawInvs n S) gw)) = true := by
  have hpt := wordA_pt hS hb hp gw hgl
  refine CFSG.KC.Co2Mem.isInvA_invCand (fun i hi => ?_) (fun i j hi hj e => ?_)
  · rw [(hpt i hi).1]
    exact (hpt i hi).2
  · rw [(hpt i hi).1, (hpt j hj).1] at e
    rw [← (ptK_ptKI hp gw hgl i hi).2.2.1, e, (ptK_ptKI hp gw hgl j hj).2.2.1]

theorem invCand_wordA {gw : List Int} (hgl : lettersOK kS gw = true) {y : Nat} (hy : y < n) :
    (invCand n (wordA n S (rawInvs n S) gw))[y]! = ptKI w PS PSI gw y := by
  have hpt := wordA_pt hS hb hp gw hgl
  obtain ⟨-, hz, -, hzy⟩ := ptK_ptKI hp gw hgl y hy
  have hc := CFSG.KC.Co2Mem.invCand_spec (t := wordA n S (rawInvs n S) gw)
    (fun i hi => by rw [(hpt i hi).1]; exact (hpt i hi).2)
    (fun i j hi hj e => by
      rw [(hpt i hi).1, (hpt j hj).1] at e
      rw [← (ptK_ptKI hp gw hgl i hi).2.2.1, e, (ptK_ptKI hp gw hgl j hj).2.2.1])
    _ hz
  rw [(hpt _ hz).1, hzy] at hc
  exact hc

theorem letX_pt {gw : List Int} (hgl : lettersOK kS gw = true) {z : Int} (hz0 : z ≠ 0)
    (hzk : z.natAbs ≤ kS + 1) {y : Nat} (hy : y < n) :
    (letterA (S.push (wordA n S (rawInvs n S) gw))
        (rawInvs n (S.push (wordA n S (rawInvs n S) gw))) z)[y]! = letX w kS PS PSI gw z y ∧
      letX w kS PS PSI gw z y < n := by
  set g := wordA n S (rawInvs n S) gw with hg
  have hri : rawInvs n (S.push g) = (rawInvs n S).push (invCand n g) := by
    simp [rawInvs, Array.map_push]
  have hrs : (rawInvs n S).size = kS := by simp [rawInvs, hS]
  have hpt := wordA_pt hS hb hp gw hgl
  cases z with
  | ofNat k =>
    have hk0 : k ≠ 0 := fun h => hz0 (by rw [h]; rfl)
    have hkk : k ≤ kS + 1 := hzk
    have hpos : (0 : Int) < Int.ofNat k := by
      have : (0 : Int) < (k : Int) := by omega
      exact this
    have e1 : letterA (S.push g) (rawInvs n (S.push g)) (Int.ofNat k) = (S.push g)[k - 1]! := by
      simp only [letterA, hpos, if_true]
      rfl
    have e2 : letX w kS PS PSI gw (Int.ofNat k) y = nIf(Nat.beq k (Nat.succ kS),
        ptK w PS PSI gw y, pg w (mask w) (PS (Nat.sub k 1)) y) := rfl
    rw [e1, e2, nIf_eq]
    by_cases hk : k = kS + 1
    · subst hk
      rw [push_get_last (T := S) (i := kS + 1 - 1) (by omega), if_pos (Nat.beq_refl _)]
      exact hpt y hy
    · rw [push_get_lt (T := S) (i := k - 1) (by omega), if_neg (by rw [beq_false_of_ne hk]; simp), hb _ (by omega),
        Raw.Orb.unpack_get hy]
      exact ⟨rfl, (pair_facts (hp (k - 1) (by omega)) hy).1⟩
  | negSucc k =>
    have hkk : k ≤ kS := by
      have : (Int.negSucc k).natAbs = k + 1 := rfl
      omega
    have hneg : ¬ (0 : Int) < Int.negSucc k := by
      have := Int.negSucc_lt_zero k
      omega
    have e1 : letterA (S.push g) (rawInvs n (S.push g)) (Int.negSucc k) =
        (rawInvs n (S.push g))[k]! := by
      simp only [letterA, hneg, if_false]
      congr 1
    have e2 : letX w kS PS PSI gw (Int.negSucc k) y = nIf(Nat.beq k kS,
        ptKI w PS PSI gw y, pg w (mask w) (PSI k) y) := rfl
    rw [e1, e2, nIf_eq, hri]
    by_cases hk : k = kS
    · subst hk
      rw [push_get_last (T := rawInvs n S) hrs.symm, if_pos (Nat.beq_refl _), invCand_wordA hS hb hp hgl hy]
      exact ⟨rfl, (ptK_ptKI hp gw hgl y hy).2.1⟩
    · have hk' : k < kS := by omega
      rw [push_get_lt (T := rawInvs n S) (i := k) (by omega),
        if_neg (by rw [beq_false_of_ne hk]; simp), CFSG.Quasithin.rawInvs_getElem! (by omega), hb k hk',
        CFSG.KC.LQT.Cov.T.invCand_unpack (hp k hk'), Raw.Orb.unpack_get hy]
      exact ⟨rfl, (pair_facts (hp k hk') hy).2.1⟩

theorem ptX_pt {gw : List Int} (hgl : lettersOK kS gw = true) :
    ∀ wd : List Int, lettersOK (kS + 1) wd = true → ∀ x < n,
      (wordA n (S.push (wordA n S (rawInvs n S) gw))
        (rawInvs n (S.push (wordA n S (rawInvs n S) gw))) wd)[x]! = ptX w kS PS PSI gw wd x ∧
      ptX w kS PS PSI gw wd x < n
  | [], _, x, hx => by
    rw [wordA, idA_get hx]
    exact ⟨rfl, hx⟩
  | z :: wd, hl, x, hx => by
    simp only [CFSG.Monster.B.Co2.Native.lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne,
      ne_eq, decide_eq_true_eq] at hl
    obtain ⟨⟨hz0, hzk⟩, hl⟩ := hl
    obtain ⟨e, hlt⟩ := ptX_pt hgl wd hl x hx
    have ep : ptX w kS PS PSI gw (z :: wd) x = letX w kS PS PSI gw z (ptX w kS PS PSI gw wd x) :=
      strictN_eq _ _
    rw [wordA, compA_get hx, e, ep]
    exact letX_pt hS hb hp hgl hz0 hzk hlt

theorem fixX_all {g : Array Nat} {x : Nat} (hx : x < n) :
    ∀ wd : List Int, lettersOK (kS + 1) wd = true → fixX w kS PS x wd = true →
      wd.all (fun l => l.natAbs == (S.push g).size || (S[l.natAbs - 1]!)[x]! == x) = true
  | [], _, _ => rfl
  | z :: wd, hl, hf => by
    simp only [CFSG.Monster.B.Co2.Native.lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne,
      ne_eq, decide_eq_true_eq] at hl
    obtain ⟨⟨hz0, hzk⟩, hl⟩ := hl
    have hf' : (bIf(Nat.beq z.natAbs (Nat.succ kS), true,
        Nat.beq (pg w (mask w) (PS (Nat.sub z.natAbs 1)) x) x) && fixX w kS PS x wd) = true := by
      rw [← bAnd_eq]
      exact hf
    rw [Bool.and_eq_true] at hf'
    have ih := fixX_all (g := g) hx wd hl hf'.2
    rw [List.all_cons, ih, Bool.and_true, Array.size_push, hS, Bool.or_eq_true, beq_iff_eq,
      beq_iff_eq]
    by_cases hz : z.natAbs = kS + 1
    · exact Or.inl hz
    · right
      have h1 := hf'.1
      rw [bIf_eq, if_neg (by rw [beq_false_of_ne hz]; simp), Nat.beq_eq] at h1
      rw [hb _ (by omega), Raw.Orb.unpack_get hx]
      exact h1

end Words

theorem lineWalkK_cons {N : Nat} {ok : Nat → List Int → Bool} {l : List Char}
    {L : List (List Char)} {i : Nat} :
    lineWalkK N ok (l :: L) i = Option.rec (motive := fun _ => Bool) false
      (fun wd => bAnd(ok i wd, strictB (Nat.succ i) (lineWalkK N ok L))) (intsSK (tokK l)) := rfl

theorem lineWalkK_sound {N : Nat} {ok : Nat → List Int → Bool} :
    ∀ (L : List (List Char)) (i : Nat), lineWalkK N ok L i = true →
      i + L.length = N ∧ ∀ m < L.length, ∃ wd,
        intsSK (tokK (L.getD m [])) = some wd ∧ ok (i + m) wd = true
  | [], i, h => by
    have h' : Nat.beq i N = true := h
    rw [Nat.beq_eq] at h'
    exact ⟨by simpa using h', fun m hm => absurd hm (Nat.not_lt_zero _)⟩
  | l :: L, i, h => by
    rw [lineWalkK_cons] at h
    cases hl : intsSK (tokK l) with
    | none => rw [hl] at h; exact absurd h Bool.false_ne_true
    | some wd =>
      rw [hl] at h
      change bAnd(ok i wd, strictB (Nat.succ i) (lineWalkK N ok L)) = true at h
      rw [bAnd_eq, Bool.and_eq_true, strictB_eq] at h
      obtain ⟨h1, h2⟩ := lineWalkK_sound L (Nat.succ i) h.2
      refine ⟨by simp only [List.length_cons]; omega, fun m hm => ?_⟩
      rcases m with _ | m
      · exact ⟨wd, hl, by simpa using h.1⟩
      · obtain ⟨wd', e1, e2⟩ := h2 m (by simpa using hm)
        refine ⟨wd', by simpa using e1, ?_⟩
        have e : i + (m + 1) = Nat.succ i + m := by omega
        rw [e]
        exact e2

theorem parsed_get (T : List (List Char)) (r : Nat) :
    ((T.map fun l => CFSG.YGroups.ModelNative.parseInts (String.ofList l)).toArray)[r]! =
      CFSG.YGroups.ModelNative.parseInts (String.ofList (T.getD r [])) := by
  by_cases hr : r < T.length
  · rw [getElem!_pos _ r (by simpa using hr), List.getElem_toArray, List.getElem_map,
      List.getD_eq_getElem _ _ hr]
  · rw [getElem!_neg _ r (by simpa using hr), List.getD_eq_default _ _ (by omega),
      parseInts_eq (l := []) (xs := []) rfl]
    rfl

theorem reachCheck_of_walk {n w kS k x : Nat} {PS PSI L R : Nat → Nat} {S : Array (Array Nat)}
    (hS : S.size = kS) (hb : ∀ j < kS, S[j]! = unpack n w (PS j))
    (hp : ∀ j < kS, permOK n w (mask w) (n * w) (PS j) (PSI j) = true)
    {labels roots : Array Nat} (hL : labels[x]! = L x) (hR : ∀ j < k, roots[j]! = R j)
    (hx : x < n) {T H : List (List Char)}
    (hw : reachWalkK w kS n k x PS PSI L R T H = true) :
    reachCheck n S x labels roots k
      ((T.map fun l => CFSG.YGroups.ModelNative.parseInts (String.ofList l)).toArray)
      ((H.map fun l => CFSG.YGroups.ModelNative.parseInts (String.ofList l)).toArray) = true := by
  obtain ⟨hlen, hall⟩ := lineWalkK_sound H 0 hw
  rw [Nat.zero_add] at hlen
  have hn : 0 < n := by omega
  unfold reachCheck
  rw [allLt_iff]
  intro j hj
  rw [Bool.or_eq_true, beq_iff_eq, hL]
  by_cases hjl : j = L x
  · exact Or.inl hjl
  right
  have key : ∀ p < n, ∃ wd gw, intsSK (tokK (H.getD (j * n + p) [])) = some wd ∧
      intsSK (tokK (T.getD (R j) [])) = some gw ∧ lettersOK kS gw = true ∧
      lettersOK (kS + 1) wd = true ∧ fixX w kS PS x wd = true ∧
      ptX w kS PS PSI gw wd x = p := by
    intro p hpn
    have hidx : j * n + p < H.length := by
      have : (j + 1) * n ≤ k * n := Nat.mul_le_mul_right _ hj
      have hl : H.length = k * n := hlen
      rw [hl]
      rw [Nat.succ_mul] at this
      omega
    obtain ⟨wd, hwd, hok⟩ := hall _ hidx
    rw [Nat.zero_add] at hok
    have hdiv : Nat.div (j * n + p) n = j := by
      change (j * n + p) / n = j
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hpn, Nat.zero_add]
    have hmod : Nat.mod (j * n + p) n = p := by
      change (j * n + p) % n = p
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hpn]
    unfold reachOK at hok
    rw [strictB_eq, hdiv, strictB_eq, hmod, bIf_eq, if_neg (by rw [beq_false_of_ne hjl]; simp)]
      at hok
    cases hg : intsSK (tokK (T.getD (R j) [])) with
    | none => rw [hg] at hok; exact absurd hok Bool.false_ne_true
    | some gw =>
      rw [hg] at hok
      change bAnd(CFSG.KS.Raw.lettersK kS gw, bAnd(CFSG.KS.Raw.lettersK (Nat.succ kS) wd,
        bAnd(fixX w kS PS x wd, Nat.beq (ptX w kS PS PSI gw wd x) p))) = true at hok
      simp only [bAnd_eq, Bool.and_eq_true, Nat.beq_eq, CFSG.KS.Co2SShape.lettersK_eq] at hok
      exact ⟨wd, gw, hwd, rfl, hok.1, hok.2.1, hok.2.2.1, hok.2.2.2⟩
  obtain ⟨-, gw, -, hgw, hgl, -⟩ := key 0 hn
  have htw : ((T.map fun l => CFSG.YGroups.ModelNative.parseInts (String.ofList l)).toArray)[
      roots[j]!]! = gw := by
    rw [hR j hj, parsed_get, parseInts_eq hgw]
  dsimp only
  rw [htw, Bool.and_eq_true, allLt_iff]
  refine ⟨isInvA_wordA hS hb hp hgl, fun p hpn => ?_⟩
  obtain ⟨wd, gw', hwd, hgw', -, hwl, hfx, hpt⟩ := key p hpn
  rw [hgw] at hgw'
  cases Option.some.inj hgw'
  rw [parsed_get, parseInts_eq hwd]
  simp only [Bool.and_eq_true, beq_iff_eq]
  have hsz : (S.push (wordA n S (rawInvs n S) gw)).size = kS + 1 := by
    rw [Array.size_push, hS]
  refine ⟨⟨by rw [hsz]; exact hwl, fixX_all hS hb hp hx wd hwl hfx⟩, ?_⟩
  rw [(ptX_pt hS hb hp hgl wd hwl x hx).1, hpt]

@[expose] def MemR (w d : Nat) (M : Nat → Nat) (x y : Nat) : Prop :=
  ∃ i < d, pg w (mask w) (M x) i = y

private theorem fld_one (B y : Nat) : fld(B, y, 1) = 1 ↔ B.testBit y = true := by
  have e : fld(B, y, 1) = B / 2 ^ y % 2 := by
    change (B >>> y) &&& 1 = B / 2 ^ y % 2
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [e, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]

theorem testBit_bitK (w r y : Nat) : ∀ d : Nat,
    (bitK w d r).testBit y = true ↔ ∃ i < d, pg w (mask w) r i = y
  | 0 => by
    have e : bitK w 0 r = 0 := rfl
    rw [e, Nat.zero_testBit]
    simp
  | d + 1 => by
    have e : bitK w (d + 1) r = (1 <<< pg w (mask w) r d) ||| bitK w d r := rfl
    rw [e, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
      decide_eq_true_eq, testBit_bitK w r y d]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨d, by omega, h⟩
      · exact ⟨i, by omega, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inr ⟨i, hi, h⟩
      · exact Or.inl h

theorem relK_sound {n w d A : Nat} {M : Nat → Nat} {σ : Equiv.Perm (Fin n)}
    (h : relK n w d A M = true) (hA : Raw.Orb.PRep n w A σ) :
    ∀ x y : Fin n, MemR w d M x y → MemR w d M (σ x) (σ y) := by
  rintro x y ⟨i, hi, hy⟩
  have h1 := allN_spec h x x.2
  rw [strictB_eq] at h1
  have h2 := allN_spec h1 i hi
  rw [strictB_eq, bAnd_eq, Bool.and_eq_true, Nat.beq_eq, hy, hA x, hA y] at h2
  exact (testBit_bitK w _ _ d).1 ((fld_one _ _).1 h2.2)

theorem moveK_sound {n w d G : Nat} {M : Nat → Nat} {x i : Nat} {σ : Equiv.Perm (Fin n)}
    (h : moveK n w d G M x i = true) (hG : Raw.Orb.PRep n w G σ) :
    ∃ a b : Fin n, MemR w d M a b ∧ ¬ MemR w d M (σ a) (σ b) := by
  unfold moveK at h
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq, strictB_eq,
    bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨hx, hi, hy, hbit⟩ := h
  refine ⟨⟨x, hx⟩, ⟨_, hy⟩, ⟨i, hi, rfl⟩, fun hm => ?_⟩
  have h1 : fld(bitK w d (M (σ ⟨x, hx⟩)), (σ ⟨_, hy⟩ : Nat), 1) = 1 :=
    (fld_one _ _).2 ((testBit_bitK w _ _ d).2 hm)
  rw [← hG ⟨x, hx⟩, ← hG ⟨_, hy⟩] at h1
  have h2 : (1 : Nat) = 0 := h1.symm.trans hbit
  exact absurd h2 (by decide)

theorem card_le_half_of_rel {α : Type*} [Finite α] {R : α → α → Prop}
    {s : Set (Equiv.Perm α)} {J : Subgroup (Equiv.Perm α)}
    (hs : ∀ σ ∈ s, ∀ x y, R x y → R (σ x) (σ y)) (hle : Subgroup.closure s ≤ J)
    {g : Equiv.Perm α} (hg : g ∈ J) {x y : α} (hxy : R x y) (hgxy : ¬ R (g x) (g y)) :
    Nat.card (Subgroup.closure s) * 2 ≤ Nat.card J := by
  let K : Subgroup (Equiv.Perm α) :=
    { carrier := {σ | ∀ x y, R x y ↔ R (σ x) (σ y)}
      one_mem' := fun _ _ => Iff.rfl
      mul_mem' := fun {a b} ha hb x y => (hb x y).trans (ha _ _)
      inv_mem' := fun {a} ha x y => by
        have := ha (a⁻¹ x) (a⁻¹ y)
        simp only [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply] at this
        exact this.symm }
  have hK : ∀ σ : Equiv.Perm α, (∀ x y, R x y → R (σ x) (σ y)) → σ ∈ K := by
    intro σ hσ x y
    refine ⟨hσ x y, fun h => ?_⟩
    let f : {p : α × α // R p.1 p.2} → {p : α × α // R p.1 p.2} :=
      fun p => ⟨(σ p.1.1, σ p.1.2), hσ _ _ p.2⟩
    have hf : Function.Injective f := by
      intro p q e
      have e1 := congrArg (fun r => r.1.1) e
      have e2 := congrArg (fun r => r.1.2) e
      simp only [f, EmbeddingLike.apply_eq_iff_eq] at e1 e2
      exact Subtype.ext (Prod.ext e1 e2)
    obtain ⟨p, hp⟩ := (Finite.injective_iff_surjective.1 hf) ⟨(σ x, σ y), h⟩
    have e1 := congrArg (fun r => r.1.1) hp
    have e2 := congrArg (fun r => r.1.2) hp
    simp only [f, EmbeddingLike.apply_eq_iff_eq] at e1 e2
    rw [← e1, ← e2]
    exact p.2
  have hsK : Subgroup.closure s ≤ K := (Subgroup.closure_le K).2 fun σ hσ => hK σ (hs σ hσ)
  have hgK : g ∉ K := fun h => hgxy ((h x y).1 hxy)
  have h1 : Nat.card (Subgroup.closure s) ≤ Nat.card (K ⊓ J : Subgroup (Equiv.Perm α)) :=
    Subgroup.card_le_of_le (le_inf hsK hle)
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le (inf_le_right : K ⊓ J ≤ J)
  have hpos : 0 < Nat.card (K ⊓ J : Subgroup (Equiv.Perm α)) := Nat.card_pos
  have hJpos : 0 < Nat.card J := Nat.card_pos
  have hm1 : m ≠ 1 := by
    rintro rfl
    have he : K ⊓ J = J := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hm, mul_one])
    have hgKJ : g ∈ K ⊓ J := by rw [he]; exact hg
    exact hgK (Subgroup.mem_inf.1 hgKJ).1
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    omega
  have h2 : 2 ≤ m := by omega
  calc Nat.card (Subgroup.closure s) * 2 ≤ Nat.card (K ⊓ J : Subgroup (Equiv.Perm α)) * m :=
        Nat.mul_le_mul h1 h2
    _ = Nat.card J := hm.symm

theorem natWalkK_sound {w P N : Nat} : ∀ (xs : List Nat) (i : Nat), natWalkK w P N xs i = true →
    i + xs.length = N ∧ ∀ m < xs.length, xs[m]! = pg w (mask w) P (i + m)
  | [], i, h => by
    have h' : Nat.beq i N = true := h
    rw [Nat.beq_eq] at h'
    exact ⟨by simpa using h', fun m hm => absurd hm (Nat.not_lt_zero _)⟩
  | x :: xs, i, h => by
    change bAnd(Nat.beq x (pg w (mask w) P i), strictB (Nat.succ i) (natWalkK w P N xs)) = true at h
    rw [bAnd_eq, Bool.and_eq_true, strictB_eq, Nat.beq_eq] at h
    obtain ⟨h1, h2⟩ := natWalkK_sound xs (Nat.succ i) h.2
    refine ⟨by simp only [List.length_cons]; omega, fun m hm => ?_⟩
    rcases m with _ | m
    · simpa using h.1
    · have e : i + (m + 1) = Nat.succ i + m := by omega
      rw [e, ← h2 m (by simpa using hm)]
      simp

theorem natsPK_sound {w P N : Nat} {cs : List Char} (h : natsPK w P N cs = true) :
    ∃ xs, natsK cs = some xs ∧ xs.length = N ∧ ∀ m < N, xs[m]! = pg w (mask w) P m := by
  unfold natsPK at h
  cases hx : natsK cs with
  | none => rw [hx] at h; exact absurd h Bool.false_ne_true
  | some xs =>
    rw [hx] at h
    obtain ⟨h1, h2⟩ := natWalkK_sound xs 0 h
    refine ⟨xs, rfl, by omega, fun m hm => ?_⟩
    rw [h2 m (by omega), Nat.zero_add]

theorem intLinesOK_mem : ∀ {L : List (List Char)}, intLinesOK L = true →
    ∀ l ∈ L, ∃ xs, intsSK (tokK l) = some xs
  | [], _, _, hl => absurd hl List.not_mem_nil
  | l :: L, h, l', hl => by
    change bAnd(Option.rec (motive := fun _ => Bool) false (fun _ => true) (intsSK (tokK l)),
      intLinesOK L) = true at h
    rw [bAnd_eq, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hl with rfl | hl
    · cases e : intsSK (tokK l') with
      | none => rw [e] at h; exact absurd h.1 Bool.false_ne_true
      | some xs => exact ⟨xs, rfl⟩
    · exact intLinesOK_mem h.2 l' hl

theorem textWords_eq {cs : List Char} (h : intLinesOK (bodyK cs) = true) :
    textWords (String.ofList cs) = (wordsK cs).toArray := by
  unfold textWords wordsK
  rw [lines_ofList, ← List.map_dropLast, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l hl
  obtain ⟨xs, hxs⟩ := intLinesOK_mem h l hl
  rw [Function.comp_apply, parseInts_eq hxs]
  unfold lineInts
  rw [hxs]

theorem textWords_body (cs : List Char) :
    textWords (String.ofList cs) =
      ((bodyK cs).map fun l => CFSG.YGroups.ModelNative.parseInts (String.ofList l)).toArray := by
  unfold textWords bodyK
  rw [lines_ofList, ← List.map_dropLast, List.map_map]
  rfl

private theorem natsRec_fold : ∀ (ts : List (List Char)) (xs : List Nat) (acc : Array Nat),
    List.rec (motive := fun _ => Option (List Nat)) (some [])
      (fun t _ ih => Option.rec (motive := fun _ => Option (List Nat)) none
        (fun x => Option.rec (motive := fun _ => Option (List Nat)) none
          (fun xs => some (List.cons x xs)) ih) (natK t)) ts = some xs →
    (ts.map String.ofList).foldl (fun a t => if t.isEmpty then a else a.push t.toNat!) acc =
      acc ++ xs.toArray
  | [], xs, acc, h => by
    cases Option.some.inj h
    simp
  | t :: ts, xs, acc, h => by
    obtain ⟨x, hx, h⟩ := CFSG.KC.LQT.Cov.Parse.orec_some h
    obtain ⟨ys, hys, h⟩ := CFSG.KC.LQT.Cov.Parse.orec_some h
    cases Option.some.inj h
    have hne : (String.ofList t).isEmpty = false := by
      have h0 := (CFSG.KC.LQT.Cov.Parse.natK_spec hx).1
      cases e : (String.ofList t).isEmpty
      · rfl
      · exact absurd (by simpa using e) h0
    rw [List.map_cons, List.foldl_cons, hne, if_neg Bool.false_ne_true,
      CFSG.KC.LQT.Cov.Parse.toNat!_natK hx, natsRec_fold ts ys _ hys]
    simp

theorem parseNats_natsK {l : List Char} {xs : List Nat} (h : natsK l = some xs) :
    CFSG.YGroups.ModelNative.parseNats (String.ofList l) = xs.toArray := by
  unfold CFSG.YGroups.ModelNative.parseNats
  rw [CFSG.KC.LQT.Cov.Parse.sp_eq, CFSG.KC.Str.splitOn_ofList]
  cases l with
  | nil =>
    cases Option.some.inj h
    simp
  | cons c l =>
    rw [← CFSG.KC.LQT.Cov.Parse.tokK_eq]
    have e := natsRec_fold (tokK (c :: l)) xs #[] h
    rw [e]
    simp

theorem parseNats_get {w P N : Nat} {cs : List Char} (h : natsPK w P N cs = true) :
    ∀ m < N, (CFSG.YGroups.ModelNative.parseNats (String.ofList cs))[m]! = pg w (mask w) P m := by
  obtain ⟨xs, hx, -, hm⟩ := natsPK_sound h
  intro m hmN
  rw [parseNats_natsK hx, List.getElem!_toArray]
  exact hm m hmN

theorem blockArr_of_K {n w m wT G T TI : Nat} {L R : Nat → Nat} {lab rep : Array Nat}
    (hL : ∀ x < n, lab[x]! = L x) (hR : ∀ j < m, rep[j]! = R j)
    (h : blockK n w m wT G T TI L R = true) : blockArr lab rep m (unpack n w G) = unpack m wT T := by
  unfold blockK at h
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  exact blockArr_eq hL hR (allN_spec h.1) (allN_spec h.2.1)

theorem arr_unpack {n w P : Nat} {a : Array Nat} (hs : a.size = n)
    (h : ∀ x < n, a[x]! = pg w (mask w) P x) : a = unpack n w P := by
  apply Array.ext
  · simp [unpack, hs]
  · intro i h1 h2
    have hi : i < n := by omega
    rw [← getElem!_pos a i h1, h i hi, ← Raw.Orb.unpack_get hi, getElem!_pos _ i h2]

theorem wordA_size (n : Nat) (S Sinv : Array (Array Nat)) (wd : List Int) :
    (wordA n S Sinv wd).size = n := by
  cases wd <;> simp [wordA, idA, compA]

theorem wordA_unpack {n w kS : Nat} {PS PSI : Nat → Nat} {S : Array (Array Nat)}
    (hS : S.size = kS) (hb : ∀ j < kS, S[j]! = unpack n w (PS j))
    (hp : ∀ j < kS, permOK n w (mask w) (n * w) (PS j) (PSI j) = true) {wd : List Int}
    (hl : lettersOK kS wd = true) {P : Nat} (hP : ∀ y < n, pg w (mask w) P y = ptK w PS PSI wd y) :
    wordA n S (rawInvs n S) wd = unpack n w P := by
  apply arr_unpack (wordA_size _ _ _ _)
  intro x hx
  rw [hP x hx]
  exact (wordA_pt hS hb hp wd hl x hx).1

theorem isInvA_of_perm {n w P Q : Nat} (h : permOK n w (mask w) (n * w) P Q = true) :
    isInvA n (unpack n w P) (invCand n (unpack n w P)) = true := by
  rw [CFSG.KC.LQT.Cov.T.invCand_unpack h]
  exact Raw.Orb.isInvA_unpack h

theorem canon_of_perm {n w P Q : Nat} (hs : CFSG.KS.Raw.szOK n w = true)
    (h : permOK n w (mask w) (n * w) P Q = true) : CFSG.KS.Prim.canonK n w (mask w) (n * w) P = true := by
  obtain ⟨h1, -, h3⟩ := Raw.Orb.permOK_facts h
  have h4 : allN n (fun i => Nat.blt (pg w (mask w) P i) n) = true :=
    Raw.Orb.allN_iff.2 fun i hi => by rw [Nat.blt_eq]; exact (h3 i hi).1
  unfold CFSG.KS.Prim.canonK
  rw [hs, h1, h4]
  rfl

section Powers

variable {n w : Nat} (hid : CFSG.KS.Prim.canonK n w (mask w) (n * w) (pidn n w) = true)
  (hidA : idA n = unpack n w (pidn n w))
include hid hidA

theorem powA_unpack {p : Nat} (hp : CFSG.KS.Prim.canonK n w (mask w) (n * w) p = true) :
    ∀ e, CFSG.Quasithin.powA n (unpack n w p) e = unpack n w (CFSG.KC.PermTool.powK n w p e)
  | 0 => by
    rw [CFSG.Quasithin.powA, hidA]
    rfl
  | e + 1 => by
    rw [CFSG.Quasithin.powA, powA_unpack hp e,
      CFSG.KC.BfsPin.compA_unpack hp (CFSG.KC.PermTool.canonK_powK hid hp e)]
    rfl

theorem ord_of_K {P e : Nat} (hP : CFSG.KS.Prim.canonK n w (mask w) (n * w) P = true)
    (h : (Nat.beq (CFSG.KC.PermTool.powK n w P e) (pidn n w) && !Nat.beq P (pidn n w)) = true) :
    eqA n (CFSG.Quasithin.powA n (unpack n w P) e) (idA n) = true ∧
      eqA n (unpack n w P) (idA n) = false := by
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  rw [powA_unpack hid hidA hP, hidA,
    CFSG.KC.BfsPin.eqA_unpack (CFSG.KC.PermTool.canonK_powK hid hP e) hid,
    CFSG.KC.BfsPin.eqA_unpack hP hid]
  exact h

end Powers

theorem perms_of_head {n w kS kO nb BP : Nat} {PS PSI : Nat → Nat} {D : List (List Int)}
    (hh : CFSG.KS.Raw.headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true) :
    allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true := by
  unfold CFSG.KS.Raw.headK at hh
  simp only [bAnd_eq, Bool.and_eq_true] at hh
  exact hh.2.2.2.2.1

end CFSG.KC.SuzOut

end
