module

public import Certificates.Data.Kernel.Misc.TitsPrim
public import CFSG.Quasithin.Recognition.CertPermSimple
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import Certificates.Data.CFSGNative.YGroups.ExactCheck
import CFSG.Certificates.Kernel.Spor.Co2ChainSound
import CFSG.Certificates.Kernel.LocalQTCovTPrim
import CFSG.Certificates.Kernel.LocalQTCovTParse
import CFSG.Certificates.Kernel.Common.StrSplit
import CFSG.Certificates.Kernel.YModel.TextSound
import all Init.Data.String.Slice
import all Init.Data.String.Search

public section

namespace CFSG.KC.TitsPrim

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.IntLines CFSG.KC.LQT.Cov
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Quasithin

private theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

private theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

private theorem bAnd_eq (a b : Bool) : bAnd(a, b) = (a && b) := by cases a <;> rfl

section Words

variable {n w kS : Nat} {PS PSI : Nat → Nat} {S : Array (Array Nat)}

theorem letter_pt (hS : S.size = kS) (hb : ∀ j < kS, S[j]! = unpack n w (PS j))
    (hp : ∀ j < kS, permOK n w (mask w) (n * w) (PS j) (PSI j) = true)
    {z : Int} (hz0 : z ≠ 0) (hzk : z.natAbs ≤ kS) {y : Nat} (hy : y < n) :
    (letterA S (rawInvs n S) z)[y]! = pg w (mask w) (letP PS PSI z) y ∧
      pg w (mask w) (letP PS PSI z) y < n := by
  cases z with
  | ofNat k =>
    have hk0 : k ≠ 0 := fun h => hz0 (by rw [h]; rfl)
    have hkk : k ≤ kS := hzk
    have hpos : (0 : Int) < Int.ofNat k := by
      have : (0 : Int) < (k : Int) := by omega
      exact this
    have e1 : letterA S (rawInvs n S) (Int.ofNat k) = S[k - 1]! := by
      simp only [letterA, hpos, if_true]
      rfl
    have e2 : letP PS PSI (Int.ofNat k) = PS (k - 1) := rfl
    rw [e1, e2, hb _ (by omega), CFSG.KS.Raw.Orb.unpack_get hy]
    exact ⟨rfl, ((CFSG.KC.LQT.Cov.T.perm_facts (hp _ (by omega))).1 y hy).1⟩
  | negSucc k =>
    have hkk : k < kS := by
      have : (Int.negSucc k).natAbs = k + 1 := rfl
      omega
    have hneg : ¬ (0 : Int) < Int.negSucc k := by
      have := Int.negSucc_lt_zero k
      omega
    have e1 : letterA S (rawInvs n S) (Int.negSucc k) = (rawInvs n S)[k]! := by
      simp only [letterA, hneg, if_false]
      congr 1
    have e2 : letP PS PSI (Int.negSucc k) = PSI k := rfl
    have hP := hp k hkk
    rw [e1, e2, rawInvs_getElem! (by omega), hb k hkk, CFSG.KC.LQT.Cov.T.invCand_unpack hP,
      CFSG.KS.Raw.Orb.unpack_get hy]
    refine ⟨rfl, ?_⟩
    obtain ⟨hpr, hs⟩ := CFSG.KC.LQT.Cov.T.perm_facts hP
    obtain ⟨i, hi, e⟩ := hs y hy
    rw [← e, (hpr i hi).2]
    exact hi

theorem wordA_pt (hS : S.size = kS) (hb : ∀ j < kS, S[j]! = unpack n w (PS j))
    (hp : ∀ j < kS, permOK n w (mask w) (n * w) (PS j) (PSI j) = true) :
    ∀ wd : List Int, lettersOK kS wd = true → ∀ x < n,
      (wordA n S (rawInvs n S) wd)[x]! = ptK w PS PSI wd x ∧ ptK w PS PSI wd x < n
  | [], _, x, hx => by
    rw [wordA, idA_get hx]
    exact ⟨rfl, hx⟩
  | z :: wd, hl, x, hx => by
    simp only [CFSG.Monster.B.Co2.Native.lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hl
    obtain ⟨⟨hz0, hzk⟩, hl⟩ := hl
    obtain ⟨e, hlt⟩ := wordA_pt hS hb hp wd hl x hx
    have ep : ptK w PS PSI (z :: wd) x = pg w (mask w) (letP PS PSI z) (ptK w PS PSI wd x) :=
      strictN_eq _ _
    rw [wordA, compA_get hx, e, ep]
    exact letter_pt hS hb hp hz0 hzk hlt

theorem fixK_sound (hS : S.size = kS) (hb : ∀ j < kS, S[j]! = unpack n w (PS j))
    {x : Nat} (hx : x < n) :
    ∀ wd : List Int, lettersOK kS wd = true → fixK w PS x wd = true → fixLetters S x wd = true
  | [], _, _ => rfl
  | z :: wd, hl, hf => by
    simp only [CFSG.Monster.B.Co2.Native.lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hl
    obtain ⟨⟨hz0, hzk⟩, hl⟩ := hl
    have hf' : (Nat.beq (pg w (mask w) (PS (z.natAbs - 1)) x) x && fixK w PS x wd) = true := by
      rw [← bAnd_eq]
      exact hf
    rw [Bool.and_eq_true, Nat.beq_eq] at hf'
    have ih := fixK_sound hS hb hx wd hl hf'.2
    have hz1 : z.natAbs - 1 < kS := by omega
    simp only [fixLetters, List.all_cons, Bool.and_eq_true, beq_iff_eq]
    refine ⟨?_, ih⟩
    rw [hb _ hz1, CFSG.KS.Raw.Orb.unpack_get hx]
    exact hf'.1

end Words

theorem intsSK_parse : ∀ (ts : List (List Char)) (xs : List Int), intsSK ts = some xs →
    ts.filterMap (fun t => if (String.ofList t).isEmpty then none else
      some (String.ofList t).toInt!) = xs
  | [], xs, h => Option.some.inj h
  | [] :: ts, xs, h => by
    rw [List.filterMap_cons]
    exact intsSK_parse ts xs h
  | (c :: cs) :: ts, xs, h => by
    change Option.rec (motive := fun _ => Option (List Int)) none
      (fun x => Option.rec (motive := fun _ => Option (List Int)) none
        (fun xs => some (List.cons x xs)) (intsSK ts)) (intK (c :: cs)) = some xs at h
    cases hk : intK (c :: cs) with
    | none => rw [hk] at h; exact absurd h (by simp)
    | some x =>
      rw [hk] at h
      cases hr : intsSK ts with
      | none => rw [hr] at h; exact absurd h (by simp)
      | some ys =>
        rw [hr] at h
        have hx := CFSG.KC.LQT.Cov.T.intK_sound hk
        have he : (String.ofList (c :: cs)).isEmpty = false := by
          rw [CFSG.KC.YModel.TextSem.isEmpty_ofList]
          rfl
        rw [List.filterMap_cons, he, intsSK_parse ts ys hr, ← Option.some.inj h]
        have ht : (String.ofList (c :: cs)).toInt! = x := by
          unfold String.toInt? at hx
          unfold String.toInt! String.Slice.toInt!
          rw [hx]
        simp only [Bool.false_eq_true, if_false, ht]

theorem parseInts_eq {l : List Char} {xs : List Int} (h : intsSK (tokK l) = some xs) :
    CFSG.YGroups.ModelNative.parseInts (String.ofList l) = xs := by
  unfold CFSG.YGroups.ModelNative.parseInts
  rw [CFSG.KC.LQT.Cov.Parse.sp_eq, CFSG.KC.Str.splitOn_ofList, List.filterMap_map,
    ← CFSG.KC.LQT.Cov.Parse.tokK_eq]
  exact intsSK_parse _ xs h

theorem lines_ofList (cs : List Char) :
    ((String.ofList cs).splitOn "\n").drop 1 = ((linesK cs).drop 1).map String.ofList := by
  rw [CFSG.KC.LQT.Cov.Parse.nl_eq, CFSG.KC.Str.splitOn_ofList,
    ← CFSG.KC.LQT.Cov.Parse.linesK_eq, List.map_drop]

theorem walkK_nil_nil {n : Nat} {ok : Nat → List Int → List Int → Bool} {p : Nat} :
    walkK n ok [] [] p = Nat.beq p n := rfl

theorem walkK_cons_cons {n : Nat} {ok : Nat → List Int → List Int → Bool} {t h : List Char}
    {T H : List (List Char)} {p : Nat} :
    walkK n ok (t :: T) (h :: H) p = Option.rec (motive := fun _ => Bool) false
      (fun a => Option.rec (motive := fun _ => Bool) false
        (fun b => bAnd(ok p a b, walkK n ok T H (Nat.succ p))) (intsSK (tokK h)))
      (intsSK (tokK t)) := rfl

theorem walkK_sound {n : Nat} {ok : Nat → List Int → List Int → Bool} :
    ∀ (T H : List (List Char)) (p : Nat), walkK n ok T H p = true →
      H.length = T.length ∧ p + T.length = n ∧ ∀ i < T.length, ∃ a b,
        intsSK (tokK (T.getD i [])) = some a ∧ intsSK (tokK (H.getD i [])) = some b ∧
          ok (p + i) a b = true
  | [], [], p, h => by
    rw [walkK_nil_nil, Nat.beq_eq] at h
    exact ⟨rfl, by simpa using h, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | [], _ :: _, _, h => absurd h Bool.false_ne_true
  | _ :: _, [], _, h => absurd h Bool.false_ne_true
  | t :: T, hl :: H, p, h => by
    rw [walkK_cons_cons] at h
    cases ha : intsSK (tokK t) with
    | none => rw [ha] at h; exact absurd h Bool.false_ne_true
    | some a =>
      rw [ha] at h
      cases hb : intsSK (tokK hl) with
      | none => rw [hb] at h; exact absurd h Bool.false_ne_true
      | some b =>
        rw [hb] at h
        change bAnd(ok p a b, walkK n ok T H (Nat.succ p)) = true at h
        rw [bAnd_eq, Bool.and_eq_true] at h
        obtain ⟨h1, h2, h3⟩ := walkK_sound T H (Nat.succ p) h.2
        refine ⟨by simp [h1], by simp only [List.length_cons]; omega, fun i hi => ?_⟩
        rcases i with _ | i
        · exact ⟨a, b, ha, hb, by simpa using h.1⟩
        · obtain ⟨a', b', e1, e2, e3⟩ := h3 i (by simpa using hi)
          refine ⟨a', b', by simpa using e1, by simpa using e2, ?_⟩
          have e : p + (i + 1) = Nat.succ p + i := by omega
          rw [e]
          exact e3

theorem primCheck_of_walk {n w kS k x : Nat} {PS PSI L R : Nat → Nat} {S : Array (Array Nat)}
    (hS : S.size = kS) (hb : ∀ j < kS, S[j]! = unpack n w (PS j))
    (hp : ∀ j < kS, permOK n w (mask w) (n * w) (PS j) (PSI j) = true)
    {labels roots : Array Nat} (hL : ∀ p < n, labels[p]! = L p) (hR : ∀ i < k, roots[i]! = R i)
    (hx : x < n) {T H : List (List Char)}
    (hw : walkK n (primOK w kS n k x PS PSI L R) T H 0 = true) :
    primCheck n S x labels roots k
      ((T.map fun l => CFSG.YGroups.ModelNative.parseInts (String.ofList l)).toArray)
      ((H.map fun l => CFSG.YGroups.ModelNative.parseInts (String.ofList l)).toArray) = true := by
  obtain ⟨hHT, hTn, hall⟩ := walkK_sound T H 0 hw
  rw [Nat.zero_add] at hTn
  unfold primCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.size_toArray, List.length_map]
  refine ⟨⟨⟨hx, hTn⟩, hHT.trans hTn⟩, allLt_iff.2 fun p hpn => ?_⟩
  have hpT : p < T.length := by rw [hTn]; exact hpn
  have hpH : p < H.length := by rw [hHT]; exact hpT
  obtain ⟨a, b, ea, eb, hok⟩ := hall p hpT
  rw [Nat.zero_add] at hok
  have gT : ((T.map fun l => CFSG.YGroups.ModelNative.parseInts (String.ofList l)).toArray)[p]! =
      a := by
    rw [getElem!_pos _ p (by simpa using hpT), List.getElem_toArray, List.getElem_map,
      ← parseInts_eq ea, List.getD_eq_getElem _ _ hpT]
  have gH : ((H.map fun l => CFSG.YGroups.ModelNative.parseInts (String.ofList l)).toArray)[p]! =
      b := by
    rw [getElem!_pos _ p (by simpa using hpH), List.getElem_toArray, List.getElem_map,
      ← parseInts_eq eb, List.getD_eq_getElem _ _ hpH]
  rw [gT, gH, hS]
  unfold primOK at hok
  simp only [bAnd_eq, strictB_eq, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at hok
  obtain ⟨hla, hpa, hlb, hfb, hlk, hrn, hpb⟩ := hok
  rw [CFSG.KS.Co2SShape.lettersK_eq] at hla hlb
  have hlab := hL p hpn
  have hroot := hR _ hlk
  obtain ⟨e1, -⟩ := wordA_pt hS hb hp a hla x hx
  obtain ⟨e2, -⟩ := wordA_pt hS hb hp b hlb (R (L p)) hrn
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, hlab, hroot]
  exact ⟨⟨⟨⟨⟨⟨hla, by rw [e1, hpa]⟩, hlb⟩, fixK_sound hS hb hx b hlb hfb⟩, hlk⟩, hrn⟩,
    by rw [e2, hpb]⟩

end CFSG.KC.TitsPrim

end
