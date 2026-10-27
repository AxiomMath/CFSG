module

public import CFSG.Certificates.Kernel.LocalQTCovHBase
import CFSG.Certificates.Kernel.LocalQTCovParse
import CFSG.Certificates.Kernel.Common.StrSplit

public section

namespace CFSG.KC.LQT.Cov.H

open CFSG.KC.LQT.Cov CFSG.KC.LQT.Cov.Parse CFSG.KC.Ord CFSG.KC.LQT.Syl
open CFSG.QuasithinUnique.Ch1.HSCover

private theorem parseH_natsK {l : List Char} {xs : List Nat} (h : natsK l = some xs) :
    parseNats (String.ofList l) = xs :=
  natsK_sound h

private theorem parseH_wordK {l : List Char} {w : List Nat} (h : wordK l = some w) :
    parseWord (String.ofList l) = w ∧ ∀ x ∈ w, x < 3 :=
  wordK_sound h

private theorem parseH_getElem! (l : List Nat) (i : Nat) : l[i]! = getK l i 0 := by
  rw [getK_getD, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rfl

private noncomputable def parseH_stepP (Ls : List (List Char)) (b : Array Rec × Nat) (_ : Nat) :
    Array Rec × Nat :=
  (b.1.push
      { gw := parseNats (String.ofList (getK Ls b.2 [])),
        a := (parseNats (String.ofList (getK Ls (b.2 + 1) [])))[0]!,
        b := (parseNats (String.ofList (getK Ls (b.2 + 1) [])))[1]! },
    b.2 + 2)

private noncomputable def parseH_stepA (Ls : List (List Char)) (b : Nat × Array Rec) (_ : Nat) :
    Nat × Array Rec :=
  (b.1 + 2,
    b.2.push
      { gw := parseNats (String.ofList (getK Ls b.1 [])), a := 0,
        b := (String.ofList (getK Ls (b.1 + 1) [])).toNat! })

private theorem parseH_pairs_loop (Ls : List (List Char)) : ∀ (np s : Nat) (acc : Array Rec)
    (p : Nat) (ps : List (List Nat × Nat × Nat)) (q : Nat),
    pairsH Ls np p = some (ps, q) →
    List.foldl (parseH_stepP Ls) (acc, p) (List.range' s np) =
      ((acc.toList ++ ps.map fun r => ({ gw := r.1, a := r.2.1, b := r.2.2 } : Rec)).toArray, q)
  | 0, _, acc, p, ps, q, h => by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    simp
  | np + 1, s, acc, p, ps, q, h => by
    obtain ⟨gw, hgw, h⟩ := orec_some h
    obtain ⟨ab, hab, h⟩ := orec_some h
    obtain ⟨rest, hrest, h⟩ := orec_some h
    have e := brec_some h
    simp only [Nat.add_eq] at hab hrest
    have hst : parseH_stepP Ls (acc, p) s =
        (acc.push { gw := gw, a := getK ab 0 0, b := getK ab 1 0 }, p + 2) := by
      simp only [parseH_stepP, parseH_natsK hgw, parseH_natsK hab, parseH_getElem!]
    rw [List.range'_succ, List.foldl_cons, hst,
      parseH_pairs_loop Ls np (s + 1) _ (p + 2) rest.1 rest.2 hrest]
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    simp

private theorem parseH_anchors_loop (Ls : List (List Char)) : ∀ (na s p : Nat) (acc : Array Rec)
    (ans : List (List Nat × Nat)),
    anchorsH Ls na p = some ans →
    (List.foldl (parseH_stepA Ls) (p, acc) (List.range' s na)).2.toList =
      acc.toList ++ ans.map fun r => ({ gw := r.1, a := 0, b := r.2 } : Rec)
  | 0, _, _, _, _, h => by
    rw [← Option.some.inj h]
    simp
  | na + 1, s, p, acc, ans, h => by
    obtain ⟨gw, hgw, h⟩ := orec_some h
    obtain ⟨b, hb, h⟩ := orec_some h
    obtain ⟨rest, hrest, h⟩ := orec_some h
    simp only [Nat.add_eq] at hb hrest
    have hst : parseH_stepA Ls (p, acc) s = (p + 2, acc.push { gw := gw, a := 0, b := b }) := by
      simp only [parseH_stepA, parseH_natsK hgw, toNat!_natK hb]
    rw [← Option.some.inj h, List.range'_succ, List.foldl_cons, hst,
      parseH_anchors_loop Ls na (s + 1) (p + 2) _ rest hrest]
    simp

theorem parseH_sound {cs : List Char} {D : CH} (h : parseH cs = some D) :
    D.xw.length = 3 ∧ D.words.length = D.nV ∧ (∀ w ∈ D.words, ∀ l ∈ w, l < 3) ∧
    parseData (String.ofList cs) = ofCH D := by
  unfold parseH at h
  obtain ⟨xw, hxw, h⟩ := orec_some h
  obtain ⟨nV, hnV, h⟩ := orec_some h
  obtain ⟨words, hwords, h⟩ := orec_some h
  obtain ⟨tgt, htgt, h⟩ := orec_some h
  obtain ⟨back, hback, h⟩ := orec_some h
  obtain ⟨np, hnp, h⟩ := orec_some h
  obtain ⟨⟨ps, q⟩, hpr, h⟩ := orec_some h
  obtain ⟨na, hna, h⟩ := orec_some h
  obtain ⟨ans, hans, h⟩ := orec_some h
  obtain rfl := Option.some.inj h
  simp only [Nat.add_eq, Nat.succ_eq_add_one] at htgt hback hnp hpr hna hans
  have hX := (manyK_spec (linesK cs) natsK (fun l => parseNats (String.ofList l))
    (fun _ _ h => parseH_natsK h) 3 0 xw hxw).1
  have hW := manyK_spec (linesK cs) wordK (fun l => parseWord (String.ofList l))
    (fun _ _ h => (parseH_wordK h).1) nV 4 words hwords
  have hP := parseH_pairs_loop (linesK cs) np 0 #[] (7 + nV) ps q hpr
  have hA := parseH_anchors_loop (linesK cs) na 0 (q + 1) #[] ans hans
  have hL : (String.ofList cs).splitOn "\n" = (linesK cs).map String.ofList := by
    rw [nl_eq, CFSG.KC.Str.splitOn_ofList, linesK_eq]
  refine ⟨by rw [← hX]; simp, by rw [← hW.1]; simp, fun w hw x hx => ?_, ?_⟩
  · obtain ⟨l, hl⟩ := hW.2 w hw
    exact (parseH_wordK hl).2 x hx
  have hx0 : parseNats (String.ofList (getK (linesK cs) 0 [])) = xw.getD 0 [] := by
    rw [← hX]
    rfl
  have hx1 : parseNats (String.ofList (getK (linesK cs) 1 [])) = xw.getD 1 [] := by
    rw [← hX]
    rfl
  have hx2 : parseNats (String.ofList (getK (linesK cs) 2 [])) = xw.getD 2 [] := by
    rw [← hX]
    rfl
  have hw : Array.map (fun v => parseWord (String.ofList (getK (linesK cs) (4 + v) [])))
      (Array.range nV) = words.toArray := by
    rw [← hW.1, range'_shift 4, List.map_map]
    apply Array.toList_inj.1
    rw [Array.toList_map, Array.toList_range, List.range_eq_range']
    rfl
  simp only [parseData, Std.Legacy.Range.forIn_eq_forIn_range',
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, pure_bind, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, Id.run_pure, hL, getElem!_lines, toNat!_natK hnV,
    toNat!_natK hnp, parseH_natsK htgt, parseH_natsK hback, hx0, hx1, hx2, hw, ofCH]
  erw [hP]
  simp only [toNat!_natK hna]
  erw [hA]
  simp

end CFSG.KC.LQT.Cov.H

end
