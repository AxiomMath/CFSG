module

public import Certificates.Data.Kernel.TabMat
public import CFSG.Certificates.Kernel.VecKRegs
public import CFSG.Sporadic.Recognition.CoverRecipe

public section

namespace CFSG.KC.TabMat

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.VecK CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Bridge.TwoGen.Native CFSG.Sporadic.Recognition.CoverRecipe CFSG.CosetTable

private theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem andB_eq (a b : Bool) : andB a b = (a && b) := by
  cases a <;> rfl

theorem real_letter {d n : Nat} {p : Nat → Nat} {α αi β βi : Table} {NA NAi NB NBi : Nat}
    (ha : Realizes d n p α NA) (hai : Realizes d n p αi NAi) (hb : Realizes d n p β NB)
    (hbi : Realizes d n p βi NBi) (l : Nat × Bool) :
    Realizes d n p (letterTab α αi β βi l) (letM NA NAi NB NBi l) := by
  obtain ⟨g, b⟩ := l
  unfold letterTab letM
  by_cases hg : g = 0
  · subst hg
    cases b
    · exact hai
    · exact ha
  · have e : Nat.beq g 0 = false := Bool.eq_false_iff.2 fun h => hg (Nat.eq_of_beq_eq_true h)
    simp only [hg, if_false, e]
    cases b
    · exact hbi
    · exact hb

theorem real_wordTab {d n : Nat} {p : Nat → Nat} (hP : VPts d n p) {α αi β βi : Table}
    {NA NAi NB NBi : Nat} (ha : Realizes d n p α NA) (hai : Realizes d n p αi NAi)
    (hb : Realizes d n p β NB) (hbi : Realizes d n p βi NBi) :
    ∀ v : List (Nat × Bool), Realizes d n p (wordTab n α αi β βi v) (matW d NA NAi NB NBi v)
  | [] => real_id hP
  | l :: v => by
    change Realizes d n p (compT n (letterTab α αi β βi l) (wordTab n α αi β βi v))
      (mulF d (matW d NA NAi NB NBi v) (letM NA NAi NB NBi l))
    exact real_comp (real_letter ha hai hb hbi l) (real_wordTab hP ha hai hb hbi v)

theorem vmF_matW_append (d NA NAi NB NBi : Nat) (v : List (Nat × Bool)) (x : Nat) :
    ∀ u : List (Nat × Bool), vmF d (matW d NA NAi NB NBi (u ++ v)) x =
      vmF d (matW d NA NAi NB NBi u) (vmF d (matW d NA NAi NB NBi v) x)
  | [] => (vmF_idF (CFSG.KC.F2W.vmF_lt _ _ _)).symm
  | l :: u => by
    change vmF d (mulF d (matW d NA NAi NB NBi (u ++ v)) (letM NA NAi NB NBi l)) x =
      vmF d (mulF d (matW d NA NAi NB NBi u) (letM NA NAi NB NBi l)) _
    rw [vmF_mulF, vmF_mulF, vmF_matW_append d NA NAi NB NBi v x u]

theorem invNAcc_eq : ∀ (w acc : List (Nat × Bool)),
    invNAcc w acc = (w.map fun l => (l.1, !l.2)).reverse ++ acc
  | [], _ => rfl
  | (g, b) :: w, acc => by
    change invNAcc w ((g, Bool.rec (motive := fun _ => Bool) true false b) :: acc) = _
    rw [invNAcc_eq w]
    cases b <;> simp

theorem natWord_append {m : Nat} (a b : List (Fin m × Bool)) :
    natWord (a ++ b) = natWord a ++ natWord b :=
  List.map_append

theorem natWord_invRev {m : Nat} (s : List (Fin m × Bool)) :
    natWord (FreeGroup.invRev s) = invN (natWord s) := by
  unfold invN natWord FreeGroup.invRev
  rw [invNAcc_eq]
  simp [List.map_reverse]

theorem gensK_eq (d NA NAi NB NBi : Nat) : ∀ (segs : List (List (Nat × Bool))) (k : List Nat → Bool),
    gensK d NA NAi NB NBi segs k =
      k (segs.flatMap fun s => [matW d NA NAi NB NBi s, matW d NA NAi NB NBi (invN s)])
  | [], _ => rfl
  | s :: segs, k => by
    change strictB (matW d NA NAi NB NBi s) (fun g => strictB (matW d NA NAi NB NBi (invN s))
      fun gi => gensK d NA NAi NB NBi segs fun L => k (g :: gi :: L)) = _
    rw [strictB_eq, strictB_eq, gensK_eq d NA NAi NB NBi segs]
    rfl

theorem getL_pairs (f g : List (Nat × Bool) → Nat) :
    ∀ (L : List (List (Nat × Bool))) (i : Nat) (hi : i < L.length),
      getL 0 (L.flatMap fun s => [f s, g s]) (2 * i) = f L[i] ∧
        getL 0 (L.flatMap fun s => [f s, g s]) (2 * i + 1) = g L[i]
  | [], _, hi => absurd hi (Nat.not_lt_zero _)
  | s :: L, 0, _ => ⟨rfl, rfl⟩
  | s :: L, i + 1, hi => by
    have e : 2 * (i + 1) = 2 * i + 1 + 1 := by omega
    rw [e]
    exact getL_pairs f g L i (by simpa using hi)

theorem vmF_subst {d NA NAi NB NBi m k : Nat} (gws : List (List (Fin m × Bool)))
    (hk : k ≤ gws.length) (x : Nat) : ∀ w : List (Fin k × Bool),
    vmF d (matW d NA NAi NB NBi (natWord (substWord gws w))) x =
      vmF d (matG d ((gws.map natWord).flatMap fun s =>
        [matW d NA NAi NB NBi s, matW d NA NAi NB NBi (invN s)]) (natWord w)) x
  | [] => rfl
  | (i, b) :: w => by
    have hi : i.val < (gws.map natWord).length := by simp; omega
    obtain ⟨e1, e2⟩ := getL_pairs (matW d NA NAi NB NBi) (fun s => matW d NA NAi NB NBi (invN s))
      (gws.map natWord) i.val hi
    have hsub : substWord gws ((i, b) :: w) =
        (if b then gws.getD i [] else FreeGroup.invRev (gws.getD i [])) ++ substWord gws w := by
      simp [substWord, List.flatMap_cons]
    have hgd : gws.getD i.val [] = gws[i.val]'(by simpa using hi) := by
      rw [List.getD_eq_getElem]
    rw [hsub, natWord_append]
    change vmF d (matW d NA NAi NB NBi (natWord _ ++ natWord (substWord gws w))) x =
      vmF d (mulF d (matG d _ (natWord w)) (gM _ (i.val, b))) x
    rw [vmF_matW_append, vmF_subst gws hk x w, vmF_mulF]
    refine congrArg (fun M => vmF d M _) ?_
    unfold gM
    cases b
    · change _ = getL 0 _ (2 * i.val + 1)
      rw [e2, List.getElem_map, ← hgd]
      simp only [Bool.false_eq_true, if_false]
      rw [natWord_invRev]
    · change _ = getL 0 _ (2 * i.val)
      rw [e1, List.getElem_map, ← hgd]
      rfl

theorem pairsK_spec {d NA NAi NB NBi : Nat} {G : List Nat} :
    ∀ ps : List (List (Nat × Bool) × List (Nat × Bool)), pairsK d NA NAi NB NBi G ps = true →
      ∀ q ∈ ps, mulF d (matW d NA NAi NB NBi q.2) (matG d G q.1) = idF d
  | [], _, _, hq => absurd hq List.not_mem_nil
  | (w, t) :: ps, h, q, hq => by
    change andB (Nat.beq (mulF d (matW d NA NAi NB NBi t) (matG d G w)) (idF d))
      (pairsK d NA NAi NB NBi G ps) = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hq with e | e
    · subst e
      exact Nat.eq_of_beq_eq_true h.1
    · exact pairsK_spec ps h.2 q e

private theorem tab_eq_idT {n : Nat} (hn : n < 2 ^ 32) {T : Table} (hs : T.size = n)
    (hT : ∀ h < n, ap T h = h) : T = idT n := by
  obtain ⟨is, iv⟩ := CFSG.KS.TW.idT_TR hn
  apply Array.ext (by rw [hs, is])
  intro i h1 h2
  have hi : i < n := by omega
  have a1 := hT i hi
  have a2 := (iv i hi).1
  unfold ap at a1 a2
  rw [getElem!_pos T i h1] at a1
  rw [getElem!_pos (idT n) i h2] at a2
  exact UInt32.toNat_inj.1 (by rw [a1, a2])

theorem relCheck_of_tabMatK {d n m k : Nat} {p : Nat → Nat} (hP : VPts d n p) {α αi β βi : Table}
    {NA NAi NB NBi : Nat} (ha : Realizes d n p α NA) (hai : Realizes d n p αi NAi)
    (hb : Realizes d n p β NB) (hbi : Realizes d n p βi NBi)
    (gws : List (List (Fin m × Bool))) (hk : k ≤ gws.length)
    (ps : List (List (Fin k × Bool) × List (Fin m × Bool)))
    (h : tabMatK d NA NAi NB NBi (gws.map natWord) (ps.map fun q => (natWord q.1, natWord q.2)) = true) :
    CFSG.Sporadic.Bridge.TwoGen.Native.relCheck n α αi β βi ((ps.map fun q => substWord gws q.1 ++ q.2).map natWord) = true := by
  unfold tabMatK at h
  rw [gensK_eq] at h
  have hq := pairsK_spec _ h
  unfold CFSG.Sporadic.Bridge.TwoGen.Native.relCheck
  rw [List.all_eq_true]
  intro v hv
  simp only [List.mem_map] at hv
  obtain ⟨_, ⟨q, hq', rfl⟩, rfl⟩ := hv
  have hm := hq (natWord q.1, natWord q.2) (List.mem_map.2 ⟨q, hq', rfl⟩)
  have hact : ∀ x < 2 ^ d, vmF d (matW d NA NAi NB NBi (natWord (substWord gws q.1 ++ q.2))) x = x := by
    intro x hx
    rw [natWord_append, vmF_matW_append, vmF_subst gws hk, ← vmF_mulF, hm, vmF_idF hx]
  have hR := real_wordTab hP ha hai hb hbi (natWord (substWord gws q.1 ++ q.2))
  have hn : n < 2 ^ 32 := by have := hP.n_lt; omega
  rw [tab_eq_idT hn hR.1 fun x hx => hP.inj _ (hR.2 x hx).1 _ hx (by
    rw [(hR.2 x hx).2, hact _ (hP.lt x hx)])]
  exact beq_self_eq_true _

end CFSG.KC.TabMat

end
