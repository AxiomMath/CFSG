module

public import Certificates.Data.Kernel.J2VertK
public import CFSG.Quasithin.Background.Harris.R1.J2VertCheck
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.Certificates.Kernel.MonsterB.Co2PermSound
import CFSG.Certificates.Kernel.Spor.PackFld
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.KC.J2VertK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native
open CFSG.Quasithin.Background.Harris.R1.J2Vert

theorem anyN_spec {f : Nat → Bool} {n : Nat} (h : anyN n f = true) : ∃ i < n, f i = true := by
  by_contra hne
  have hall : allN n (fun i => bIf(f i, false, true)) = true := by
    refine CFSG.KS.PackFld.allN_of_forall fun i hi => ?_
    cases hf : f i
    · rfl
    · exact absurd ⟨i, hi, hf⟩ hne
  unfold anyN at h
  rw [hall] at h
  exact Bool.false_ne_true h

theorem countN_eq (f : Nat → Bool) : ∀ n, countN n f = (List.range n).countP f
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.countP_append, ← countN_eq f n]
    change nIf(f n, Nat.succ (countN n f), countN n f) = _
    cases h : f n <;> simp [h]

theorem allL_spec {α : Type} {f : α → Bool} : ∀ {l : List α}, allL l f = true → ∀ a ∈ l, f a = true
  | [], _, a, ha => absurd ha List.not_mem_nil
  | x :: l, h, a, ha => by
    change bAnd(f x, allL l f) = true at h
    rw [bAnd_iff] at h
    rcases List.mem_cons.1 ha with rfl | ha
    · exact h.1
    · exact allL_spec h.2 a ha

variable {n w : Nat}

abbrev cK (n w p : Nat) : Prop := canonK n w (mask w) (n * w) p = true

theorem unpack_inj {p q : Nat} (hp : cK n w p) (hq : cK n w q) (e : unpack n w p = unpack n w q) :
    p = q := by
  have h1 := eqA_unpack hp hq
  rw [e, eqA_unpack hq hq, Nat.beq_refl] at h1
  exact (Nat.eq_of_beq_eq_true h1.symm)

section Tree

variable {ng : Nat} {G T : Nat → Nat} {gs : Array (Array Nat)}

theorem treeK_cons (pr : Nat × Nat) (rest : List (Nat × Nat)) (k : Nat) :
    treeK n w ng G T (pr :: rest) k = bAnd(Nat.ble pr.1 k, bAnd(Nat.blt pr.2 ng,
      bAnd(Nat.beq (T (Nat.succ k)) (pcomp n w (mask w) (T pr.1) (G pr.2)),
        treeK n w ng G T rest (Nat.succ k)))) := rfl

theorem fold_eq (hG : ∀ l < ng, gs.getD l (idA n) = unpack n w (G l))
    (cG : ∀ l < ng, cK n w (G l)) : ∀ (pl : List (Nat × Nat)) (acc : Array (Array Nat)) (k : Nat),
    acc.toList = (List.range (k + 1)).map (fun j => unpack n w (T j)) →
    (∀ j ≤ k, cK n w (T j)) → treeK n w ng G T pl k = true →
    (pl.foldl (fun (acc : Array (Array Nat)) (pr : Nat × Nat) =>
        acc.push (compA n (acc.getD pr.1 (idA n)) (gs.getD pr.2 (idA n)))) acc).toList =
      (List.range (k + 1 + pl.length)).map (fun j => unpack n w (T j)) ∧
      ∀ j ≤ k + pl.length, cK n w (T j)
  | [], acc, k, hacc, hc, _ => by
    simpa using ⟨hacc, hc⟩
  | pr :: rest, acc, k, hacc, hc, h => by
    rw [treeK_cons] at h
    simp only [bAnd_iff, Nat.ble_eq, Nat.blt_eq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    have h3' : T (k + 1) = pcomp n w (mask w) (T pr.1) (G pr.2) := Nat.eq_of_beq_eq_true h3
    have hsz : acc.size = k + 1 := by
      have := congrArg List.length hacc
      simpa using this
    have hget : acc.getD pr.1 (idA n) = unpack n w (T pr.1) := by
      rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, hacc, List.getElem?_map,
        List.getElem?_range (by omega)]
      rfl
    have hx : compA n (acc.getD pr.1 (idA n)) (gs.getD pr.2 (idA n)) = unpack n w (T (k + 1)) := by
      rw [hget, hG _ h2, compA_unpack (hc _ h1) (cG _ h2), h3']
    have hc' : ∀ j ≤ k + 1, cK n w (T j) := by
      intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hj) with hj | rfl
      · exact hc j (by omega)
      · rw [h3']
        exact canonK_pcomp (hc _ h1) (cG _ h2)
    have hacc' : (acc.push (compA n (acc.getD pr.1 (idA n)) (gs.getD pr.2 (idA n)))).toList =
        (List.range (k + 1 + 1)).map (fun j => unpack n w (T j)) := by
      rw [Array.toList_push, hacc, hx, List.range_succ (n := k + 1), List.map_append]
      rfl
    obtain ⟨e, c⟩ := fold_eq hG cG rest _ (k + 1) hacc' hc' h4
    rw [List.foldl_cons]
    have hl : k + 1 + (pr :: rest).length = k + 1 + 1 + rest.length := by
      simp only [List.length_cons]
      omega
    rw [hl]
    exact ⟨e, fun j hj => c j (by omega)⟩

theorem buildTab_eq (hG : ∀ l < ng, gs.getD l (idA n) = unpack n w (G l))
    (cG : ∀ l < ng, cK n w (G l)) (hid : idA n = unpack n w (pidn n w)) (cid : cK n w (pidn n w))
    {pl : List (Nat × Nat)} (h0 : T 0 = pidn n w) (h : treeK n w ng G T pl 0 = true) :
    buildTab n gs pl = (List.range (pl.length + 1)).map (fun j => unpack n w (T j)) ∧
      ∀ j ≤ pl.length, cK n w (T j) := by
  have hacc : (#[idA n] : Array (Array Nat)).toList =
      (List.range (0 + 1)).map (fun j => unpack n w (T j)) := by
    have e1 : (List.range (0 + 1)).map (fun j => unpack n w (T j)) = [unpack n w (T 0)] := rfl
    rw [e1, h0, ← hid]
  have hc : ∀ j ≤ 0, cK n w (T j) := fun j hj => by
    rw [Nat.le_zero.1 hj, h0]
    exact cid
  obtain ⟨e, c⟩ := fold_eq hG cG pl _ 0 hacc hc h
  unfold buildTab
  rw [e, Nat.zero_add, Nat.add_comm]
  exact ⟨rfl, fun j hj => c j (by omega)⟩

end Tree

theorem lt_of_chain {N : Nat} {f : Nat → Nat} (h : ∀ i, i + 1 < N → f i < f (i + 1)) :
    ∀ a b, a < b → b < N → f a < f b := by
  intro a b hab hb
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with hab | rfl
    · exact Nat.lt_trans (ih hab (by omega)) (h b hb)
    · exact h a hb

theorem inj_of_sortK {N : Nat} {T : Nat → Nat} {S ws : Nat} (h : sortK N T S ws = true) :
    ∀ i j, i < N → j < N → T i = T j → i = j := by
  unfold sortK at h
  rw [bAnd_iff] at h
  obtain ⟨hp, hs⟩ := h
  obtain ⟨hb, hi⟩ := CFSG.KC.Co2Mem.permK_sound hp
  let σ : Nat → Nat := fun a => pg ws (mask ws) S a
  have hmono : ∀ a b, a < b → b < N → T (σ a) < T (σ b) := by
    refine lt_of_chain (N := N) fun i hi' => ?_
    have := allN_spec hs i (by change i < N - 1; omega)
    exact Nat.blt_eq.mp this
  have hsurj : ∀ q < N, ∃ a < N, σ a = q := by
    let f : Fin N → Fin N := fun a => ⟨σ a.1, hb a.1 a.2⟩
    have hf : Function.Injective f := fun a b e =>
      Fin.ext (hi a.1 b.1 a.2 b.2 (congrArg Fin.val e))
    intro q hq
    obtain ⟨a, ha⟩ := (Finite.injective_iff_surjective.1 hf) ⟨q, hq⟩
    exact ⟨a.1, a.2, congrArg Fin.val ha⟩
  intro i j hiN hjN e
  obtain ⟨a, ha, rfl⟩ := hsurj i hiN
  obtain ⟨b, hb', rfl⟩ := hsurj j hjN
  rcases Nat.lt_trichotomy a b with hab | rfl | hab
  · exact absurd e (Nat.ne_of_lt (hmono a b hab hb'))
  · rfl
  · exact absurd e.symm (Nat.ne_of_lt (hmono b a hab ha))

theorem nodup_of_sortK {N : Nat} {T : Nat → Nat} {S ws : Nat} (h : sortK N T S ws = true)
    (c : ∀ j < N, cK n w (T j)) : ((List.range N).map (fun j => unpack n w (T j))).Nodup := by
  refine List.Nodup.map_on (fun x hx y hy e => ?_) List.nodup_range
  rw [List.mem_range] at hx hy
  exact inj_of_sortK h x y hx hy (unpack_inj (c x hx) (c y hy) e)

theorem contains_of_anyN {N X : Nat} {T : Nat → Nat}
    (h : anyN N (fun k => Nat.beq (T k) X) = true) :
    ((List.range N).map (fun j => unpack n w (T j))).contains (unpack n w X) = true := by
  obtain ⟨k, hk, e⟩ := anyN_spec h
  rw [List.contains_iff_mem, List.mem_map]
  exact ⟨k, List.mem_range.2 hk, by rw [Nat.eq_of_beq_eq_true e]⟩

theorem relK_cons (G GI : Nat → Nat) (p : Fin 8 × Bool) (r : List (Fin 8 × Bool)) :
    relK n w G GI (p :: r) = pcomp n w (mask w) (nIf(p.2, G p.1.val, GI p.1.val)) (relK n w G GI r) :=
  rfl

theorem relVal_eq {gs : Array (Array Nat)} {G GI : Nat → Nat}
    (hG : ∀ l < 8, gs.getD l (idA n) = unpack n w (G l)) (cG : ∀ l < 8, cK n w (G l))
    (hGI : ∀ l < 8, invCand n (unpack n w (G l)) = unpack n w (GI l)) (cGI : ∀ l < 8, cK n w (GI l))
    (hid : idA n = unpack n w (pidn n w)) (cid : cK n w (pidn n w)) :
    ∀ r : List (Fin 8 × Bool), relVal n gs r = unpack n w (relK n w G GI r) ∧ cK n w (relK n w G GI r)
  | [] => ⟨hid, cid⟩
  | p :: r => by
    obtain ⟨e, c⟩ := relVal_eq hG cG hGI cGI hid cid r
    have hl : (if p.2 then gs.getD p.1.val (idA n) else invCand n (gs.getD p.1.val (idA n))) =
        unpack n w (nIf(p.2, G p.1.val, GI p.1.val)) ∧ cK n w (nIf(p.2, G p.1.val, GI p.1.val)) := by
      cases p.2
      · exact ⟨by rw [if_neg (by decide), hG _ p.1.2, hGI _ p.1.2], cGI _ p.1.2⟩
      · exact ⟨by rw [if_pos rfl, hG _ p.1.2], cG _ p.1.2⟩
    have e2 : relVal n gs (p :: r) = compA n (if p.2 then gs.getD p.1.val (idA n)
        else invCand n (gs.getD p.1.val (idA n))) (relVal n gs r) := rfl
    rw [e2, e, hl.1, relK_cons, compA_unpack hl.2 c]
    exact ⟨rfl, canonK_pcomp hl.2 c⟩

theorem evalW_eq {base : Array (Array Nat)} {B : Nat → Nat}
    (hB : ∀ k < 3, base.getD k (idA n) = unpack n w (B k)) (cB : ∀ k < 3, cK n w (B k))
    (hid : idA n = unpack n w (pidn n w)) (cid : cK n w (pidn n w)) :
    ∀ wd : List (Fin 3), evalW n base wd = unpack n w (evalK n w B wd) ∧ cK n w (evalK n w B wd)
  | [] => ⟨hid, cid⟩
  | k :: wd => by
    obtain ⟨e, c⟩ := evalW_eq hB cB hid cid wd
    have e2 : evalW n base (k :: wd) = compA n (base.getD k.val (idA n)) (evalW n base wd) := rfl
    have e3 : evalK n w B (k :: wd) = pcomp n w (mask w) (B k.val) (evalK n w B wd) := rfl
    rw [e2, e, hB _ k.2, e3, compA_unpack (cB _ k.2) c]
    exact ⟨rfl, canonK_pcomp (cB _ k.2) c⟩

section Tab

variable {G GI T : Nat → Nat} {gs : Array (Array Nat)}

theorem getD_of_bind {ng : Nat} (hs : gs.size = ng)
    (h : allN ng (fun k => bindArrK gs[k]! n w (G k)) = true) :
    ∀ l < ng, gs.getD l (idA n) = unpack n w (G l) := by
  intro l hl
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega), Option.getD_some,
    ← getElem!_pos gs l (by omega)]
  exact unpack_eq_of_bindArrK (allN_spec h l hl)

theorem genCheck_of {k : Nat} (hG : ∀ l < k, gs.getD l (idA n) = unpack n w (G l))
    (h : allN k (fun i => invEqK n w (mask w) (n * w) (G i) (GI i)) = true) :
    genCheck n gs k = true := by
  unfold genCheck
  rw [List.all_eq_true]
  intro i hi
  have hi' := List.mem_range.1 hi
  obtain ⟨e1, e2⟩ := invEqK_sound (allN_spec h i hi')
  rw [hG i hi', e1]
  exact e2

theorem tabLower_of {pl : List (Nat × Nat)} {N S ws : Nat}
    (hb : buildTab n gs pl = (List.range (pl.length + 1)).map (fun j => unpack n w (T j)))
    (c : ∀ j ≤ pl.length, cK n w (T j)) (hN : pl.length + 1 = N) (hs : sortK N T S ws = true) :
    tabLower n gs pl N = true := by
  unfold tabLower
  rw [hb, hN]
  simp only [List.length_map, List.length_range, decide_true, Bool.true_and]
  exact decide_eq_true (nodup_of_sortK hs (fun j hj => c j (by omega)))

theorem tabMem_of {pl : List (Nat × Nat)} {N k : Nat} {ts : Array (Array Nat)} {TS : Nat → Nat}
    (hts : ∀ i < k, ts.getD i (idA n) = unpack n w (TS i))
    (hb : buildTab n gs pl = (List.range N).map (fun j => unpack n w (T j)))
    (h : allN k (fun i => anyN N (fun j => Nat.beq (T j) (TS i))) = true) :
    tabMem n gs pl ts k = true := by
  unfold tabMem
  rw [hb, List.all_eq_true]
  intro i hi
  have hi' := List.mem_range.1 hi
  rw [hts i hi']
  exact contains_of_anyN (allN_spec h i hi')

theorem tabClosed_of {pl : List (Nat × Nat)} {N k : Nat}
    (hG : ∀ l < k, gs.getD l (idA n) = unpack n w (G l)) (cG : ∀ l < k, cK n w (G l))
    (cGI : ∀ l < k, cK n w (GI l))
    (hgen : allN k (fun i => invEqK n w (mask w) (n * w) (G i) (GI i)) = true)
    (hb : buildTab n gs pl = (List.range N).map (fun j => unpack n w (T j)))
    (c : ∀ j < N, cK n w (T j))
    (h : allN N (fun x => allN k (fun i =>
      bAnd(anyN N (fun j => Nat.beq (T j) (pcomp n w (mask w) (T x) (G i))),
        anyN N (fun j => Nat.beq (T j) (pcomp n w (mask w) (T x) (GI i)))))) = true) :
    tabClosed n gs k pl = true := by
  have hGI : ∀ l < k, invCand n (unpack n w (G l)) = unpack n w (GI l) := fun l hl =>
    (invEqK_sound (allN_spec hgen l hl)).1
  unfold tabClosed
  rw [genCheck_of hG hgen, hb, Bool.true_and, List.all_eq_true]
  intro x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
  have ha' := List.mem_range.1 ha
  rw [List.all_eq_true]
  intro i hi
  have hi' := List.mem_range.1 hi
  have h2 := allN_spec (allN_spec h a ha') i hi'
  rw [bAnd_iff] at h2
  rw [hG i hi', compA_unpack (c a ha') (cG i hi'), hGI i hi', compA_unpack (c a ha') (cGI i hi'),
    contains_of_anyN h2.1, contains_of_anyN h2.2]
  rfl

theorem relCheck_of (hG : ∀ l < 8, gs.getD l (idA n) = unpack n w (G l)) (cG : ∀ l < 8, cK n w (G l))
    (cGI : ∀ l < 8, cK n w (GI l))
    (hgen : allN 8 (fun i => invEqK n w (mask w) (n * w) (G i) (GI i)) = true)
    (hid : idA n = unpack n w (pidn n w)) (cid : cK n w (pidn n w)) {rels : List (List (Fin 8 × Bool))}
    (h : allL rels (fun r => Nat.beq (relK n w G GI r) (pidn n w)) = true) :
    relCheck n gs rels = true := by
  have hGI : ∀ l < 8, invCand n (unpack n w (G l)) = unpack n w (GI l) := fun l hl =>
    (invEqK_sound (allN_spec hgen l hl)).1
  unfold relCheck
  rw [genCheck_of hG hgen, Bool.true_and, List.all_eq_true]
  intro r hr
  obtain ⟨e, c⟩ := relVal_eq hG cG hGI cGI hid cid r
  rw [e, hid, eqA_unpack c cid]
  exact allL_spec h r hr

end Tab

end CFSG.KC.J2VertK

end
