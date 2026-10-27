module

public import Certificates.Data.Kernel.AS91K468.K46C
public import CFSG.Certificates.Kernel.AS91K468.Sound46J

public section

set_option exponentiation.threshold 5000

namespace Certificates.Kernel.AS91K468

open CFSG.KC.Mat12P CFSG.KC.Mat8P Certificates.Kernel.HJ12K

theorem laneW_eq (P g : ℕ) : laneW P g = P / 2 ^ (4096 * g) % 2 ^ 4096 := by
  change (P >>> (4096 * g)) &&& (2 ^ 4096 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem laneW_packW : ∀ (W : List ℕ), (∀ x ∈ W, x < 2 ^ 4096) →
    ∀ (g : ℕ) (h : g < W.length), laneW (packW W) g = W[g]
  | [], _, g, h => absurd h (Nat.not_lt_zero _)
  | x :: W, hW, g, h => by
    have e : packW (x :: W) = x + packW W * 2 ^ 4096 := by
      change x + (packW W <<< 4096) = _
      rw [Nat.shiftLeft_eq]
    have hx : x < 2 ^ 4096 := hW x List.mem_cons_self
    rcases g with _ | g
    · rw [laneW_eq, e, Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt hx]
      rfl
    · have ih := laneW_packW W (fun y hy => hW y (List.mem_cons_of_mem x hy)) g
        (by simpa using h)
      rw [laneW_eq] at ih ⊢
      rw [e, Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (4096 * g)), ← Nat.div_div_eq_div_mul,
        Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hx, Nat.zero_add, ih]
      rfl

section

variable (P nW : ℕ) (W fr' S : List ℕ) (hW : W = fr' ++ S) (hnW : nW = W.length) (hn : W.Nodup)
  (hP : ∀ (g : ℕ) (h : g < W.length), laneW P g = W[g]) (d' : ℕ)

include hW hnW hn hP in
theorem walk_sound : ∀ (X cs : List ℕ) (d : ℕ) (t : NT ℕ), d ≤ fr'.length →
    (∀ q, memP t q = (W.drop d).contains q) → walkI P nW d' X cs d = true →
    d' ≤ fr'.length ∧ (X.foldl stepN (fr'.drop d, t)).1 = fr'.drop d' ∧
      (∀ q, memP (X.foldl stepN (fr'.drop d, t)).2 q = (W.drop d').contains q) ∧ ∀ y ∈ X, y ∈ W
  | [], cs, d, t, hp, ht, hw => by
    have e : walkI P nW d' [] cs d = (cs.isEmpty && Nat.beq d d') := rfl
    rw [e, Bool.and_eq_true, Nat.beq_eq] at hw
    obtain ⟨_, rfl⟩ := hw
    exact ⟨hp, rfl, ht, fun _ h => absurd h List.not_mem_nil⟩
  | y :: X, [], d, t, _, _, hw => by
    have e : walkI P nW d' (y :: X) [] d = false := rfl
    rw [e] at hw
    exact absurd hw Bool.false_ne_true
  | y :: X, g :: cs, d, t, hp, ht, hw => by
    have e0 : walkI P nW d' (y :: X) (g :: cs) d = (Nat.beq (laneW P g) y && Nat.blt g nW &&
        Bool.rec (motive := fun _ => Bool) (Nat.beq (Nat.succ g) d && walkI P nW d' X cs g)
          (walkI P nW d' X cs d) (Nat.ble d g)) := rfl
    rw [e0] at hw
    cases hb : Nat.ble d g with
    | true =>
      rw [hb] at hw
      change (Nat.beq (laneW P g) y && Nat.blt g nW && walkI P nW d' X cs d) = true at hw
      rw [Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at hw
      obtain ⟨⟨h1, h2⟩, hw⟩ := hw
      rw [hnW] at h2
      rw [hP g h2] at h1
      rw [Nat.ble_eq] at hb
      have hy : memP t y = true := by
        rw [ht y, List.contains_iff_mem, List.mem_drop_iff_getElem]
        refine ⟨g - d, by omega, ?_⟩
        convert h1 using 2
        omega
      have es : stepN (fr'.drop d, t) y = (fr'.drop d, t) := by simp only [stepN, hy, if_true]
      rw [List.foldl_cons, es]
      obtain ⟨a1, a2, a3, a4⟩ := walk_sound X cs d t hp ht hw
      refine ⟨a1, a2, a3, fun z hz => ?_⟩
      rcases List.mem_cons.1 hz with rfl | hz
      · rw [← h1]
        exact List.getElem_mem h2
      · exact a4 z hz
    | false =>
      rw [hb] at hw
      change (Nat.beq (laneW P g) y && Nat.blt g nW &&
        (Nat.beq (Nat.succ g) d && walkI P nW d' X cs g)) = true at hw
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq,
        Nat.beq_eq] at hw
      obtain ⟨⟨h1, h2⟩, h3, hw⟩ := hw
      subst h3
      rw [hnW] at h2
      rw [hP g h2] at h1
      have hgf : g < fr'.length := by omega
      have hWg : W.drop g = y :: W.drop (g + 1) := by
        rw [List.drop_eq_getElem_cons h2, h1]
      have hfg : fr'.drop g = y :: fr'.drop (g + 1) := by
        rw [List.drop_eq_getElem_cons hgf, ← h1]
        congr 1
        subst hW
        rw [List.getElem_append_left hgf]
      have hny : y ∉ W.drop (g + 1) := by
        have := hn.sublist (List.drop_sublist g W)
        rw [hWg, List.nodup_cons] at this
        exact this.1
      have hy : memP t y = false := by
        rw [ht y, Bool.eq_false_iff, ne_eq, List.contains_iff_mem]
        exact hny
      have es : stepN (fr'.drop (g + 1), t) y = (y :: fr'.drop (g + 1), insP t y) := by
        simp only [stepN, hy, Bool.false_eq_true, if_false]
      rw [List.foldl_cons, es, ← hfg]
      obtain ⟨a1, a2, a3, a4⟩ := walk_sound X cs g (insP t y) (Nat.le_of_lt hgf) (fun q => by
        rw [memP_insP, ht q, hWg, List.contains_cons, HJ12K.beq_symm y q]) hw
      refine ⟨a1, a2, a3, fun z hz => ?_⟩
      rcases List.mem_cons.1 hz with rfl | hz
      · rw [← h1]
        exact List.getElem_mem h2
      · exact a4 z hz

end

theorem imgsF_append (fs : List (ℕ → ℕ)) (a b : List ℕ) :
    imgsF fs (a ++ b) = imgsF fs a ++ imgsF fs b := List.flatMap_append

theorem fold_walks (PF : List (ℕ × ℕ)) (c : ℕ) (fr S fr' : List ℕ) (cs : List (List ℕ))
    (ds : List ℕ) (hn : (fr' ++ S).Nodup)
    (hP : ∀ (g : ℕ) (h : g < (fr' ++ S).length), laneW (packW (fr' ++ S)) g = (fr' ++ S)[g]) :
    ∀ (m i : ℕ), fr.length ≤ c * (i + m) →
      (∀ j, i ≤ j → j < i + m → chunkW PF c fr S fr' cs ds j = true) →
      ∀ t : NT ℕ, ds.getD i 0 ≤ fr'.length →
        (∀ q, memP t q = ((fr' ++ S).drop (ds.getD i 0)).contains q) →
        ((imgsF (fsOf PF) (fr.drop (c * i))).foldl stepN (fr'.drop (ds.getD i 0), t)).1 =
          fr'.drop (ds.getD (i + m) 0) ∧ ∀ y ∈ imgsF (fsOf PF) (fr.drop (c * i)), y ∈ fr' ++ S
  | 0, i, hl', _, t, _, _ => by
    have hz : fr.drop (c * i) = [] := List.drop_eq_nil_of_le (by simpa using hl')
    rw [hz]
    exact ⟨rfl, fun _ h => by simp [imgsF] at h⟩
  | m + 1, i, hl', hc, t, hp, ht => by
    have hd : fr.drop (c * i) = chunkL c i fr ++ fr.drop (c * (i + 1)) := by
      rw [chunkL, Nat.mul_succ, ← List.drop_drop, List.take_append_drop]
    rw [hd, imgsF_append, List.foldl_append]
    have hw := hc i le_rfl (by omega)
    rw [chunkW] at hw
    obtain ⟨w1, w2, w3, w4⟩ := walk_sound (packW (fr' ++ S)) (fr' ++ S).length (fr' ++ S) fr' S
      rfl rfl hn hP (ds.getD (i + 1) 0) _ _ (ds.getD i 0) t hp ht hw
    have hp2 : (imgsF (fsOf PF) (chunkL c i fr)).foldl stepN (fr'.drop (ds.getD i 0), t) =
        (fr'.drop (ds.getD (i + 1) 0), ((imgsF (fsOf PF) (chunkL c i fr)).foldl stepN
          (fr'.drop (ds.getD i 0), t)).2) := by
      rw [← w2]
    rw [hp2]
    obtain ⟨v1, v2⟩ := fold_walks PF c fr S fr' cs ds hn hP m (i + 1)
      (by rw [Nat.add_right_comm]; exact hl') (fun j h1 h2 => hc j (by omega) (by omega)) _ w1 w3
    refine ⟨?_, fun y hy => ?_⟩
    · rw [v1]
      congr 2
      omega
    · rcases List.mem_append.1 hy with hy | hy
      · exact w4 y hy
      · exact v2 y hy

theorem round_walk (PF : List (ℕ × ℕ)) (c n : ℕ) (fr S fr' : List ℕ) (cs : List (List ℕ))
    (ds : List ℕ) (he : chunksEnd c n fr S fr' ds = true)
    (hc : ∀ i, i < n → chunkW PF c fr S fr' cs ds i = true) :
    (roundN (fsOf PF) fr (ofListP S)).1 = fr' ∧
      ∀ F ∈ fr, ∀ rf ∈ PF, F &&& rf.2 ∈ fr' ++ S := by
  rw [chunksEnd, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Nat.beq_eq, Nat.beq_eq, Nat.ble_eq, nodupP_iff, List.all_eq_true] at he
  obtain ⟨⟨⟨⟨h0, hn'⟩, hl'⟩, hnd⟩, hlt⟩ := he
  have hP := laneW_packW (fr' ++ S) fun x hx => by
    have := hlt x hx
    have e2 : Nat.shiftLeft 1 4096 = 2 ^ 4096 := (Nat.shiftLeft_eq 1 4096).trans (Nat.one_mul _)
    rw [Nat.blt_eq, e2] at this
    exact this
  have hS : (fr' ++ S).drop fr'.length = S := List.drop_left
  obtain ⟨v1, v2⟩ := fold_walks PF c fr S fr' cs ds hnd hP n 0 (by simpa using hl')
    (fun j _ h2 => hc j (by simpa using h2)) (ofListP S) (by rw [h0])
    (fun q => by rw [memP_ofListP, h0, hS])
  rw [Nat.mul_zero, List.drop_zero, h0, List.drop_length, Nat.zero_add, hn', List.drop_zero] at v1
  refine ⟨v1, fun F hF rf hrf => v2 _ ?_⟩
  rw [Nat.mul_zero, List.drop_zero, imgsF, List.mem_flatMap]
  refine ⟨F, hF, ?_⟩
  rw [fsOf, List.map_map, List.mem_map]
  exact ⟨rf, hrf, rfl⟩

theorem jAll1_of (PF : List (ℕ × ℕ)) (L Fs W : List ℕ) (hW : ∀ x ∈ W, x ∈ L)
    (h : ∀ F ∈ Fs, ∀ rf ∈ PF, F &&& rf.2 ∈ W) : jAll1 PF L Fs = true := by
  rw [jAll1, List.all_eq_true]
  intro F hF
  rw [List.all_eq_true]
  intro rf hrf
  rw [memP_ofListP, List.contains_iff_mem]
  exact hW _ (h F hF rf hrf)

theorem round_walkNE (PF : List (ℕ × ℕ)) (c n : ℕ) (fr S fr' : List ℕ) (cs : List (List ℕ))
    (ds : List ℕ) (he : (chunksEnd c n fr S fr' ds && !fr'.isEmpty) = true)
    (hc : ∀ i, i < n → chunkW PF c fr S fr' cs ds i = true) :
    ((roundN (fsOf PF) fr (ofListP S)).1 = fr' ∧ ∀ F ∈ fr, ∀ rf ∈ PF, F &&& rf.2 ∈ fr' ++ S) ∧
      fr'.isEmpty = false := by
  rw [Bool.and_eq_true] at he
  exact ⟨round_walk PF c n fr S fr' cs ds he.1 hc, by simpa using he.2⟩

theorem ok46_ofW (hw : wordsOK46 = true) (h1 : w1OK46Q = true) (h2 : eb46Q = true)
    (h3 : trans46Q = true) (hn : pNodup46Q = true) (PF : List (ℕ × ℕ))
    (hPF : (pfOf (enumQ pQ) == PF) = true) (f0 f1 f2 f3 f4 : List ℕ) (hf0 : (f0 == [fullM]) = true)
    (r0 : ((roundN (fsOf PF) f0 (ofListP f0)).1 = f1 ∧
      ∀ F ∈ f0, ∀ rf ∈ PF, F &&& rf.2 ∈ f1 ++ f0) ∧ f1.isEmpty = false)
    (r1 : ((roundN (fsOf PF) f1 (ofListP (f1 ++ f0))).1 = f2 ∧
      ∀ F ∈ f1, ∀ rf ∈ PF, F &&& rf.2 ∈ f2 ++ (f1 ++ f0)) ∧ f2.isEmpty = false)
    (r2 : ((roundN (fsOf PF) f2 (ofListP (f2 ++ (f1 ++ f0)))).1 = f3 ∧
      ∀ F ∈ f2, ∀ rf ∈ PF, F &&& rf.2 ∈ f3 ++ (f2 ++ (f1 ++ f0))) ∧ f3.isEmpty = false)
    (r3 : ((roundN (fsOf PF) f3 (ofListP (f3 ++ (f2 ++ (f1 ++ f0))))).1 = f4 ∧
      ∀ F ∈ f3, ∀ rf ∈ PF, F &&& rf.2 ∈ f4 ++ (f3 ++ (f2 ++ (f1 ++ f0)))) ∧ f4.isEmpty = false)
    (r4 : (roundN (fsOf PF) f4 (ofListP (f4 ++ (f3 ++ (f2 ++ (f1 ++ f0)))))).1 = [] ∧
      ∀ F ∈ f4, ∀ rf ∈ PF, F &&& rf.2 ∈ [] ++ (f4 ++ (f3 ++ (f2 ++ (f1 ++ f0)))))
    (b0 : jAll2 PF f0 = true) (b1 : jAll2 PF f1 = true) (b2 : jAll2 PF f2 = true)
    (b3 : jAll2 PF f3 = true) (b4 : jAll2 PF f4 = true) :
    CFSG.Quasithin.H13.AS91.Two.ok46 () = true := by
  have ok : ∀ {PF : List (ℕ × ℕ)} {fr S fr' : List ℕ}, (roundN (fsOf PF) fr (ofListP S)).1 = fr' →
      fr'.isEmpty = false → roundOK PF fr S fr' = true := fun h1 h2 => by
    rw [roundOK, h1, beq_self_eq_true, Bool.true_and, h2]
    rfl
  have sub : ∀ W : List ℕ, (∀ x ∈ W, x ∈ f4 ++ (f3 ++ (f2 ++ (f1 ++ (f0 ++ []))))) →
      ∀ Fs, (∀ F ∈ Fs, ∀ rf ∈ PF, F &&& rf.2 ∈ W) →
        jAll1 PF (f4 ++ (f3 ++ (f2 ++ (f1 ++ (f0 ++ []))))) Fs = true :=
    fun W hW Fs h => jAll1_of PF _ Fs W hW h
  refine ok46_ofL hw h1 h2 h3 hn PF hPF f0 f1 f2 f3 f4 hf0 (ok r0.1.1 r0.2) (ok r1.1.1 r1.2)
    (ok r2.1.1 r2.2) (ok r3.1.1 r3.2) (by rw [roundEnd, r4.1]; rfl)
    (sub _ ?_ _ r0.1.2) (sub _ ?_ _ r1.1.2) (sub _ ?_ _ r2.1.2) (sub _ ?_ _ r3.1.2)
    (sub _ ?_ _ r4.2) b0 b1 b2 b3 b4 <;>
  · intro x hx
    rw [List.append_nil]
    first
    | exact hx
    | exact List.mem_append_right _ hx
    | exact List.mem_append_right _ (List.mem_append_right _ hx)
    | exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ hx))
    | simpa using hx

theorem all_chunks (p : ℕ → Bool) (fr : List ℕ) (c : ℕ) : ∀ (m i : ℕ), fr.length ≤ c * (i + m) →
    (∀ j, i ≤ j → j < i + m → (chunkL c j fr).all p = true) → (fr.drop (c * i)).all p = true
  | 0, i, hl, _ => by
    rw [List.drop_eq_nil_of_le (by simpa using hl)]
    rfl
  | m + 1, i, hl, hc => by
    have hd : fr.drop (c * i) = chunkL c i fr ++ fr.drop (c * (i + 1)) := by
      rw [chunkL, Nat.mul_succ, ← List.drop_drop, List.take_append_drop]
    rw [hd, List.all_append, hc i le_rfl (by omega),
      all_chunks p fr c m (i + 1) (by rw [Nat.add_right_comm]; exact hl)
        (fun j h1 h2 => hc j (by omega) (by omega))]
    rfl

theorem chunksEnd_len {c n : ℕ} {fr S fr' ds : List ℕ} (he : chunksEnd c n fr S fr' ds = true) :
    fr.length ≤ c * n := by
  rw [chunksEnd, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Nat.ble_eq] at he
  exact he.1.1.2

theorem chunksEnd_len' {c n : ℕ} {fr S fr' ds : List ℕ} {b : Bool}
    (he : (chunksEnd c n fr S fr' ds && b) = true) : fr.length ≤ c * n :=
  chunksEnd_len (Bool.and_eq_true _ _ ▸ he).1

theorem jAll2_chunks (PF : List (ℕ × ℕ)) (c n : ℕ) (fr : List ℕ) (hl : fr.length ≤ c * n)
    (hc : ∀ i, i < n → jAll2 PF (chunkL c i fr) = true) : jAll2 PF fr = true := by
  have := all_chunks (jFQ PF w1M) fr c n 0 (by simpa using hl) (fun j _ h2 => by
    have := hc j (by simpa using h2)
    rw [jAll2] at this
    exact this)
  rw [Nat.mul_zero, List.drop_zero] at this
  rw [jAll2]
  exact this

theorem lt_snoc {P : ℕ → Prop} {n : ℕ} (h : ∀ i, i < n → P i) (hn : P n) :
    ∀ i, i < n + 1 → P i := fun i hi => by
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
  · exact h i hi
  · exact hn

theorem lt_zero' {P : ℕ → Prop} : ∀ i, i < 0 → P i := fun _ hi => absurd hi (Nat.not_lt_zero _)

end Certificates.Kernel.AS91K468
