module

public import Certificates.Data.Kernel.HcReplay
import all Certificates.Data.Kernel.HcReplay
import all Certificates.Data.G23RecogGlueInputs

public section

namespace CFSG.KC.HcPack

open CFSG.GH74.QTGen4.Recog.G23

theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem strictB_eq (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem splitE_eq : ∀ (l : List ℕ) (k : ℕ),
    (splitE l).1.getD k 0 = l.getD (2 * k) 0 ∧ (splitE l).2.getD k 0 = l.getD (2 * k + 1) 0
  | [], k => by simp [splitE]
  | x :: l, k => by
    have e : splitE (x :: l) = (x :: (splitE l).2, (splitE l).1) := rfl
    rw [e]
    cases k with
    | zero =>
      refine ⟨by simp, ?_⟩
      rw [(splitE_eq l 0).1]
      simp
    | succ k =>
      have e2 : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
      refine ⟨?_, ?_⟩
      · rw [List.getD_cons_succ, (splitE_eq l k).2, e2, List.getD_cons_succ]
      · rw [List.getD_cons_succ, (splitE_eq l (k + 1)).1]

theorem splitE_length : ∀ l : List ℕ,
    (splitE l).1.length ≤ (l.length + 1) / 2 ∧ (splitE l).2.length ≤ l.length / 2
  | [] => by simp [splitE]
  | x :: l => by
    have e : splitE (x :: l) = (x :: (splitE l).2, (splitE l).1) := rfl
    rw [e]
    obtain ⟨h1, h2⟩ := splitE_length l
    simp only [List.length_cons]
    omega

theorem getT_ofT : ∀ (n : ℕ) (l : List ℕ), l.length ≤ n → ∀ i, getT (ofT n l) i = l.getD i 0
  | 0, l, h, i => by
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 h)]
    rfl
  | n + 1, [], _, i => by simp only [List.getD_nil]; rfl
  | n + 1, x :: l, h, 0 => rfl
  | n + 1, x :: l, h, i + 1 => by
    simp only [List.length_cons] at h
    obtain ⟨hl1, hl2⟩ := splitE_length l
    have e : getT (ofT (n + 1) (x :: l)) (i + 1) =
        Bool.rec (motive := fun _ => ℕ) (getT (ofT n (splitE l).2) (i / 2))
          (getT (ofT n (splitE l).1) (i / 2)) (Nat.beq (i % 2) 0) := rfl
    rw [e, List.getD_cons_succ]
    rcases Nat.mod_two_eq_zero_or_one i with hi | hi
    · have hb : Nat.beq (i % 2) 0 = true := by rw [hi]; rfl
      rw [hb]
      change getT (ofT n (splitE l).1) (i / 2) = _
      rw [getT_ofT n _ (by omega), (splitE_eq l _).1]
      congr 1
      omega
    · have hb : Nat.beq (i % 2) 0 = false := by rw [hi]; rfl
      rw [hb]
      change getT (ofT n (splitE l).2) (i / 2) = _
      rw [getT_ofT n _ (by omega), (splitE_eq l _).2]
      congr 1
      omega

theorem incT_sound (get : ℕ → ℕ) (n : ℕ) :
    ∀ (ord : List ℕ) (prev : ℕ), incT get n ord prev = true →
      (∀ i ∈ ord, i < n ∧ prev < get i) ∧ (ord.map get).Pairwise (· < ·)
  | [], _, _ => ⟨fun _ h => absurd h List.not_mem_nil, List.Pairwise.nil⟩
  | i :: ord, prev, h => by
    have e1 : incT get n (i :: ord) prev =
        andB (Nat.blt i n) (andB (Nat.blt prev (get i)) (incT get n ord (get i))) := by
      change andB (Nat.blt i n) (strictB (get i) fun x => andB (Nat.blt prev x)
        (incT get n ord x)) = _
      rw [strictB_eq]
    rw [e1] at h
    obtain ⟨h0, h⟩ := andB_true h
    obtain ⟨h1, h2⟩ := andB_true h
    have hin : i < n := Nat.blt_eq.mp h0
    have hlt : prev < get i := Nat.blt_eq.mp h1
    obtain ⟨ih1, ih2⟩ := incT_sound get n ord _ h2
    refine ⟨fun j hj => ?_, ?_⟩
    · rcases List.mem_cons.1 hj with rfl | hj
      · exact ⟨hin, hlt⟩
      · exact ⟨(ih1 j hj).1, hlt.trans (ih1 j hj).2⟩
    · rw [List.map_cons, List.pairwise_cons]
      refine ⟨fun x hx => ?_, ih2⟩
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
      exact (ih1 j hj).2

theorem nodup_of_incT {E ord : List ℕ} (hl : ord.length = E.length)
    (h : incT (getT (ofT E.length E)) E.length ord 0 = true) : E.Nodup := by
  classical
  obtain ⟨hb, hpw⟩ := incT_sound _ _ ord 0 h
  have hnd : (ord.map (getT (ofT E.length E))).Nodup := hpw.imp fun hab => Nat.ne_of_lt hab
  have hsub : (ord.map (getT (ofT E.length E))).toFinset ⊆ E.toFinset := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hx)
    rw [getT_ofT _ _ (Nat.le_refl _), List.getD_eq_getElem _ _ (hb i hi).1]
    exact List.mem_toFinset.2 (List.getElem_mem _)
  have hc := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, List.length_map, hl, List.card_toFinset] at hc
  rw [← (List.dedup_sublist E).eq_of_length_le hc]
  exact List.nodup_dedup E

section Replay

variable (mul : ℕ → ℕ → ℕ) (get : ℕ → ℕ) (cap : ℕ) (E : List ℕ)
  (hg : ∀ i, get i = E.getD i 0) (hE : E.Nodup)

include hg hE in
theorem gensJ_sound (x : ℕ) (k : ℕ → List ℕ → List ℕ → Bool) :
    ∀ (gs : List ℕ) (m : ℕ) (ds nf : List ℕ), m ≤ E.length →
      gensJ mul get cap E.length x gs k m ds nf = true →
      ∃ m' ds' nf', m' ≤ E.length ∧
        gs.foldl (addOne cap mul x) (E.take m, nf) = (E.take m', nf') ∧ k m' ds' nf' = true
  | [], m, ds, nf, hm, h => ⟨m, ds, nf, hm, rfl, h⟩
  | g :: gs, m, [], nf, _, h => absurd h Bool.false_ne_true
  | g :: gs, m, j :: ds, nf, hm, h => by
    have e : gensJ mul get cap E.length x (g :: gs) k m (j :: ds) nf =
        Bool.rec (motive := fun _ => Bool)
          (andB (Nat.blt j m) (andB (Nat.beq (get j) (mul x g))
            (gensJ mul get cap E.length x gs k m ds nf)))
          (andB (Nat.blt m cap) (andB (Nat.blt m E.length) (andB (Nat.beq (get m) (mul x g))
            (gensJ mul get cap E.length x gs k (m + 1) ds (nf ++ [mul x g])))))
          (Nat.beq j m) := by
      change strictB (mul x g) (fun y => Bool.rec (motive := fun _ => Bool)
          (andB (Nat.blt j m) (andB (Nat.beq (get j) y)
            (gensJ mul get cap E.length x gs k m ds nf)))
          (andB (Nat.blt m cap) (andB (Nat.blt m E.length) (andB (Nat.beq (get m) y)
            (strictB (Nat.succ m) fun m' => gensJ mul get cap E.length x gs k m' ds (nf ++ [y])))))
          (Nat.beq j m)) = _
      rw [strictB_eq, strictB_eq]
    rw [e] at h
    have hlen : (E.take m).length = m := List.length_take_of_le hm
    rw [List.foldl_cons]
    cases hj : Nat.beq j m
    · rw [hj] at h
      obtain ⟨h1, h⟩ := andB_true h
      obtain ⟨h2, h3⟩ := andB_true h
      have hjm : j < m := Nat.blt_eq.mp h1
      have hy : E.getD j 0 = mul x g := by rw [← hg j]; exact Nat.eq_of_beq_eq_true h2
      have hmem : (E.take m).contains (mul x g) = true := by
        rw [List.contains_iff_mem, ← hy, List.getD_eq_getElem _ _ (by omega)]
        rw [List.mem_iff_getElem]
        exact ⟨j, by omega, by rw [List.getElem_take]⟩
      have ha : addOne cap mul x (E.take m, nf) g = (E.take m, nf) := by
        unfold addOne
        rw [if_neg (fun hc => hc.2 hmem)]
      rw [ha]
      exact gensJ_sound x k gs m ds nf hm h3
    · rw [hj] at h
      obtain ⟨h1, h⟩ := andB_true h
      obtain ⟨h2, h⟩ := andB_true h
      obtain ⟨h3, h4⟩ := andB_true h
      have hc : m < cap := Nat.blt_eq.mp h1
      have hn : m < E.length := Nat.blt_eq.mp h2
      have hy : E[m] = mul x g := by
        rw [← List.getD_eq_getElem _ 0 hn, ← hg m]
        exact Nat.eq_of_beq_eq_true h3
      have hnot : ¬ (E.take m).contains (mul x g) = true := by
        rw [List.contains_iff_mem, ← hy, List.mem_iff_getElem]
        rintro ⟨i, hi, he⟩
        rw [List.getElem_take] at he
        have := (List.Nodup.getElem_inj_iff hE).mp he
        omega
      have ha : addOne cap mul x (E.take m, nf) g = (E.take (m + 1), nf ++ [mul x g]) := by
        unfold addOne
        rw [if_pos ⟨by rw [hlen]; exact hc, hnot⟩, List.take_add_one, List.getElem?_eq_getElem hn,
          hy]
        rfl
      rw [ha]
      exact gensJ_sound x k gs (m + 1) ds _ hn h4

include hg hE in
theorem frJ_sound (gs : List ℕ) (k : ℕ → List ℕ → List ℕ → Bool) :
    ∀ (fr : List ℕ) (m : ℕ) (ds nf : List ℕ), m ≤ E.length →
      frJ mul get cap E.length gs fr k m ds nf = true →
      ∃ m' ds' nf', m' ≤ E.length ∧
        fr.foldl (fun acc x => gs.foldl (addOne cap mul x) acc) (E.take m, nf) = (E.take m', nf') ∧
        k m' ds' nf' = true
  | [], m, ds, nf, hm, h => ⟨m, ds, nf, hm, rfl, h⟩
  | x :: fr, m, ds, nf, hm, h => by
    have e : frJ mul get cap E.length gs (x :: fr) k m ds nf =
        gensJ mul get cap E.length x gs (frJ mul get cap E.length gs fr k) m ds nf := rfl
    rw [e] at h
    obtain ⟨m1, ds1, nf1, hm1, he1, h1⟩ :=
      gensJ_sound mul get cap E hg hE x _ gs m ds nf hm h
    rw [List.foldl_cons, he1]
    exact frJ_sound gs k fr m1 ds1 nf1 hm1 h1

include hg hE in
theorem bfsJ_sound (gs : List ℕ) :
    ∀ (fuel m : ℕ) (ds fr : List ℕ), m ≤ E.length →
      bfsJ mul get cap E.length gs fuel m ds fr = true →
      bfsAux cap mul gs fuel (E.take m) fr = E
  | 0, m, ds, fr, _, h => by
    have hm : m = E.length := Nat.eq_of_beq_eq_true h
    rw [bfsAux, hm, List.take_length]
  | fuel + 1, m, ds, [], _, h => by
    have hm : m = E.length := Nat.eq_of_beq_eq_true h
    simp only [bfsAux, List.isEmpty_nil, if_true]
    rw [hm, List.take_length]
  | fuel + 1, m, ds, x :: fr, hm, h => by
    have e : bfsJ mul get cap E.length gs (fuel + 1) m ds (x :: fr) =
        frJ mul get cap E.length gs (x :: fr) (bfsJ mul get cap E.length gs fuel) m ds [] := rfl
    rw [e] at h
    obtain ⟨m1, ds1, nf1, hm1, he1, h1⟩ :=
      frJ_sound mul get cap E hg hE gs _ (x :: fr) m ds [] hm h
    simp only [bfsAux, List.isEmpty_cons, Bool.false_eq_true, if_false]
    rw [bfsStep, he1]
    exact bfsJ_sound gs fuel m1 ds1 nf1 hm1 h1

end Replay

theorem bfsAux_of_replayB (mul : ℕ → ℕ → ℕ) (cap fuel : ℕ) (gs E ds ord : List ℕ) (a : ℕ)
    (h : replayB mul cap fuel gs E ds ord a = true) : bfsAux cap mul gs fuel [a] [a] = E := by
  unfold replayB at h
  rw [strictB_eq] at h
  obtain ⟨h0, h⟩ := andB_true h
  obtain ⟨h1, h⟩ := andB_true h
  obtain ⟨h2, h⟩ := andB_true h
  obtain ⟨h3, h4⟩ := andB_true h
  have hg : ∀ i, getT (ofT E.length E) i = E.getD i 0 := getT_ofT _ _ (Nat.le_refl _)
  have hE := nodup_of_incT (Nat.eq_of_beq_eq_true h0) h1
  have hn : 0 < E.length := Nat.blt_eq.mp h2
  have ha : E[0] = a := by
    rw [← List.getD_eq_getElem _ 0 hn, ← hg 0]
    exact Nat.eq_of_beq_eq_true h3
  have ht : E.take 1 = [a] := by
    rw [List.take_add_one, List.take_zero, List.getElem?_eq_getElem hn, ha]
    rfl
  have := bfsJ_sound mul _ cap E hg hE gs fuel 1 ds [a] hn h4
  rwa [ht] at this

end CFSG.KC.HcPack

end
