module

public import Certificates.Data.Kernel.U43.Defs
public import CFSG.Certificates.Kernel.Misc.PermG2USound
public import CFSG.Certificates.Kernel.G2Three.Tables
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U43Code

public section

namespace CFSG.KC.U43

open CFSG.KC.Loop CFSG.KC.Misc.G2U CFSG.KD.U43 CFSG.RankThree.PartTwo.Sec4.Item434RemU43
  CFSG.KC.G2Three

@[expose] def Dat (c : List ℕ) (C : ℕ) : Prop := canon4 c = true ∧ codes9 c = C

theorem canon4_iff {c : List ℕ} : canon4 c = true ↔ c.length = 16 ∧ ∀ x ∈ c, x < 9 := by
  simp [canon4]

theorem lt16 {c : List ℕ} (h : canon4 c = true) : ∀ x ∈ c, x < 2 ^ 4 := fun x hx => by
  have := (canon4_iff.1 h).2 x hx
  omega

theorem e4_codes9 {c : List ℕ} (h : ∀ x ∈ c, x < 2 ^ 4) (k : ℕ) :
    e4 (codes9 c) k = c.getD k 0 := by
  rw [e4, fldN_eq, codes9_eq]
  exact fld_pk h k

theorem M4_eq (x y : ℕ) : M4 x y = bld 4 (fun k => ent4 x y (k / 4) (k % 4)) 16 := rfl

theorem M4_codes9 {m n : List ℕ} (hm : canon4 m = true) (hn : canon4 n = true) :
    M4 (codes9 m) (codes9 n) = codes9 (mul4 m n) := by
  rw [M4_eq, bld_eq, codes9_eq (mul4 m n)]
  congr 1
  simp only [mul4]
  refine List.map_congr_left fun k _ => ?_
  simp only [ent4, e4_codes9 (lt16 hm), e4_codes9 (lt16 hn), Array.getD_eq_getD_getElem?,
    List.getElem?_toArray, List.getD_eq_getElem?_getD]
  rfl

theorem inj4 {a b : List ℕ} (ha : canon4 a = true) (hb : canon4 b = true)
    (h : codes9 a = codes9 b) : a = b := by
  rw [codes9_eq, codes9_eq] at h
  exact pk_inj (lt16 ha) (lt16 hb) (by rw [(canon4_iff.1 ha).1, (canon4_iff.1 hb).1]) h

theorem mulD {a b : List ℕ} {A B : ℕ} (ha : Dat a A) (hb : Dat b B) :
    Dat (mul4 a b) (M4 A B) :=
  ⟨canon4_mul4 a b, by rw [← ha.2, ← hb.2, M4_codes9 ha.1 hb.1]⟩

theorem beqD {a b : List ℕ} {A B : ℕ} (ha : Dat a A) (hb : Dat b B) :
    (a == b) = Nat.beq A B := by
  apply Bool.eq_iff_iff.2
  rw [beq_iff_eq, Nat.beq_eq, ← ha.2, ← hb.2]
  exact ⟨fun h => h ▸ rfl, inj4 ha.1 hb.1⟩

theorem oneD : Dat one4 ONE4 := ⟨canon4_one4, rfl⟩

theorem commD {a b : List ℕ} {A B : ℕ} (ha : Dat a A) (hb : Dat b B) :
    commutes4 a b = Nat.beq (M4 A B) (M4 B A) :=
  beqD (mulD ha hb) (mulD hb ha)

theorem cubeD {a : List ℕ} {A : ℕ} (ha : Dat a A) :
    (cube4 a == one4) = Nat.beq (M4 A (M4 A A)) ONE4 :=
  beqD (mulD ha (mulD ha ha)) oneD

theorem canon4_letterCode (l : ℕ) : canon4 (letterCode l) = true := by
  unfold letterCode
  split_ifs <;> decide

theorem letD {A : ℕ → ℕ} (hA : lettersK A = true) (l : ℕ) : Dat (letterCode l) (letP A l) := by
  have h4 := allBelow_g2 hA (by decide)
  have hs : ∀ s < 4, Dat (letterCode s) (A s) := fun s hs =>
    ⟨canon4_letterCode s, Nat.eq_of_beq_eq_true (h4 s hs)⟩
  unfold letP
  by_cases hl : l < 3
  · rw [Nat.blt_eq.mpr hl, cond_true]
    exact hs l (by omega)
  · have hb : Nat.blt l 3 = false := by
      cases hq : Nat.blt l 3
      · rfl
      · exact absurd (Nat.blt_eq.mp hq) hl
    rw [hb, cond_false]
    have e : letterCode l = letterCode 3 := by
      unfold letterCode
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rfl
    rw [e]
    exact hs 3 (by omega)

theorem foldD {A : ℕ → ℕ} (hA : lettersK A = true) :
    ∀ (w : List ℕ) (acc : List ℕ) (C : ℕ), Dat acc C →
      Dat (w.foldl (fun c l => mul4 c (letterCode l)) acc)
        (w.foldl (fun c l => M4 c (letP A l)) C)
  | [], _, _, h => h
  | l :: w, acc, C, h => foldD hA w _ _ (mulD h (letD hA l))

theorem wordD {A : ℕ → ℕ} (hA : lettersK A = true) (w : List ℕ) :
    Dat (wordCode w) (wordP A w) :=
  foldD hA w one4 ONE4 oneD

theorem conjD {A : ℕ → ℕ} (hA : lettersK A = true) (w : List ℕ) {x : List ℕ} {X : ℕ}
    (hx : Dat x X) :
    Dat (conjStep (wordPair w) x) (M4 (M4 (wordP A w) X) (wordP A (invWord w))) := by
  have hw := wordD hA w
  have hl : (wordCode w).length = 16 := (canon4_iff.1 hw.1).1
  unfold conjStep wordPair
  rw [List.take_left' hl, List.drop_left' hl]
  exact mulD (mulD hw hx) (wordD hA (invWord w))

theorem build_par {X G : ℕ → ℕ} {K : ℕ} {gens : List (List ℕ)}
    (hg : ∀ s < K, Dat (gens.getD s one4) (G s)) :
    ∀ (par : List (ℕ × ℕ)) (acc : Array (List ℕ)) (i : ℕ), acc.size = i + 1 →
      (∀ t < i + 1, Dat (acc.getD t one4) (X t)) → parK X G K par i = true →
      (par.foldl (fun acc ps => acc.push (mul4 (acc.getD ps.1 one4) (gens.getD ps.2 one4)))
          acc).size = i + 1 + par.length ∧
        ∀ t < i + 1 + par.length,
          Dat ((par.foldl (fun acc ps => acc.push (mul4 (acc.getD ps.1 one4)
            (gens.getD ps.2 one4))) acc).getD t one4) (X t)
  | [], acc, i, hs, hd, _ => by
    simp only [List.foldl_nil, List.length_nil, Nat.add_zero]
    exact ⟨hs, hd⟩
  | ps :: par, acc, i, hs, hd, h => by
    have h' : Bool.rec (motive := fun _ => Bool) false (parK X G K par (i + 1))
        (Nat.ble ps.1 i && Nat.blt ps.2 K && Nat.beq (X (i + 1)) (M4 (X ps.1) (G ps.2))) =
        true := h
    obtain ⟨h1, h2⟩ := bAnd_g2 h'
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.beq_eq] at h1
    obtain ⟨⟨hp, hsK⟩, hx⟩ := h1
    have hnew : Dat (mul4 (acc.getD ps.1 one4) (gens.getD ps.2 one4)) (X (i + 1)) := by
      rw [hx]
      exact mulD (hd _ (by omega)) (hg _ hsK)
    have ih := build_par hg par
      (acc.push (mul4 (acc.getD ps.1 one4) (gens.getD ps.2 one4))) (i + 1)
      (by rw [Array.size_push, hs]) (fun t ht => by
        rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | ht
        · rw [getD_push_lt one4 (by rw [hs]; exact ht)]
          exact hd t ht
        · rw [ht, ← hs, getD_push_eq]
          rw [hs]
          exact hnew) h2
    rw [List.foldl_cons, List.length_cons]
    exact ⟨by rw [ih.1]; omega, fun t ht => ih.2 t (by omega)⟩

theorem close_at4 {X G POS : ℕ → ℕ} {n k hi : ℕ} (h : closeU X G POS n k hi = true)
    (hm : n * k ≤ 64 * hi) :
    ∀ i < n * k, POS i < n ∧ X (POS i) = M4 (X (i / k)) (G (i % k)) := by
  intro i hi'
  have := allBelow_g2 h hm i hi'
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at this
  exact this

end CFSG.KC.U43

end
