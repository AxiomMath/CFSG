module

public import Certificates.Data.Kernel.U43Twin.Wit
public import Certificates.Data.U43TwinCheck
public import CFSG.Certificates.Kernel.U43Pk.CoverSound
import CFSG.Certificates.Kernel.PackSetSound

public section

namespace CFSG.KS.U43Twin

open CFSG.KD.U43Pk CFSG.KD.U43Twin CFSG.KS.U43Pk CFSG.KC.Enum CFSG.KC.Pack
open CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43.Check Certificates.U43Twin

theorem idK_dig : Dig IDK := by
  unfold Dig
  decide +kernel

theorem powK_succ (P n : ℕ) : powK P (n + 1) = mulK P (powK P n) :=
  strictN_eq (powK P n) fun a => mulK P a

theorem powK_dig {P : ℕ} (hP : Dig P) : ∀ n, Dig (powK P n)
  | 0 => idK_dig
  | n + 1 => by
    rw [powK_succ]
    exact mulK_dig hP (powK_dig hP n)

theorem powK_lt (P : ℕ) : ∀ n, powK P n < 16 ^ 17
  | 0 => by
    change IDK < 16 ^ 17
    unfold IDK
    norm_num
  | n + 1 => by
    rw [powK_succ]
    exact mulK_lt _ _

theorem powRaw_dec {P : ℕ} (hP : Dig P) : ∀ n, powRaw (dec P) n = dec (powK P n)
  | 0 => by
    rw [powRaw.eq_1, ← idCode_eq]
    rfl
  | n + 1 => by
    rw [powRaw.eq_2, powRaw_dec hP n, powK_succ, mulRaw_dec hP (powK_dig hP n)]

theorem conjBy_dec {C X : ℕ} (hC : Dig C) (hX : Dig X) :
    conjBy (dec C) (dec X) = dec (cbK C X) := by
  unfold conjBy cbK
  rw [strictN_eq, conjT_dec hC, mulRaw_dec hC hX, mulRaw_dec (mulK_dig hC hX) (conjTK_dig C hC)]

theorem cbK_dig {C X : ℕ} (hC : Dig C) (hX : Dig X) : Dig (cbK C X) := by
  unfold cbK
  rw [strictN_eq]
  exact mulK_dig (mulK_dig hC hX) (conjTK_dig C hC)

theorem q8Elts_dec {P Q : ℕ} (hP : Dig P) (hQ : Dig Q) :
    q8Elts (dec P) (dec Q) = [dec IDK, dec P, dec (powK P 2), dec (powK P 3), dec Q, dec (mulK Q P),
      dec (mulK Q (powK P 2)), dec (mulK Q (powK P 3))] := by
  unfold q8Elts
  rw [powRaw_dec hP 2, powRaw_dec hP 3, mulRaw_dec hQ hP, mulRaw_dec hQ (powK_dig hP 2),
    mulRaw_dec hQ (powK_dig hP 3), idCode_eq]

theorem evenC_dec {W : ℕ} (hW : W < 16 ^ 17) (hd : Dig W) : evenC (dec W) = evenK W := by
  unfold evenC evenK
  rw [powRaw_dec hd 2, powRaw_dec hd 4, isZ_dec (powK_lt W 2), isZ_dec hW, isZ_dec (powK_lt W 4),
    strictB_eq, bIf_eq, band_eq, band_eq, notK_eq, notK_eq]
  by_cases h : (isZK (powK W 2) && !isZK W) = true
  · rw [if_pos h, h, Bool.true_or]
  · rw [if_neg h, Bool.not_eq_true] at *
    rw [h, Bool.false_or]

theorem neqK_spec {A1 A2 B1 B2 W : ℕ} (hA1 : Dig A1) (hA2 : Dig A2) (hB1 : Dig B1) (hB2 : Dig B2)
    (h : neqK A1 A2 B1 B2 W = true) :
    eqZ (mulRaw (dec A1) (dec A2)) (mulRaw (dec B1) (dec B2)) = false := by
  rw [mulRaw_dec hA1 hA2, mulRaw_dec hB1 hB2, eqZ_dec (mulK_dig hA1 hA2) (mulK_dig hB1 hB2)]
  unfold neqK at h
  obtain ⟨hlt, hc⟩ := bAnd_spec h
  have hW : W < 256 := Eq.mp Nat.blt_eq hlt
  simp only [strictB_eq, notK_eq, Bool.not_eq_true'] at hc
  have hp : Nat.div W 16 < 16 := by change W / 16 < 16; omega
  have hq : Nat.mod W 16 < 16 := Nat.mod_lt _ (by norm_num)
  rw [enK_eq _ _ hp, enK_eq _ _ hq, enK_eq _ _ hq, enK_eq _ _ hp] at hc
  apply Bool.eq_false_iff.2
  intro he
  have := cross_of_nrm (mulK_dig hA1 hA2) (mulK_dig hB1 hB2) (Nat.eq_of_beq_eq_true he) hp hq
  rw [this, Nat.beq_refl] at hc
  exact absurd hc (by decide)

theorem commC_false {X Y W : ℕ} (hX : Dig X) (hY : Dig Y) (h : neqK X Y Y X W = true) :
    commC (dec X) (dec Y) = false := by
  unfold commC
  exact neqK_spec hX hY hY hX h

theorem memL_of {x y : Array ℕ} {L : List (Array ℕ)} (hy : y ∈ L) (h : eqZ x y = true) :
    memL x L = true := by
  unfold memL
  exact List.any_eq_true.2 ⟨y, hy, h⟩

theorem memL_dec {X Y : ℕ} {L : List (Array ℕ)} (hX : Dig X) (hY : Dig Y) (hy : dec Y ∈ L)
    (h : Nat.beq (nrmK X) (nrmK Y) = true) : memL (dec X) L = true :=
  memL_of hy (by rw [eqZ_dec hX hY]; exact h)

theorem notK_true {b : Bool} (h : notK b = true) : b = false := by
  rw [notK_eq] at h
  simpa using h

theorem land1 (a : ℕ) : Nat.land a 1 = 0 ∨ Nat.land a 1 = 1 := by
  have : Nat.land a 1 ≤ 1 := Nat.and_le_right
  omega

theorem land_lt {a m : ℕ} : Nat.land a m < m + 1 := Nat.lt_succ_of_le Nat.and_le_right

theorem violC_of_wit {E : List (Array ℕ)} {c x y : Array ℕ} (hy : y ∈ E.map (conjBy c))
    (hn : ∀ e ∈ E, eqZ y e = false) (hx : x ∈ E) (hc : commC x y = false) : violC E c = true := by
  unfold violC
  have hm : memL y E = false := by
    unfold memL
    exact List.any_eq_false.2 fun e he h => by rw [hn e he] at h; exact absurd h (by decide)
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true]
  refine ⟨⟨y, hy, by rw [hm]; rfl⟩, Or.inl ⟨x, hx, y, hy, by rw [hc]; rfl⟩⟩

theorem invK_spec {T F W : ℕ → ℕ} {Z i : ℕ} {cands : Array (Array ℕ)} {t0 : Array ℕ}
    (hc : cands.toList = (List.range 35).map fun w => dec (F w)) (hZ : t0 = dec Z) (hZd : Dig Z)
    (hT : rawValidK (T i) = true) (h : invK T F W Z i = true) :
    (!(isZ (mulRaw (dec (T i)) (dec (T i))) && !isZ (dec (T i))) ||
      cands.toList.any fun e => rawValid e && eqZ (mulRaw e (dec (T i))) (mulRaw t0 e)) = true := by
  obtain ⟨hlt, hd, -⟩ := rawValidK_spec hT
  unfold invK at h
  rw [strictB_eq, strictB_eq, bIf_eq, band_eq, notK_eq] at h
  rw [mulRaw_dec hd hd, isZ_dec (mulK_lt _ _), isZ_dec hlt]
  by_cases hi : (isZK (mulK (T i) (T i)) && !isZK (T i)) = true
  · rw [if_pos hi] at h
    rw [strictB_eq, strictB_eq] at h
    obtain ⟨h1, h⟩ := bAnd_spec h
    obtain ⟨h2, h3⟩ := bAnd_spec h
    have hw : W i < 35 := Eq.mp Nat.blt_eq h1
    have hed := (rawValidK_spec h2).2.1
    rw [Bool.or_eq_true, hc]
    right
    refine List.any_eq_true.2 ⟨dec (F (W i)), List.mem_map.2 ⟨W i, List.mem_range.2 hw, rfl⟩, ?_⟩
    rw [rawValid_dec h2, hZ, mulRaw_dec hed hd, mulRaw_dec hZd hed,
      eqZ_dec (mulK_dig hed hd) (mulK_dig hZd hed), h3, Bool.and_self]
  · rw [Bool.not_eq_true] at hi
    rw [hi]
    rfl

theorem sqK_spec {T SP R : ℕ → ℕ} {Z i : ℕ} (hd : Dig (T i)) (hZ : Dig Z)
    (h : sqK T SP R Z i = true) (hs : eqZ (mulRaw (dec (T i)) (dec (T i))) (dec Z) = true) :
    ∃ k < 96, R k = i := by
  rw [mulRaw_dec hd hd, eqZ_dec (mulK_dig hd hd) hZ] at hs
  unfold sqK at h
  rw [strictB_eq, bIf_eq, if_pos hs, strictB_eq] at h
  obtain ⟨h1, h⟩ := bAnd_spec h
  obtain ⟨h2, h3⟩ := bAnd_spec h
  have e1 : 0 < SP i := Eq.mp Nat.blt_eq h1
  have e2 : SP i < 97 := Eq.mp Nat.blt_eq h2
  exact ⟨SP i - 1, by omega, Nat.eq_of_beq_eq_true h3⟩

theorem sqpK_spec {T R : ℕ → ℕ} {X : ℕ → ℕ → ℕ} {C Z k : ℕ} (h : sqpK T R X C Z k = true) :
    R k < 1024 ∧ X 0 k = powK (T (R k)) 2 ∧ X 1 k = powK (T (R k)) 3 ∧
      X 2 k = mulK Z (T (R k)) ∧ X 3 k = cbK C (T (R k)) := by
  unfold sqpK at h
  rw [strictB_eq] at h
  obtain ⟨h1, h⟩ := bAnd_spec h
  rw [strictB_eq] at h
  obtain ⟨h2, h⟩ := bAnd_spec h
  obtain ⟨h3, h⟩ := bAnd_spec h
  obtain ⟨h4, h5⟩ := bAnd_spec h
  have e2 := Nat.eq_of_beq_eq_true h2
  refine ⟨Eq.mp Nat.blt_eq h1, e2, ?_, Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5⟩
  rw [Nat.eq_of_beq_eq_true h3, powK_succ, e2]

theorem q8pK_spec {T R : ℕ → ℕ} {X EL : ℕ → ℕ → ℕ} {w k l C Z : ℕ} {E1 E2 cands : List (Array ℕ)}
    {t0 c : Array ℕ} (hi : rawValidK (T (R k)) = true) (hj : rawValidK (T (R l)) = true)
    (hk : sqpK T R X C Z k = true) (hl : sqpK T R X C Z l = true) (hZ : t0 = dec Z) (hZd : Dig Z)
    (hc : c ∈ cands) (hcC : c = dec C) (hCd : Dig C)
    (hE1 : ∀ u < 8, Dig (EL 0 u) ∧ dec (EL 0 u) ∈ E1) (hE2 : ∀ u < 8, Dig (EL 1 u) ∧ dec (EL 1 u) ∈ E2)
    (h : q8pK T R X EL w k l = true) :
    (!eqZ (mulRaw (dec (T (R l))) (dec (T (R k))))
        (mulRaw (mulRaw t0 (dec (T (R k)))) (dec (T (R l)))) ||
      (memL (dec (T (R k))) E1 && memL (dec (T (R l))) E1) ||
      (memL (dec (T (R k))) E2 && memL (dec (T (R l))) E2) ||
      cands.any fun c => violC (q8Elts (dec (T (R k))) (dec (T (R l)))) c) = true := by
  obtain ⟨-, x0, x1, x2, x3⟩ := sqpK_spec hk
  obtain ⟨-, -, -, -, y3⟩ := sqpK_spec hl
  set Pi := T (R k)
  set Pj := T (R l)
  have di := (rawValidK_spec hi).2.1
  have dj := (rawValidK_spec hj).2.1
  unfold q8pK at h
  rw [strictB_eq, strictB_eq, strictB_eq, bIf_eq] at h
  simp only [Bool.or_eq_true]
  by_cases t0' : Nat.beq (fld(w, 0, 3)) 0 = true
  · rw [if_pos t0', x2] at h
    have := neqK_spec dj di (mulK_dig hZd di) dj h
    rw [hZ, mulRaw_dec hZd di, this]
    simp
  rw [if_neg t0', bIf_eq] at h
  by_cases t1 : Nat.beq (fld(w, 0, 3)) 1 = true
  · rw [if_pos t1, strictB_eq] at h
    obtain ⟨h1, h2⟩ := bAnd_spec h
    have hu := land_lt (a := Nat.shiftRight w 3) (m := 7)
    have hv := land_lt (a := Nat.shiftRight w 6) (m := 7)
    rcases land1 (Nat.shiftRight w 2) with hs | hs <;> rw [hs] at h1 h2
    · obtain ⟨d1, m1⟩ := hE1 (fld(w, 3, 7)) (by omega)
      obtain ⟨d2, m2⟩ := hE1 (fld(w, 6, 7)) (by omega)
      left; left; right
      rw [Bool.and_eq_true]
      exact ⟨memL_dec di d1 m1 h1, memL_dec dj d2 m2 h2⟩
    · obtain ⟨d1, m1⟩ := hE2 (fld(w, 3, 7)) (by omega)
      obtain ⟨d2, m2⟩ := hE2 (fld(w, 6, 7)) (by omega)
      left; right
      rw [Bool.and_eq_true]
      exact ⟨memL_dec di d1 m1 h1, memL_dec dj d2 m2 h2⟩
  rw [if_neg t1] at h
  obtain ⟨-, h⟩ := bAnd_spec h
  right
  refine List.any_eq_true.2 ⟨c, hc, ?_⟩
  rw [x0, x1] at h
  have p2 := powK_dig di 2
  have p3 := powK_dig di 3
  have fi := cbK_dig hCd di
  have fj := cbK_dig hCd dj
  generalize hFa : nIf(Nat.beq (fld(w, 2, 1)) 1, X 3 l, X 3 k) = Fa at h
  generalize hEb : nIf(Nat.beq (fld(w, 3, 1)) 1, Pj, Pi) = Eb at h
  have hF : (Fa = cbK C Pi ∨ Fa = cbK C Pj) := by
    rw [← hFa, x3, y3]
    cases Nat.beq (fld(w, 2, 1)) 1
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hE : (Eb = Pi ∨ Eb = Pj) := by
    rw [← hEb]
    cases Nat.beq (fld(w, 3, 1)) 1
    · exact Or.inl rfl
    · exact Or.inr rfl
  have dF : Dig Fa := by
    rcases hF with e | e
    · rw [e]
      exact fi
    · rw [e]
      exact fj
  have dE : Dig Eb := by
    rcases hE with e | e
    · rw [e]
      exact di
    · rw [e]
      exact dj
  unfold vioK at h
  simp only [strictB_eq] at h
  obtain ⟨n0, h⟩ := bAnd_spec h
  obtain ⟨n1, h⟩ := bAnd_spec h
  obtain ⟨n2, h⟩ := bAnd_spec h
  obtain ⟨n3, h⟩ := bAnd_spec h
  obtain ⟨n4, h⟩ := bAnd_spec h
  obtain ⟨n5, h⟩ := bAnd_spec h
  obtain ⟨n6, h⟩ := bAnd_spec h
  obtain ⟨n7, hn⟩ := bAnd_spec h
  rw [hcC, q8Elts_dec di dj]
  apply violC_of_wit (y := dec Fa) (x := dec Eb)
  · rw [List.mem_map]
    rcases hF with e | e
    · exact ⟨dec Pi, by simp, by rw [conjBy_dec hCd di, e]⟩
    · exact ⟨dec Pj, by simp, by rw [conjBy_dec hCd dj, e]⟩
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [eqZ_dec dF idK_dig]; exact notK_true n0
    · rw [eqZ_dec dF di]; exact notK_true n1
    · rw [eqZ_dec dF p2]; exact notK_true n2
    · rw [eqZ_dec dF p3]; exact notK_true n3
    · rw [eqZ_dec dF dj]; exact notK_true n4
    · rw [eqZ_dec dF (mulK_dig dj di)]; exact notK_true n5
    · rw [eqZ_dec dF (mulK_dig dj p2)]; exact notK_true n6
    · rw [eqZ_dec dF (mulK_dig dj p3)]; exact notK_true n7
  · rcases hE with e | e <;> rw [e] <;> simp
  · exact commC_false dE dF hn

theorem permK_spec {T W : ℕ → ℕ} {EL : ℕ → ℕ → ℕ} {P1 Q1 i : ℕ} {E1 E2 : List (Array ℕ)}
    (hT : rawValidK (T i) = true) (hP1 : Dig P1) (hQ1 : Dig Q1)
    (hE1 : ∀ u < 8, Dig (EL 0 u) ∧ dec (EL 0 u) ∈ E1) (hE2 : ∀ u < 8, Dig (EL 1 u) ∧ dec (EL 1 u) ∈ E2)
    (h : permK T W EL P1 Q1 i = true) :
    (invertC (dec (T i)) &&
      ((memL (conjBy (dec (T i)) (dec P1)) E1 && memL (conjBy (dec (T i)) (dec Q1)) E1) ||
        (memL (conjBy (dec (T i)) (dec P1)) E2 && memL (conjBy (dec (T i)) (dec Q1)) E2))) = true := by
  have hd := (rawValidK_spec hT).2.1
  have hH := conjTK_dig _ hd
  unfold permK at h
  rw [strictB_eq, strictB_eq, strictB_eq] at h
  obtain ⟨h1, h⟩ := bAnd_spec h
  obtain ⟨h2, h⟩ := bAnd_spec h
  rw [strictB_eq] at h
  obtain ⟨h3, h4⟩ := bAnd_spec h
  have c1 : conjBy (dec (T i)) (dec P1) = dec (mulK (mulK (T i) P1) (conjTK (T i))) := by
    rw [conjBy_dec hd hP1]
    unfold cbK
    rw [strictN_eq]
  have c2 : conjBy (dec (T i)) (dec Q1) = dec (mulK (mulK (T i) Q1) (conjTK (T i))) := by
    rw [conjBy_dec hd hQ1]
    unfold cbK
    rw [strictN_eq]
  have d1 := mulK_dig (mulK_dig hd hP1) hH
  have d2 := mulK_dig (mulK_dig hd hQ1) hH
  have hu := land_lt (a := Nat.shiftRight (W i) 1) (m := 7)
  have hv := land_lt (a := Nat.shiftRight (W i) 4) (m := 7)
  unfold invertC
  rw [conjT_dec hd, rawValid_dec hT, rawValid_dec h1, mulRaw_dec hd hH, isZ_dec (mulK_lt _ _), h2,
    c1, c2]
  simp only [Bool.true_and, Bool.or_eq_true, Bool.and_eq_true]
  rcases land1 (Nat.shiftRight (W i) 0) with hs | hs <;> rw [hs] at h3 h4
  · obtain ⟨e1, m1⟩ := hE1 (fld(W i, 1, 7)) (by omega)
    obtain ⟨e2, m2⟩ := hE1 (fld(W i, 4, 7)) (by omega)
    exact Or.inl ⟨memL_dec d1 e1 m1 h3, memL_dec d2 e2 m2 h4⟩
  · obtain ⟨e1, m1⟩ := hE2 (fld(W i, 1, 7)) (by omega)
    obtain ⟨e2, m2⟩ := hE2 (fld(W i, 4, 7)) (by omega)
    exact Or.inr ⟨memL_dec d1 e1 m1 h3, memL_dec d2 e2 m2 h4⟩

theorem halfK_spec {P A B w : ℕ} {L : ℕ → ℕ} {Ls : List (Array ℕ)} (hP : Dig P) (hA : Dig A)
    (hB : Dig B) (hL : ∀ v < 24, Dig (L v) ∧ dec (L v) ∈ Ls) (h : halfK P A B L w = true) :
    (!(commC (dec P) (dec A) && commC (dec P) (dec B)) || memL (dec P) Ls) = true := by
  unfold halfK at h
  rw [strictB_eq, strictB_eq, bIf_eq] at h
  by_cases t0 : Nat.beq (fld(w, 0, 3)) 0 = true
  · rw [if_pos t0] at h
    obtain ⟨h1, h2⟩ := bAnd_spec h
    obtain ⟨d, m⟩ := hL _ (Eq.mp Nat.blt_eq h1)
    rw [memL_dec hP d m h2, Bool.or_true]
  rw [if_neg t0, bIf_eq] at h
  by_cases t1 : Nat.beq (fld(w, 0, 3)) 1 = true
  · rw [if_pos t1] at h
    rw [commC_false hP hA h]
    rfl
  · rw [if_neg t1] at h
    rw [commC_false hP hB h, Bool.and_false]
    rfl

theorem oddK_spec {T W G : ℕ → ℕ} {i : ℕ} {Gs : List (Array ℕ)} (hT : rawValidK (T i) = true)
    (hG : ∀ g < 16, Dig (G g) ∧ dec (G g) ∈ Gs) (h : oddK T W G i = true) :
    (isZ (dec (T i)) || !isZ (powRaw (dec (T i)) 9) ||
      Gs.any fun g => evenC (mulRaw (mulRaw (mulRaw (dec (T i)) g) (powRaw (dec (T i)) 8))
        (powRaw g 3))) = true := by
  obtain ⟨hlt, hd, -⟩ := rawValidK_spec hT
  unfold oddK at h
  rw [strictB_eq, bIf_eq] at h
  rw [isZ_dec hlt]
  by_cases z : isZK (T i) = true
  · rw [z]
    rfl
  rw [if_neg z, strictB_eq, bIf_eq] at h
  rw [Bool.not_eq_true] at z
  have e9 : powK (T i) 9 = mulK (T i) (powK (T i) 8) := powK_succ _ 8
  rw [z, Bool.false_or, powRaw_dec hd 9, e9, isZ_dec (mulK_lt _ _)]
  by_cases z9 : isZK (mulK (T i) (powK (T i) 8)) = true
  · rw [if_pos z9, strictB_eq] at h
    obtain ⟨h1, h⟩ := bAnd_spec h
    rw [strictB_eq] at h
    obtain ⟨dg, mg⟩ := hG _ (Eq.mp Nat.blt_eq h1)
    rw [z9, Bool.not_true, Bool.false_or]
    refine List.any_eq_true.2 ⟨_, mg, ?_⟩
    have d8 := powK_dig hd 8
    rw [powRaw_dec hd 8, powRaw_dec dg 3, mulRaw_dec hd dg, mulRaw_dec (mulK_dig hd dg) d8,
      mulRaw_dec (mulK_dig (mulK_dig hd dg) d8) (powK_dig dg 3),
      evenC_dec (mulK_lt _ _) (mulK_dig (mulK_dig (mulK_dig hd dg) d8) (powK_dig dg 3))]
    exact h
  · rw [Bool.not_eq_true] at z9
    rw [z9]
    rfl

end CFSG.KS.U43Twin

end
