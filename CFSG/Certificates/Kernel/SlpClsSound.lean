module

public import Certificates.Data.Kernel.SlpCls
public import CFSG.Certificates.Kernel.SlpPcSound
public import CFSG.LocalAnalysis.StandardType.GGSporKRestClassesCl
public import CFSG.Certificates.Kernel.Fam.Lin

public section

namespace CFSG.KS.SlpCls

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KC.SlpPc
open CFSG CFSG.StandardType CFSG.Assembly CFSG.StandardType.SporadicShape

abbrev Mat (q d : ℕ) := Matrix (Fin d) (Fin d) (ZMod q)

@[expose] def wM {M : Type} [Monoid M] (R : ℕ → M) (sg w : List ℕ) : M :=
  (w.map fun l => R (sg.getD l 0)).prod

structure ClsFacts {q d : ℕ} (MA MB : Mat q d) (p k t rx : ℕ) (sg tb cb : List ℕ)
    (ent : List (ℕ × (List ℕ × List ℕ))) (R : ℕ → Mat q d) : Prop where
  reg : ∀ r, R r ∈ Submonoid.closure ({MA, MB} : Set (Mat q d))
  r0 : R 0 = 1
  ne : R rx ≠ 1
  pow : R rx ^ p = 1
  tr : (R rx).trace = (t : ZMod q)
  tpos : 0 < tb.length
  t0 : R (tb.getD 0 0) = 1
  mulT : ∀ i < tb.length, ∀ j < sg.length, ∃ c < tb.length,
    R (tb.getD i 0) * R (sg.getD j 0) = R (tb.getD c 0)
  powT : ∀ i < tb.length, cb.getD i 0 < tb.length ∧
    R (tb.getD i 0) ^ p = R (tb.getD (cb.getD i 0) 0)
  itT : ∀ i < tb.length, (fun j => cb.getD j 0)^[k] i = 0
  entF : ∀ e ∈ ent, R rx * R e.1 = R e.1 * wM R sg e.2.1 ∧
    ∀ z ∈ e.2.2, R z * wM R sg e.2.1 = wM R sg e.2.1 * R z
  seeds : MA ∈ Submonoid.closure ({Y | ∃ s ∈ sg, Y = R s} ∪
      {Y | ∃ z ∈ ent.flatMap (·.2.2), Y = R z}) ∧
    MB ∈ Submonoid.closure ({Y | ∃ s ∈ sg, Y = R s} ∪ {Y | ∃ z ∈ ent.flatMap (·.2.2), Y = R z})

theorem slc_sB (y : ℕ) (k : ℕ → Bool) : sB y k = k y := by cases y <;> rfl

theorem slc_strictN (y : ℕ) (k : ℕ → ℕ) : CFSG.KC.Loop.strictN y k = k y := by cases y <;> rfl

theorem slc_and {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem slc_not {a : Bool} : notB a = true ↔ a = false := by cases a <;> decide

theorem slc_nthD {α : Type} (d : α) : ∀ (l : List α) (i : ℕ), nthD d l i = l.getD i d
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => by
    rw [List.getD_cons_succ, ← slc_nthD d l i]
    rfl

theorem slc_tl (c : List ℕ) (j : ℕ) : (tl c).getD j 0 = c.getD (j + 1) 0 := by
  cases c with
  | nil => rfl
  | cons a c => rw [List.getD_cons_succ]; rfl

theorem slc_mapS {α : Type} (f : α → ℕ) : ∀ (l : List α) (k : List ℕ → Bool),
    mapS f l k = k (l.map f)
  | [], _ => rfl
  | a :: l, k => by
    have e : mapS f (a :: l) k = sB (f a) (fun x => mapS f l fun xs => k (x :: xs)) := rfl
    rw [e]
    simp only [slc_sB, slc_mapS f l, List.map_cons]

theorem slc_revOnto : ∀ (l acc : List ℕ), revOnto l acc = l.reverse ++ acc
  | [], _ => rfl
  | x :: l, acc => by
    have e : revOnto (x :: l) acc = revOnto l (x :: acc) := rfl
    rw [e, slc_revOnto l]
    simp

theorem slc_lenN : ∀ l : List ℕ, lenN l = l.length
  | [] => rfl
  | _ :: l => by
    have e : lenN (List.cons 0 l) = Nat.succ (lenN l) := rfl
    rw [List.length_cons, ← slc_lenN l]
    rfl

theorem slc_zsE : ∀ es : List (ℕ × (List ℕ × List ℕ)), zsE es = es.flatMap (·.2.2)
  | [] => rfl
  | e :: es => by
    have h : zsE (e :: es) = revOnto (revOnto e.2.2 []) (zsE es) := rfl
    rw [h, slc_revOnto, slc_revOnto, slc_zsE es]
    simp

theorem slc_itN (cb : List ℕ) (i : ℕ) : ∀ k, itN cb k i = (fun j => cb.getD j 0)^[k] i
  | 0 => rfl
  | k + 1 => by
    have e : itN cb (k + 1) i = nthD 0 cb (itN cb k i) := rfl
    rw [e, slc_nthD, slc_itN cb i k, Function.iterate_succ_apply']

theorem slc_bitsN (x o m : ℕ) : bitsN x o m = x / 2 ^ o % 2 ^ m := by
  have e : bitsN x o m = (x >>> o) &&& (1 <<< m - 1) := rfl
  rw [e, Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem slc_trL (w S X : ℕ) :
    ∀ n, trL w S n X = ∑ i ∈ Finset.range n, X / 2 ^ (S * i + w * i) % 2 ^ w
  | 0 => by rw [Finset.sum_range_zero]; rfl
  | n + 1 => by
    have e : trL w S (n + 1) X = trL w S n X + bitsN X (S * n + w * n) w := rfl
    rw [e, slc_trL w S X n, Finset.sum_range_succ, slc_bitsN]

theorem slc_getD_map {f : ℕ → ℕ} {l : List ℕ} {i : ℕ} (hi : i < l.length) (a b : ℕ) :
    (l.map f).getD i a = f (l.getD i b) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi, List.getElem_map]

theorem slc_getD_P {α : Type} {P : α → Prop} {d : α} (hd : P d) {l : List α}
    (hl : ∀ x ∈ l, P x) (i : ℕ) : P (l.getD i d) := by
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact hl _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact hd

@[expose] def slcAll (P : ℕ → Prop) (bl : List (List ℕ)) (cur : List ℕ) : Prop :=
  (∀ b ∈ bl, ∀ x ∈ b, P x) ∧ ∀ x ∈ cur, P x

theorem slc_lk_P {P : ℕ → Prop} {ONE : ℕ} (h1 : P ONE) {bl : List (List ℕ)} {cur : List ℕ}
    (h : slcAll P bl cur) (n r : ℕ) : P (lk ONE bl cur n r) := by
  unfold lk
  cases Nat.beq (Nat.shiftRight r 6) (Nat.shiftRight n 6)
  · simp only [slc_nthD]
    exact slc_getD_P h1 (slc_getD_P (P := fun b : List ℕ => ∀ x ∈ b, P x)
      (fun x hx => absurd hx List.not_mem_nil) h.1 _) _
  · simp only [slc_nthD]
    exact slc_getD_P h1 h.2 _

@[expose] def slcZ (ONE : ℕ) (bl : List (List ℕ)) (cur : List ℕ) (n : ℕ) : Prop :=
  0 < n ∧ bl.length = n / 64 ∧ cur.length = n % 64 ∧ (n < 64 → cur.getD (n - 1) ONE = ONE) ∧
    (64 ≤ n → (bl.getD (n / 64 - 1) []).getD 63 ONE = ONE)

theorem slc_lk0 {ONE : ℕ} {bl : List (List ℕ)} {cur : List ℕ} {n : ℕ} (h : slcZ ONE bl cur n) :
    lk ONE bl cur n 0 = ONE := by
  obtain ⟨h0, -, -, h1, h2⟩ := h
  have e1 : Nat.shiftRight 0 6 = 0 := rfl
  have e2 : Nat.shiftRight n 6 = n / 64 := by
    change n >>> 6 = _
    rw [Nat.shiftRight_eq_div_pow]
  unfold lk
  rw [e1, e2]
  by_cases hn : n < 64
  · have hz : n / 64 = 0 := Nat.div_eq_of_lt hn
    rw [hz, Nat.beq_refl]
    change nthD ONE cur (Nat.sub (Nat.sub n 1) 0) = ONE
    rw [slc_nthD, Nat.sub_eq, Nat.sub_eq, Nat.sub_zero]
    exact h1 hn
  · have hz : Nat.beq 0 (n / 64) = false :=
      Bool.eq_false_iff.2 fun e => by have := Nat.eq_of_beq_eq_true e; omega
    rw [hz]
    change nthD ONE (nthD [] bl (Nat.sub (Nat.sub (n / 64) 0) 1)) (Nat.sub 63 (Nat.land 0 63)) = ONE
    rw [slc_nthD, slc_nthD]
    have e3 : Nat.sub (Nat.sub (n / 64) 0) 1 = n / 64 - 1 := by simp
    have e4 : Nat.sub 63 (Nat.land 0 63) = 63 := rfl
    rw [e3, e4]
    exact h2 (by omega)

theorem slc_push {ONE : ℕ} {bl : List (List ℕ)} {cur : List ℕ} {n : ℕ} {x : ℕ}
    (h : slcZ ONE bl cur n) :
    (Nat.beq (Nat.land (n + 1) 63) 0 = false → slcZ ONE bl (x :: cur) (n + 1)) ∧
    (Nat.beq (Nat.land (n + 1) 63) 0 = true → slcZ ONE ((x :: cur) :: bl) [] (n + 1)) := by
  obtain ⟨h0, hbl, hcur, h1, h2⟩ := h
  have hl : Nat.land (n + 1) 63 = (n + 1) % 64 := by
    change (n + 1) &&& (2 ^ 6 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod]
  rw [hl]
  constructor
  · intro hb
    have hm : (n + 1) % 64 ≠ 0 := fun e => by rw [e] at hb; exact Bool.noConfusion hb
    refine ⟨by omega, by rw [hbl]; omega, by rw [List.length_cons, hcur]; omega, fun hn => ?_,
      fun hn => ?_⟩
    · have hn' : n < 64 := by omega
      have e : n + 1 - 1 = (n - 1) + 1 := by omega
      rw [e, List.getD_cons_succ]
      exact h1 hn'
    · have hn' : 64 ≤ n := by omega
      have e : (n + 1) / 64 = n / 64 := by omega
      rw [e]
      exact h2 hn'
  · intro hb
    have hm : (n + 1) % 64 = 0 := Nat.eq_of_beq_eq_true hb
    refine ⟨by omega, by rw [List.length_cons, hbl]; omega, by rw [List.length_nil]; omega,
      fun hn => absurd hm (by omega), fun _ => ?_⟩
    by_cases hn : n < 64
    · have e : (n + 1) / 64 - 1 = 0 := by omega
      have e2 : (63 : ℕ) = (n - 1) + 1 := by omega
      rw [e, List.getD_cons_zero, e2, List.getD_cons_succ]
      exact h1 hn
    · have e : (n + 1) / 64 - 1 = (n / 64 - 1) + 1 := by omega
      rw [e, List.getD_cons_succ]
      exact h2 (by omega)

theorem slc_runP {mul : ℕ → ℕ → ℕ} {ONE : ℕ} {Q : List (List ℕ) → List ℕ → ℕ → Prop}
    (hA : ∀ bl cur n (q : ℕ × ℕ), Q bl cur n → Nat.beq (Nat.land (n + 1) 63) 0 = false →
      Q bl (mul (lk ONE bl cur n q.1) (lk ONE bl cur n q.2) :: cur) (n + 1))
    (hB : ∀ bl cur n (q : ℕ × ℕ), Q bl cur n → Nat.beq (Nat.land (n + 1) 63) 0 = true →
      Q ((mul (lk ONE bl cur n q.1) (lk ONE bl cur n q.2) :: cur) :: bl) [] (n + 1)) :
    ∀ (prg : List (ℕ × ℕ)) (bl : List (List ℕ)) (cur : List ℕ) (n : ℕ)
      (k : List (List ℕ) → List ℕ → ℕ → Bool), Q bl cur n →
      runP mul ONE prg bl cur n k = true → ∃ bl' cur' n', Q bl' cur' n' ∧ k bl' cur' n' = true
  | [], bl, cur, n, k, hQ, h => ⟨bl, cur, n, hQ, h⟩
  | q :: prg, bl, cur, n, k, hQ, h => by
    have e : runP mul ONE (q :: prg) bl cur n k =
        sB (mul (lk ONE bl cur n q.1) (lk ONE bl cur n q.2)) (fun x =>
          Bool.rec (motive := fun _ => Bool) (runP mul ONE prg bl (List.cons x cur) (Nat.succ n) k)
            (runP mul ONE prg (List.cons (List.cons x cur) bl) List.nil (Nat.succ n) k)
            (Nat.beq (Nat.land (Nat.succ n) 63) 0)) := rfl
    rw [e, slc_sB] at h
    cases hb : Nat.beq (Nat.land (Nat.succ n) 63) 0
    · rw [hb] at h
      exact slc_runP hA hB prg _ _ _ k (hA bl cur n q hQ hb) h
    · rw [hb] at h
      exact slc_runP hA hB prg _ _ _ k (hB bl cur n q hQ hb) h

theorem slc_pw1 {M : Type} [Monoid M] {mul : ℕ → ℕ → ℕ} {OM : ℕ → M} {C : ℕ → Prop}
    (hm : ∀ a b, C a → C b → C (mul a b) ∧ OM (mul a b) = OM a * OM b) {X : ℕ} (hX : C X) :
    ∀ n, C (pw1 mul X n) ∧ OM (pw1 mul X n) = OM X ^ (n + 1)
  | 0 => ⟨hX, by rw [Nat.zero_add, pow_one]; rfl⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := slc_pw1 hm hX n
    have e : pw1 mul X (n + 1) = mul (pw1 mul X n) X := rfl
    obtain ⟨h3, h4⟩ := hm _ _ h1 hX
    rw [e]
    exact ⟨h3, by rw [h4, h2, ← pow_succ]⟩

theorem slc_wordGo {M : Type} [Monoid M] {mul : ℕ → ℕ → ℕ} {OM : ℕ → M} {C : ℕ → Prop}
    (hm : ∀ a b, C a → C b → C (mul a b) ∧ OM (mul a b) = OM a * OM b) {R : ℕ → ℕ}
    (hR : ∀ l, C (R l)) : ∀ (w : List ℕ) (acc : ℕ), C acc →
      C (wordGo mul R w acc) ∧ OM (wordGo mul R w acc) = OM acc * (w.map fun l => OM (R l)).prod
  | [], acc, h => ⟨h, by rw [List.map_nil, List.prod_nil, mul_one]; rfl⟩
  | l :: w, acc, h => by
    have e : wordGo mul R (l :: w) acc = CFSG.KC.Loop.strictN (mul acc (R l)) (wordGo mul R w) :=
      rfl
    obtain ⟨h1, h2⟩ := hm _ _ h (hR l)
    obtain ⟨h3, h4⟩ := slc_wordGo hm hR w _ h1
    rw [e, slc_strictN]
    exact ⟨h3, by rw [h4, h2, List.map_cons, List.prod_cons, mul_assoc]⟩

theorem slc_commOK {mul : ℕ → ℕ → ℕ} {R : ℕ → ℕ} {y : ℕ} : ∀ zs : List ℕ,
    commOK mul R y zs = true → ∀ z ∈ zs, mul (R z) y = mul y (R z)
  | [], _, z, hz => absurd hz List.not_mem_nil
  | z :: zs, h, z', hz' => by
    have e : commOK mul R y (z :: zs) =
        andB (Nat.beq (mul (R z) y) (mul y (R z))) (commOK mul R y zs) := rfl
    rw [e, slc_and] at h
    rcases List.mem_cons.1 hz' with rfl | hz'
    · exact Nat.eq_of_beq_eq_true h.1
    · exact slc_commOK zs h.2 z' hz'

theorem slc_entsOK {mul : ℕ → ℕ → ℕ} {ONE : ℕ} {R : ℕ → ℕ} {sv : List ℕ} {X : ℕ} :
    ∀ es : List (ℕ × (List ℕ × List ℕ)), entsOK mul ONE R sv X es = true → ∀ e ∈ es,
      mul X (R e.1) = mul (R e.1) (wordP mul ONE (nthD ONE sv) e.2.1) ∧
        commOK mul R (wordP mul ONE (nthD ONE sv) e.2.1) e.2.2 = true
  | [], _, e, he => absurd he List.not_mem_nil
  | e :: es, h, e', he' => by
    have eq : entsOK mul ONE R sv X (e :: es) = andB (sB (wordP mul ONE (nthD ONE sv) e.2.1)
        fun y => sB (R e.1) fun H => andB (Nat.beq (mul X H) (mul H y)) (commOK mul R y e.2.2))
        (entsOK mul ONE R sv X es) := rfl
    rw [eq] at h
    simp only [slc_sB, slc_and] at h
    rcases List.mem_cons.1 he' with rfl | he'
    · exact ⟨Nat.eq_of_beq_eq_true h.1.1, h.1.2⟩
    · exact slc_entsOK es h.2 e' he'

theorem slc_rowOK {mul : ℕ → ℕ → ℕ} {n : ℕ} {tv : List ℕ} {t : ℕ} : ∀ (sv c : List ℕ),
    rowOK mul n tv t sv c = true → ∀ j < sv.length,
      c.getD j 0 < n ∧ mul t (sv.getD j 0) = tv.getD (c.getD j 0) 0
  | [], _, _, j, hj => absurd hj (by simp)
  | g :: sv, c, h, j, hj => by
    have e : rowOK mul n tv t (g :: sv) c = andB (Nat.blt (nthD 0 c 0) n)
        (andB (Nat.beq (mul t g) (nthD 0 tv (nthD 0 c 0))) (rowOK mul n tv t sv (tl c))) := rfl
    rw [e] at h
    simp only [slc_and, slc_nthD, Nat.blt_eq] at h
    cases j with
    | zero =>
      simp only [List.getD_cons_zero]
      exact ⟨h.1, Nat.eq_of_beq_eq_true h.2.1⟩
    | succ j =>
      obtain ⟨h1, h2⟩ := slc_rowOK sv (tl c) h.2.2 j (by simpa using hj)
      rw [slc_tl] at h1 h2
      rw [List.getD_cons_succ]
      exact ⟨h1, h2⟩

theorem slc_tabOK {mul : ℕ → ℕ → ℕ} {p k n : ℕ} {tv sv : List ℕ} {cl : List (List ℕ)}
    {cb : List ℕ} : ∀ (l : List ℕ) (i : ℕ), tabOK mul p k n tv sv cl cb l i = true →
      ∀ m < l.length, rowOK mul n tv (l.getD m 0) sv (cl.getD (i + m) []) = true ∧
        cb.getD (i + m) 0 < n ∧ pw1 mul (l.getD m 0) (p - 1) = tv.getD (cb.getD (i + m) 0) 0 ∧
        itN cb k (i + m) = 0
  | [], _, _, m, hm => absurd hm (by simp)
  | t :: l, i, h, m, hm => by
    have e : tabOK mul p k n tv sv cl cb (t :: l) i = andB (rowOK mul n tv t sv (nthD [] cl i))
        (andB (Nat.blt (nthD 0 cb i) n)
          (andB (Nat.beq (pw1 mul t (Nat.sub p 1)) (nthD 0 tv (nthD 0 cb i)))
            (andB (Nat.beq (itN cb k i) 0) (tabOK mul p k n tv sv cl cb l (Nat.succ i))))) := rfl
    rw [e] at h
    simp only [slc_and, slc_nthD, Nat.blt_eq, Nat.sub_eq] at h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    cases m with
    | zero =>
      simp only [Nat.add_zero, List.getD_cons_zero]
      exact ⟨h1, h2, Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4⟩
    | succ m =>
      have := slc_tabOK l (i + 1) h5 m (by simpa using hm)
      have e2 : i + 1 + m = i + (m + 1) := by omega
      rw [e2] at this
      rw [List.getD_cons_succ]
      exact this

theorem slc_inj {q d w S X Y : ℕ} (hS : S = d * w) (hX : Canon q d w X) (hY : Canon q d w Y)
    (h : ordMat q d w S X = ordMat q d w S Y) : X = Y := by
  have hlane : ∀ t < d * d, lane w X t = lane w Y t := by
    intro t ht
    have hd : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h0 | h0
      · subst h0
        simp at ht
      · exact h0
    have hi : t / d < d := (Nat.div_lt_iff_lt_mul hd).2 ht
    have hj : t % d < d := Nat.mod_lt _ hd
    have e := congrFun (congrFun h ⟨t / d, hi⟩) ⟨t % d, hj⟩
    simp only [ordMat] at e
    have ex : S * (t / d) + w * (t % d) = w * t := by
      rw [hS]
      calc d * w * (t / d) + w * (t % d) = w * (t % d + d * (t / d)) := by ring
        _ = w * t := by rw [Nat.mod_add_div]
    rw [ex, ZMod.natCast_eq_natCast_iff'] at e
    have h1 := hX.2 t ht
    have h2 := hY.2 t ht
    unfold lane at h1 h2 ⊢
    rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at e
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < w * (d * d)
  · have hw : 0 < w := by
      rcases Nat.eq_zero_or_pos w with h0 | h0
      · rw [h0, Nat.zero_mul] at hb
        omega
      · exact h0
    have ht : b / w < d * d := (Nat.div_lt_iff_lt_mul hw).2 (by rw [Nat.mul_comm]; exact hb)
    have key : ∀ Z : ℕ, Z.testBit b = (lane w Z (b / w)).testBit (b % w) := by
      intro Z
      unfold lane
      rw [Nat.testBit_mod_two_pow, decide_eq_true (Nat.mod_lt _ hw), Bool.true_and,
        Nat.testBit_div_two_pow, Nat.mod_add_div]
    rw [key X, key Y, hlane _ ht]
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hX.1 (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hY.1 (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem clsL_sound {q w S d T L H CM RM ONE LV HV A B p k t : ℕ}
    (hc : constsOK q w S d T L H CM RM ONE LV HV = true) (hd : 0 < d) (hq : 1 < q) (hp : 0 < p)
    (hA : Canon q d w A) (hB : Canon q d w B) {prg : List (ℕ × ℕ)} {rx : ℕ} {sg tb : List ℕ}
    {cl : List (List ℕ)} {cb : List ℕ} {ent : List (ℕ × (List ℕ × List ℕ))} {lp : List (ℕ × ℕ)}
    {ab : List ℕ}
    (h : clsL (mulR q w S d T L H CM RM) ONE A B p q k t w S d prg rx sg tb cl cb ent lp ab = true) :
    ∃ R, ClsFacts (ordMat q d w S A) (ordMat q d w S B) p k t rx sg tb cb ent R := by
  have hS : S = d * w := by
    unfold constsOK at hc
    rw [slc_and, slc_and] at hc
    exact Nat.eq_of_beq_eq_true hc.2.1
  have hq1 : Fact (1 < q) := ⟨hq⟩
  have hone := one_sound hc
  have hmulC : ∀ a b, Canon q d w a → Canon q d w b →
      Canon q d w (mulR q w S d T L H CM RM a b) ∧ ordMat q d w S (mulR q w S d T L H CM RM a b) =
        ordMat q d w S a * ordMat q d w S b := fun a b ha hb => mulR_sound hc ha hb
  let P : ℕ → Prop := fun x => Canon q d w x ∧
    ordMat q d w S x ∈ Submonoid.closure ({ordMat q d w S A, ordMat q d w S B} : Set (Mat q d))
  have hP1 : P ONE := ⟨hone.1, by rw [hone.2]; exact Submonoid.one_mem _⟩
  have hPm : ∀ a b, P a → P b → P (mulR q w S d T L H CM RM a b) := fun a b ha hb =>
    ⟨(hmulC a b ha.1 hb.1).1, by rw [(hmulC a b ha.1 hb.1).2]; exact Submonoid.mul_mem _ ha.2 hb.2⟩
  have hZ0 : slcZ ONE [] [B, A, ONE] 3 :=
    ⟨by norm_num, rfl, rfl, fun _ => rfl, fun h => absurd h (by norm_num)⟩
  unfold clsL at h
  obtain ⟨bl, cur, n, ⟨hall, hZ⟩, hk⟩ :=
    slc_runP (Q := fun bl cur n => slcAll P bl cur ∧ slcZ ONE bl cur n)
      (fun bl cur n r hQ hb => ⟨⟨hQ.1.1, fun x hx => by
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hPm _ _ (slc_lk_P hP1 hQ.1 _ _) (slc_lk_P hP1 hQ.1 _ _)
        · exact hQ.1.2 x hx⟩, (slc_push hQ.2).1 hb⟩)
      (fun bl cur n r hQ hb => ⟨⟨fun b hb' x hx => by
        rcases List.mem_cons.1 hb' with rfl | hb'
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact hPm _ _ (slc_lk_P hP1 hQ.1 _ _) (slc_lk_P hP1 hQ.1 _ _)
          · exact hQ.1.2 x hx
        · exact hQ.1.1 b hb' x hx, fun x hx => absurd hx List.not_mem_nil⟩, (slc_push hQ.2).2 hb⟩)
      prg [] [B, A, ONE] 3 _ ⟨⟨fun b hb => absurd hb List.not_mem_nil, fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact ⟨hB, Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)⟩
        · exact ⟨hA, Submonoid.subset_closure (Set.mem_insert _ _)⟩
        · exact hP1⟩, hZ0⟩ h
  simp only [slc_sB, slc_mapS, slc_and, slc_not, slc_nthD, slc_lenN, slc_revOnto, slc_zsE,
    List.length_map, Nat.sub_eq] at hk
  obtain ⟨hne, hpw, htr, ht0, htab, hent, hlp⟩ := hk
  have hPl : ∀ r, P (lk ONE bl cur n r) := fun r => slc_lk_P hP1 hall n r
  have hR0 : ordMat q d w S (lk ONE bl cur n 0) = 1 := by
    rw [slc_lk0 hZ]
    exact hone.2
  have htpos : 0 < tb.length := by
    rcases Nat.eq_zero_or_pos tb.length with h0 | h0
    · exfalso
      rw [List.length_eq_zero_iff] at h0
      rw [h0] at ht0
      have e : 0 = ONE := Nat.eq_of_beq_eq_true ht0
      have h1 := congrFun (congrFun hone.2 ⟨0, hd⟩) ⟨0, hd⟩
      rw [← e] at h1
      simp [ordMat] at h1
    · exact h0
  refine ⟨fun r => ordMat q d w S (lk ONE bl cur n r), fun r => (hPl r).2, hR0, ?_, ?_, ?_, htpos,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro he
    exact Nat.ne_of_beq_eq_false hne (slc_inj hS (hPl rx).1 hone.1 (he.trans hone.2.symm))
  ·
    have hpe : pw1 (mulR q w S d T L H CM RM) (lk ONE bl cur n rx) (p - 1) = ONE :=
      Nat.eq_of_beq_eq_true hpw
    have h2 := (slc_pw1 hmulC (hPl rx).1 (p - 1)).2
    rw [hpe, hone.2, Nat.sub_add_cancel hp] at h2
    exact h2.symm
  ·
    have e1 : Nat.mod (trL w S d (lk ONE bl cur n rx)) q = t := Nat.eq_of_beq_eq_true htr
    have e2 : Nat.mod (trL w S d (lk ONE bl cur n rx)) q = trL w S d (lk ONE bl cur n rx) % q := rfl
    rw [← e1, e2, ZMod.natCast_mod, slc_trL, Nat.cast_sum]
    simp only [Matrix.trace, Matrix.diag, ordMat]
    exact Fin.sum_univ_eq_sum_range
      (fun i => ((lk ONE bl cur n rx / 2 ^ (S * i + w * i) % 2 ^ w : ℕ) : ZMod q)) d
  ·
    have e : (tb.map (lk ONE bl cur n)).getD 0 0 = ONE := Nat.eq_of_beq_eq_true ht0
    rw [slc_getD_map htpos 0 0] at e
    beta_reduce
    rw [e]
    exact hone.2
  ·
    intro i hi j hj
    have ht := slc_tabOK _ 0 htab i (by simpa using hi)
    rw [Nat.zero_add] at ht
    have hr := slc_rowOK _ _ ht.1 j (by simpa using hj)
    have hc := hr.1
    refine ⟨_, hc, ?_⟩
    have e := hr.2
    rw [slc_getD_map hi 0 0, slc_getD_map hj 0 0, slc_getD_map hc 0 0] at e
    beta_reduce
    rw [← (hmulC _ _ (hPl _).1 (hPl _).1).2, e]
  ·
    intro i hi
    have ht := slc_tabOK _ 0 htab i (by simpa using hi)
    rw [Nat.zero_add] at ht
    obtain ⟨-, hc, hp1, -⟩ := ht
    refine ⟨hc, ?_⟩
    rw [slc_getD_map hi 0 0, slc_getD_map hc 0 0] at hp1
    beta_reduce
    have h2 := (slc_pw1 hmulC (hPl (tb.getD i 0)).1 (p - 1)).2
    rw [hp1, Nat.sub_add_cancel hp] at h2
    exact h2.symm
  ·
    intro i hi
    have ht := slc_tabOK _ 0 htab i (by simpa using hi)
    rw [Nat.zero_add] at ht
    rw [← slc_itN]
    exact ht.2.2.2
  ·
    intro e he
    obtain ⟨h1, h2⟩ := slc_entsOK ent hent e he
    have hRv : ∀ l, Canon q d w (nthD ONE (sg.map (lk ONE bl cur n)) l) ∧
        ordMat q d w S (nthD ONE (sg.map (lk ONE bl cur n)) l) =
          ordMat q d w S (lk ONE bl cur n (sg.getD l 0)) := by
      intro l
      rw [slc_nthD]
      by_cases hl : l < sg.length
      · rw [slc_getD_map hl ONE 0]
        exact ⟨(hPl _).1, rfl⟩
      · rw [List.getD_eq_default _ _ (by simpa using hl), List.getD_eq_default _ _ (by omega), hR0]
        exact hone
    have hw := slc_wordGo hmulC (fun l => (hRv l).1) e.2.1 ONE hone.1
    have hwM : ordMat q d w S (wordP (mulR q w S d T L H CM RM) ONE
        (nthD ONE (sg.map (lk ONE bl cur n))) e.2.1) =
        wM (fun r => ordMat q d w S (lk ONE bl cur n r)) sg e.2.1 := by
      unfold wordP
      rw [hw.2, hone.2, one_mul, wM]
      congr 1
      exact List.map_congr_left fun l _ => (hRv l).2
    have hyC : Canon q d w (wordP (mulR q w S d T L H CM RM) ONE
        (nthD ONE (sg.map (lk ONE bl cur n))) e.2.1) := hw.1
    refine ⟨?_, fun z hz => ?_⟩
    · beta_reduce
      rw [← hwM, ← (hmulC _ _ (hPl _).1 (hPl _).1).2, ← (hmulC _ _ (hPl _).1 hyC).2, h1]
    · beta_reduce
      rw [← hwM, ← (hmulC _ _ (hPl _).1 hyC).2, ← (hmulC _ _ hyC (hPl _).1).2,
        slc_commOK _ h2 z hz]
  ·
    let P2 : ℕ → Prop := fun x => Canon q d w x ∧ ordMat q d w S x ∈ Submonoid.closure
      ({Y | ∃ s ∈ sg, Y = ordMat q d w S (lk ONE bl cur n s)} ∪
        {Y | ∃ z ∈ ent.flatMap (·.2.2), Y = ordMat q d w S (lk ONE bl cur n z)})
    have hP21 : P2 ONE := ⟨hone.1, by rw [hone.2]; exact Submonoid.one_mem _⟩
    have hP2m : ∀ a b, P2 a → P2 b → P2 (mulR q w S d T L H CM RM a b) := fun a b ha hb =>
      ⟨(hmulC a b ha.1 hb.1).1, by rw [(hmulC a b ha.1 hb.1).2]; exact Submonoid.mul_mem _ ha.2 hb.2⟩
    have hinit : slcAll P2 [] (((ent.flatMap (·.2.2)).map (lk ONE bl cur n)).reverse ++
        ((sg.map (lk ONE bl cur n)).reverse ++ [ONE])) := by
      refine ⟨fun b hb => absurd hb List.not_mem_nil, fun x hx => ?_⟩
      simp only [List.mem_append, List.mem_reverse, List.mem_map, List.mem_singleton] at hx
      rcases hx with ⟨z, hz, rfl⟩ | ⟨s, hs, rfl⟩ | rfl
      · exact ⟨(hPl z).1, Submonoid.subset_closure (Or.inr ⟨z, hz, rfl⟩)⟩
      · exact ⟨(hPl s).1, Submonoid.subset_closure (Or.inl ⟨s, hs, rfl⟩)⟩
      · exact hP21
    obtain ⟨bl', cur', n', hall', hk'⟩ := slc_runP (Q := fun bl cur _ => slcAll P2 bl cur)
      (fun bl cur n r hQ _ => ⟨hQ.1, fun x hx => by
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hP2m _ _ (slc_lk_P hP21 hQ _ _) (slc_lk_P hP21 hQ _ _)
        · exact hQ.2 x hx⟩)
      (fun bl cur n r hQ _ => ⟨fun b hb x hx => by
        rcases List.mem_cons.1 hb with rfl | hb
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact hP2m _ _ (slc_lk_P hP21 hQ _ _) (slc_lk_P hP21 hQ _ _)
          · exact hQ.2 x hx
        · exact hQ.1 b hb x hx, fun x hx => absurd hx List.not_mem_nil⟩)
      lp [] _ _ _ hinit hlp
    simp only [slc_and] at hk'
    obtain ⟨ha, hb⟩ := hk'
    have eA : lk ONE bl' cur' n' (ab.getD 0 0) = A := Nat.eq_of_beq_eq_true ha
    have eB : lk ONE bl' cur' n' (ab.getD 1 0) = B := Nat.eq_of_beq_eq_true hb
    have hA2 := (slc_lk_P hP21 hall' n' (ab.getD 0 0)).2
    have hB2 := (slc_lk_P hP21 hall' n' (ab.getD 1 0)).2
    rw [eA] at hA2
    rw [eB] at hB2
    exact ⟨hA2, hB2⟩

section Group

variable {G : Type} [Group G] [Finite G]

theorem inv_mem_mclosure {X : Set G} {g : G} (hg : g ∈ Submonoid.closure X) :
    g⁻¹ ∈ Submonoid.closure X := by
  have hn := orderOf_pos g
  have e : g⁻¹ = g ^ (orderOf g - 1) := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ', Nat.sub_add_cancel hn, pow_orderOf_eq_one]
  rw [e]
  exact Submonoid.pow_mem _ hg _

theorem mem_mclosure_of_mem_closure {X : Set G} {g : G} (hg : g ∈ Subgroup.closure X) :
    g ∈ Submonoid.closure X := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact Submonoid.subset_closure hx
  | one => exact Submonoid.one_mem _
  | mul x y _ _ hx hy => exact Submonoid.mul_mem _ hx hy
  | inv x _ hx => exact inv_mem_mclosure hx

theorem generating_of_clsFacts {q d : ℕ} (ρ : G →* Mat q d) (hρ : Function.Injective ρ) {p : ℕ}
    (hp : p.Prime) (a b : G) (hab : Subgroup.closure ({a, b} : Set G) = ⊤) {k t rx : ℕ}
    {sg tb cb : List ℕ} {ent : List (ℕ × (List ℕ × List ℕ))} {R : ℕ → Mat q d}
    (hF : ClsFacts (ρ a) (ρ b) p k t rx sg tb cb ent R) :
    ∃ x₀ : G, ρ x₀ = R rx ∧ orderOf x₀ = p ∧ ∀ x : G, IsConj x₀ x → SporKRestGenerating p x := by
  have : Fact p.Prime := ⟨hp⟩
  choose rr hrr using fun r => CFSG.KS.SlpPc.exists_of_mclosure ρ a b (hF.reg r)
  have hr0 : rr 0 = 1 := hρ (by rw [hrr, hF.r0, map_one])
  have hit : ∀ m, ∀ i < tb.length, (fun j => cb.getD j 0)^[m] i < tb.length ∧
      rr (tb.getD i 0) ^ (p ^ m) = rr (tb.getD ((fun j => cb.getD j 0)^[m] i) 0) := by
    intro m
    induction m with
    | zero =>
      intro i hi
      exact ⟨hi, by rw [pow_zero, pow_one, Function.iterate_zero_apply]⟩
    | succ m ih =>
      intro i hi
      obtain ⟨h1, h2⟩ := ih i hi
      obtain ⟨h3, h4⟩ := hF.powT _ h1
      rw [Function.iterate_succ_apply']
      refine ⟨h3, ?_⟩
      rw [pow_succ, pow_mul, h2]
      exact hρ (by rw [map_pow, hrr, hrr]; exact h4)
  have hexp : ∀ i < tb.length, rr (tb.getD i 0) ^ (p ^ k) = 1 := by
    intro i hi
    rw [(hit k i hi).2, hF.itT i hi]
    exact hρ (by rw [hrr, hF.t0, map_one])
  have hstep : ∀ g ∈ Submonoid.closure {g : G | ∃ s ∈ sg, g = rr s}, ∀ i < tb.length,
      ∃ c < tb.length, rr (tb.getD i 0) * g = rr (tb.getD c 0) := by
    intro g hg
    induction hg using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨s, hs, rfl⟩ := hx
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
      intro i hi
      obtain ⟨c, hc, e⟩ := hF.mulT i hi j hj
      have hgj : sg.getD j 0 = sg[j] := by simp [List.getD_eq_getElem?_getD, hj]
      rw [hgj] at e
      exact ⟨c, hc, hρ (by rw [map_mul, hrr, hrr, hrr, e])⟩
    | one =>
      intro i hi
      exact ⟨i, hi, mul_one _⟩
    | mul x y _ _ hx hy =>
      intro i hi
      obtain ⟨c, hc, e⟩ := hx i hi
      obtain ⟨c', hc', e'⟩ := hy c hc
      exact ⟨c', hc', by rw [← mul_assoc, e, e']⟩
  set S₀ : Subgroup G := Subgroup.closure {g : G | ∃ s ∈ sg, g = rr s} with hS₀
  have hT0 : rr (tb.getD 0 0) = 1 := hρ (by rw [hrr, hF.t0, map_one])
  have hpg : IsPGroup p S₀ := by
    intro g
    refine ⟨k, Subtype.ext ?_⟩
    obtain ⟨c, hc, e⟩ := hstep _ (mem_mclosure_of_mem_closure g.2) 0 hF.tpos
    rw [hT0, one_mul] at e
    rw [Subgroup.coe_pow, e, hexp c hc, Subgroup.coe_one]
  have hW : ∀ w : List ℕ, ρ ((w.map fun l => rr (sg.getD l 0)).prod) = wM R sg w ∧
      (w.map fun l => rr (sg.getD l 0)).prod ∈ S₀ := by
    intro w
    refine ⟨?_, ?_⟩
    · simp only [wM, map_list_prod, List.map_map, Function.comp_def, hrr]
    · refine Subgroup.list_prod_mem (K := S₀) ?_
      intro x hx
      obtain ⟨l, -, rfl⟩ := List.mem_map.mp hx
      by_cases hl : l < sg.length
      · refine Subgroup.subset_closure ⟨sg[l], List.getElem_mem hl, ?_⟩
        simp [List.getD_eq_getElem?_getD, hl]
      · rw [List.getD_eq_default _ _ (by omega), hr0]
        exact S₀.one_mem
  set Z : Set G := {g : G | ∃ z ∈ ent.flatMap (·.2.2), g = rr z} with hZdef
  have hZ : ∀ z ∈ Z, ∃ h y : G, y ∈ S₀ ∧ h⁻¹ * rr rx * h = y ∧ z * y = y * z := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨e, he, hze⟩ := List.mem_flatMap.mp hz
    obtain ⟨h1, h2⟩ := hF.entF e he
    obtain ⟨hy1, hy2⟩ := hW e.2.1
    refine ⟨rr e.1, _, hy2, ?_, hρ ?_⟩
    · have hm : rr rx * rr e.1 = rr e.1 * (e.2.1.map fun l => rr (sg.getD l 0)).prod :=
        hρ (by rw [map_mul, map_mul, hrr, hrr, hy1, h1])
      rw [mul_assoc, hm, ← mul_assoc, inv_mul_cancel, one_mul]
    · rw [map_mul, map_mul, hrr, hy1, h2 z hze]
  have hS : ∀ Y ∈ ({Y | ∃ s ∈ sg, Y = R s} ∪ {Y | ∃ z ∈ ent.flatMap (·.2.2), Y = R z}),
      ∃ u ∈ Subgroup.closure ((S₀ : Set G) ∪ Z), ρ u = Y := by
    rintro Y (⟨s, hs, rfl⟩ | ⟨z, hz, rfl⟩)
    · exact ⟨rr s, Subgroup.subset_closure (Or.inl (Subgroup.subset_closure ⟨s, hs, rfl⟩)), hrr s⟩
    · exact ⟨rr z, Subgroup.subset_closure (Or.inr ⟨z, hz, rfl⟩), hrr z⟩
  have ha := CFSG.KS.SlpPc.mem_of_mclosure ρ hρ _ hS hF.seeds.1
  have hb := CFSG.KS.SlpPc.mem_of_mclosure ρ hρ _ hS hF.seeds.2
  have hpow : rr rx ^ p = 1 := hρ (by rw [map_pow, hrr, hF.pow, map_one])
  have hne : rr rx ≠ 1 := fun e => hF.ne (by rw [← hrr, e, map_one])
  exact ⟨rr rx, hrr rx, orderOf_eq_prime hpow hne, fun x hx =>
    sporKRest_generating_of_pgroup_closure hp a b hab S₀ hpg (rr rx) Z hZ ha hb hx⟩

end Group

end CFSG.KS.SlpCls

end
