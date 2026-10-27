module

public import CFSG.Certificates.Kernel.TcRes.RootSound
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs

public section

namespace CFSG.KC.TcRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.TcRes.TK

@[expose] noncomputable def v3 (u : ℕ) : Fin 6 → ZMod 3 := fun m => (dg u m : ZMod 3)

@[expose] def KSet
    (w : WeylGroup Tag.E6) (s : ZMod 3) : Set (Fin 6 → ZMod 3) :=
  {u | ∀ j : Fin 6, ∑ m : Fin 6,
    (((w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) m : ℤ) : ZMod 3) * u m = s * u j}

@[expose] def RedPairs (K : Set (Fin 6 → ZMod 3)) : Set ((Fin 6 → ZMod 3) × (Fin 6 → ZMod 3)) :=
  {x | x.1 ∈ K ∧ x.2 ∈ K ∧ IsReduced x.1 x.2}

structure SweepRaw (K : Set (Fin 6 → ZMod 3)) (a e : ℕ)
    (pr : ℕ → (Fin 6 → ZMod 3) × (Fin 6 → ZMod 3)) : Prop where
  mem : ∀ p, a ≤ p → p < e → pr p ∈ RedPairs K
  inj : ∀ p, a ≤ p → p < e → ∀ p', a ≤ p' → p' < e → pr p = pr p' → p = p'
  card : Nat.card (RedPairs K) = e - a

section SweepDecode

open CFSG.KC.TcRes.Lane

def LaneEq (x : ℕ) (f : ℕ → ℕ) (B : ℕ) : Prop := ∀ k < 729, fld x 12 k = f k ∧ f k ≤ B

theorem LaneEq.add {a b : ℕ} {f g : ℕ → ℕ} {A B : ℕ} (ha : LaneEq a f A) (hb : LaneEq b g B)
    (hAB : A + B < 4096) : LaneEq (a + b) (fun k => f k + g k) (A + B) := by
  intro k hk
  refine ⟨?_, Nat.add_le_add (ha k hk).2 (hb k hk).2⟩
  change fld (a + b) 12 k = f k + g k
  rw [fld_add_low (fun k' hk' => ?_), (ha k hk).1, (hb k hk).1]
  rw [(ha k' (by omega)).1, (hb k' (by omega)).1]
  have h1 := (ha k' (by omega)).2
  have h2 := (hb k' (by omega)).2
  have h3 : f k' + g k' < 4096 := by omega
  exact lt_of_lt_of_eq h3 (by norm_num)

theorem LaneEq.smul {a : ℕ} {f : ℕ → ℕ} {A : ℕ} (c : ℕ) (ha : LaneEq a f A) (hc : c * A < 4096) :
    LaneEq (c * a) (fun k => c * f k) (c * A) := by
  intro k hk
  refine ⟨?_, Nat.mul_le_mul_left c (ha k hk).2⟩
  change fld (c * a) 12 k = c * f k
  rw [fld_smul_low (fun k' hk' => ?_), (ha k hk).1]
  rw [(ha k' (by omega)).1]
  exact lt_of_le_of_lt (Nat.mul_le_mul_left c (ha k' (by omega)).2)
    (lt_of_lt_of_eq hc (by norm_num))

theorem tab_lanes {U L M : ℕ → ℕ} (htab : ∀ i < 9, tabsOK U L M i = true) {u : ℕ} (hu : u < 729)
    {m : ℕ} (hm : m < 6) :
    fld (U m) 12 u = dg u m ∧ fld (L m) 12 u = b2n (ldOK u m) ∧
      fld (M m) 12 u = b2n (mPred u m) := by
  have h := htab (u / 81) (by omega)
  simp only [tabsOK, allLt_iff, nadd, nmul] at h
  have h2 := h (u % 81) (Nat.mod_lt _ (by norm_num))
  rw [Nat.div_add_mod] at h2
  simp only [tabOK, allLt_iff, andB_eq_true, beq_eq_true] at h2
  exact h2 m hm

theorem dg_lt (u m : ℕ) : dg u m < 3 := Nat.mod_lt _ (by norm_num)

theorem rc_lane {RC : ℕ → ℕ} {V : ℕ} (hrc : ∀ g < 72, rcOK RC V g = true) {g : ℕ} (hg : g < 72)
    {m : ℕ} (hm : m < 6) : fld (RC m) 5 g = (fld (fld V 96 g) 16 m + 2) % 3 := by
  have h := hrc g hg
  simp only [rcOK, strictB_eq, allLt_iff, beq_eq_true, nadd, nmod] at h
  exact h m hm

theorem natCast_zmod3_eq_zero (n : ℕ) : (n : ZMod 3) = 0 ↔ n % 3 = 0 := by
  rw [← ZMod.natCast_mod]
  have := Nat.mod_lt n (by norm_num : 0 < 3)
  generalize n % 3 = a at this ⊢
  interval_cases a <;> decide

theorem sOf_le (b : ℕ) : 1 ≤ sOf b ∧ sOf b ≤ 2 := by
  change 1 ≤ Bool.rec (motive := fun _ => ℕ) 2 1 (Nat.beq b 1) ∧
    Bool.rec (motive := fun _ => ℕ) 2 1 (Nat.beq b 1) ≤ 2
  cases Nat.beq b 1
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩

theorem kj_lane {U L M RC : ℕ → ℕ} (htab : ∀ i < 9, tabsOK U L M i = true) {s γ j u : ℕ}
    (hs1 : 1 ≤ s) (hs : s ≤ 3) (hc : ∀ m < 6, fld (RC m) 5 γ ≤ 2) (hj : j < 6) (hu : u < 729) :
    fld (kj U RC s γ j) 12 u = if (fld (RC 0) 5 γ * dg u 0 + (fld (RC 1) 5 γ * dg u 1 +
      (fld (RC 2) 5 γ * dg u 2 + (fld (RC 3) 5 γ * dg u 3 + (fld (RC 4) 5 γ * dg u 4 +
      (fld (RC 5) 5 γ * dg u 5 + (3 - s) * dg u j)))))) % 3 = 0 then 1 else 0 := by
  have hU : ∀ m < 6, LaneEq (U m) (fun k => dg k m) 2 := fun m hm k hk =>
    ⟨(tab_lanes htab hk hm).1, by
      change dg k m ≤ 2
      have := dg_lt k m
      omega⟩
  have c0 := hc 0 (by norm_num)
  have c1 := hc 1 (by norm_num)
  have c2 := hc 2 (by norm_num)
  have c3 := hc 3 (by norm_num)
  have c4 := hc 4 (by norm_num)
  have c5 := hc 5 (by norm_num)
  have hx := ((hU 0 (by norm_num)).smul (fld (RC 0) 5 γ) (by omega)).add
    (((hU 1 (by norm_num)).smul (fld (RC 1) 5 γ) (by omega)).add
    (((hU 2 (by norm_num)).smul (fld (RC 2) 5 γ) (by omega)).add
    (((hU 3 (by norm_num)).smul (fld (RC 3) 5 γ) (by omega)).add
    (((hU 4 (by norm_num)).smul (fld (RC 4) 5 γ) (by omega)).add
    (((hU 5 (by norm_num)).smul (fld (RC 5) 5 γ) (by omega)).add
    ((hU j hj).smul (3 - s) (by omega)) (by omega)) (by omega)) (by omega)) (by omega))
      (by omega)) (by omega)
  change fld (zl (lowW 12 729) (fld (RC 0) 5 γ * U 0 + (fld (RC 1) 5 γ * U 1 +
      (fld (RC 2) 5 γ * U 2 + (fld (RC 3) 5 γ * U 3 + (fld (RC 4) 5 γ * U 4 +
      (fld (RC 5) 5 γ * U 5 + (3 - s) * U j))))))) 12 u = _
  rw [fld_zl_any (w := 12) (K := 729) (by norm_num) (fun k hk => by
    rw [(hx k hk).1]
    have := (hx k hk).2
    simp only at this ⊢
    omega) hu, (hx u hu).1]

theorem rc_le {RC : ℕ → ℕ} {V : ℕ} (hrc : ∀ g < 72, rcOK RC V g = true) {g : ℕ} (hg : g < 72)
    {m : ℕ} (hm : m < 6) : fld (RC m) 5 g ≤ 2 := by
  rw [rc_lane hrc hg hm]
  have := Nat.mod_lt (fld (fld V 96 g) 16 m + 2) (by norm_num : 0 < 3)
  omega

theorem kq_rec {f : ℕ → ℕ} {u : ℕ} (hu : u < 729) : ∀ n, (∀ j < n, fld (f j) 12 u ≤ 1) →
    fld (Nat.rec (motive := fun _ => ℕ) LOW12 (fun j ih => strictN ih fun a => a &&& f j) n) 12 u =
      if ∀ j < n, fld (f j) 12 u = 1 then 1 else 0 := by
  intro n
  induction n with
  | zero =>
    intro _
    have := fld_mul_low (w := 12) (K := 729) (c := 1) (by norm_num) (by norm_num) hu
    rw [one_mul] at this
    rw [if_pos (fun j hj => absurd hj (Nat.not_lt_zero _))]
    exact this
  | succ n ih =>
    intro hf
    change fld (strictN (Nat.rec (motive := fun _ => ℕ) LOW12
      (fun j ih => strictN ih fun a => a &&& f j) n) fun a => a &&& f n) 12 u = _
    rw [strictN_eq, fld_land, ih (fun j hj => hf j (by omega))]
    obtain h | h : fld (f n) 12 u = 0 ∨ fld (f n) 12 u = 1 := by
      have := hf n (by omega)
      omega
    · rw [h, if_neg (fun hB : ∀ j < n + 1, fld (f j) 12 u = 1 => by
        have := hB n (Nat.lt_succ_self n)
        omega)]
      split_ifs <;> rfl
    · rw [h]
      by_cases hA : ∀ j < n, fld (f j) 12 u = 1
      · rw [if_pos hA, if_pos (fun j hj => by
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · exact hA j hj
          · exact h)]
        rfl
      · rw [if_neg hA, if_neg (fun hB => hA fun j hj => hB j (by omega))]
        rfl

theorem kq_lane
    {vec : ℕ → Fin Tag.E6.rank → ℤ} {V REPS : ℕ} {U L M RC : ℕ → ℕ} (hvec : vec = vecOf 6 V)
    (htab : ∀ i < 9, tabsOK U L M i = true) (hrc : ∀ g < 72, rcOK RC V g = true) {q : ℕ}
    {w : WeylGroup Tag.E6} (hw : TupleOf vec 72 (Nat.land (Nat.shiftRight REPS (q / 3 * 42)) M42) w)
    {u : ℕ} (hu : u < 729) :
    (fld (kq U RC REPS q) 12 u = 1 ↔ v3 u ∈ KSet w (sOf (q % 3) : ZMod 3)) ∧
      fld (kq U RC REPS q) 12 u ≤ 1 := by
  have hs := sOf_le (q % 3)
  have h3 : (3 : ZMod 3) = 0 := by decide
  have h9 : (9 : ZMod 3) = 0 := by decide
  set t := Nat.land (Nat.shiftRight REPS (q / 3 * 42)) M42 with ht
  set s := sOf (q % 3) with hsd
  have hkj : ∀ j : Fin 6, fld (kj U RC s (tf t j) j) 12 u = 1 ↔
      ∑ m : Fin 6, (((w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) m : ℤ) : ZMod 3) * v3 u m =
        (s : ZMod 3) * v3 u j := by
    intro j
    have hγ : tf t j < 72 := (hw j).1
    have hF : ∀ m : Fin 6, (((w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) m : ℤ) : ZMod 3) =
        ((fld (RC m) 5 (tf t j) : ℕ) : ZMod 3) := by
      intro m
      rw [← (hw j).2, hvec, rc_lane hrc hγ m.2, ZMod.natCast_mod]
      simp only [vecOf, show (16 * 6 : ℕ) = 96 from rfl]
      push_cast
      linear_combination -h9
    rw [kj_lane htab hs.1 (by omega) (fun m hm => rc_le hrc hγ hm) j.2 hu]
    have e1 : ∀ X : ℕ, ((if X % 3 = 0 then 1 else 0) = 1 ↔ (X : ZMod 3) = 0) := by
      intro X
      rw [natCast_zmod3_eq_zero]
      split_ifs with h <;> simp [h]
    rw [e1, Fin.sum_univ_six]
    have v0 : ((0 : Fin 6) : ℕ) = 0 := rfl
    have v1 : ((1 : Fin 6) : ℕ) = 1 := rfl
    have v2 : ((2 : Fin 6) : ℕ) = 2 := rfl
    have v3' : ((3 : Fin 6) : ℕ) = 3 := rfl
    have v4 : ((4 : Fin 6) : ℕ) = 4 := rfl
    have v5 : ((5 : Fin 6) : ℕ) = 5 := rfl
    simp only [hF, v3, v0, v1, v2, v3', v4, v5]
    push_cast [Nat.cast_sub (by omega : s ≤ 3)]
    constructor
    · intro h
      linear_combination h - ((dg u j : ℕ) : ZMod 3) * h3
    · intro h
      linear_combination h + ((dg u j : ℕ) : ZMod 3) * h3
  have e0 : fld (kq U RC REPS q) 12 u = fld (Nat.rec (motive := fun _ => ℕ) LOW12
      (fun j ih => strictN ih fun a => a &&& (fun j => kj U RC s (tf t j) j) j) 6) 12 u := by
    rw [kq, strictN_eq, strictN_eq]
    rfl
  have e := kq_rec (f := fun j => kj U RC s (tf t j) j) hu 6 (fun j hj => by
      change fld (kj U RC s (tf t j) j) 12 u ≤ 1
      rw [kj_lane htab hs.1 (by omega) (fun m hm => rc_le hrc (hw ⟨j, hj⟩).1 hm) hj hu]
      split_ifs <;> norm_num)
  rw [e0, e]
  split_ifs with hA
  · exact ⟨⟨fun _ j => (hkj j).1 (hA j j.2), fun _ => rfl⟩, le_refl _⟩
  · refine ⟨⟨fun h => absurd h (by norm_num), fun h => absurd (fun j hj => (hkj ⟨j, hj⟩).2
      (h ⟨j, hj⟩)) hA⟩, by norm_num⟩

theorem rec_le (f : ℕ → ℕ) : ∀ n, Nat.rec (motive := fun _ => ℕ) LOW12
    (fun j ih => strictN ih fun a => Nat.land a (f j)) n ≤ LOW12 := by
  intro n
  induction n with
  | zero => exact le_refl _
  | succ n ih =>
    change strictN (Nat.rec (motive := fun _ => ℕ) LOW12
      (fun j ih => strictN ih fun a => Nat.land a (f j)) n) (fun a => Nat.land a (f n)) ≤ _
    rw [strictN_eq]
    exact Nat.and_le_left.trans ih

theorem kq_le (U RC : ℕ → ℕ) (REPS q : ℕ) : kq U RC REPS q ≤ LOW12 := by
  rw [kq, strictN_eq, strictN_eq]
  exact rec_le (fun j => kj U RC (sOf (q % 3)) (tf (Nat.land (Nat.shiftRight REPS (q / 3 * 42))
    M42) j) j) 6

theorem LOW12_lt : LOW12 < 2 ^ (12 * 729) := low_lt (w := 12) (by decide) 729

theorem fld_LOW12 {i : ℕ} (hi : i < 729) : fld LOW12 12 i = 1 := by
  have := fld_mul_low (w := 12) (K := 729) (c := 1) (by norm_num) (by norm_num) hi
  rwa [one_mul] at this

theorem pop12_eq {x : ℕ} (hx : x < 2 ^ (12 * 729)) (hxl : ∀ i, fld x 12 i ≤ 1) :
    pop12 x = ∑ u ∈ Finset.range 729, fld x 12 u := by
  have hLl : ∀ i, fld LOW12 12 i ≤ 1 := fun i => by
    rcases lt_or_ge i 729 with h | h
    · rw [fld_LOW12 h]
    · rw [fld_eq_zero_of_lt 12 729 _ LOW12_lt h]
      omega
  have hb := conv_le 12 729 x LOW12 1 1 hx hxl hLl
  change fld (x * LOW12) 12 728 = _
  rw [fld_mul 12 729 729 x LOW12 hx LOW12_lt (fun k => lt_of_le_of_lt (hb k) (by norm_num)) 728]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [fld_LOW12 (by omega), mul_one]

theorem npairs_eq (L M : ℕ → ℕ) (K : ℕ) :
    npairs L M K = ∑ j ∈ Finset.range 6, pop12 (K &&& L j) * pop12 (K &&& M j) := by
  have h : ∀ n, Nat.rec (motive := fun _ => ℕ) 0 (fun j ih => Nat.add (Nat.mul
      (pop12 (Nat.land K (L j))) (pop12 (Nat.land K (M j)))) ih) n =
      ∑ j ∈ Finset.range n, pop12 (K &&& L j) * pop12 (K &&& M j) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Finset.sum_range_succ, ← ih]
      exact Nat.add_comm _ _
  exact h 6

theorem dg_digits : ∀ u < 729, u = ∑ m ∈ Finset.range 6, dg u m * 3 ^ m := by
  decide +kernel

theorem ldOK_iff_dg : ∀ u < 729, ∀ j < 6, ldOK u j = true ↔
    (dg u j = 1 ∧ ∀ i < 6, j < i → dg u i = 0) := by
  decide +kernel

theorem v3_eq_iff {u u' : ℕ} {m : Fin 6} : v3 u m = v3 u' m ↔ dg u m = dg u' m := by
  simp only [v3]
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (dg_lt u m), Nat.mod_eq_of_lt (dg_lt u' m)]

theorem v3_eq_nat {u a : ℕ} {m : Fin 6} (ha : a < 3) : v3 u m = (a : ZMod 3) ↔ dg u m = a := by
  simp only [v3]
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (dg_lt u m), Nat.mod_eq_of_lt ha]

theorem v3_inj {u u' : ℕ} (hu : u < 729) (hu' : u' < 729) (h : v3 u = v3 u') : u = u' := by
  rw [dg_digits u hu, dg_digits u' hu']
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_range] at hm
  have := (v3_eq_iff (m := ⟨m, hm⟩)).1 (congrFun h _)
  exact congrArg (· * 3 ^ m) this

theorem v3_surj (x : Fin 6 → ZMod 3) : ∃ u < 729, v3 u = x := by
  have hN : Nat.card (Fin 6 → ZMod 3) = 729 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    norm_num
  have hinj : Function.Injective (fun u : Fin 729 => v3 u) := fun u u' h =>
    Fin.ext (v3_inj u.2 u'.2 h)
  obtain ⟨u, hu⟩ := surjective_of_injective_card hN _ hinj x
  exact ⟨u, u.2, hu⟩

theorem isLead_iff {u : ℕ} (hu : u < 729) (j : Fin 6) : ldOK u j = true ↔ IsLead (v3 u) j := by
  rw [ldOK_iff_dg u hu j j.2, IsLead]
  have e1 : v3 u j = 1 ↔ dg u j = 1 := by
    have := v3_eq_nat (u := u) (m := j) (a := 1) (by norm_num)
    rwa [Nat.cast_one] at this
  have e0 : ∀ i : Fin 6, v3 u i = 0 ↔ dg u i = 0 := fun i => by
    have := v3_eq_nat (u := u) (m := i) (a := 0) (by norm_num)
    rwa [Nat.cast_zero] at this
  rw [e1]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i hi => (e0 i).2 (h2 i.1 i.2 hi)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i hi hji => (e0 ⟨i, hi⟩).1 (h2 ⟨i, hi⟩ hji)⟩

theorem mPred_iff {u : ℕ} (hu : u < 729) (j : Fin 6) : mPred u j = true ↔
    (∃ i : Fin 6, j < i ∧ IsLead (v3 u) i) ∧ v3 u j = 0 := by
  have e0 : v3 u j = 0 ↔ dg u j = 0 := by
    have := v3_eq_nat (u := u) (m := j) (a := 0) (by norm_num)
    rwa [Nat.cast_zero] at this
  simp only [mPred, andB_eq_true, anyLt_iff, blt_eq_true, beq_eq_true, e0]
  constructor
  · rintro ⟨⟨i, hi, hji, hl⟩, h0⟩
    exact ⟨⟨⟨i, hi⟩, hji, (isLead_iff hu ⟨i, hi⟩).1 hl⟩, h0⟩
  · rintro ⟨⟨i, hji, hl⟩, h0⟩
    exact ⟨⟨i, i.2, hji, (isLead_iff hu i).2 hl⟩, h0⟩

theorem isLead_unique {v : Fin 6 → ZMod 3} {i j : Fin 6} (hi : IsLead v i) (hj : IsLead v j) :
    i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have := hi.2 j h
    rw [hj.1] at this
    exact absurd this one_ne_zero
  · exact h
  · have := hj.2 i h
    rw [hi.1] at this
    exact absurd this one_ne_zero

open Classical in
theorem card_redPairs (K : Set (Fin 6 → ZMod 3)) : Nat.card (RedPairs K) =
    ∑ j ∈ Finset.range 6, ((Finset.range 729).filter (fun u => v3 u ∈ K ∧ mPred u j = true)).card *
      ((Finset.range 729).filter (fun u => v3 u ∈ K ∧ ldOK u j = true)).card := by
  let S : Finset (ℕ × ℕ) := ((Finset.range 729) ×ˢ (Finset.range 729)).filter
    (fun p => v3 p.1 ∈ K ∧ v3 p.2 ∈ K ∧ IsReduced (v3 p.1) (v3 p.2))
  let f : ℕ × ℕ → (Fin 6 → ZMod 3) × (Fin 6 → ZMod 3) := fun p => (v3 p.1, v3 p.2)
  have himg : RedPairs K = f '' ↑S := by
    ext ⟨x1, x2⟩
    constructor
    · rintro ⟨h1, h2, h3⟩
      obtain ⟨a, ha, rfl⟩ := v3_surj x1
      obtain ⟨b, hb, rfl⟩ := v3_surj x2
      refine ⟨(a, b), ?_, rfl⟩
      simp only [S, Finset.coe_filter, Finset.mem_product, Finset.mem_range, Set.mem_setOf_eq]
      exact ⟨⟨ha, hb⟩, h1, h2, h3⟩
    · rintro ⟨⟨a, b⟩, hab, he⟩
      simp only [S, Finset.coe_filter, Finset.mem_product, Finset.mem_range,
        Set.mem_setOf_eq] at hab
      simp only [f, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨hab.2.1, hab.2.2.1, hab.2.2.2⟩
  have hinj : Set.InjOn f ↑S := by
    rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' he
    simp only [S, Finset.coe_filter, Finset.mem_product, Finset.mem_range,
      Set.mem_setOf_eq] at hab hab'
    simp only [f, Prod.mk.injEq] at he
    rw [v3_inj hab.1.1 hab'.1.1 he.1, v3_inj hab.1.2 hab'.1.2 he.2]
  have hS : S = (Finset.range 6).biUnion (fun j =>
      ((Finset.range 729).filter (fun u => v3 u ∈ K ∧ mPred u j = true)) ×ˢ
      ((Finset.range 729).filter (fun u => v3 u ∈ K ∧ ldOK u j = true))) := by
    ext ⟨a, b⟩
    simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_biUnion]
    constructor
    · rintro ⟨⟨ha, hb⟩, h1, h2, ⟨i, j, hji, hi, hj, h0⟩⟩
      exact ⟨j, j.2, ⟨ha, h1, (mPred_iff ha j).2 ⟨⟨i, hji, hi⟩, h0⟩⟩,
        ⟨hb, h2, (isLead_iff hb j).2 hj⟩⟩
    · rintro ⟨j, hj, ⟨ha, h1, hm⟩, ⟨hb, h2, hl⟩⟩
      obtain ⟨⟨i, hji, hi⟩, h0⟩ := (mPred_iff ha ⟨j, hj⟩).1 hm
      exact ⟨⟨ha, hb⟩, h1, h2, ⟨i, ⟨j, hj⟩, hji, hi, (isLead_iff hb ⟨j, hj⟩).1 hl, h0⟩⟩
  rw [himg, Nat.card_image_of_injOn hinj]
  have hc : Nat.card (↑(↑S : Set (ℕ × ℕ))) = S.card := by
    rw [Nat.card_eq_card_toFinset, Finset.toFinset_coe]
  rw [hc, hS, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun j _ => Finset.card_product _ _
  · intro j hj j' hj' hne
    rw [Function.onFun, Finset.disjoint_left]
    rintro ⟨a, b⟩ h1 h2
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at h1 h2
    rw [Finset.mem_coe, Finset.mem_range] at hj hj'
    have := isLead_unique ((isLead_iff h1.2.1 ⟨j, hj⟩).1 h1.2.2.2)
      ((isLead_iff h2.2.1 ⟨j', hj'⟩).1 h2.2.2.2)
    exact hne (congrArg Fin.val this)

theorem swWalk_spec (L M LF : ℕ → ℕ) (K q tot : ℕ) : ∀ c p prev,
    swWalk L M LF K q tot c p prev = true →
    (∀ t < c, redOK L M (pu1 (prec LF (p + t))) (pu2 (prec LF (p + t))) = true ∧
      lane1 K (pu1 (prec LF (p + t))) = true ∧ lane1 K (pu2 (prec LF (p + t))) = true) ∧
    ∀ t t', t < t' → t' < c →
      729 * pu1 (prec LF (p + t)) + pu2 (prec LF (p + t)) <
        729 * pu1 (prec LF (p + t')) + pu2 (prec LF (p + t')) := by
  intro c
  induction c with
  | zero => intro p prev _; exact ⟨fun t h => absurd h (Nat.not_lt_zero _),
      fun t t' _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ c ih =>
    intro p prev h
    change swStep L M LF K q tot p prev (swWalk L M LF K q tot c (p + 1)) = true at h
    simp only [swStep, strictB_eq, andB_eq_true, blt_eq_true, nadd, nmul] at h
    obtain ⟨-, -, hr, -, h1, h2, hw⟩ := h
    obtain ⟨i1, i2⟩ := ih _ _ hw
    have hfirst : ∀ c' (p' prev' : ℕ), swWalk L M LF K q tot (c' + 1) p' prev' = true →
        prev' < 729 * pu1 (prec LF p') + pu2 (prec LF p') := by
      intro c' p' prev' h'
      change swStep L M LF K q tot p' prev' (swWalk L M LF K q tot c' (p' + 1)) = true at h'
      simp only [swStep, strictB_eq, andB_eq_true, blt_eq_true, nadd, nmul] at h'
      exact h'.2.2.2.1
    have hs : ∀ t, p + 1 + t = p + (t + 1) := fun t => by omega
    refine ⟨fun t ht => ?_, fun t t' htt ht' => ?_⟩
    · rcases t with _ | t
      · exact ⟨hr, h1, h2⟩
      · rw [← hs]
        exact i1 t (by omega)
    · obtain ⟨t', rfl⟩ : ∃ u, t' = u + 1 := ⟨t' - 1, by omega⟩
      rw [← hs]
      rcases t with _ | t
      · rcases t' with _ | t'
        · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
          simpa using hfirst c' (p + 1) _ hw
        · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
          have a1 := hfirst c' (p + 1) _ hw
          have a2 := i2 0 (t' + 1) (by omega) (by omega)
          simp only [add_zero] at a1 a2 ⊢
          exact a1.trans a2
      · rw [← hs]
        exact i2 t t' (by omega) (by omega)

theorem b2n_eq_one {b : Bool} : b2n b = 1 ↔ b = true := by
  cases b <;> decide

open Classical in
theorem pop_link {Kq X : ℕ} {P : ℕ → Prop} {B : ℕ → Bool} (hK : Kq ≤ LOW12)
    (hKl : ∀ u < 729, (fld Kq 12 u = 1 ↔ P u) ∧ fld Kq 12 u ≤ 1)
    (hX : ∀ u < 729, fld X 12 u = b2n (B u)) :
    pop12 (Kq &&& X) = ((Finset.range 729).filter (fun u => P u ∧ B u = true)).card := by
  have hlt : Kq &&& X < 2 ^ (12 * 729) := lt_of_le_of_lt (Nat.and_le_left.trans hK) LOW12_lt
  have hl : ∀ u < 729, fld (Kq &&& X) 12 u = if P u ∧ B u = true then 1 else 0 := by
    intro u hu
    rw [fld_land, hX u hu, b2n_eq]
    obtain ⟨h1, h2⟩ := hKl u hu
    rcases (by omega : fld Kq 12 u = 0 ∨ fld Kq 12 u = 1) with h | h
    · have hP : ¬ P u := fun hp => by
        have := h1.2 hp
        omega
      rw [h, if_neg (fun hc : P u ∧ B u = true => hP hc.1)]
      split_ifs <;> rfl
    · have hP : P u := h1.1 h
      rw [h]
      by_cases hB : B u = true
      · rw [if_pos hB, if_pos ⟨hP, hB⟩]
        rfl
      · rw [if_neg hB, if_neg (fun hc => hB hc.2)]
        rfl
  have hl1 : ∀ i, fld (Kq &&& X) 12 i ≤ 1 := fun i => by
    rcases lt_or_ge i 729 with h | h
    · rw [hl i h]
      split_ifs <;> norm_num
    · rw [fld_eq_zero_of_lt 12 729 _ hlt h]
      omega
  rw [pop12_eq hlt hl1, Finset.card_filter]
  exact Finset.sum_congr rfl fun u hu => hl u (Finset.mem_range.1 hu)

theorem lane1_lt {K u : ℕ} (hK : K ≤ LOW12) (h : lane1 K u = true) : u < 729 := by
  by_contra hu
  have := fld_eq_zero_of_lt 12 729 K (lt_of_le_of_lt hK LOW12_lt) (by omega : 729 ≤ u)
  simp only [lane1, beq_eq_true, this] at h
  exact absurd h (by norm_num)

end SweepDecode

open CFSG.KC.TcRes.Lane in
theorem sweepRaw_of_checks
    {vec : ℕ → Fin Tag.E6.rank → ℤ} {rt : ℕ → ℕ → ℕ} {adj : ℕ → ℕ → Bool} {neg : ℕ → ℕ}
    {V REPS START : ℕ} {U RC L M LF : ℕ → ℕ} (hvec : vec = vecOf 6 V)
    (hD : DatumRaw Tag.E6 72 vec rt adj neg)
    (htab : ∀ i < 9, tabsOK U L M i = true) (hrc : ∀ g < 72, rcOK RC V g = true)
    {q : ℕ} (hq : q < 75) (hsw : swOK U RC L M LF REPS START q = true) {w : WeylGroup Tag.E6}
    (hw : TupleOf vec 72 (Nat.land (Nat.shiftRight REPS (q / 3 * 42)) M42) w) :
    SweepRaw (KSet w (sOf (q % 3) : ZMod 3)) (fld START 16 q) (fld START 16 (q + 1))
      (fun p => (v3 (pu1 (prec LF p)), v3 (pu2 (prec LF p)))) := by
  classical
  simp only [swOK, strictB_eq, andB_eq_true, beq_eq_true, nsub, Nat.succ_eq_add_one] at hsw
  obtain ⟨hnp, hwalk⟩ := hsw
  have hK := kq_le U RC REPS q
  have hKl := fun u (hu : u < 729) => kq_lane hvec htab hrc hw hu
  obtain ⟨hr, hmono⟩ := swWalk_spec L M LF _ q _ _ _ _ hwalk
  have hlane : ∀ {u}, lane1 (kq U RC REPS q) u = true →
      u < 729 ∧ v3 u ∈ KSet w (sOf (q % 3) : ZMod 3) := fun {u} h =>
    ⟨lane1_lt hK h, ((hKl u (lane1_lt hK h)).1).1 (beq_eq_true.1 h)⟩
  refine ⟨fun p hap hpe => ?_, fun p hap hpe p' hap' hpe' hpp => ?_, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hr (p - fld START 16 q) (by omega)
    rw [show fld START 16 q + (p - fld START 16 q) = p by omega] at h1 h2 h3
    obtain ⟨u1l, u1K⟩ := hlane h2
    obtain ⟨u2l, u2K⟩ := hlane h3
    refine ⟨u1K, u2K, ?_⟩
    simp only [redOK, anyLt_iff, andB_eq_true, lane1, beq_eq_true] at h1
    obtain ⟨j, hj, hL, hM⟩ := h1
    rw [(tab_lanes htab u2l hj).2.1, b2n_eq_one] at hL
    rw [(tab_lanes htab u1l hj).2.2, b2n_eq_one] at hM
    obtain ⟨⟨i, hji, hli⟩, h0⟩ := (mPred_iff u1l ⟨j, hj⟩).1 hM
    exact ⟨i, ⟨j, hj⟩, hji, hli, (isLead_iff u2l ⟨j, hj⟩).1 hL, h0⟩
  · obtain ⟨-, a2, a3⟩ := hr (p - fld START 16 q) (by omega)
    obtain ⟨-, b2, b3⟩ := hr (p' - fld START 16 q) (by omega)
    rw [show fld START 16 q + (p - fld START 16 q) = p by omega] at a2 a3
    rw [show fld START 16 q + (p' - fld START 16 q) = p' by omega] at b2 b3
    simp only [Prod.mk.injEq] at hpp
    have e1 := v3_inj (hlane a2).1 (hlane b2).1 hpp.1
    have e2 := v3_inj (hlane a3).1 (hlane b3).1 hpp.2
    have hk : 729 * pu1 (prec LF (fld START 16 q + (p - fld START 16 q))) +
        pu2 (prec LF (fld START 16 q + (p - fld START 16 q))) =
        729 * pu1 (prec LF (fld START 16 q + (p' - fld START 16 q))) +
        pu2 (prec LF (fld START 16 q + (p' - fld START 16 q))) := by
      rw [show fld START 16 q + (p - fld START 16 q) = p by omega,
        show fld START 16 q + (p' - fld START 16 q) = p' by omega, e1, e2]
    rcases lt_trichotomy (p - fld START 16 q) (p' - fld START 16 q) with h | h | h
    · exact absurd hk (ne_of_lt (hmono _ _ h (by omega)))
    · omega
    · exact absurd hk (ne_of_gt (hmono _ _ h (by omega)))
  · rw [card_redPairs, ← hnp, npairs_eq]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [pop_link (P := fun u => v3 u ∈ KSet w (sOf (q % 3) : ZMod 3)) (B := fun u => ldOK u j) hK
        (fun u hu => hKl u hu) (fun u hu => (tab_lanes htab hu hj).2.1),
      pop_link (P := fun u => v3 u ∈ KSet w (sOf (q % 3) : ZMod 3)) (B := fun u => mPred u j) hK
        (fun u hu => hKl u hu) (fun u hu => (tab_lanes htab hu hj).2.2), mul_comm]

theorem SweepRaw.surj {K : Set (Fin 6 → ZMod 3)} {a e : ℕ}
    {pr : ℕ → (Fin 6 → ZMod 3) × (Fin 6 → ZMod 3)} (h : SweepRaw K a e pr)
    {x : (Fin 6 → ZMod 3) × (Fin 6 → ZMod 3)} (hx : x ∈ RedPairs K) :
    ∃ p, a ≤ p ∧ p < e ∧ pr p = x := by
  classical
  let f : Fin (e - a) → RedPairs K := fun i => ⟨pr (a + i), h.mem _ (by omega) (by omega)⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have := h.inj _ (by omega) (by omega) _ (by omega) (by omega) (congrArg Subtype.val hij)
    exact Fin.ext (by omega)
  have hfin : Finite (RedPairs K) := Subtype.finite
  obtain ⟨i, hi⟩ := surjective_of_injective_card h.card f hinj ⟨x, hx⟩
  exact ⟨a + i, by omega, by omega, congrArg Subtype.val hi⟩

theorem SweepRaw.exists_record {K : Set (Fin 6 → ZMod 3)} {a e : ℕ}
    {pr : ℕ → (Fin 6 → ZMod 3) × (Fin 6 → ZMod 3)} (h : SweepRaw K a e pr)
    {P : Submodule (ZMod 3) (Fin 6 → ZMod 3)} (hP : Module.finrank (ZMod 3) P = 2)
    (hPK : ∀ v ∈ P, v ∈ K) :
    ∃ p, a ≤ p ∧ p < e ∧ (pr p).1 ∈ P ∧ (pr p).2 ∈ P ∧ IsReduced (pr p).1 (pr p).2 ∧
      ∀ v, v ∈ P ↔ ∃ s t : ZMod 3, v = s • (pr p).1 + t • (pr p).2 := by
  obtain ⟨u1, hu1, u2, hu2, hu⟩ := exists_reduced hP
  obtain ⟨p, hap, hpe, hp⟩ := h.surj (x := (u1, u2)) ⟨hPK _ hu1, hPK _ hu2, hu⟩
  refine ⟨p, hap, hpe, ?_⟩
  rw [hp]
  exact ⟨hu1, hu2, hu, hu.mem_iff hP hu1 hu2⟩

@[expose] def PhiP (vec : ℕ → Fin Tag.E6.rank → ℤ) (u1 u2 : Fin 6 → ZMod 3) : Set ℕ :=
  {g | g < 72 ∧ ∑ m : Fin 6, u1 m * ((vec g m : ℤ) : ZMod 3) = 0 ∧
    ∑ m : Fin 6, u2 m * ((vec g m : ℤ) : ZMod 3) = 0}

@[expose] def Conn (vec : ℕ → Fin Tag.E6.rank → ℤ) (S : Set ℕ) : ℕ → ℕ → Prop :=
  Relation.ReflTransGen fun a b => a ∈ S ∧ b ∈ S ∧ iform (vec a) (vec b) ≠ 0

section PlaneDecode

open CFSG.KC.TcRes.Lane

def LaneEq5 (x : ℕ) (f : ℕ → ℕ) (B : ℕ) : Prop := ∀ k < 72, fld x 5 k = f k ∧ f k ≤ B

theorem LaneEq5.add {a b : ℕ} {f g : ℕ → ℕ} {A B : ℕ} (ha : LaneEq5 a f A) (hb : LaneEq5 b g B)
    (hAB : A + B < 32) : LaneEq5 (a + b) (fun k => f k + g k) (A + B) := by
  intro k hk
  refine ⟨?_, Nat.add_le_add (ha k hk).2 (hb k hk).2⟩
  change fld (a + b) 5 k = f k + g k
  rw [fld_add_low (fun k' hk' => ?_), (ha k hk).1, (hb k hk).1]
  rw [(ha k' (by omega)).1, (hb k' (by omega)).1]
  have h1 := (ha k' (by omega)).2
  have h2 := (hb k' (by omega)).2
  have h3 : f k' + g k' < 32 := by omega
  exact lt_of_lt_of_eq h3 (by norm_num)

theorem LaneEq5.smul {a : ℕ} {f : ℕ → ℕ} {A : ℕ} (c : ℕ) (ha : LaneEq5 a f A) (hc : c * A < 32) :
    LaneEq5 (c * a) (fun k => c * f k) (c * A) := by
  intro k hk
  refine ⟨?_, Nat.mul_le_mul_left c (ha k hk).2⟩
  change fld (c * a) 5 k = c * f k
  rw [fld_smul_low (fun k' hk' => ?_), (ha k hk).1]
  rw [(ha k' (by omega)).1]
  exact lt_of_le_of_lt (Nat.mul_le_mul_left c (ha k' (by omega)).2)
    (lt_of_lt_of_eq hc (by norm_num))

theorem squash_rec (x : ℕ) : ∀ n, n ≤ 72 → ∀ i,
    (Nat.rec (motive := fun _ => ℕ) 0 (fun g ih => strictN ih fun a => Nat.lor (Nat.shiftLeft a 1)
      (Nat.land (Nat.shiftRight x (Nat.mul (Nat.sub 71 g) 5)) 1)) n).testBit i =
      (decide (i < n) && x.testBit (5 * (72 - n + i))) := by
  intro n
  induction n with
  | zero => intro _ i; simp
  | succ n ih =>
    intro hn i
    change (strictN (Nat.rec (motive := fun _ => ℕ) 0 (fun g ih => strictN ih fun a =>
      Nat.lor (Nat.shiftLeft a 1) (Nat.land (Nat.shiftRight x (Nat.mul (Nat.sub 71 g) 5)) 1)) n)
      fun a => Nat.lor (Nat.shiftLeft a 1)
        (Nat.land (Nat.shiftRight x (Nat.mul (Nat.sub 71 n) 5)) 1)).testBit i = _
    rw [strictN_eq, nlor, nshl, nland, nshr, nmul, nsub, Nat.testBit_or, Nat.testBit_shiftLeft,
      Nat.testBit_and, Nat.testBit_shiftRight]
    rcases i with _ | i
    · rw [show (71 - n) * 5 + 0 = 5 * (72 - (n + 1) + 0) by omega]
      simp
    · rw [Nat.add_sub_cancel, ih (by omega) i]
      have e : 5 * (72 - n + i) = 5 * (72 - (n + 1) + (i + 1)) := by omega
      rw [e]
      have h1 : (1 : ℕ).testBit (i + 1) = false := by
        rw [Nat.testBit_succ]
        simp
      simp only [h1, Bool.and_false, Bool.or_false]
      by_cases hi : i < n
      · simp [hi, show i + 1 < n + 1 by omega, show 1 ≤ i + 1 by omega]
      · simp [hi, show ¬ i + 1 < n + 1 by omega]

theorem squash_testBit (x : ℕ) {i : ℕ} : (squash x).testBit i = (decide (i < 72) && x.testBit (5 * i)) := by
  have := squash_rec x 72 le_rfl i
  rw [show 72 - 72 + i = i by omega] at this
  exact this

theorem dotmask_bit {RC : ℕ → ℕ} {V : ℕ} (hrc : ∀ g < 72, rcOK RC V g = true) (u : ℕ) {g : ℕ}
    (hg : g < 72) : (squash (zl LOW5 (dot5 RC u))).testBit g = true ↔
      ∑ m : Fin 6, v3 u m * (((fld (fld V 96 g) 16 m : ℤ) - 7 : ℤ) : ZMod 3) = 0 := by
  have hR : ∀ m < 6, LaneEq5 (RC m) (fun k => fld (RC m) 5 k) 2 := fun m hm k hk =>
    ⟨rfl, rc_le hrc hk hm⟩
  have d := fun m => dg_lt u m
  have hx := ((hR 0 (by norm_num)).smul (dg u 0) (by have := d 0; omega)).add
    (((hR 1 (by norm_num)).smul (dg u 1) (by have := d 1; omega)).add
    (((hR 2 (by norm_num)).smul (dg u 2) (by have := d 2; omega)).add
    (((hR 3 (by norm_num)).smul (dg u 3) (by have := d 3; omega)).add
    (((hR 4 (by norm_num)).smul (dg u 4) (by have := d 4; omega)).add
    ((hR 5 (by norm_num)).smul (dg u 5) (by have := d 5; omega))
      (by have := d 4; have := d 5; omega)) (by have := d 3; have := d 4; have := d 5; omega))
      (by have := d 2; have := d 3; have := d 4; have := d 5; omega))
      (by have := d 1; have := d 2; have := d 3; have := d 4; have := d 5; omega))
      (by have := d 0; have := d 1; have := d 2; have := d 3; have := d 4; have := d 5; omega)
  have hz := fld_zl_any (w := 5) (K := 72) (x := dot5 RC u) le_rfl (fun k hk => by
    change fld (dg u 0 * RC 0 + (dg u 1 * RC 1 + (dg u 2 * RC 2 + (dg u 3 * RC 3 +
      (dg u 4 * RC 4 + dg u 5 * RC 5))))) 5 k ≤ 28
    rw [(hx k hk).1]
    have := (hx k hk).2
    have := d 0
    have := d 1
    have := d 2
    have := d 3
    have := d 4
    have := d 5
    simp only at *
    omega) hg
  have hb : (squash (zl LOW5 (dot5 RC u))).testBit g =
      (fld (zl LOW5 (dot5 RC u)) 5 g).testBit 0 := by
    rw [squash_testBit, testBit_fld, decide_eq_true hg, Bool.true_and, add_zero]
    simp
  have hlane : fld (dot5 RC u) 5 g = dg u 0 * fld (RC 0) 5 g + (dg u 1 * fld (RC 1) 5 g +
      (dg u 2 * fld (RC 2) 5 g + (dg u 3 * fld (RC 3) 5 g + (dg u 4 * fld (RC 4) 5 g +
      dg u 5 * fld (RC 5) 5 g)))) := (hx g hg).1
  rw [hb]
  change (fld (zl (lowW 5 72) (dot5 RC u)) 5 g).testBit 0 = true ↔ _
  rw [hz, hlane]
  have h9 : (9 : ZMod 3) = 0 := by decide
  have e : ∀ m : Fin 6, v3 u m * (((fld (fld V 96 g) 16 m : ℤ) - 7 : ℤ) : ZMod 3) =
      ((dg u m * fld (RC m) 5 g : ℕ) : ZMod 3) := by
    intro m
    rw [rc_lane hrc hg m.2]
    push_cast
    rw [ZMod.natCast_mod]
    simp only [v3]
    push_cast
    congr 1
    rw [show (7 : ZMod 3) = -2 by decide]
    exact sub_neg_eq_add _ _
  rw [Fin.sum_univ_six]
  simp only [e]
  have v0 : ((0 : Fin 6) : ℕ) = 0 := rfl
  have v1 : ((1 : Fin 6) : ℕ) = 1 := rfl
  have v2 : ((2 : Fin 6) : ℕ) = 2 := rfl
  have v3' : ((3 : Fin 6) : ℕ) = 3 := rfl
  have v4 : ((4 : Fin 6) : ℕ) = 4 := rfl
  have v5 : ((5 : Fin 6) : ℕ) = 5 := rfl
  simp only [v0, v1, v2, v3', v4, v5]
  rw [← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add,
    natCast_zmod3_eq_zero]
  have hassoc : dg u 0 * fld (RC 0) 5 g + dg u 1 * fld (RC 1) 5 g + dg u 2 * fld (RC 2) 5 g +
      dg u 3 * fld (RC 3) 5 g + dg u 4 * fld (RC 4) 5 g + dg u 5 * fld (RC 5) 5 g =
      dg u 0 * fld (RC 0) 5 g + (dg u 1 * fld (RC 1) 5 g + (dg u 2 * fld (RC 2) 5 g +
      (dg u 3 * fld (RC 3) 5 g + (dg u 4 * fld (RC 4) 5 g + dg u 5 * fld (RC 5) 5 g)))) := by ring
  rw [hassoc]
  split_ifs <;> simp_all

theorem kmask_bit {vec : ℕ → Fin Tag.E6.rank → ℤ} {RC : ℕ → ℕ} {V : ℕ} (hvec : vec = vecOf 6 V)
    (hrc : ∀ g < 72, rcOK RC V g = true) (u1 u2 g : ℕ) :
    (kmask RC u1 u2).testBit g = true ↔ g ∈ PhiP vec (v3 u1) (v3 u2) := by
  rw [kmask, strictN_eq, strictN_eq, nland, Nat.testBit_and]
  subst hvec
  rcases lt_or_ge g 72 with hg | hg
  · rw [Bool.and_eq_true, dotmask_bit hrc u1 hg, dotmask_bit hrc u2 hg]
    exact ⟨fun h => ⟨hg, h.1, h.2⟩, fun h => ⟨h.2.1, h.2.2⟩⟩
  · rw [squash_testBit, decide_eq_false (by omega)]
    simp only [Bool.false_and, Bool.false_eq_true, false_iff]
    exact fun h => absurd h.1 (by omega)

theorem testBit_or_pow (a g x : ℕ) : (a ||| 1 <<< g).testBit x = (a.testBit x || decide (x = g)) := by
  rw [Nat.testBit_or, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
  by_cases h : x = g
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem pow_testBit (g x : ℕ) : (1 <<< g).testBit x = decide (x = g) := by
  rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
  by_cases h : x = g
  · subst h
    simp
  · simp [h, Ne.symm h]

end PlaneDecode

section Walk

open CFSG.KC.TcRes.Lane

variable {vec : ℕ → Fin Tag.E6.rank → ℤ} {S : Set ℕ} {ph : ℕ → ℕ}

def Good (vec : ℕ → Fin Tag.E6.rank → ℤ) (S : Set ℕ) (ph : ℕ → ℕ) (x : ℕ) : Prop :=
  ∃ r ∈ S, Conn vec S r x ∧ Conn vec S r (ph r)

def WInv (vec : ℕ → Fin Tag.E6.rank → ℤ) (S : Set ℕ) (ph : ℕ → ℕ) (acc C rt : ℕ) : Prop :=
  (∀ x, acc.testBit x = true → x ∈ S ∧ (C.testBit x = true ∨ Good vec S ph x)) ∧
  (C ≠ 0 → rt ∈ S ∧ ∀ x, C.testBit x = true → acc.testBit x = true ∧ Conn vec S rt x)

theorem finOK_close {P C rt NB : ℕ} (h : finOK ph P 0 C rt NB = true) {acc : ℕ}
    (hI : WInv vec S ph acc C rt) : ∀ x, C.testBit x = true → Good vec S ph x := by
  intro x hx
  have hC : C ≠ 0 := fun h0 => by
    rw [h0, Nat.zero_testBit] at hx
    exact absurd hx (by decide)
  simp only [finOK, orB_eq_true, beq_eq_true, strictB_eq, andB_eq_true, nland] at h
  rcases h with h | ⟨-, h⟩
  · exact absurd h hC
  · rcases h with h | h
    · exact absurd h (by norm_num)
    · obtain ⟨hrt, hall⟩ := hI.2 hC
      rw [bit_iff] at h
      exact ⟨rt, hrt, (hall x hx).2, (hall _ h).2⟩

theorem entWalk_succ (ADJ P mv c rest acc C rt NB : ℕ) :
    entWalk ADJ ph P mv (c + 1) rest acc C rt NB =
      CFSG.TcRes.TK.andB (bit P (rest &&& 127)) (CFSG.TcRes.TK.andB (CFSG.TcRes.TK.notB (bit acc (rest &&& 127)))
        (Bool.rec (motive := fun _ => Bool)
          (CFSG.TcRes.TK.andB (bit C ((rest >>> 7) &&& 127)) (CFSG.TcRes.TK.andB (bit (fld ADJ 72 (rest &&& 127))
              ((rest >>> 7) &&& 127))
            (entWalk ADJ ph P mv c (rest >>> 14) (acc ||| 1 <<< (rest &&& 127))
              (C ||| 1 <<< (rest &&& 127)) rt (NB ||| fld ADJ 72 (rest &&& 127)))))
          (CFSG.TcRes.TK.andB (finOK ph P mv C rt NB)
            (entWalk ADJ ph P mv c (rest >>> 14) (acc ||| 1 <<< (rest &&& 127))
              (1 <<< (rest &&& 127)) (rest &&& 127) (fld ADJ 72 (rest &&& 127))))
          (Nat.beq (rest &&& 127) ((rest >>> 7) &&& 127)))) := by
  simp only [entWalk, strictB_eq]
  rfl

theorem entWalk_spec {ADJ P : ℕ} (hP : ∀ g, P.testBit g = true ↔ g ∈ S)
    (hadj : ∀ g ∈ S, ∀ pa ∈ S, (fld ADJ 72 g).testBit pa = true → iform (vec pa) (vec g) ≠ 0) :
    ∀ c rest acc C rt NB, WInv vec S ph acc C rt → entWalk ADJ ph P 0 c rest acc C rt NB = true →
      ∀ g ∈ S, Good vec S ph g := by
  intro c
  induction c with
  | zero =>
    intro rest acc C rt NB hI h
    change CFSG.TcRes.TK.andB (finOK ph P 0 C rt NB) (Nat.beq acc P) = true at h
    rw [andB_eq_true, beq_eq_true] at h
    obtain ⟨hfin, rfl⟩ := h
    intro g hg
    rcases (hI.1 g ((hP g).2 hg)).2 with h | h
    · exact finOK_close hfin hI g h
    · exact h
  | succ c ih =>
    intro rest acc C rt NB hI h
    rw [entWalk_succ] at h
    simp only [andB_eq_true, notB_eq_true, boolRec_true, beq_eq_true, beq_eq_false] at h
    obtain ⟨hPg, hacc, hroot, hnon⟩ := h
    rw [bit_iff, hP] at hPg
    by_cases hgp : (rest &&& 127) = ((rest >>> 7) &&& 127)
    · obtain ⟨hfin, hw⟩ := hroot hgp
      refine ih _ _ _ _ _ ⟨fun x hx => ?_, fun _ => ⟨hPg, fun x hx => ?_⟩⟩ hw
      · rw [testBit_or_pow, Bool.or_eq_true, decide_eq_true_eq] at hx
        rcases hx with hx | rfl
        · obtain ⟨hxS, hx'⟩ := hI.1 x hx
          refine ⟨hxS, Or.inr ?_⟩
          rcases hx' with hx' | hx'
          · exact finOK_close hfin hI x hx'
          · exact hx'
        · exact ⟨hPg, Or.inl (by rw [pow_testBit, decide_eq_true rfl])⟩
      · rw [pow_testBit, decide_eq_true_eq] at hx
        subst hx
        exact ⟨by rw [testBit_or_pow]; simp, Relation.ReflTransGen.refl⟩
    · obtain ⟨hCpa, hag, hw⟩ := hnon hgp
      rw [bit_iff] at hCpa hag
      have hC : C ≠ 0 := fun h0 => by
        rw [h0, Nat.zero_testBit] at hCpa
        exact absurd hCpa (by decide)
      obtain ⟨hrt, hall⟩ := hI.2 hC
      have hpaS : ((rest >>> 7) &&& 127) ∈ S := (hI.1 _ (hall _ hCpa).1).1
      refine ih _ _ _ _ _ ⟨fun x hx => ?_, fun _ => ⟨hrt, fun x hx => ?_⟩⟩ hw
      · rw [testBit_or_pow, Bool.or_eq_true, decide_eq_true_eq] at hx
        rcases hx with hx | rfl
        · obtain ⟨hxS, hx'⟩ := hI.1 x hx
          refine ⟨hxS, ?_⟩
          rcases hx' with hx' | hx'
          · exact Or.inl (by rw [testBit_or_pow, hx']; rfl)
          · exact Or.inr hx'
        · exact ⟨hPg, Or.inl (by rw [testBit_or_pow]; simp)⟩
      · rw [testBit_or_pow, Bool.or_eq_true, decide_eq_true_eq] at hx
        rcases hx with hx | rfl
        · obtain ⟨h1, h2⟩ := hall x hx
          exact ⟨by rw [testBit_or_pow, h1]; rfl, h2⟩
        · refine ⟨by rw [testBit_or_pow]; simp, ?_⟩
          exact Relation.ReflTransGen.tail (hall _ hCpa).2
            ⟨hpaS, hPg, hadj _ hPg _ hpaS hag⟩

end Walk

open CFSG.KC.TcRes.Lane in
theorem planeRec_of_checks {vec : ℕ → Fin Tag.E6.rank → ℤ} {rt : ℕ → ℕ → ℕ} {neg : ℕ → ℕ}
    {V ADJ PW NEG e : ℕ} {RC : ℕ → ℕ} (hvec : vec = vecOf 6 V)
    (hD : DatumRaw Tag.E6 72 vec rt (fun g v => Nat.beq (fld (fld ADJ 72 g) 1 v) 1) neg)
    (hrc : ∀ g < 72, rcOK RC V g = true) (hpl : plOK RC ADJ PW NEG e = true)
    (hmv : Nat.land (Nat.shiftRight e 27) 1 = 0) :
    ∀ g ∈ PhiP vec (v3 (pu1 e)) (v3 (pu2 e)), ∃ r ∈ PhiP vec (v3 (pu1 e)) (v3 (pu2 e)),
      Conn vec (PhiP vec (v3 (pu1 e)) (v3 (pu2 e))) r g ∧
      Conn vec (PhiP vec (v3 (pu1 e)) (v3 (pu2 e))) r (phq PW NEG (pq e) r) := by
  simp only [plOK, strictB_eq] at hpl
  rw [hmv] at hpl
  refine entWalk_spec (S := PhiP vec (v3 (pu1 e)) (v3 (pu2 e)))
    (fun g => kmask_bit hvec hrc (pu1 e) (pu2 e) g) (fun g hg pa hpa h => ?_) _ _ 0 0 0 0
    ⟨fun x hx => by rw [Nat.zero_testBit] at hx; exact absurd hx (by decide),
      fun h => absurd rfl h⟩ hpl
  have := (hD.adj g hg.1 pa hpa.1).1
  apply this
  rw [CFSG.KC.TcRes.Lane.beq_eq_true, CFSG.KC.TcRes.Lane.fld_one_eq_one]
  exact h

theorem componentOrbitLength_eq_one_of_neg {τ : Tag} {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {Ψ : Set (Fin τ.rank → ℤ)} (hfin : Ψ.Finite) (hneg : ∀ γ ∈ Ψ, -γ ∈ Ψ)
    (hρ : ∀ γ ∈ Ψ, ρ γ = -γ) :
    CFSG.HardMathSupport.Timmesfeld.LangTorus.componentOrbitLength ρ Ψ = 1 := by
  have hmaps : ∀ γ ∈ Ψ, ρ γ ∈ Ψ := fun γ hγ => by
    rw [hρ γ hγ]
    exact hneg γ hγ
  have himg : (ρ : (Fin τ.rank → ℤ) → _)^[1] '' Ψ = Ψ := by
    rw [Function.iterate_one]
    exact ((hfin.injOn_iff_bijOn_of_mapsTo hmaps).1 ρ.injective.injOn).image_eq
  have hmem : 1 ∈ {s : ℕ | 0 < s ∧ (ρ : (Fin τ.rank → ℤ) → _)^[s] '' Ψ = Ψ} := ⟨one_pos, himg⟩
  refine le_antisymm (Nat.sInf_le hmem) ?_
  exact (Nat.sInf_mem ⟨1, hmem⟩).1

end CFSG.KC.TcRes

end
