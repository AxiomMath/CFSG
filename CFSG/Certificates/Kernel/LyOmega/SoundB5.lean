module

public import CFSG.Certificates.Kernel.LyOmega.Defs
public import CFSG.Certificates.Kernel.Spor.OrdSound
import all CFSG.Certificates.Kernel.Spor.OrdSound
public import Certificates.Data.Kernel.LyOmega.Small

public section
namespace CFSG.KS.LyOm.SB5
open CFSG.KC.LyOm CFSG.KC.LL CFSG.KS.LyOm

private theorem bAnd_true' {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a <;> simp_all

private theorem bAnd_eq (a b : Bool) :
    Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

private theorem nIf_eq (c : Bool) (t e : ℕ) :
    Bool.rec (motive := fun _ => ℕ) e t c = if c = true then t else e := by
  cases c <;> rfl

private theorem bIf_eq (c : Bool) (t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by
  cases c <;> rfl

private theorem sc_consts {C : SConsts} (hC : sConstsOK C = true) :
    CFSG.KC.Ord.constsOK 5 11 77 7 7 C.L7 C.H7 C.CM7 (Nat.sub (Nat.shiftLeft 1 77) 1) C.ONE
      (CFSG.KC.Ord.rep1 11 7) (Nat.shiftLeft (CFSG.KC.Ord.rep1 11 7) 10) = true := by
  unfold sConstsOK at hC
  obtain ⟨-, hC⟩ := bAnd_true' hC
  obtain ⟨-, hC⟩ := bAnd_true' hC
  obtain ⟨-, hC⟩ := bAnd_true' hC
  obtain ⟨hL7, hC⟩ := bAnd_true' hC
  obtain ⟨hH7, hC⟩ := bAnd_true' hC
  obtain ⟨hCM, hONE⟩ := bAnd_true' hC
  have e1 := Nat.eq_of_beq_eq_true hL7
  have e2 := Nat.eq_of_beq_eq_true hH7
  have e3 := Nat.eq_of_beq_eq_true hCM
  have e4 := Nat.eq_of_beq_eq_true hONE
  rw [e2, e1, e3, e4]
  decide +kernel


open CFSG.KS.Ord in
private theorem lcanon_iff {X : ℕ} : LCanon 11 7 7 X ↔ Canon 5 7 11 X := by
  unfold LCanon Canon
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by simpa using h1, fun t ht => ?_⟩
    have := h2 (t / 7) (by omega) (t % 7) (by omega)
    have e : 11 * 7 * (t / 7) + 11 * (t % 7) = 11 * t := by omega
    unfold lane
    rw [e] at this
    simpa using this
  · rintro ⟨h1, h2⟩
    refine ⟨by simpa using h1, fun i hi j hj => ?_⟩
    have := h2 (7 * i + j) (by omega)
    have e : 11 * 7 * i + 11 * j = 11 * (7 * i + j) := by ring
    unfold lane at this
    rw [e]
    simpa using this

theorem smM_eq (X : ℕ) : smM X = CFSG.KS.Ord.ordMat 5 7 11 77 X := rfl

open CFSG.KS.Ord in
private theorem ordMat_lane {X : ℕ} (i j : Fin 7) :
    ordMat 5 7 11 77 X i j = ((lane 11 X (7 * i.val + j.val) : ℕ) : ZMod 5) := by
  unfold ordMat lane
  have e : 77 * i.val + 11 * j.val = 11 * (7 * i.val + j.val) := by ring
  rw [e]

open CFSG.KS.Ord in
private theorem ord_inj {X Y : ℕ} (hX : Canon 5 7 11 X) (hY : Canon 5 7 11 Y)
    (h : ordMat 5 7 11 77 X = ordMat 5 7 11 77 Y) : X = Y := by
  have hl : ∀ t < 7 * 7, lane 11 X t = lane 11 Y t := by
    intro t ht
    have := congrFun (congrFun h ⟨t / 7, by omega⟩) ⟨t % 7, by omega⟩
    rw [ordMat_lane, ordMat_lane] at this
    have e : 7 * (t / 7) + t % 7 = t := by omega
    simp only [e] at this
    have := (ZMod.natCast_eq_natCast_iff' _ _ 5).1 this
    rwa [Nat.mod_eq_of_lt (hX.2 t ht), Nat.mod_eq_of_lt (hY.2 t ht)] at this
  rw [pk_lane (by norm_num) hX.1, pk_lane (by norm_num) hY.1]
  exact pk_congr (fun t ht => hl t ht)

open CFSG.KS.Ord in
private theorem sMul_fact {C : SConsts} (hC : sConstsOK C = true) {X Y : ℕ}
    (hX : LCanon 11 7 7 X) (hY : LCanon 11 7 7 Y) :
    LCanon 11 7 7 (sMul C X Y) ∧ smM (sMul C X Y) = smM X * smM Y := by
  have := mulR_sound (sc_consts hC) (lcanon_iff.1 hX) (lcanon_iff.1 hY)
  exact ⟨lcanon_iff.2 this.1, this.2⟩

open CFSG.KS.Ord in
private theorem one_fact {C : SConsts} (hC : sConstsOK C = true) :
    LCanon 11 7 7 C.ONE ∧ smM C.ONE = 1 := by
  have := one_sound (sc_consts hC)
  exact ⟨lcanon_iff.2 this.1, this.2⟩

private theorem canon_inj {X Y : ℕ} (hX : LCanon 11 7 7 X) (hY : LCanon 11 7 7 Y)
    (h : smM X = smM Y) : X = Y :=
  ord_inj (lcanon_iff.1 hX) (lcanon_iff.1 hY) h

private theorem zero_fact : LCanon 11 7 7 0 ∧ smM 0 = 0 := by
  refine ⟨⟨by norm_num, fun i _ j _ => by simp⟩, ?_⟩
  funext i j
  simp [smM, ent]


open CFSG.KS.Ord in
private theorem canon_decomp {p d w X : ℕ} (hw : 0 < w) (hX : Canon p d w X) :
    ∃ x, X = pk w (d * d) x ∧ ∀ t < d * d, x t < p :=
  ⟨lane w X, pk_lane hw hX.1, hX.2⟩

open CFSG.KS.Ord in
private theorem ordMat77_pk {g : ℕ → ℕ} (hg : ∀ t < 7 * 7, g t < 2 ^ 11) (i j : Fin 7) :
    ordMat 5 7 11 77 (pk 11 (7 * 7) g) i j = ((g (7 * i.val + j.val) : ℕ) : ZMod 5) :=
  ordMat_pk hg i j

open CFSG.KS.Ord in
private theorem sSub1_key {C : SConsts} (hC : sConstsOK C = true) {x : ℕ → ℕ}
    (hx : ∀ t < 7 * 7, x t < 5) :
    LCanon 11 7 7 (sSub1 C (pk 11 (7 * 7) x)) ∧
      smM (sSub1 C (pk 11 (7 * 7) x)) = smM (pk 11 (7 * 7) x) - 1 := by
  obtain ⟨-, -, hw, -, hT, -, hL, hH, -, -, hONE⟩ := consts_facts (sc_consts hC)
  have hx' : ∀ t < 7 * 7, x t < 2 ^ 11 := fun t ht => Nat.lt_of_lt_of_le (hx t ht) (by norm_num)
  have hδ : ∀ t < 7 * 7, (if t / 7 = t % 7 then 1 else 0) < 2 ^ 11 := fun t _ => by split <;> norm_num
  have hone : ∀ i j : Fin 7, (1 : Matrix (Fin 7) (Fin 7) (ZMod 5)) i j =
      (((if (7 * i.val + j.val) / 7 = (7 * i.val + j.val) % 7 then 1 else 0 : ℕ)) : ZMod 5) := by
    intro i j
    rw [← (one_fact hC).2, smM_eq, hONE]
    exact ordMat77_pk hδ i j
  have e : pk 11 (7 * 7) x + 4 * C.ONE =
      pk 11 (7 * 7) (fun t => x t + 4 * (if t / 7 = t % 7 then 1 else 0)) := by
    rw [hONE, Nat.mul_comm 4, pk_mul, pk_add]
    exact pk_congr fun t _ => by ring
  have hf : ∀ t < 7 * 7, x t + 4 * (if t / 7 = t % 7 then 1 else 0) < 2 ^ (11 - 1) := by
    intro t ht
    have := hx t ht
    split <;> norm_num <;> omega
  have hf2 : ∀ t < 7 * 7, x t + 4 * (if t / 7 = t % 7 then 1 else 0) < 5 * 2 ^ (7 + 1) := by
    intro t ht
    have := hx t ht
    split <;> norm_num <;> omega
  have hr : sSub1 C (pk 11 (7 * 7) x) = pk 11 (7 * 7)
      (fun t => (x t + 4 * (if t / 7 = t % 7 then 1 else 0)) % 5) := by
    unfold sSub1
    have h1 : Nat.add (pk 11 (7 * 7) x) (Nat.mul 4 C.ONE) = pk 11 (7 * 7) x + 4 * C.ONE := rfl
    rw [h1, e, hL, hH]
    exact redP_pk (by norm_num) (by norm_num) hf hf2
  have hg : ∀ t < 7 * 7, (x t + 4 * (if t / 7 = t % 7 then 1 else 0)) % 5 < 5 :=
    fun t _ => Nat.mod_lt _ (by norm_num)
  rw [hr]
  refine ⟨lcanon_iff.2 (canon_pk hg (by norm_num)), ?_⟩
  funext i j
  rw [smM_eq, ordMat77_pk (fun t ht => Nat.lt_of_lt_of_le (hg t ht) (by norm_num)),
    Matrix.sub_apply, hone, smM_eq, ordMat77_pk hx', ZMod.natCast_mod]
  push_cast
  have h4 : (4 : ZMod 5) = -1 := by decide
  rw [h4]
  ring

open CFSG.KS.Ord in
private theorem sSub1_fact {C : SConsts} (hC : sConstsOK C = true) {X : ℕ}
    (hX : LCanon 11 7 7 X) : LCanon 11 7 7 (sSub1 C X) ∧ smM (sSub1 C X) = smM X - 1 := by
  obtain ⟨x, hXx, hx⟩ := canon_decomp (by norm_num : 0 < 11) (lcanon_iff.1 hX)
  have := sSub1_key hC hx
  rw [← hXx] at this
  exact this

private theorem rank_le_one_of {K : Type*} [Field K] (M : Matrix (Fin 7) (Fin 7) K)
    (h : ∀ i k j l, M i j * M k l = M i l * M k j) : M.rank ≤ 1 := by
  by_cases h0 : M = 0
  · subst h0; simp
  obtain ⟨r, c, hrc⟩ : ∃ r c, M r c ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h0 (by ext i j; exact hcon i j)
  rw [M.rank_eq_finrank_span_row]
  have hle : Submodule.span K (Set.range M.row) ≤ Submodule.span K {M.row r} := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    refine Submodule.mem_span_singleton.2 ⟨M i c / M r c, ?_⟩
    funext j
    simp only [Matrix.row, Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, div_eq_iff hrc]
    have := h i r j c
    rw [this]
  refine (Submodule.finrank_mono hle).trans ?_
  simpa using finrank_span_le_card (R := K) ({M.row r} : Set (Fin 7 → K))

private theorem two_le_rank_of {K : Type*} [Field K] (M : Matrix (Fin 7) (Fin 7) K)
    (h : ¬ ∀ i k j l, M i j * M k l = M i l * M k j) : 2 ≤ M.rank := by
  push Not at h
  obtain ⟨i, k, j, l, hne⟩ := h
  have hli : LinearIndependent K (M.submatrix ![i, k] id).row := by
    have e : (M.submatrix ![i, k] id).row = ![M i, M k] := by
      ext a b
      fin_cases a <;> rfl
    rw [e, LinearIndependent.pair_iff]
    intro a b hab
    have h1 := congrFun hab j
    have h2 := congrFun hab l
    simp at h1 h2
    have hd : M i j * M k l - M i l * M k j ≠ 0 := sub_ne_zero.2 hne
    have ha : a * (M i j * M k l - M i l * M k j) = 0 := by linear_combination M k l * h1 - M k j * h2
    have hb : b * (M i j * M k l - M i l * M k j) = 0 := by linear_combination M i j * h2 - M i l * h1
    exact ⟨(mul_eq_zero.1 ha).resolve_right hd, (mul_eq_zero.1 hb).resolve_right hd⟩
  have h3 : (M.submatrix ![i, k] id).rank = 2 := by simpa using hli.rank_matrix
  have h2 := Matrix.rank_submatrix_le M ![i, k] (id : Fin 7 → Fin 7)
  omega

private theorem fldW_eq (r o w : ℕ) : fldW r o w = r / 2 ^ o % 2 ^ w := by
  change (r >>> o) &&& (1 <<< w - 1) = _
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

private theorem sEnt_eq (X i j : ℕ) : sEnt X i j = X / 2 ^ (77 * i + 11 * j) % 2 ^ 11 := by
  unfold sEnt
  rw [fldW_eq]
  rfl

private theorem smM_apply (X : ℕ) (i j : Fin 7) :
    smM X i j = ((sEnt X i.val j.val : ℕ) : ZMod 5) := by
  rw [sEnt_eq]
  rfl

private theorem beq_iff {a b : ℕ} : Nat.beq a b = true ↔ a = b := by rw [Nat.beq_eq]

private theorem blt_iff {a b : ℕ} : Nat.blt a b = true ↔ a < b := by rw [Nat.blt_eq]

private theorem rec_add (f : ℕ → ℕ) : ∀ n,
    Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.add acc (f i)) n = ∑ i ∈ Finset.range n, f i
  | 0 => rfl
  | n + 1 => by
    rw [Finset.sum_range_succ, ← rec_add f n]
    rfl

private theorem trace_iff (X : ℕ) : sTrace X = 1 ↔ (smM X).trace = 1 := by
  have h1 : sTrace X = (∑ i ∈ Finset.range 7, sEnt X i i) % 5 := by
    unfold sTrace
    exact congrArg (· % 5) (rec_add (fun i => sEnt X i i) 7)
  have h2 : (smM X).trace = ((∑ i ∈ Finset.range 7, sEnt X i i : ℕ) : ZMod 5) := by
    rw [Matrix.trace, Nat.cast_sum, ← Fin.sum_univ_eq_sum_range (fun i => ((sEnt X i i : ℕ) : ZMod 5)) 7]
    simp only [Matrix.diag, smM_apply]
  rw [h1, h2]
  have := ZMod.natCast_eq_natCast_iff' (∑ i ∈ Finset.range 7, sEnt X i i) 1 5
  rw [Nat.cast_one] at this
  rw [this]

private theorem recAll_iff (g : ℕ → Bool) : ∀ n,
    Nat.rec (motive := fun _ => Bool) true (fun k ih => Bool.rec (motive := fun _ => Bool) false ih (g k)) n = true ↔
      ∀ k < n, g k = true
  | 0 => by simp
  | n + 1 => by
    show Bool.rec (motive := fun _ => Bool) false (Nat.rec (motive := fun _ => Bool) true
      (fun k ih => Bool.rec (motive := fun _ => Bool) false ih (g k)) n) (g n) = true ↔ _
    rw [bAnd_eq, Bool.and_eq_true, recAll_iff g n]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
      · exact h2 k h
      · exact h ▸ h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun k hk => h k (Nat.lt_succ_of_lt hk)⟩

private theorem allBelow_iff {m hi : ℕ} {f : ℕ → Bool} (hm : m ≤ 64 * hi) :
    CFSG.KC.Loop.allBelow m hi f = true ↔ ∀ i < m, f i = true := by
  unfold CFSG.KC.Loop.allBelow
  rw [recAll_iff (fun h => Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      Bool.rec (motive := fun _ => Bool) false ih2
        ((fun i => Bool.rec (motive := fun _ => Bool) true (f i) (Nat.blt i m))
          (Nat.add (Nat.shiftLeft h 6) l))) 64) hi]
  have e : ∀ h l, Nat.add (Nat.shiftLeft h 6) l = 64 * h + l := by
    intro h l
    change (h <<< 6) + l = _
    rw [Nat.shiftLeft_eq]
    show h * 2 ^ 6 + l = _
    omega
  have inner : ∀ h, Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      Bool.rec (motive := fun _ => Bool) false ih2
        ((fun i => Bool.rec (motive := fun _ => Bool) true (f i) (Nat.blt i m))
          (Nat.add (Nat.shiftLeft h 6) l))) 64 = true ↔ ∀ l < 64, (64 * h + l < m → f (64 * h + l) = true) := by
    intro h
    rw [recAll_iff (fun l => (fun i => Bool.rec (motive := fun _ => Bool) true (f i) (Nat.blt i m))
          (Nat.add (Nat.shiftLeft h 6) l)) 64]
    refine forall_congr' fun l => imp_congr_right fun _ => ?_
    simp only [e]
    rw [bIf_eq]
    by_cases hlt : 64 * h + l < m
    · have : Nat.blt (64 * h + l) m = true := blt_iff.2 hlt
      simp [this, hlt]
    · have : ¬ Nat.blt (64 * h + l) m = true := fun hh => hlt (blt_iff.1 hh)
      simp [this, hlt]
  simp only [inner]
  constructor
  · intro H i hi
    have := H (i / 64) (by omega) (i % 64) (by omega)
    have e2 : 64 * (i / 64) + i % 64 = i := by omega
    rw [e2] at this
    exact this hi
  · intro H h hh l hl hlt
    exact H _ hlt

private noncomputable def minorB (Y i k j l : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) true
    (Nat.beq (Nat.mod (Nat.add (Nat.mul (sEnt Y i j) (sEnt Y k l))
      (Nat.mul 4 (Nat.mul (sEnt Y i l) (sEnt Y k j)))) 5) 0)
    (Bool.rec (motive := fun _ => Bool) false (Nat.blt j l) (Nat.blt i k))

private theorem sRk1_eq (Y : ℕ) : sRk1 Y = CFSG.KC.Loop.allBelow 2401 38
    (fun t => minorB Y (t / 343) (t / 49 % 7) (t / 7 % 7) (t % 7)) := rfl

private theorem minorB_iff (Y i k j l : ℕ) : minorB Y i k j l = true ↔
    (i < k → j < l → (sEnt Y i j * sEnt Y k l + 4 * (sEnt Y i l * sEnt Y k j)) % 5 = 0) := by
  unfold minorB
  rw [bAnd_eq, bIf_eq]
  by_cases h1 : i < k
  · by_cases h2 : j < l
    · have e1 : Nat.blt i k = true := blt_iff.2 h1
      have e2 : Nat.blt j l = true := blt_iff.2 h2
      simp [e1, e2, h1, h2, beq_iff]
      exact Iff.rfl
    · have e2 : ¬ Nat.blt j l = true := fun hh => h2 (blt_iff.1 hh)
      simp [h1, h2, e2]
  · have e1 : ¬ Nat.blt i k = true := fun hh => h1 (blt_iff.1 hh)
    simp [h1, e1]

private theorem minor_zmod (Y i k j l : ℕ) :
    (sEnt Y i j * sEnt Y k l + 4 * (sEnt Y i l * sEnt Y k j)) % 5 = 0 ↔
      ((sEnt Y i j : ℕ) : ZMod 5) * ((sEnt Y k l : ℕ) : ZMod 5) =
        ((sEnt Y i l : ℕ) : ZMod 5) * ((sEnt Y k j : ℕ) : ZMod 5) := by
  have := ZMod.natCast_eq_natCast_iff' (sEnt Y i j * sEnt Y k l + 4 * (sEnt Y i l * sEnt Y k j)) 0 5
  rw [Nat.zero_mod] at this
  rw [← this]
  push_cast
  have h4 : (4 : ZMod 5) = -1 := by decide
  rw [h4]
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

private theorem sRk1_iff (Y : ℕ) : sRk1 Y = true ↔
    ∀ i k j l : Fin 7, smM Y i j * smM Y k l = smM Y i l * smM Y k j := by
  rw [sRk1_eq, allBelow_iff (by norm_num)]
  constructor
  · intro H
    have H' : ∀ i k j l : Fin 7, i.val < k.val → j.val < l.val →
        smM Y i j * smM Y k l = smM Y i l * smM Y k j := by
      intro i k j l hik hjl
      have := H (343 * i.val + 49 * k.val + 7 * j.val + l.val) (by omega)
      have e1 : (343 * i.val + 49 * k.val + 7 * j.val + l.val) / 343 = i.val := by omega
      have e2 : (343 * i.val + 49 * k.val + 7 * j.val + l.val) / 49 % 7 = k.val := by omega
      have e3 : (343 * i.val + 49 * k.val + 7 * j.val + l.val) / 7 % 7 = j.val := by omega
      have e4 : (343 * i.val + 49 * k.val + 7 * j.val + l.val) % 7 = l.val := by omega
      simp only [e1, e2, e3, e4] at this
      have := ((minorB_iff _ _ _ _ _).1 this) hik hjl
      simp only [smM_apply]
      exact (minor_zmod _ _ _ _ _).1 this
    intro i k j l
    rcases lt_trichotomy i.val k.val with hik | hik | hik
    · rcases lt_trichotomy j.val l.val with hjl | hjl | hjl
      · exact H' i k j l hik hjl
      · have : j = l := Fin.ext hjl
        subst this; ring
      · have := H' i k l j hik hjl
        linear_combination -this
    · have : i = k := Fin.ext hik
      subst this; ring
    · rcases lt_trichotomy j.val l.val with hjl | hjl | hjl
      · have := H' k i j l hik hjl
        linear_combination -this
      · have : j = l := Fin.ext hjl
        subst this; ring
      · have := H' k i l j hik hjl
        linear_combination this
  · intro H t ht
    rw [minorB_iff]
    intro _ _
    have := H ⟨t / 343, by omega⟩ ⟨t / 49 % 7, by omega⟩ ⟨t / 7 % 7, by omega⟩ ⟨t % 7, by omega⟩
    simp only [smM_apply] at this
    exact (minor_zmod _ _ _ _ _).2 this

private instance fact5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

private theorem sRk1_rank {Y : ℕ} :
    (sRk1 Y = true ↔ (smM Y).rank ≤ 1) ∧ (sRk1 Y = false ↔ 2 ≤ (smM Y).rank) := by
  have h1 : sRk1 Y = true ↔ (smM Y).rank ≤ 1 := by
    rw [sRk1_iff]
    constructor
    · exact rank_le_one_of (smM Y)
    · intro h
      by_contra hn
      have := two_le_rank_of (smM Y) hn
      omega
  refine ⟨h1, ?_⟩
  rw [Bool.eq_false_iff, ne_eq, h1]
  omega

theorem sClass_sound {C : SConsts} (hC : sConstsOK C = true) {X : ℕ} (hX : LCanon 11 7 7 X) :
    sClass C X = (if smM X ^ 2 = 1 ∧ smM X ≠ 1 then 1 else 0) +
      (if smM X ^ 3 = 1 ∧ smM X ≠ 1 ∧ (smM X).trace = 1 then 2 ^ 16 else 0) +
      (if smM X ^ 5 = 1 ∧ smM X ≠ 1 ∧ (smM X - 1) ^ 2 = 0 then 2 ^ 32 else 0) +
      (if smM X ^ 5 = 1 ∧ smM X ≠ 1 ∧ 2 ≤ ((smM X - 1) ^ 2).rank then 2 ^ 48 else 0) := by
  obtain ⟨hO1, hO2⟩ := one_fact hC
  obtain ⟨h22, e22⟩ := sMul_fact hC hX hX
  obtain ⟨h3, e3⟩ := sMul_fact hC h22 hX
  obtain ⟨h5, e5⟩ := sMul_fact hC h3 h22
  obtain ⟨hS, eS⟩ := sSub1_fact hC hX
  obtain ⟨hW, eW⟩ := sMul_fact hC hS hS
  have hOne : ∀ Z, LCanon 11 7 7 Z → (Nat.beq Z C.ONE = true ↔ smM Z = 1) := by
    intro Z hZ
    rw [beq_iff]
    constructor
    · intro h; rw [h, hO2]
    · intro h; exact canon_inj hZ hO1 (by rw [hO2, h])
  have hZero : ∀ Z, LCanon 11 7 7 Z → (Nat.beq Z 0 = true ↔ smM Z = 0) := by
    intro Z hZ
    rw [beq_iff]
    constructor
    · intro h; rw [h, zero_fact.2]
    · intro h; exact canon_inj hZ zero_fact.1 (by rw [zero_fact.2, h])
  classical
  have p2 : smM X * smM X = smM X ^ 2 := (pow_two _).symm
  have p3 : smM X * smM X * smM X = smM X ^ 3 := by noncomm_ring
  have p5 : smM X * smM X * smM X * (smM X * smM X) = smM X ^ 5 := by noncomm_ring
  have pW : (smM X - 1) * (smM X - 1) = (smM X - 1) ^ 2 := (pow_two _).symm
  have b1 : Nat.beq X C.ONE = decide (smM X = 1) := by
    cases h : Nat.beq X C.ONE <;> simp [← hOne X hX, h]
  have b2 : Nat.beq (sMul C X X) C.ONE = decide (smM X ^ 2 = 1) := by
    have := hOne _ h22
    rw [e22, p2] at this
    cases h : Nat.beq (sMul C X X) C.ONE <;> simp_all
  have b3 : Nat.beq (sMul C (sMul C X X) X) C.ONE = decide (smM X ^ 3 = 1) := by
    have := hOne _ h3
    rw [e3, e22, p3] at this
    cases h : Nat.beq (sMul C (sMul C X X) X) C.ONE <;> simp_all
  have b5 : Nat.beq (sMul C (sMul C (sMul C X X) X) (sMul C X X)) C.ONE = decide (smM X ^ 5 = 1) := by
    have := hOne _ h5
    rw [e5, e3, e22, p5] at this
    cases h : Nat.beq (sMul C (sMul C (sMul C X X) X) (sMul C X X)) C.ONE <;> simp_all
  have bt : Nat.beq (sTrace X) 1 = decide ((smM X).trace = 1) := by
    have := trace_iff X
    rw [← beq_iff] at this
    cases h : Nat.beq (sTrace X) 1 <;> simp_all
  have bW : Nat.beq (sMul C (sSub1 C X) (sSub1 C X)) 0 = decide ((smM X - 1) ^ 2 = 0) := by
    have := hZero _ hW
    rw [eW, eS, pW] at this
    cases h : Nat.beq (sMul C (sSub1 C X) (sSub1 C X)) 0 <;> simp_all
  have hR := (sRk1_rank (Y := sMul C (sSub1 C X) (sSub1 C X))).1
  rw [eW, eS, pW] at hR
  have bR : sRk1 (sMul C (sSub1 C X) (sSub1 C X)) = decide (((smM X - 1) ^ 2).rank ≤ 1) := by
    cases h : sRk1 (sMul C (sSub1 C X) (sSub1 C X)) <;> simp_all
  have hz : (smM X - 1) ^ 2 = 0 → ¬ 2 ≤ ((smM X - 1) ^ 2).rank := by
    intro h; rw [h]; simp
  unfold sClass
  beta_reduce
  have s16 : Nat.shiftLeft (nat_lit 1) (nat_lit 16) = 65536 := rfl
  have s32 : Nat.shiftLeft (nat_lit 1) (nat_lit 32) = 4294967296 := rfl
  have s48 : Nat.shiftLeft (nat_lit 1) (nat_lit 48) = 281474976710656 := rfl
  simp only [bAnd_eq, nIf_eq, bIf_eq, b1, b2, b3, b5, bt, bW, bR, s16, s32, s48, Nat.add_eq,
    decide_eq_true_eq, Bool.and_eq_true, Bool.false_eq_true, ite_false, ite_true, Bool.not_eq_true]
  by_cases ha : smM X = 1
  · simp [ha]
  by_cases hz : (smM X - 1) ^ 2 = 0
  · have hr : ((smM X - 1) ^ 2).rank ≤ 1 := by rw [hz]; simp
    by_cases hb : smM X ^ 2 = 1 <;> by_cases hc : smM X ^ 3 = 1 <;>
      by_cases ht : (smM X).trace = 1 <;> by_cases he : smM X ^ 5 = 1 <;>
      simp [ha, hb, hc, ht, he, hz, hr] <;> first | rfl | omega
  · by_cases hr : ((smM X - 1) ^ 2).rank ≤ 1
    · have hr' : ¬ 2 ≤ ((smM X - 1) ^ 2).rank := by omega
      by_cases hb : smM X ^ 2 = 1 <;> by_cases hc : smM X ^ 3 = 1 <;>
        by_cases ht : (smM X).trace = 1 <;> by_cases he : smM X ^ 5 = 1 <;>
        simp [ha, hb, hc, ht, he, hz, hr, hr'] <;> first | rfl | omega
    · have hr' : 2 ≤ ((smM X - 1) ^ 2).rank := by omega
      by_cases hb : smM X ^ 2 = 1 <;> by_cases hc : smM X ^ 3 = 1 <;>
        by_cases ht : (smM X).trace = 1 <;> by_cases he : smM X ^ 5 = 1 <;>
        simp [ha, hb, hc, ht, he, hz, hr, hr'] <;> first | rfl | omega

end CFSG.KS.LyOm.SB5
end
