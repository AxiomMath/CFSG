module

public import Certificates.Data.Kernel.E8Five.Defs
public import Certificates.Data.E8FiveStab

public section

namespace CFSG.KC.E8Five

open CFSG.RankThree.PartOne.KE8F CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice
open CFSG.RankThree.E6 (charVal)

theorem bandK_eq (a b : Bool) : bandK a b = (a && b) := by cases a <;> rfl

theorem beqB_eq_true {a b : Bool} (h : beqB a b = true) : a = b := by
  cases a <;> cases b <;> simp_all [beqB]

theorem bitK_eq (b : Bool) : bitK b = if b = true then 1 else 0 := by cases b <;> rfl

theorem allNK_iff (n : ℕ) (f : ℕ → Bool) : allNK n f = true ↔ ∀ k < n, f k = true := by
  induction n with
  | zero => simp [allNK]
  | succ n ih =>
    change bandK (f n) (allNK n f) = true ↔ _
    rw [bandK_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact h2 k hk
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun k hk => h k (Nat.lt_succ_of_lt hk)⟩

theorem cntNK_eq (n : ℕ) (f : ℕ → Bool) :
    cntNK n f = ((Finset.range n).filter fun k => f k = true).card := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change bitK (f n) + cntNK n f = _
    rw [ih, Finset.range_add_one, Finset.filter_insert, bitK_eq]
    by_cases h : f n = true
    · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem (by simp)]
      omega
    · rw [if_neg h, if_neg h]
      omega

theorem cntRootsK_eq (rows : List ℕ) (n : ℕ) :
    cntRootsK rows n = rows.countP fun r => Nat.beq (dot5 r n) 0 := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    change bitK (Nat.beq (dot5 r n) 0) + cntRootsK rows n = _
    rw [ih, List.countP_cons, bitK_eq]
    omega

theorem t40K_iff (rows : List ℕ) (n : ℕ) :
    t40K rows n = true ↔ n ≠ 0 ∧ cntRootsK rows n = 40 := by
  unfold t40K
  rw [bandK_eq, Bool.and_eq_true]
  by_cases h : n = 0
  · subst h
    simp
  · have h' : Nat.beq n 0 = false := by
      cases hb : Nat.beq n 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) h
    rw [h']
    simp [h]

theorem dot5_eq (a b : ℕ) : dot5 a b =
    (a % 5 * (b % 5) + a / 5 % 5 * (b / 5 % 5) + (a / 25 % 5 * (b / 25 % 5) +
      a / 125 % 5 * (b / 125 % 5))) % 5 := rfl

theorem dot5_lt (a b : ℕ) : dot5 a b < 5 := by
  rw [dot5_eq]
  exact Nat.mod_lt _ (by norm_num)

@[expose] def enc (c : Fin 4 → ZMod 5) : ℕ :=
  (c 0).val + 5 * (c 1).val + 25 * (c 2).val + 125 * (c 3).val

@[expose] def dec (n : ℕ) : Fin 4 → ZMod 5 :=
  ![((n % 5 : ℕ) : ZMod 5), ((n / 5 % 5 : ℕ) : ZMod 5), ((n / 25 % 5 : ℕ) : ZMod 5),
    ((n / 125 % 5 : ℕ) : ZMod 5)]

theorem enc_digits (c : Fin 4 → ZMod 5) :
    enc c % 5 = (c 0).val ∧ enc c / 5 % 5 = (c 1).val ∧ enc c / 25 % 5 = (c 2).val ∧
      enc c / 125 % 5 = (c 3).val ∧ enc c < 625 := by
  have h0 := ZMod.val_lt (c 0)
  have h1 := ZMod.val_lt (c 1)
  have h2 := ZMod.val_lt (c 2)
  have h3 := ZMod.val_lt (c 3)
  unfold enc
  omega

theorem enc_lt (c : Fin 4 → ZMod 5) : enc c < 625 := (enc_digits c).2.2.2.2

theorem dec_enc (c : Fin 4 → ZMod 5) : dec (enc c) = c := by
  obtain ⟨h0, h1, h2, h3, -⟩ := enc_digits c
  funext k
  fin_cases k <;> simp [dec, h0, h1, h2, h3, ZMod.natCast_zmod_val]

theorem enc_dec {n : ℕ} (hn : n < 625) : enc (dec n) = n := by
  have e0 : dec n 0 = ((n % 5 : ℕ) : ZMod 5) := rfl
  have e1 : dec n 1 = ((n / 5 % 5 : ℕ) : ZMod 5) := rfl
  have e2 : dec n 2 = ((n / 25 % 5 : ℕ) : ZMod 5) := rfl
  have e3 : dec n 3 = ((n / 125 % 5 : ℕ) : ZMod 5) := rfl
  rw [enc, e0, e1, e2, e3]
  simp only [ZMod.val_natCast, Nat.mod_mod]
  omega

theorem enc_eq_zero_iff (c : Fin 4 → ZMod 5) : enc c = 0 ↔ c = 0 := by
  constructor
  · intro h
    rw [← dec_enc c, h]
    funext k
    fin_cases k <;> rfl
  · rintro rfl
    rfl

theorem card_filter_eq (P : (Fin 4 → ZMod 5) → Prop) [DecidablePred P] (Q : ℕ → Bool)
    (h : ∀ c, P c ↔ Q (enc c) = true) :
    (Finset.univ.filter P).card = ((Finset.range 625).filter fun n => Q n = true).card := by
  apply Finset.card_bij (fun c _ => enc c)
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨enc_lt c, (h c).1 hc⟩
  · intro a _ b _ hab
    rw [← dec_enc a, ← dec_enc b, hab]
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    refine ⟨dec n, ?_, enc_dec hn.1⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [h, enc_dec hn.1]
    exact hn.2

theorem natCast_eq_zero_iff_of_lt {x : ℕ} (hx : x < 5) : ((x : ℕ) : ZMod 5) = 0 ↔ x = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  constructor
  · intro h
    exact Nat.eq_zero_of_dvd_of_lt h hx
  · rintro rfl
    exact dvd_zero 5

theorem dotProduct_eq_zero_iff (f c : Fin 4 → ZMod 5) :
    dotProduct f c = 0 ↔ dot5 (enc f) (enc c) = 0 := by
  have hcast : dotProduct f c = ((dot5 (enc f) (enc c) : ℕ) : ZMod 5) := by
    obtain ⟨f0, f1, f2, f3, -⟩ := enc_digits f
    obtain ⟨c0, c1, c2, c3, -⟩ := enc_digits c
    rw [dot5_eq, f0, f1, f2, f3, c0, c1, c2, c3, ZMod.natCast_mod]
    simp only [dotProduct, Fin.sum_univ_four]
    push_cast
    simp only [ZMod.natCast_zmod_val]
    ring
  rw [hcast, natCast_eq_zero_iff_of_lt (dot5_lt _ _)]

@[expose] def colMap (M : List (List ℤ)) (c : Fin 4 → ZMod 5) : Fin Tag.E8.rank → ZMod 5 :=
  fun i => ∑ k : Fin 4, (((M.getD i []).getD k 0 : ℤ) : ZMod 5) * c k

theorem coef5K_cast (M : List (List ℤ)) (l : List ℤ) (k : ℕ) :
    ((coef5K M l k : ℕ) : ZMod 5) = ((coefK M l k : ℤ) : ZMod 5) := by
  have h := Int.emod_nonneg (coefK M l k) (by norm_num : (5 : ℤ) ≠ 0)
  rw [coef5K, ← Int.cast_natCast, Int.toNat_of_nonneg h]
  exact ZMod.intCast_mod (coefK M l k) 5

theorem coef5K_lt (M : List (List ℤ)) (l : List ℤ) (k : ℕ) : coef5K M l k < 5 := by
  have h := Int.emod_nonneg (coefK M l k) (by norm_num : (5 : ℤ) ≠ 0)
  have h' := Int.emod_lt_of_pos (coefK M l k) (by norm_num : (0 : ℤ) < 5)
  rw [coef5K]
  omega

theorem charVal_colMap (M : List (List ℤ)) (l : List ℤ) (c : Fin 4 → ZMod 5) :
    charVal (colMap M c) (toVec Tag.E8.rank l) =
      ∑ k : Fin 4, ((coefK M l k : ℤ) : ZMod 5) * c k := by
  change (∑ i : Fin 8, ((vget l i : ℤ) : ZMod 5) * colMap M c i) = _
  simp only [Fin.sum_univ_eight, Fin.sum_univ_four, colMap, coefK, vget]
  push_cast
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two]
  norm_num
  ring

theorem charVal_colMap_eq_zero_iff (M : List (List ℤ)) (l : List ℤ) (c : Fin 4 → ZMod 5) :
    charVal (colMap M c) (toVec Tag.E8.rank l) = 0 ↔ dot5 (rowCodeK M l) (enc c) = 0 := by
  have hcast : charVal (colMap M c) (toVec Tag.E8.rank l) =
      ((dot5 (rowCodeK M l) (enc c) : ℕ) : ZMod 5) := by
    obtain ⟨c0, c1, c2, c3, -⟩ := enc_digits c
    have r0 := coef5K_lt M l 0
    have r1 := coef5K_lt M l 1
    have r2 := coef5K_lt M l 2
    have r3 := coef5K_lt M l 3
    have d0 : rowCodeK M l % 5 = coef5K M l 0 := by unfold rowCodeK; omega
    have d1 : rowCodeK M l / 5 % 5 = coef5K M l 1 := by unfold rowCodeK; omega
    have d2 : rowCodeK M l / 25 % 5 = coef5K M l 2 := by unfold rowCodeK; omega
    have d3 : rowCodeK M l / 125 % 5 = coef5K M l 3 := by unfold rowCodeK; omega
    rw [charVal_colMap, dot5_eq, d0, d1, d2, d3, c0, c1, c2, c3, ZMod.natCast_mod]
    push_cast
    simp only [coef5K_cast, ZMod.natCast_zmod_val, Fin.sum_univ_four]
    have v0 : ((0 : Fin 4) : ℕ) = 0 := rfl
    have v1 : ((1 : Fin 4) : ℕ) = 1 := rfl
    have v2 : ((2 : Fin 4) : ℕ) = 2 := rfl
    have v3 : ((3 : Fin 4) : ℕ) = 3 := rfl
    simp only [v0, v1, v2, v3]
    ring
  rw [hcast, natCast_eq_zero_iff_of_lt (dot5_lt _ _)]

theorem e8Count5_colMap (M : List (List ℤ)) (c : Fin 4 → ZMod 5) :
    e8Count5 (colMap M c) = cntRootsK (rowsOfK M Tag.E8.artifactRoots) (enc c) := by
  rw [cntRootsK_eq, rowsOfK, List.countP_map, List.countP_eq_length_filter, e8Count5]
  congr 1
  apply List.filter_congr
  intro l _
  rw [Function.comp_apply]
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff, Nat.beq_eq, charVal_colMap_eq_zero_iff]

theorem eig2_eq : e8FiveEig2 = colMap mEig2 := by
  funext c i
  change Fin 8 at i
  fin_cases i <;> simp [e8FiveEig2, colMap, mEig2, Fin.sum_univ_four] <;> ring

theorem eig3_eq : e8FiveEig3 = colMap mEig3 := by
  funext c i
  change Fin 8 at i
  fin_cases i <;> simp [e8FiveEig3, colMap, mEig3, Fin.sum_univ_four] <;> ring

theorem fix1_eq : e8FiveFix1 = colMap mFix1 := by
  funext c i
  change Fin 8 at i
  fin_cases i <;> simp [e8FiveFix1, colMap, mFix1, Fin.sum_univ_four]

theorem fix2_eq : e8FiveFix2 = colMap mFix2 := by
  funext c i
  change Fin 8 at i
  fin_cases i <;> simp [e8FiveFix2, colMap, mFix2, Fin.sum_univ_four] <;> ring

theorem t40_iff (M : List (List ℤ)) (c : Fin 4 → ZMod 5) :
    (c ≠ 0 ∧ e8Count5 (colMap M c) = 40) ↔
      t40K (rowsOfK M Tag.E8.artifactRoots) (enc c) = true := by
  rw [t40K_iff, e8Count5_colMap, Ne, Ne, enc_eq_zero_iff]

theorem card_t40 (M : List (List ℤ)) :
    (e8FiveT40 (colMap M)).card = cntNK 625 (t40K (rowsOfK M Tag.E8.artifactRoots)) := by
  rw [cntNK_eq, e8FiveT40]
  exact card_filter_eq _ _ (t40_iff M)

theorem card_t40_filter (M : List (List ℤ)) (mask : ℕ)
    (hm : maskOK (rowsOfK M Tag.E8.artifactRoots) mask = true) (f : Fin 4 → ZMod 5) :
    ((e8FiveT40 (colMap M)).filter fun c => dotProduct f c = 0).card = hypCntK mask (enc f) := by
  have hbit : ∀ c, bitOf mask (enc c) = t40K (rowsOfK M Tag.E8.artifactRoots) (enc c) :=
    fun c => beqB_eq_true ((allNK_iff _ _).1 hm (enc c) (enc_lt c))
  rw [hypCntK, cntNK_eq, e8FiveT40, Finset.filter_filter]
  apply card_filter_eq
  intro c
  rw [bandK_eq, Bool.and_eq_true, hbit, ← t40_iff, Nat.beq_eq, dotProduct_eq_zero_iff]

theorem hyp_of_chunks (mask : ℕ) (h : ∀ j < 5, hypOKFrom mask (125 * j) 125 = true) :
    ∀ m < 625, m ≠ 0 → 25 ≤ hypCntK mask m := by
  intro m hm hm0
  have h1 := (allNK_iff _ _).1 (h (m / 125) (by omega)) (m % 125) (Nat.mod_lt _ (by norm_num))
  have he : Nat.add (125 * (m / 125)) (m % 125) = m := Nat.div_add_mod m 125
  rw [he] at h1
  have h0 : Nat.beq m 0 = false := by
    cases hb : Nat.beq m 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) hm0
  rw [h0] at h1
  exact Nat.le_of_ble_eq_true h1

theorem torsionCount_of_checks
    (h2m : maskOK (rowsOfK mEig2 Tag.E8.artifactRoots) mask2 = true)
    (h3m : maskOK (rowsOfK mEig3 Tag.E8.artifactRoots) mask3 = true)
    (h2 : ∀ j < 5, hypOKFrom mask2 (125 * j) 125 = true)
    (h3 : ∀ j < 5, hypOKFrom mask3 (125 * j) 125 = true) : E8FiveTorsionCount := by
  intro f hf
  have hf' : enc f ≠ 0 := fun h => hf ((enc_eq_zero_iff f).1 h)
  rw [e8FiveT40Two, e8FiveT40Three, eig2_eq, eig3_eq, card_t40_filter _ _ h2m,
    card_t40_filter _ _ h3m]
  exact ⟨hyp_of_chunks _ h2 _ (enc_lt f) hf', hyp_of_chunks _ h3 _ (enc_lt f) hf'⟩

theorem fixOK_le {rows : List ℕ} (h : fixOK rows = true) : cntNK 625 (t40K rows) ≤ 24 := by
  unfold fixOK at h
  exact Nat.le_of_ble_eq_true h

theorem sylowCount_of_checks (h1 : fixOK (rowsOfK mFix1 Tag.E8.artifactRoots) = true)
    (h2 : fixOK (rowsOfK mFix2 Tag.E8.artifactRoots) = true) : E8FiveSylowCount := by
  rw [E8FiveSylowCount, fix1_eq, fix2_eq, card_t40, card_t40]
  exact ⟨fixOK_le h1, fixOK_le h2⟩

end CFSG.KC.E8Five
