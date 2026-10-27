module

public import Certificates.Data.Kernel.Co2HeavyK
public import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

public section

namespace CFSG.KC.Co2HeavyK

open CFSG.KC.Loop CFSG.KC.Co2InvS CFSG.KS CFSG.KC.M1F2
open CFSG.KC.Enum (pg)

theorem pOf_lt (w : ℕ) : pOf w < 262144 :=
  lt_of_le_of_lt Nat.and_le_right (by decide)

theorem cjOf_lt (w : ℕ) : cjOf w < 262144 :=
  lt_of_le_of_lt Nat.and_le_right (by decide)

theorem t1Of_lt (w : ℕ) : t1Of w < 2 :=
  lt_of_le_of_lt Nat.and_le_right (by decide)

theorem t2Of_lt (w : ℕ) : t2Of w < 2 :=
  lt_of_le_of_lt Nat.and_le_right (by decide)

theorem andK_eq' (a b : Bool) : andK a b = (a && b) := by cases a <;> rfl

theorem letB_eq' (v : ℕ) (k : ℕ → Bool) : letB v k = k v := by cases v <;> rfl

theorem notK_eq' (b : Bool) : notK b = !b := by cases b <;> rfl

private theorem strictN_eq' (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by cases y <;> rfl

private theorem sumBelow_eq_sum (m hi : ℕ) (f : ℕ → ℕ) (hm : m ≤ 64 * hi) :
    sumBelow m hi f = ∑ i ∈ Finset.range m, f i := by
  have rec_sum : ∀ (G : ℕ → ℕ) (k : ℕ),
      Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 => Nat.add (G l) ih2) k =
        ∑ l ∈ Finset.range k, G l := by
    intro G k
    induction k with
    | zero =>
      rw [Finset.sum_range_zero]
      rfl
    | succ k ih =>
      rw [Finset.sum_range_succ, ← ih]
      exact Nat.add_comm _ _
  have sel : ∀ (b : Bool) (x : ℕ), Bool.rec (motive := fun _ => ℕ) 0 x b =
      if b = true then x else 0 := by
    intro b x
    cases b <;> rfl
  have hgen : ∀ h, sumBelow m h f =
      ∑ i ∈ Finset.range (64 * h), if i < m then f i else 0 := by
    intro h
    induction h with
    | zero =>
      rw [Nat.mul_zero, Finset.sum_range_zero]
      rfl
    | succ h ih =>
      change Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 =>
        Nat.add ((fun i => Bool.rec (motive := fun _ => ℕ) 0 (f i) (Nat.blt i m))
          (Nat.add (Nat.shiftLeft h 6) l)) ih2) 64 + sumBelow m h f = _
      rw [rec_sum, ih, Nat.mul_succ, Finset.sum_range_add,
        Nat.add_comm (Finset.sum (Finset.range 64) _)]
      refine Nat.add_left_cancel_iff.2 (Finset.sum_congr rfl fun l _ => ?_)
      have e : Nat.add (Nat.shiftLeft h 6) l = 64 * h + l := by
        change h <<< 6 + l = 64 * h + l
        rw [Nat.shiftLeft_eq, show (2 : ℕ) ^ 6 = 64 from rfl]
        omega
      simp only [e, sel, Nat.blt_eq]
  rw [hgen hi, show 64 * hi = m + (64 * hi - m) by omega, Finset.sum_range_add]
  rw [Finset.sum_eq_zero (s := Finset.range (64 * hi - m)) (fun i _ => ite_eq_right (by omega)),
    Nat.add_zero]
  exact Finset.sum_congr rfl fun i hi' => if_pos (Finset.mem_range.1 hi')

private theorem sumBelow_nIf_eq_card (m hi : ℕ) (p : ℕ → Bool) (hm : m ≤ 64 * hi) :
    sumBelow m hi (fun i => nIf(p i, 1, 0)) =
      ((Finset.range m).filter fun i => p i = true).card := by
  rw [sumBelow_eq_sum m hi _ hm, Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases p i <;> rfl

private theorem sumBelow_ind_card {m hi a b : ℕ} (c : ℕ → Bool) (hm : m ≤ 64 * hi)
    (ha : a = 1) (hb : b = 0) :
    sumBelow m hi (fun i => nIf(c i, a, b)) =
      ((Finset.range m).filter fun i => c i = true).card := by
  subst ha hb
  exact sumBelow_nIf_eq_card m hi c hm

private theorem sumBelow_comm_card {m hi a b : ℕ} (K : ℕ → ℕ → Bool) (S : ℕ → ℕ) (Y : ℕ)
    (hm : m ≤ 64 * hi) (ha : a = 1) (hb : b = 0) :
    sumBelow m hi (fun i => nIf(K (S i) Y, a, b)) =
      ((Finset.range m).filter fun i => K (S i) Y = true).card := by
  subst ha hb
  exact sumBelow_nIf_eq_card m hi (fun i => K (S i) Y) hm

private theorem sumBelow_comm2_card {m hi a b c d : ℕ} (T V : ℕ → ℕ) (K : ℕ → ℕ → Bool)
    (S : ℕ → ℕ) (Y : ℕ) (hm : m ≤ 64 * hi) (ha : a = 1) (hb : b = 0) (hc : c = 0)
    (hd : d = 1) :
    sumBelow m hi (fun i => nIf(Nat.beq (T (V i)) d, nIf(K (S i) Y, a, b), c)) =
      ((Finset.range m).filter fun i => T (V i) = 1 ∧ K (S i) Y = true).card := by
  subst ha hb hc hd
  rw [sumBelow_eq_sum m hi _ hm, Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases hT : Nat.beq (T (V i)) 1
  · rw [if_neg fun h => Nat.ne_of_beq_eq_false hT h.1]
  · rw [Nat.eq_of_beq_eq_true hT]
    cases K (S i) Y <;> rfl

private theorem commK_iff {X Y : ℕ} : commK X Y = true ↔ mulV X Y = mulV Y X :=
  ⟨Nat.eq_of_beq_eq_true, fun e => by rw [commK, e, Nat.beq_refl]⟩

theorem bind_sound {CF SQ W CA : ℕ → ℕ} {i : ℕ} (h : bindK CF SQ W CA i = true) :
    SQ i = elemAt CF (pOf (wAt W i)) ∧ mulV (SQ i) (SQ i) = IDP := by
  unfold bindK at h
  rw [letB_eq'] at h
  simp only [andK_eq', Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2.1⟩

private theorem sqc_implK {a b : Bool} (h : implK a b = true) (ha : a = true) : b = true := by
  unfold implK at h
  rw [ha] at h
  exact h

private theorem sqc_caK {CA : ℕ → ℕ} (h : caK CA = true) :
    CA 0 = 0 ∧ CA 64 = 6144 := by
  unfold caK at h
  simp only [andK_eq', Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩

private theorem sqc_ca_step {CF CA : ℕ → ℕ} {c : ℕ} (h : chunkK CF CA c = true) :
    CA c ≤ CA (Nat.succ c) := by
  unfold chunkK at h
  simp only [andK_eq', Bool.and_eq_true, Nat.ble_eq] at h
  exact h.1

private theorem sqc_ca_mono {CF CA : ℕ → ℕ} (hc : ∀ c < 64, chunkK CF CA c = true) :
    ∀ {a b : ℕ}, a ≤ b → b ≤ 64 → CA a ≤ CA b := by
  intro a b
  induction b with
  | zero =>
    intro hab _
    have : a = 0 := by omega
    subst this
    exact le_rfl
  | succ n ih =>
    intro hab hb
    rcases Nat.lt_or_eq_of_le hab with h | h
    · exact le_trans (ih (by omega) (by omega)) (sqc_ca_step (hc n (by omega)))
    · subst h
      exact le_rfl

private theorem sqc_lt_6144 {CF CA : ℕ → ℕ} (hc : ∀ c < 64, chunkK CF CA c = true)
    (hca : caK CA = true) {c i : ℕ} (hc64 : c < 64) (hi : i < CA (Nat.succ c)) :
    i < 6144 := by
  have h64 := (sqc_caK hca).2
  have hm := sqc_ca_mono hc (a := Nat.succ c) (b := 64) (by omega) (le_rfl)
  omega

private theorem sqc_bind {CF SQ W CA : ℕ → ℕ} {i : ℕ} (h : bindK CF SQ W CA i = true) :
    SQ i = elemAt CF (pOf (wAt W i)) ∧ mulV (SQ i) (SQ i) = IDP ∧
      (Nat.succ i < 6144 → pOf (wAt W i) < pOf (wAt W (Nat.succ i))) ∧
      CA (Nat.shiftRight (pOf (wAt W i)) 12) ≤ i ∧
        i < CA (Nat.succ (Nat.shiftRight (pOf (wAt W i)) 12)) := by
  unfold bindK at h
  rw [letB_eq'] at h
  simp only [andK_eq', Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, ?_, ?_, ?_⟩
  · intro hi
    have hb := sqc_implK h3 (by simpa only [Nat.blt_eq] using hi)
    simpa only [Nat.blt_eq] using hb
  · simpa only [Nat.ble_eq] using h4
  · simpa only [Nat.blt_eq] using h5

private theorem sqc_P_lt {CF SQ W CA : ℕ → ℕ}
    (hb : ∀ i < 6144, bindK CF SQ W CA i = true) :
    ∀ {i j : ℕ}, i < j → j < 6144 → pOf (wAt W i) < pOf (wAt W j) := by
  intro i j
  induction j with
  | zero => intro hij; omega
  | succ n ih =>
    intro hij hj
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hij) with h | h
    · have hn : n < 6144 := by omega
      exact lt_trans (ih h hn) ((sqc_bind (hb n hn)).2.2.1 hj)
    · have hn : n < 6144 := by omega
      have hstep := (sqc_bind (hb n hn)).2.2.1 hj
      rwa [h]

private theorem sqc_chunk {CF SQ W CA : ℕ → ℕ}
    (hb : ∀ i < 6144, bindK CF SQ W CA i = true)
    (hc : ∀ c < 64, chunkK CF CA c = true) (hca : caK CA = true)
    {c i : ℕ} (hc64 : c < 64) (h1 : CA c ≤ i) (h2 : i < CA (Nat.succ c)) :
    pOf (wAt W i) / 4096 = c ∧ 4096 * c ≤ pOf (wAt W i) ∧
      pOf (wAt W i) - 4096 * c < 4096 ∧
      mulV (elemAt CF (pOf (wAt W i))) (elemAt CF (pOf (wAt W i))) = IDP := by
  have hi := sqc_lt_6144 hc hca hc64 h2
  have hB := sqc_bind (hb i hi)
  have hci : Nat.shiftRight (pOf (wAt W i)) 12 < 64 := by
    change pOf (wAt W i) >>> 12 < 64
    rw [Nat.shiftRight_eq_div_pow, show (2 : ℕ) ^ 12 = 4096 by decide]
    exact Nat.div_lt_of_lt_mul (by have := pOf_lt (wAt W i); omega)
  have hshift : Nat.shiftRight (pOf (wAt W i)) 12 = c := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have hle : Nat.succ (Nat.shiftRight (pOf (wAt W i)) 12) ≤ c := by omega
      have hm := sqc_ca_mono hc hle (by omega : c ≤ 64)
      omega
    · have hle : Nat.succ c ≤ Nat.shiftRight (pOf (wAt W i)) 12 := by omega
      have hm := sqc_ca_mono hc hle (by omega : Nat.shiftRight (pOf (wAt W i)) 12 ≤ 64)
      omega
  have hdiv : pOf (wAt W i) / 4096 = c := by
    rw [← hshift]
    change pOf (wAt W i) / 4096 = pOf (wAt W i) >>> 12
    rw [Nat.shiftRight_eq_div_pow, show (2 : ℕ) ^ 12 = 4096 by decide]
  have hdecomp := Nat.div_add_mod (pOf (wAt W i)) 4096
  rw [hdiv] at hdecomp
  have hmod := Nat.mod_lt (pOf (wAt W i)) (by decide : 0 < 4096)
  have hle : 4096 * c ≤ pOf (wAt W i) := by
    simpa [hdiv] using Nat.mul_div_le (pOf (wAt W i)) 4096
  refine ⟨hdiv, hle, by omega, ?_⟩
  rw [← hB.1]
  exact hB.2.1

private theorem sqc_strictN {a b : ℕ} (y I : ℕ) (G : ℕ → ℕ → ℕ) (ha : a = 1) (hb : b = 0) :
    strictN y (fun X => nIf(Nat.beq (G X X) I, a, b)) = if G y y = I then 1 else 0 := by
  subst ha hb
  rw [strictN_eq']
  cases h : Nat.beq (G y y) I
  · rw [if_neg (Nat.ne_of_beq_eq_false h)]
  · rw [if_pos (Nat.eq_of_beq_eq_true h)]

private theorem sqc_sq01 (CF : ℕ → ℕ) (k : ℕ) :
    sq01 CF k = if mulV (elemAt CF k) (elemAt CF k) = IDP then 1 else 0 := by
  unfold sq01
  exact sqc_strictN (elemAt CF k) IDP mulV (by rfl) (by rfl)

private theorem sqc_chunk_card {CF CA : ℕ → ℕ} {c : ℕ} (h : chunkK CF CA c = true) :
    ((Finset.range 4096).filter fun t => mulV (elemAt CF (4096 * c + t))
      (elemAt CF (4096 * c + t)) = IDP).card = CA (Nat.succ c) - CA c := by
  unfold chunkK at h
  rw [andK_eq', Bool.and_eq_true] at h
  have e := Nat.eq_of_beq_eq_true h.2
  rw [sumBelow_eq_sum _ _ _ (by decide)] at e
  rw [Finset.card_filter]
  exact (Finset.sum_congr rfl fun t _ => (sqc_sq01 CF _).symm).trans e

private theorem sqc_image_eq {CF SQ W CA : ℕ → ℕ}
    (hb : ∀ i < 6144, bindK CF SQ W CA i = true)
    (hc : ∀ c < 64, chunkK CF CA c = true) (hca : caK CA = true)
    {c : ℕ} (hc64 : c < 64) :
    (Finset.range (CA (Nat.succ c) - CA c)).image
        (fun t => pOf (wAt W (CA c + t)) - 4096 * c) =
      (Finset.range 4096).filter
        (fun t => mulV (elemAt CF (4096 * c + t)) (elemAt CF (4096 * c + t)) = IDP) := by
  have hstep : CA c ≤ CA (Nat.succ c) := sqc_ca_step (hc c hc64)
  have hmem : ∀ t ∈ Finset.range (CA (Nat.succ c) - CA c),
      CA c + t < CA (Nat.succ c) := by
    intro t ht
    rw [Finset.mem_range, Nat.lt_sub_iff_add_lt] at ht
    omega
  have hT : ∀ t ∈ Finset.range (CA (Nat.succ c) - CA c),
      pOf (wAt W (CA c + t)) - 4096 * c ∈
        (Finset.range 4096).filter
          (fun u => mulV (elemAt CF (4096 * c + u)) (elemAt CF (4096 * c + u)) = IDP) := by
    intro t ht
    obtain ⟨-, hle, hsub, hsq⟩ :=
      sqc_chunk hb hc hca hc64 (Nat.le_add_right _ _) (hmem t ht)
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨hsub, ?_⟩
    have hsum : 4096 * c + (pOf (wAt W (CA c + t)) - 4096 * c) =
        pOf (wAt W (CA c + t)) := by omega
    rw [hsum]
    exact hsq
  have hinj : Set.InjOn (fun t => pOf (wAt W (CA c + t)) - 4096 * c)
      ↑(Finset.range (CA (Nat.succ c) - CA c)) := by
    intro t ht u hu heq
    have ht' := hmem t (by simpa using ht)
    have hu' := hmem u (by simpa using hu)
    obtain ⟨-, hlet, -, -⟩ :=
      sqc_chunk hb hc hca hc64 (Nat.le_add_right _ _) ht'
    obtain ⟨-, hleu, -, -⟩ :=
      sqc_chunk hb hc hca hc64 (Nat.le_add_right _ _) hu'
    have heq' : pOf (wAt W (CA c + t)) - 4096 * c =
        pOf (wAt W (CA c + u)) - 4096 * c := heq
    have hP : pOf (wAt W (CA c + t)) = pOf (wAt W (CA c + u)) := by omega
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := sqc_P_lt hb (by omega : CA c + t < CA c + u)
        (sqc_lt_6144 hc hca hc64 hu')
      omega
    · have := sqc_P_lt hb (by omega : CA c + u < CA c + t)
        (sqc_lt_6144 hc hca hc64 ht')
      omega
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · rw [Finset.image_subset_iff]
    exact hT
  · rw [Finset.card_image_of_injOn hinj, Finset.card_range, sqc_chunk_card (hc c hc64)]

theorem sq_complete {CF SQ W CA : ℕ → ℕ} (hb : ∀ i < 6144, bindK CF SQ W CA i = true)
    (hc : ∀ c < 64, chunkK CF CA c = true) (hca : caK CA = true) :
    ∀ k < 262144, mulV (elemAt CF k) (elemAt CF k) = IDP → ∃ i < 6144, pOf (wAt W i) = k := by
  intro k hk hsq
  set c := k / 4096 with hcdef
  have hc64 : c < 64 := by
    rw [hcdef]
    exact Nat.div_lt_of_lt_mul (by omega)
  have hdecomp : 4096 * c + k % 4096 = k := by
    rw [hcdef]
    exact Nat.div_add_mod k 4096
  have hmod : k % 4096 < 4096 := Nat.mod_lt k (by decide)
  have hle : 4096 * c ≤ k := by
    simpa [hcdef] using Nat.mul_div_le k 4096
  have hmem : k - 4096 * c ∈
      (Finset.range 4096).filter
        (fun t => mulV (elemAt CF (4096 * c + t)) (elemAt CF (4096 * c + t)) = IDP) := by
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rw [show 4096 * c + (k - 4096 * c) = k by omega]
    exact hsq
  have himg := sqc_image_eq hb hc hca hc64
  rw [← himg] at hmem
  rw [Finset.mem_image] at hmem
  obtain ⟨t, ht, hft⟩ := hmem
  have ht' : CA c + t < CA (Nat.succ c) := by
    rw [Finset.mem_range, Nat.lt_sub_iff_add_lt] at ht
    omega
  obtain ⟨-, hleP, -, -⟩ := sqc_chunk hb hc hca hc64 (Nat.le_add_right _ _) ht'
  have hPk : pOf (wAt W (CA c + t)) = k := by omega
  exact ⟨CA c + t, sqc_lt_6144 hc hca hc64 ht', hPk⟩

theorem part1_sound {CF SQ RP : ℕ → ℕ} {j : ℕ} (h : part1K CF SQ RP j = true) :
    RP j < 262144 ∧ ((Finset.range 6144).filter fun i =>
      mulV (SQ i) (elemAt CF (RP j)) = mulV (elemAt CF (RP j)) (SQ i)).card < 1024 := by
  unfold part1K at h
  simp only [andK_eq', Bool.and_eq_true, Nat.blt_eq] at h
  refine ⟨h.1, lt_of_eq_of_lt ?_ h.2⟩
  rw [strictN_eq']
  unfold cnt1
  rw [sumBelow_comm_card commK SQ _ (by decide) (by rfl) (by rfl)]
  exact congrArg Finset.card (Finset.filter_congr fun i _ => commK_iff.symm)

theorem part2_sound {CF SQ W RP : ℕ → ℕ} {j : ℕ} (h : part2K CF SQ W RP j = true) :
    RP (31 + j) < 262144 ∧ ((Finset.range 6144).filter fun i => t1Of (wAt W i) = 1 ∧
      mulV (SQ i) (elemAt CF (RP (31 + j))) = mulV (elemAt CF (RP (31 + j))) (SQ i)).card <
        1024 := by
  unfold part2K at h
  simp only [andK_eq', Bool.and_eq_true, Nat.blt_eq] at h
  refine ⟨h.1, lt_of_eq_of_lt ?_ h.2⟩
  rw [strictN_eq']
  unfold cnt2
  rw [sumBelow_comm2_card t1Of (wAt W) commK SQ _ (by decide) (by rfl) (by rfl) (by rfl)
    (by rfl)]
  exact congrArg Finset.card
    (Finset.filter_congr fun i _ => and_congr_right fun _ => commK_iff.symm)

private theorem wit_beq_one_zero : Nat.beq 1 0 = false := rfl

theorem wit_sound {CF SQ W RP : ℕ → ℕ} {i : ℕ} (h : witK CF SQ W RP i = true) :
    (t1Of (wAt W i) = 0 → jOf (wAt W i) < 31 ∧
      mulV (elemAt CF (cjOf (wAt W i))) (SQ i) =
        mulV (elemAt CF (RP (jOf (wAt W i)))) (elemAt CF (cjOf (wAt W i)))) ∧
    (t1Of (wAt W i) = 1 → t2Of (wAt W i) = 0 → jOf (wAt W i) < 17 ∧
      mulV (elemAt CF (cjOf (wAt W i))) (SQ i) =
        mulV (elemAt CF (RP (31 + jOf (wAt W i)))) (elemAt CF (cjOf (wAt W i)))) := by
  unfold witK at h
  rw [letB_eq'] at h
  have h1 : t1Of (wAt W i) = 0 ∨ t1Of (wAt W i) = 1 := by
    have := t1Of_lt (wAt W i)
    omega
  have h2 : t2Of (wAt W i) = 0 ∨ t2Of (wAt W i) = 1 := by
    have := t2Of_lt (wAt W i)
    omega
  rcases h1 with h1 | h1
  · constructor
    · intro _
      simp only [h1, Nat.beq_refl, andK_eq', Bool.and_eq_true, Nat.blt_eq] at h
      unfold conjK at h
      exact ⟨h.1, Nat.eq_of_beq_eq_true h.2⟩
    · intro e
      exact absurd e (by omega)
  · constructor
    · intro e
      exact absurd e (by omega)
    · intro _ h2'
      simp only [h1, wit_beq_one_zero, andK_eq'] at h
      rcases h2 with h2 | h2
      · simp only [h2, Nat.beq_refl, Bool.and_eq_true, Nat.blt_eq] at h
        unfold conjK at h
        exact ⟨h.1, Nat.eq_of_beq_eq_true h.2⟩
      · exact absurd h2' (by omega)

theorem inL2K_iff {W : ℕ → ℕ} {a : ℕ} :
    inL2K W a = true ↔ a < 6144 ∧ t1Of (wAt W a) = 1 ∧ t2Of (wAt W a) = 1 := by
  unfold inL2K
  rw [letB_eq']
  simp only [andK_eq', Bool.and_eq_true, Nat.blt_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3⟩
  · rintro ⟨h1, h2, h3⟩
    rw [h2, h3]
    exact ⟨h1, Nat.beq_refl 1, Nat.beq_refl 1⟩

theorem l2_sound {W : ℕ → ℕ} (h : l2K W = true) :
    ((Finset.range 6144).filter fun i => inL2K W i = true).card = 1024 := by
  unfold l2K at h
  have e := Nat.eq_of_beq_eq_true h
  rw [sumBelow_ind_card (inL2K W) (by decide) (by rfl) (by rfl)] at e
  exact e

private theorem wit_implK_true (b : Bool) : implK true b = b := rfl

theorem norm_sound {SQ W : ℕ → ℕ} {A B i : ℕ} (h : normK SQ W A B i = true)
    (hi : inL2K W i = true) :
    inL2K W (maOf (wAt W i)) = true ∧ mulV A (SQ i) = mulV (SQ (maOf (wAt W i))) A ∧
      inL2K W (mbOf (wAt W i)) = true ∧ mulV B (SQ i) = mulV (SQ (mbOf (wAt W i))) B := by
  unfold normK at h
  rw [hi, wit_implK_true, letB_eq'] at h
  simp only [andK_eq', Bool.and_eq_true] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2.1, h.2.2.1, Nat.eq_of_beq_eq_true h.2.2.2⟩

theorem inv_sound {A B Ai Bi : ℕ} (h : invK A B Ai Bi = true) :
    mulV A Ai = IDP ∧ mulV B Bi = IDP ∧ B ≠ IDP := by
  unfold invK at h
  simp only [andK_eq', notK_eq', Bool.and_eq_true, Bool.not_eq_true'] at h
  refine ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2.1, fun e => ?_⟩
  rw [e, Nat.beq_refl] at h
  exact Bool.false_ne_true h.2.2.symm

theorem rel_sound {A B Ai Bi : ℕ} (h : relK A B Ai Bi = true) :
    ∀ w ∈ m22RelsK, wordP A B Ai Bi w IDP = IDP := by
  unfold relK m22RelsK at h
  simp only [andK_eq', Bool.and_eq_true] at h
  intro w hw
  unfold m22RelsK at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · exact Nat.eq_of_beq_eq_true h.1
  · exact Nat.eq_of_beq_eq_true h.2.1
  · exact Nat.eq_of_beq_eq_true h.2.2.1

theorem mvec_sound {VP T PT i : ℕ} (h : mvecK VP T PT i = true) :
    pg 12 (mask 12) PT i < 2300 ∧
      vmF 22 T (pg 22 (mask 22) VP i) = pg 22 (mask 22) VP (pg 12 (mask 12) PT i) := by
  unfold mvecK at h
  simp only [andK_eq', Bool.and_eq_true, Nat.blt_eq] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2⟩

end CFSG.KC.Co2HeavyK

end
