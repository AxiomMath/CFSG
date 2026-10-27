module

public import CFSG.Certificates.Kernel.OmegaCY.GensSound
public import CFSG.Certificates.Kernel.OmegaCY.SearchSound

public section

namespace CFSG.KC.OmegaCY

theorem cy_bIfD (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem shl1 (n : ℕ) : Nat.shiftLeft 1 n = 2 ^ n := by
  have h := Nat.shiftLeft_eq 1 n
  rw [one_mul] at h
  exact h

theorem lane_eq (c i : ℕ) : lane c i = c / 2 ^ (7 * i) % 128 := by
  change (c >>> (7 * i)) &&& (2 ^ 7 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

@[expose] def packL (l : ℕ → ℕ) : ℕ :=
  l 0 + 128 * l 1 + 16384 * l 2 + 2097152 * l 3 + 268435456 * l 4 + 34359738368 * l 5 +
    4398046511104 * l 6

theorem lane_packL {l : ℕ → ℕ} (hl : ∀ i < 7, l i < 2 ^ 7) {i : ℕ} (hi : i < 7) :
    lane (packL l) i = l i := by
  have h0 := hl 0 (by norm_num)
  have h1 := hl 1 (by norm_num)
  have h2 := hl 2 (by norm_num)
  have h3 := hl 3 (by norm_num)
  have h4 := hl 4 (by norm_num)
  have h5 := hl 5 (by norm_num)
  have h6 := hl 6 (by norm_num)
  rw [lane_eq]
  interval_cases i <;> simp only [packL, Nat.reduceMul, Nat.reducePow] at * <;> omega

theorem packL_lt {l : ℕ → ℕ} (hl : ∀ i < 7, l i < 2 ^ 7) : packL l < 2 ^ 49 := by
  have h0 := hl 0 (by norm_num)
  have h1 := hl 1 (by norm_num)
  have h2 := hl 2 (by norm_num)
  have h3 := hl 3 (by norm_num)
  have h4 := hl 4 (by norm_num)
  have h5 := hl 5 (by norm_num)
  have h6 := hl 6 (by norm_num)
  simp only [packL, Nat.reducePow] at *
  omega

theorem lane_mod_le {c m i : ℕ} (hm : m < 7) (hi : i ≤ m) :
    lane (c % 2 ^ (7 * (m + 1))) i = lane c i := by
  rw [lane_eq, lane_eq]
  interval_cases m <;> interval_cases i <;> simp only [Nat.reduceMul, Nat.reducePow, Nat.reduceAdd] <;>
    omega

theorem xor_rel {a b x y e : ℕ} (h : a ^^^ b ^^^ x = b ^^^ a ^^^ y ^^^ e) : x ^^^ y = e := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h' := congrArg (fun n => Nat.testBit n i) h
  simp only [Nat.testBit_xor] at h' ⊢
  revert h'
  cases a.testBit i <;> cases b.testBit i <;> cases x.testBit i <;> cases y.testBit i <;>
    cases e.testBit i <;> decide

theorem lt8_of_bits {k : ℕ} (hk : k < 2 ^ 7) (h3 : k.testBit 3 = false) (h4 : k.testBit 4 = false)
    (h5 : k.testBit 5 = false) (h6 : k.testBit 6 = false) : k < 2 ^ 3 := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  by_cases h7 : 7 ≤ i
  · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hk (Nat.pow_le_pow_right (by norm_num) h7))
  · interval_cases i <;> assumption

theorem bf_lo_r (tab a : ℕ) {e : ℕ} (he : e < 2 ^ 3) : bf tab a e = 0 := by
  simp [bf_eq, bfT_eq, testBit_of_lt8 he (le_refl 3), testBit_of_lt8 he (by norm_num : 3 ≤ 4),
    testBit_of_lt8 he (by norm_num : 3 ≤ 5)]

theorem bm2_lo (tab : ℕ) {a b : ℕ} (ha : a < 2 ^ 3) : bm2 tab a b = a ^^^ b := by
  rw [bm2_eq, bf_lo tab ha, Nat.xor_zero]

theorem cg_lt (tab i j : ℕ) : cg tab i j < 2 ^ 3 :=
  Nat.lt_succ_of_le Nat.and_le_right

@[expose] noncomputable def betaP (tab c k n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i r => nIf(bt k i, bm2 tab r (lane c i), r)) n

theorem beta2_eq (tab c k : ℕ) : beta2 tab c k = betaP tab c k 7 := rfl

theorem betaP_zero (tab c k : ℕ) : betaP tab c k 0 = 0 := rfl

theorem betaP_succ (tab c k n : ℕ) : betaP tab c k (n + 1) =
    nIf(bt k n, bm2 tab (betaP tab c k n) (lane c n), betaP tab c k n) := rfl

theorem betaP_congr {tab c c' k : ℕ} : ∀ {n : ℕ},
    (∀ i < n, k.testBit i = true → lane c i = lane c' i) → betaP tab c k n = betaP tab c' k n
  | 0, _ => rfl
  | n + 1, h => by
    rw [betaP_succ, betaP_succ, cy_nIfD, cy_nIfD, bt_eq, betaP_congr fun i hi => h i (by omega)]
    split
    · rename_i hb
      rw [h n (by omega) hb]
    · rfl

theorem cen_eq (c w : ℕ) : cen c w =
    ((if w.testBit 0 = true then lane c 0 else 0) ^^^ (if w.testBit 1 = true then lane c 1 else 0)) ^^^
      (if w.testBit 2 = true then lane c 2 else 0) := by
  simp only [cen, cy_nIfD, bt_eq, cy_xorD]

theorem stage2_true {tab m c : ℕ} (h1 : bf tab (lane c m) (lane c m) = 0)
    (h2 : ∀ i < m, bf tab (lane c m) (lane c i) ^^^ bf tab (lane c i) (lane c m) =
      cen c (cg tab m i))
    (h3 : ∀ g < m + 1, lane c g < 2 ^ (m + 1) → beta2 tab c (lane c g) = 2 ^ g) :
    stage2 true tab (m + 1) c = true := by
  have e : stage2 true tab (m + 1) c = bAnd(Nat.beq (bf tab (lane c m) (lane c m)) (nat_lit 0),
      bAnd(allR m (fun i => relK tab c (lane c m) (lane c i) (cg tab m i)),
        allR (m + 1) (fun g => bIf(Nat.ble (Nat.shiftLeft (nat_lit 1) (m + 1)) (lane c g), true,
          Nat.beq (beta2 tab c (lane c g)) (Nat.shiftLeft (nat_lit 1) g))))) := rfl
  rw [e, cy_bAndD, cy_bAndD, Bool.and_eq_true, Bool.and_eq_true, allR_iff, allR_iff]
  refine ⟨?_, fun i hi => ?_, fun g hg => ?_⟩
  · rw [h1]
    rfl
  · unfold relK
    rw [cy_xorD, h2 i hi]
    simp
  · rw [cy_bIfD]
    split
    · rfl
    · rename_i hb
      have hlt : lane c g < 2 ^ (m + 1) := by
        rw [← shl1]
        simp only [Nat.ble_eq, decide_eq_true_eq, not_le] at hb
        exact hb
      rw [h3 g hg hlt, shl1]
      simp

variable {M : Type*} [Group M]

theorem psiG_map {N : Type*} [Group N] (f : M →* N) (g : ℕ → M) (k : ℕ) :
    ∀ m, f (psiG g k m) = psiG (fun i => f (g i)) k m
  | 0 => by rw [psiG_zero, psiG_zero, map_one]
  | m + 1 => by
    rw [psiG_succ, psiG_succ, map_mul, psiG_map f g k m]
    split <;> simp

theorem psiG_congrF {g g' : ℕ → M} {k : ℕ} : ∀ {m : ℕ}, (∀ i < m, g i = g' i) →
    psiG g k m = psiG g' k m
  | 0, _ => by rw [psiG_zero, psiG_zero]
  | m + 1, h => by
    rw [psiG_succ, psiG_succ, psiG_congrF fun i hi => h i (by omega), h m (by omega)]

theorem psiG_mem {S : Subgroup M} {g : ℕ → M} {k : ℕ} : ∀ {m : ℕ},
    (∀ i < m, k.testBit i = true → g i ∈ S) → psiG g k m ∈ S
  | 0, _ => by
    rw [psiG_zero]
    exact S.one_mem
  | m + 1, h => by
    rw [psiG_succ]
    refine S.mul_mem (psiG_mem fun i hi => h i (by omega)) ?_
    split
    · rename_i hb
      exact h m (by omega) hb
    · exact S.one_mem

theorem psiG_two_pow (g : ℕ → M) (j : ℕ) : ∀ m, psiG g (2 ^ j) m = if j < m then g j else 1
  | 0 => by simp [psiG_zero]
  | m + 1 => by
    rw [psiG_succ, psiG_two_pow g j m, Nat.testBit_two_pow]
    by_cases h : j = m
    · subst h
      simp
    · have e : j < m + 1 ↔ j < m := by omega
      simp [h, e]

theorem psiG_pow (g : ℕ → M) {j : ℕ} (hj : j < 7) : psiG g (2 ^ j) 7 = g j := by
  rw [psiG_two_pow, if_pos hj]

theorem psiG_lo (g : ℕ → M) {e : ℕ} (he : e < 2 ^ 3) : ∀ {m : ℕ}, 3 ≤ m →
    psiG g e m = psiG g e 3 := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hm ih => rw [psiG_succ, ih, testBit_of_lt8 he hm, if_neg (by simp), mul_one]

theorem psiG_three (g : ℕ → M) (e : ℕ) : psiG g e 3 = (if e.testBit 0 = true then g 0 else 1) *
    (if e.testBit 1 = true then g 1 else 1) * (if e.testBit 2 = true then g 2 else 1) := by
  rw [psiG_succ, psiG_succ, psiG_succ, psiG_zero, one_mul]

variable {g : ℕ → M} {tab : ℕ}

theorem psi_lo_xor (hr : CyRel tab g) {a b : ℕ} (ha : a < 2 ^ 3) (hb : b < 2 ^ 3) :
    psiG g (a ^^^ b) 7 = psiG g a 7 * psiG g b 7 := by
  have h7 : ∀ {x : ℕ}, x < 2 ^ 3 → x < 2 ^ 7 := fun hx => lt_of_lt_of_le hx (by norm_num)
  rw [← bm2_lo tab ha, psi_mul hr (h7 ha) (h7 hb)]

theorem psi_onto [Finite M] (hr : CyRel tab g)
    (hne : ∀ k, 0 < k → k < 2 ^ 7 → psiG g k 7 ≠ 1) (R : ℕ → Prop) [DecidablePred R]
    (S : Subgroup M) (hR : ∀ k < 2 ^ 7, R k → psiG g k 7 ∈ S)
    (hcard : Nat.card S ≤ ((Finset.range (2 ^ 7)).filter R).card) {x : M} (hx : x ∈ S) :
    ∃ k < 2 ^ 7, psiG g k 7 = x := by
  classical
  set F := (Finset.range (2 ^ 7)).filter R
  have hF : ∀ k ∈ F, k < 2 ^ 7 ∧ R k := fun k hk =>
    ⟨Finset.mem_range.1 (Finset.mem_filter.1 hk).1, (Finset.mem_filter.1 hk).2⟩
  have hinj : Set.InjOn (fun k => psiG g k 7) (F : Set ℕ) := fun a ha b hb e =>
    psi_inj hr hne (hF a ha).1 (hF b hb).1 e
  have hsub : ((F.image fun k => psiG g k 7 : Finset M) : Set M) ⊆ (S : Set M) := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hy
    exact hR k (hF k hk).1 (hF k hk).2
  have hle : (S : Set M).ncard ≤ ((F.image fun k => psiG g k 7 : Finset M) : Set M).ncard := by
    rw [Set.ncard_coe_finset, Finset.card_image_of_injOn hinj, ← Nat.card_coe_set_eq]
    exact hcard
  have heq := Set.eq_of_subset_of_ncard_le hsub hle (Set.toFinite _)
  have hx' : x ∈ ((F.image fun k => psiG g k 7 : Finset M) : Set M) := by
    rw [heq]
    exact hx
  obtain ⟨k, hk, e⟩ := Finset.mem_image.1 hx'
  exact ⟨k, (hF k hk).1, e⟩

abbrev R0 (k : ℕ) : Prop := k.testBit 3 = false ∧ k.testBit 5 = false

abbrev R2 (k : ℕ) : Prop := k.testBit 4 = false ∧ k.testBit 6 = false

theorem card_R0 : ((Finset.range (2 ^ 7)).filter R0).card = 32 := by decide +kernel

theorem card_R2 : ((Finset.range (2 ^ 7)).filter R2).card = 32 := by decide +kernel

theorem ne_of_bits {k i j : ℕ} (hb : k.testBit i = true) (h : k.testBit j = false) : i ≠ j := by
  rintro rfl
  rw [h] at hb
  exact Bool.false_ne_true hb

theorem lemmaY_of_srch [Finite M] (hs : srch3 tab = true) (ht : tabOK tab = true)
    (hr : CyRel tab g) (hne : ∀ k, 0 < k → k < 2 ^ 7 → psiG g k 7 ≠ 1)
    (S0 S2 : Subgroup M) (hc0 : Nat.card S0 ≤ 32) (hc2 : Nat.card S2 ≤ 32)
    (hg0 : ∀ i < 7, i ≠ 3 → i ≠ 5 → g i ∈ S0) (hg2 : ∀ i < 7, i ≠ 4 → i ≠ 6 → g i ∈ S2)
    {H : Type*} [Group H] (Φ : H →* M) (hΦ : Function.Injective Φ) (α : H →* H)
    (hα : ∀ y, α (α y) = y) {t z : H} (hΦt : Φ t = g 0) (hΦz : Φ z = g 1)
    (hαt : α t = t * z) (hαz : α z = z)
    (hrange : ∀ x, x ∈ S0 ∨ x ∈ S2 → ∃ y, Φ y = x)
    (h02 : ∀ y, Φ y ∈ S0 → Φ (α y) ∈ S2) (h20 : ∀ y, Φ y ∈ S2 → Φ (α y) ∈ S0) :
    ∃ y : H, y⁻¹ * α y * (y⁻¹ * α y) = 1 ∧ y⁻¹ * α y ≠ 1 ∧ y⁻¹ * α y ≠ z := by
  classical
  have h7 : ∀ {x : ℕ}, x < 2 ^ 3 → x < 2 ^ 7 := fun hx => lt_of_lt_of_le hx (by norm_num)
  have hinj : ∀ {a b : ℕ}, a < 2 ^ 7 → b < 2 ^ 7 → psiG g a 7 = psiG g b 7 → a = b :=
    fun ha hb e => psi_inj hr hne ha hb e
  have hR0 : ∀ k < 2 ^ 7, R0 k → psiG g k 7 ∈ S0 := fun k _ hk =>
    psiG_mem fun i hi hb => hg0 i hi (ne_of_bits hb hk.1) (ne_of_bits hb hk.2)
  have hR2 : ∀ k < 2 ^ 7, R2 k → psiG g k 7 ∈ S2 := fun k _ hk =>
    psiG_mem fun i hi hb => hg2 i hi (ne_of_bits hb hk.1) (ne_of_bits hb hk.2)
  have hk0 : Nat.card S0 ≤ ((Finset.range (2 ^ 7)).filter R0).card := by
    rw [card_R0]
    exact hc0
  have hk2 : Nat.card S2 ≤ ((Finset.range (2 ^ 7)).filter R2).card := by
    rw [card_R2]
    exact hc2
  have hlift : ∀ i < 7, ∃ y, Φ y = g i := by
    intro i hi
    by_cases h35 : i = 3 ∨ i = 5
    · exact hrange _ (Or.inr (hg2 i hi (by omega) (by omega)))
    · exact hrange _ (Or.inl (hg0 i hi (by omega) (by omega)))
  choose! h hh using hlift
  have hlane : ∀ i < 7, ∃ k < 2 ^ 7, psiG g k 7 = Φ (α (h i)) := by
    intro i hi
    by_cases h35 : i = 3 ∨ i = 5
    · exact psi_onto hr hne R0 S0 hR0 hk0
        (h20 (h i) (by rw [hh i hi]; exact hg2 i hi (by omega) (by omega)))
    · exact psi_onto hr hne R2 S2 hR2 hk2
        (h02 (h i) (by rw [hh i hi]; exact hg0 i hi (by omega) (by omega)))
  choose! l hl hψl using hlane
  have hlR2 : ∀ i < 7, i ≠ 3 → i ≠ 5 → R2 (l i) := fun i hi h3 h5 =>
    (psi_region hr hne R2 S2 hR2 hk2 (hl i hi)).1
      (by rw [hψl i hi]; exact h02 _ (by rw [hh i hi]; exact hg0 i hi h3 h5))
  have hlR0 : ∀ i < 7, i ≠ 4 → i ≠ 6 → R0 (l i) := fun i hi h4 h6 =>
    (psi_region hr hne R0 S0 hR0 hk0 (hl i hi)).1
      (by rw [hψl i hi]; exact h20 _ (by rw [hh i hi]; exact hg2 i hi h4 h6))
  have hΦψ : ∀ k, Φ (psiG h k 7) = psiG g k 7 := fun k => by
    rw [psiG_map]
    exact psiG_congrF fun i hi => hh i hi
  have hαψ : ∀ k, Φ (α (psiG h k 7)) = psiG (fun i => psiG g (l i) 7) k 7 := fun k => by
    have e := psiG_map (Φ.comp α) h k 7
    simp only [MonoidHom.comp_apply] at e
    rw [e]
    exact psiG_congrF fun i hi => (hψl i hi).symm
  have hψ1 : psiG g 1 7 = g 0 := psiG_pow g (j := 0) (by norm_num)
  have hψ2 : psiG g 2 7 = g 1 := psiG_pow g (j := 1) (by norm_num)
  have hψ3 : psiG g 3 7 = g 0 * g 1 := by
    have e : bm2 tab 1 2 = 3 := by
      rw [bm2_lo tab (by norm_num)]
      rfl
    rw [← e, psi_mul hr (by norm_num) (by norm_num), hψ1, hψ2]
  have ht0 : h 0 = t := hΦ (by rw [hh 0 (by norm_num), hΦt])
  have hz1 : h 1 = z := hΦ (by rw [hh 1 (by norm_num), hΦz])
  have hl0 : l 0 = 3 := hinj (hl 0 (by norm_num)) (by norm_num)
    (by rw [hψl 0 (by norm_num), ht0, hαt, map_mul, hΦt, hΦz, hψ3])
  have hl1 : l 1 = 2 := hinj (hl 1 (by norm_num)) (by norm_num)
    (by rw [hψl 1 (by norm_num), hz1, hαz, hΦz, hψ2])
  have hl2 : l 2 < 2 ^ 3 := by
    have a := hlR0 2 (by norm_num) (by norm_num) (by norm_num)
    have b := hlR2 2 (by norm_num) (by norm_num) (by norm_num)
    exact lt8_of_bits (hl 2 (by norm_num)) a.1 b.1 a.2 b.2
  set c := packL l with hc
  have hlc : ∀ i < 7, lane c i = l i := fun i hi => lane_packL hl hi
  have hβP : ∀ k, ∀ n ≤ 7, betaP tab c k n < 2 ^ 7 ∧
      psiG g (betaP tab c k n) 7 = psiG (fun i => psiG g (l i) 7) k n := by
    intro k n
    induction n with
    | zero =>
      intro _
      rw [betaP_zero, psiG_zero]
      exact ⟨by norm_num, psiG_of_zero 7⟩
    | succ n ih =>
      intro hn
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      rw [betaP_succ, cy_nIfD, bt_eq, psiG_succ (g := fun i => psiG g (l i) 7) k n]
      cases hb : k.testBit n
      · simpa using ⟨ih1, ih2⟩
      · simp only [if_true]
        rw [hlc n (by omega)]
        exact ⟨bm2_lt tab ih1 (hl n (by omega)), by rw [psi_mul hr ih1 (hl n (by omega)), ih2]⟩
  have hβ : ∀ k, beta2 tab c k < 2 ^ 7 ∧ psiG g (beta2 tab c k) 7 = Φ (α (psiG h k 7)) := by
    intro k
    rw [beta2_eq, hαψ]
    exact hβP k 7 le_rfl
  have hsq : ∀ i < 7, bf tab (l i) (l i) = 0 := by
    intro i hi
    have hhh : h i * h i = 1 := hΦ (by rw [map_mul, hh i hi, hr.sq i hi, map_one])
    have e : bm2 tab (l i) (l i) = 0 := hinj (bm2_lt tab (hl i hi) (hl i hi)) (by norm_num) (by
      rw [psi_mul hr (hl i hi) (hl i hi), hψl i hi, ← map_mul, ← map_mul, hhh, map_one, map_one,
        psiG_of_zero])
    rwa [bm2_eq, Nat.xor_self, Nat.zero_xor] at e
  have hcen : ∀ e < 2 ^ 3, psiG g (cen c e) 7 = psiG (fun i => psiG g (l i) 7) e 7 := by
    intro e he
    have hx : ∀ j < 3, (if e.testBit j = true then lane c j else 0) < 2 ^ 3 := by
      intro j hj
      split
      · rw [hlc j (by omega)]
        interval_cases j
        · rw [hl0]; norm_num
        · rw [hl1]; norm_num
        · exact hl2
      · norm_num
    have hxj : ∀ j < 3, psiG g (if e.testBit j = true then lane c j else 0) 7 =
        if e.testBit j = true then psiG g (l j) 7 else 1 := by
      intro j hj
      split
      · rw [hlc j (by omega)]
      · exact psiG_of_zero 7
    rw [cen_eq, psi_lo_xor hr (Nat.xor_lt_two_pow (hx 0 (by norm_num)) (hx 1 (by norm_num)))
      (hx 2 (by norm_num)), psi_lo_xor hr (hx 0 (by norm_num)) (hx 1 (by norm_num)),
      hxj 0 (by norm_num), hxj 1 (by norm_num), hxj 2 (by norm_num), psiG_lo _ he (by norm_num),
      psiG_three]
  have hcen_lt : ∀ e, cen c e < 2 ^ 3 := by
    intro e
    rw [cen_eq]
    have hx : ∀ j < 3, (if e.testBit j = true then lane c j else 0) < 2 ^ 3 := by
      intro j hj
      split
      · rw [hlc j (by omega)]
        interval_cases j
        · rw [hl0]; norm_num
        · rw [hl1]; norm_num
        · exact hl2
      · norm_num
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (hx 0 (by norm_num)) (hx 1 (by norm_num)))
      (hx 2 (by norm_num))
  have hrel : ∀ m < 7, ∀ i < m,
      bf tab (l m) (l i) ^^^ bf tab (l i) (l m) = cen c (cg tab m i) := by
    intro m hm i him
    set e := cg tab m i with he_def
    have hc := hr.comm m hm i him
    rw [bf_two_pow ht m hm i him, ← he_def, ← psiG_lo g (cg_lt tab m i) (by norm_num : 3 ≤ 7),
      ← hΦψ e, ← hh m hm, ← hh i (by omega), ← map_mul, ← map_mul, ← map_mul] at hc
    have hc' := congrArg (fun y => Φ (α y)) (hΦ hc)
    simp only [map_mul] at hc'
    rw [← hψl m hm, ← hψl i (by omega), hαψ, ← hcen e (cg_lt tab m i),
      ← psi_mul hr (hl m hm) (hl i (by omega)), ← psi_mul hr (hl i (by omega)) (hl m hm),
      ← psi_mul hr (bm2_lt tab (hl i (by omega)) (hl m hm)) (h7 (hcen_lt e))] at hc'
    have e' := hinj (bm2_lt tab (hl m hm) (hl i (by omega)))
      (bm2_lt tab (bm2_lt tab (hl i (by omega)) (hl m hm)) (h7 (hcen_lt e))) hc'
    rw [bm2_eq, bm2_eq, bm2_eq, bf_lo_r tab _ (hcen_lt e), Nat.xor_zero] at e'
    exact xor_rel e'
  have hst : ∀ m < 7, stage2 true tab (m + 1) (c % 2 ^ (7 * (m + 1))) = true := by
    intro m hm
    have hlm : ∀ i ≤ m, lane (c % 2 ^ (7 * (m + 1))) i = l i := fun i hi => by
      rw [lane_mod_le hm hi, hlc i (by omega)]
    refine stage2_true ?_ (fun i hi => ?_) (fun g' hg hlt => ?_)
    · rw [hlm m le_rfl]
      exact hsq m hm
    · rw [hlm m le_rfl, hlm i (by omega), hrel m hm i hi]
      by_cases hm3 : m < 3
      · rw [cg_zero ht hm hi (by omega)]
        rfl
      · simp only [cen_eq, hlm 0 (by omega), hlm 1 (by omega), hlm 2 (by omega),
          hlc 0 (by norm_num), hlc 1 (by norm_num), hlc 2 (by norm_num)]
    · rw [hlm g' (by omega)] at hlt ⊢
      have hbits : ∀ i < 7, (l g').testBit i = true →
          lane (c % 2 ^ (7 * (m + 1))) i = lane c i := by
        intro i hi hb
        have him : i ≤ m := by
          by_contra hne
          rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt
            (Nat.pow_le_pow_right (by norm_num) (by omega)))] at hb
          exact Bool.false_ne_true hb
        rw [lane_mod_le hm him]
      rw [beta2_eq, betaP_congr hbits, ← beta2_eq]
      have hα' : psiG h (l g') 7 = α (h g') := hΦ (by rw [hΦψ, hψl g' (by omega)])
      have hb := hβ (l g')
      rw [hα', hα, hh g' (by omega), ← psiG_pow g (j := g') (by omega)] at hb
      exact hinj hb.1 (Nat.pow_lt_pow_right (by norm_num) (by omega)) hb.2
  obtain ⟨k, hk, hgoal⟩ := srch3_sound hs (hc ▸ packL_lt hl) (by rw [hlc 0 (by norm_num), hl0])
    (by rw [hlc 1 (by norm_num), hl1]) (by rw [hlc 2 (by norm_num)]; exact hl2)
    (fun m hm => by
      have hm7 : m < 7 := by omega
      rw [hlc m hm7]
      exact hlR0 m hm7 (by omega) (by omega))
    (fun m hm => by
      have hm7 : m < 7 := by omega
      rw [hlc m hm7]
      exact hlR2 m hm7 (by omega) (by omega)) hst
  obtain ⟨hb_lt, hb⟩ := hβ k
  simp only [goalK2, goalU, cy_bAndD, Bool.and_eq_true] at hgoal
  set b := beta2 tab c k with hb_def
  set u := bm2 tab (bm2 tab k (bm2 tab k k)) b with hu_def
  obtain ⟨e1, e2, e3, e4⟩ := hgoal
  have hu : u < 2 ^ 7 := bm2_lt tab (bm2_lt tab hk (bm2_lt tab hk hk)) hb_lt
  have hku : bm2 tab k u = b := Nat.eq_of_beq_eq_true e1
  have huu : bm2 tab u u = 0 := Nat.eq_of_beq_eq_true e2
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0] at e3
    exact absurd e3 (by decide)
  have hu2 : u ≠ 2 := by
    intro h0
    rw [h0] at e4
    exact absurd e4 (by decide)
  refine ⟨psiG h k 7, ?_⟩
  have hΦu : Φ ((psiG h k 7)⁻¹ * α (psiG h k 7)) = psiG g u 7 := by
    rw [map_mul, map_inv, hΦψ, ← hb, ← hku, psi_mul hr hk hu, inv_mul_cancel_left]
  refine ⟨hΦ ?_, fun h1 => hu0 (hinj hu (by norm_num) ?_), fun h1 => hu2 (hinj hu (by norm_num) ?_)⟩
  · rw [map_mul, hΦu, ← psi_mul hr hu hu, huu, psiG_of_zero, map_one]
  · rw [← hΦu, h1, map_one, psiG_of_zero]
  · rw [← hΦu, h1, hΦz, hψ2]

end CFSG.KC.OmegaCY

end
