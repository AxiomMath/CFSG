
module

public import Certificates.Data.Kernel.Fi22S0.Check
public import CFSG.Certificates.Kernel.SporCov.BaseFix
public import CFSG.HardMathSupport.Foote.E27.SporFi22Base
public import CFSG.HardMathSupport.Foote.E27.TableSylow

public section

namespace CFSG.KD.Fi22S0

open CFSG.KC.Loop CFSG.KC.Fi22S0 CFSG.KC.SporCov CFSG.KD.SporCov CFSG.Sporadic.Th
open CFSG.Sporadic.Fi22 (J a b)
open CFSG.Sporadic.Fi22.S0 CFSG.HardMathSupport.Foote.E27 CFSG.HardMathSupport.Foote.E27.Fi22S0

theorem sB_eq (y : ℕ) (k : ℕ → Bool) : CFSG.KC.Enum.strictB y k = k y := by
  cases y <;> rfl

theorem bRec_and (x y : Bool) : Bool.rec (motive := fun _ => Bool) false y x = (x && y) := by
  cases x <;> rfl

theorem blt_iff (i k : ℕ) : Nat.blt i k = true ↔ i < k := by
  rw [Nat.blt_eq]

theorem beq_iff (i k : ℕ) : Nat.beq i k = true ↔ i = k :=
  ⟨Nat.eq_of_beq_eq_true, fun h => by rw [h, Nat.beq_refl]⟩

theorem ent_lt (P x : ℕ) : ent P x < 4096 := by
  change (P >>> (12 * x)) &&& 4095 < 4096
  exact Nat.lt_succ_of_le Nat.and_le_right

@[expose] def pk5 (y : ℕ → ℕ) : ℕ :=
  y 0 ||| (y 1 <<< 12 ||| (y 2 <<< 24 ||| (y 3 <<< 36 ||| y 4 <<< 48)))

theorem testBit_hi {x j : ℕ} (hx : x < 4096) (hj : 12 ≤ j) : x.testBit j = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx
    (by calc (4096 : ℕ) = 2 ^ 12 := rfl
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj))

theorem testBit_shl {x : ℕ} (hx : x < 4096) (s j : ℕ) :
    (x <<< (12 * s)).testBit j = (decide (12 * s ≤ j ∧ j < 12 * s + 12) && x.testBit (j - 12 * s)) := by
  rw [Nat.testBit_shiftLeft]
  by_cases h1 : 12 * s ≤ j
  · by_cases h2 : j < 12 * s + 12
    · simp [h1, h2]
    · simp [h1, h2, testBit_hi hx (by omega : 12 ≤ j - 12 * s)]
  · simp [h1]

theorem pk5_testBit (y : ℕ → ℕ) (hy : ∀ t < 5, y t < 4096) (j : ℕ) :
    (pk5 y).testBit j =
      ((decide (12 * 0 ≤ j ∧ j < 12 * 0 + 12) && (y 0).testBit (j - 12 * 0)) ||
      ((decide (12 * 1 ≤ j ∧ j < 12 * 1 + 12) && (y 1).testBit (j - 12 * 1)) ||
      ((decide (12 * 2 ≤ j ∧ j < 12 * 2 + 12) && (y 2).testBit (j - 12 * 2)) ||
      ((decide (12 * 3 ≤ j ∧ j < 12 * 3 + 12) && (y 3).testBit (j - 12 * 3)) ||
      (decide (12 * 4 ≤ j ∧ j < 12 * 4 + 12) && (y 4).testBit (j - 12 * 4)))))) := by
  rw [← testBit_shl (hy 0 (by norm_num)), ← testBit_shl (hy 1 (by norm_num)),
    ← testBit_shl (hy 2 (by norm_num)), ← testBit_shl (hy 3 (by norm_num)),
    ← testBit_shl (hy 4 (by norm_num))]
  simp only [pk5, Nat.testBit_or, Nat.mul_zero, Nat.shiftLeft_zero]

theorem term_eq {x : ℕ} (hx : x < 4096) (s t : ℕ) {i : ℕ} (hi : i < 12) :
    (decide (12 * s ≤ 12 * t + i ∧ 12 * t + i < 12 * s + 12) && x.testBit (12 * t + i - 12 * s)) =
      (decide (s = t) && x.testBit i) := by
  by_cases h : s = t
  · subst h
    simp [hi]
  · have h2 : ¬(12 * s ≤ 12 * t + i ∧ 12 * t + i < 12 * s + 12) := by omega
    simp [h, h2]

theorem pk5_fld (y : ℕ → ℕ) (hy : ∀ t < 5, y t < 4096) {t : ℕ} (ht : t < 5) :
    (pk5 y >>> (12 * t)) &&& 4095 = y t := by
  have e : (4095 : ℕ) = 2 ^ 12 - 1 := rfl
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftRight, e, Nat.testBit_two_pow_sub_one, pk5_testBit y hy]
  by_cases hi : i < 12
  · rw [term_eq (hy 0 (by norm_num)) 0 t hi, term_eq (hy 1 (by norm_num)) 1 t hi,
      term_eq (hy 2 (by norm_num)) 2 t hi, term_eq (hy 3 (by norm_num)) 3 t hi,
      term_eq (hy 4 (by norm_num)) 4 t hi]
    interval_cases t <;> simp [hi]
  · simp [hi, testBit_hi (hy t ht) (by omega : 12 ≤ i)]

theorem pk5_inj {y z : ℕ → ℕ} (hy : ∀ t < 5, y t < 4096) (hz : ∀ t < 5, z t < 4096)
    (h : pk5 y = pk5 z) : ∀ t < 5, y t = z t := fun t ht => by
  rw [← pk5_fld y hy ht, ← pk5_fld z hz ht, h]

theorem mapK_pk5 (P : ℕ) (y : ℕ → ℕ) (hy : ∀ t < 5, y t < 4096) :
    mapK P (pk5 y) = pk5 fun t => ent P (y t) := by
  have d : ∀ t < 5, (pk5 y >>> (12 * t)) &&& 4095 = y t := fun t ht => pk5_fld y hy ht
  have d0 : fld(pk5 y, nat_lit 0, nat_lit 4095) = y 0 := d 0 (by norm_num)
  have d1 : fld(pk5 y, nat_lit 12, nat_lit 4095) = y 1 := d 1 (by norm_num)
  have d2 : fld(pk5 y, nat_lit 24, nat_lit 4095) = y 2 := d 2 (by norm_num)
  have d3 : fld(pk5 y, nat_lit 36, nat_lit 4095) = y 3 := d 3 (by norm_num)
  have d4 : fld(pk5 y, nat_lit 48, nat_lit 4095) = y 4 := d 4 (by norm_num)
  unfold mapK
  rw [d0, d1, d2, d3, d4]
  rfl

theorem inj_of_sorted {key s : ℕ → ℕ} {n : ℕ} (hs : ∀ m < n, s m < n)
    (hlt : ∀ m, m + 1 < n → key (s m) < key (s (m + 1))) :
    ∀ i < n, ∀ k < n, key i = key k → i = k := by
  have mono : ∀ m₁ m₂, m₁ < m₂ → m₂ < n → key (s m₁) < key (s m₂) := by
    intro m₁ m₂ h12 h2
    induction m₂ with
    | zero => omega
    | succ m ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 h12 with h | rfl
      · exact lt_trans (ih h (by omega)) (hlt m h2)
      · exact hlt _ h2
  have inj : ∀ m₁ < n, ∀ m₂ < n, key (s m₁) = key (s m₂) → m₁ = m₂ := by
    intro m₁ h1 m₂ h2 e
    rcases lt_trichotomy m₁ m₂ with h | h | h
    · exact absurd e (ne_of_lt (mono _ _ h h2))
    · exact h
    · exact absurd e (ne_of_gt (mono _ _ h h1))
  have surj : ∀ i < n, ∃ m < n, s m = i := by
    intro i hi
    obtain ⟨m, hm, e⟩ := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range n)
      (t := Finset.range n) (fun m _ => s m)
      (fun m hm => Finset.mem_range.2 (hs m (Finset.mem_range.1 hm)))
      (fun m₁ m₂ h1 h2 e => inj m₁ (Finset.mem_range.1 h1) m₂ (Finset.mem_range.1 h2)
        (by rw [e])) le_rfl i (Finset.mem_range.2 hi)
    exact ⟨m, Finset.mem_range.1 hm, e.symm⟩
  intro i hi k hk e
  obtain ⟨m₁, h1, rfl⟩ := surj i hi
  obtain ⟨m₂, h2, rfl⟩ := surj k hk
  rw [inj m₁ h1 m₂ h2 e]

@[expose] def bp : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 11
  | _ => 3

theorem bp_lt (t : ℕ) : bp t < 3510 := by
  unfold bp
  split <;> norm_num

@[expose] noncomputable def keyOf (g : J) : ℕ := pk5 fun t => idx 3510 g (bp t)

theorem keyOf_lt (g : J) : ∀ t < 5, idx 3510 g (bp t) < 4096 := fun t _ =>
  lt_trans (idx_lt g (bp_lt t)) (by norm_num)

theorem sep_bp (g : J) (h : ∀ t < 5, idx 3510 g (bp t) = bp t) : g = 1 := by
  have hl : ∀ i ≤ 5, g ∈ CFSG.Sporadic.Fi22.lvl i := by
    intro i hi
    induction i with
    | zero => exact CFSG.Sporadic.Fi22.mem_lvl_zero g
    | succ i ih =>
      refine (CFSG.Sporadic.Fi22.chain_facts'.2.1 i
        (by rw [CFSG.Sporadic.Fi22.chainBase_size]; omega) g (ih (by omega))).1 ?_
      have hi4 : i < 5 := by omega
      interval_cases i
      · exact h 0 (by norm_num)
      · exact h 1 (by norm_num)
      · exact h 2 (by norm_num)
      · exact h 3 (by norm_num)
      · exact h 4 (by norm_num)
  have hc := CFSG.Sporadic.Fi22.chain_facts'.2.2 5 (by rw [CFSG.Sporadic.Fi22.chainBase_size])
  rw [CFSG.Sporadic.Fi22.chainBase_size, Finset.Ico_self, Finset.prod_empty] at hc
  have hb := Subgroup.eq_bot_of_card_eq _ hc
  have hg := hl 5 le_rfl
  rw [hb] at hg
  exact (Subgroup.mem_bot).1 hg

theorem eq_of_keyOf {g h : J} (e : keyOf g = keyOf h) : g = h := by
  have hp := pk5_inj (keyOf_lt g) (keyOf_lt h) e
  have h1 : h⁻¹ * g = 1 := sep_bp _ fun t ht => by
    rw [idx_mul, hp t ht, idx_inv_idx]
  rw [inv_mul_eq_one] at h1
  exact h1.symm

def RepE (P : ℕ) (g : J) : Prop := ∀ x < 3510, ent P x = idx 3510 g x

theorem mapK_keyOf {P : ℕ} {g : J} (hP : RepE P g) (h : J) :
    mapK P (keyOf h) = keyOf (g * h) := by
  unfold keyOf
  rw [mapK_pk5 P _ (keyOf_lt h)]
  congr 1
  funext t
  rw [hP _ (idx_lt h (bp_lt t)), idx_mul]

theorem rep_reg {RF oi oj A B : ℕ → ℕ} (hA : ∀ x < 3510, A x = idx 3510 a x)
    (hB : ∀ x < 3510, B x = idx 3510 b x) (hbase : baseC RF A B = true)
    (hreg : ∀ k, 3 ≤ k → k < 570 → regC RF oi oj k = true)
    (hops : ∀ k, 3 ≤ k → k < 570 → (ops[k - 3]!).1 = oi k ∧ (ops[k - 3]!).2 = oj k) :
    ∀ k < 570, RepE (RF k) (regJ k) := by
  unfold baseC at hbase
  simp only [bRec_and, Bool.and_eq_true] at hbase
  obtain ⟨h0, h1, h2⟩ := hbase
  have r0 := agB_spec h0 (by norm_num)
  have r1 := agB_spec h1 (by norm_num)
  have r2 := invB_spec h2 (by norm_num)
  have r1' : ∀ x < 3510, ent (RF 1) x = idx 3510 b x := fun x hx => (r1 x hx).trans (hB x hx)
  have r2' := inv_of_left r1' r2
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk x hx
    by_cases k3 : k < 3
    · interval_cases k
      · rw [regJ_zero]; exact (r0 x hx).trans (hA x hx)
      · rw [regJ_one]; exact r1' x hx
      · rw [regJ_two]; exact r2' x hx
    · have hr := hreg k (by omega) hk
      unfold regC compOK at hr
      simp only [sB_eq, bRec_and, Bool.and_eq_true, blt_iff] at hr
      obtain ⟨hi, hj, hc⟩ := hr
      have hc' := beq_iff _ _ |>.1 (allBelow_specF hc (by norm_num) x hx)
      obtain ⟨e1, e2⟩ := hops k (by omega) hk
      rw [regJ_succ ⟨by omega, by rw [e1]; exact hi, by rw [e2]; exact hj⟩, e1, e2, idx_mul, hc',
        ih (oj k) hj (by omega) x hx, ih (oi k) hi (by omega) _ (idx_lt _ hx)]

theorem rep_gR {RF : ℕ → ℕ} (hR : ∀ k < 570, RepE (RF k) (regJ k)) {j : ℕ} (hj : j < 3) :
    RepE (RF (Bool.rec (motive := fun _ => ℕ)
      (Bool.rec (motive := fun _ => ℕ) (nat_lit 569) (nat_lit 411) (Nat.beq j (nat_lit 1)))
      (nat_lit 218) (Nat.beq j (nat_lit 0)))) (gJ j) := by
  have hg : gens[0]! = 218 ∧ gens[1]! = 411 ∧ gens[2]! = 569 := by decide
  interval_cases j
  · change RepE (RF 218) (gJ 0)
    rw [gJ_eq, hg.1]
    exact hR 218 (by norm_num)
  · change RepE (RF 411) (gJ 1)
    rw [gJ_eq, hg.2.1]
    exact hR 411 (by norm_num)
  · change RepE (RF 569) (gJ 2)
    rw [gJ_eq, hg.2.2]
    exact hR 569 (by norm_num)

theorem key_eq {key pp pj g : ℕ → ℕ} {k0 : ℕ} (hg : ∀ j < 3, RepE (g j) (gJ j))
    (hk0 : k0 = pk5 bp) (htree : ∀ i < nS, treeC key pp pj g k0 i = true)
    (hpar : ∀ i < nS, 0 < i → (par[i]!).1 = pp i ∧ (par[i]!).2 = pj i) :
    ∀ i < nS, key i = keyOf (tabElt gJ par i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    have h := htree i hi
    unfold treeC at h
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · have e : key 0 = k0 := Nat.eq_of_beq_eq_true h
      rw [e, hk0, tabElt_zero]
      unfold keyOf
      congr 1
      funext t
      rw [idx_one]
    · have hb : Nat.beq i 0 = false := by
        cases i
        · omega
        · rfl
      rw [hb] at h
      simp only [sB_eq, bRec_and, Bool.and_eq_true, blt_iff] at h
      obtain ⟨hp, hj, he⟩ := h
      obtain ⟨e1, e2⟩ := hpar i hi hpos
      have hp' : (par[i]!).1 < i := by rw [e1]; exact hp
      rw [Nat.eq_of_beq_eq_true he, ih (pp i) hp (by omega), mapK_keyOf (hg _ hj),
        tabElt_succ gJ par hp', e1, e2]

theorem tabData_of {key pp pj g sg : ℕ → ℕ} {lt : ℕ → ℕ → ℕ} {k0 : ℕ}
    (hg : ∀ j < 3, RepE (g j) (gJ j)) (hk0 : k0 = pk5 bp)
    (htree : ∀ i < nS, treeC key pp pj g k0 i = true)
    (hleft : ∀ j < 3, ∀ i < nS, leftC key lt g nS j i = true)
    (hsort : ∀ m < nS, sortC key sg nS m = true)
    (hpar : ∀ i < nS, 0 < i → (par[i]!).1 = pp i ∧ (par[i]!).2 = pj i)
    (hL : ∀ j < 3, ∀ i < nS, (L[j]!)[i]! = lt j i) :
    TabData gJ par L nS 3 := by
  have hkey := key_eq hg hk0 htree hpar
  refine ⟨fun i hpos hi => ?_, fun j hj i hi => ?_, fun i hi k hk e => ?_⟩
  · have h := htree i hi
    unfold treeC at h
    have hb : Nat.beq i 0 = false := by
      cases i
      · omega
      · rfl
    rw [hb] at h
    simp only [sB_eq, bRec_and, Bool.and_eq_true, blt_iff] at h
    obtain ⟨e1, e2⟩ := hpar i hi hpos
    rw [e1, e2]
    exact ⟨h.1, h.2.1⟩
  · have h := hleft j hj i hi
    unfold leftC at h
    simp only [sB_eq, bRec_and, Bool.and_eq_true, blt_iff] at h
    obtain ⟨hl, he⟩ := h
    rw [hL j hj i hi]
    refine ⟨hl, eq_of_keyOf ?_⟩
    rw [← hkey _ hl, Nat.eq_of_beq_eq_true he, hkey i hi, mapK_keyOf (hg j hj)]
  · have hs : ∀ m < nS, sg m < nS ∧ (m + 1 < nS → key (sg m) < key (sg (m + 1))) := by
      intro m hm
      have h := hsort m hm
      unfold sortC at h
      simp only [sB_eq, bRec_and, Bool.and_eq_true, blt_iff] at h
      refine ⟨h.1, fun hm1 => ?_⟩
      have h2 := h.2
      have hb : Nat.blt (Nat.succ m) nS = true := (blt_iff _ _).2 hm1
      rw [hb] at h2
      simp only [sB_eq, blt_iff] at h2
      exact h2
    refine inj_of_sorted (fun m hm => (hs m hm).1) (fun m hm => (hs m (by omega)).2 hm) i hi k hk ?_
    rw [hkey i hi, hkey k hk, e]

end CFSG.KD.Fi22S0

end
