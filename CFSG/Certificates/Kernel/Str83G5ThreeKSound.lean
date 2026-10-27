module

public import Certificates.Data.Kernel.Str83G5ThreeK
public import CFSG.Certificates.Kernel.Str83G5TypeKSound
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Quasithin.Stroth.G5.K

local instance : NeZero (2 ^ 3 - 1) := ⟨by decide⟩

private theorem brec_false' (x b : Bool) : (Bool.rec false x b : Bool) = (b && x) := by
  cases b <;> rfl

private theorem brec_or' (x b : Bool) : (Bool.rec x true b : Bool) = (b || x) := by
  cases b <;> simp

private theorem brec_beq' {α : Sort _} (a b : α) (x y : ℕ) :
    (Bool.rec a b (Nat.beq x y) : α) = if x = y then b else a := by
  cases h : Nat.beq x y
  · rw [if_neg (Nat.ne_of_beq_eq_false h)]
  · rw [if_pos (Nat.eq_of_beq_eq_true h)]

private theorem brec_ble' {α : Sort _} (a b : α) (x y : ℕ) :
    (Bool.rec a b (Nat.ble x y) : α) = if x ≤ y then b else a := by
  cases h : Nat.ble x y
  · rw [if_neg (fun h' => absurd (Nat.ble_eq_true_of_le h') (by rw [h]; decide))]
  · rw [if_pos (Nat.le_of_ble_eq_true h)]

private theorem nat_mod3 (a b : ℕ) : Nat.mod a b = a % b := rfl

private theorem beq_dec' (a b : ℕ) : Nat.beq a b = decide (a = b) := by
  cases h : Nat.beq a b
  · exact (decide_eq_false (Nat.ne_of_beq_eq_false h)).symm
  · exact (decide_eq_true (Nat.eq_of_beq_eq_true h)).symm

def enc3 (v : Coord 3) : ℕ := 7 * v.1.val + v.2.val

theorem sg1K_enc : ∀ (m₀ : ZMod (2 ^ 3 - 1)) (v : Coord 3),
    sg1K m₀.val (enc3 v) = enc3 (sigma1 m₀ v) := by decide +kernel

theorem sg2K_enc : ∀ (k₀ : ZMod (2 ^ 3 - 1)) (v : Coord 3),
    sg2K k₀.val (enc3 v) = enc3 (sigma2 k₀ v) := by decide +kernel

theorem enc_psi : ∀ m₀ : ZMod (2 ^ 3 - 1), enc3 (psi m₀) = 7 + m₀.val := by decide +kernel

theorem enc_chi : ∀ k₀ : ZMod (2 ^ 3 - 1), enc3 (chi k₀) = 7 * k₀.val + 1 := by decide +kernel

theorem smK1_enc : ∀ v : Coord 3, smK 1 (enc3 v) = enc3 ((1 : ZMod (2 ^ 3 - 1)) • v) := by
  decide +kernel

theorem smK6_enc : ∀ v : Coord 3, smK 6 (enc3 v) = enc3 ((-1 : ZMod (2 ^ 3 - 1)) • v) := by
  decide +kernel

theorem smK5_enc : ∀ v : Coord 3,
    smK 5 (enc3 v) = enc3 (cen 3 • (1 : ZMod (2 ^ 3 - 1)) • v) := by
  decide +kernel

theorem smK30_enc : ∀ v : Coord 3,
    smK 30 (enc3 v) = enc3 (cen 3 • (-1 : ZMod (2 ^ 3 - 1)) • v) := by
  decide +kernel

def keyS (S : Finset (Coord 3)) : ℕ := 48 - S.sup fun x => 48 - enc3 x

theorem keyS_cls : ∀ v : Coord 3, keyS (cls v) = clsK (enc3 v) := by decide +kernel

theorem iter_fwd (k₀ m₀ : ZMod (2 ^ 3 - 1)) (v : Coord 3) (n : ℕ) :
    (Nat.rec (motive := fun _ => ℕ) (enc3 v) (fun _ w => sg2K k₀.val (sg1K m₀.val w)) n : ℕ) =
      enc3 ((sigma2 k₀ ∘ sigma1 m₀)^[n] v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.comp_apply, ← sg2K_enc, ← sg1K_enc, ← ih]

theorem iter_bwd (k₀ m₀ : ZMod (2 ^ 3 - 1)) (v : Coord 3) (n : ℕ) :
    (Nat.rec (motive := fun _ => ℕ) (enc3 v) (fun _ w => sg1K m₀.val (sg2K k₀.val w)) n : ℕ) =
      enc3 ((sigma1 m₀ ∘ sigma2 k₀)^[n] v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.comp_apply, ← sg1K_enc, ← sg2K_enc, ← ih]

theorem pwK_enc (k₀ m₀ : ZMod (2 ^ 3 - 1)) (J1 t' : ℕ) (v : Coord 3) (t : ℤ)
    (ht : (t' : ℤ) - J1 = t) :
    pwK k₀.val m₀.val J1 t' (enc3 v) = enc3 (mPow k₀ m₀ t v) := by
  unfold pwK
  rw [brec_ble']
  split_ifs with h
  · rw [iter_fwd]
    have h' : t = ((t' - J1 : ℕ) : ℤ) := by omega
    subst h'
    rfl
  · rw [iter_bwd]
    obtain ⟨u, hu⟩ : ∃ u, J1 - t' = u + 1 := ⟨J1 - t' - 1, by omega⟩
    have h' : t = Int.negSucc u := by
      rw [Int.negSucc_eq]
      omega
    subst h'
    change enc3 ((sigma1 m₀ ∘ sigma2 k₀)^[J1 - t'] v) = _
    rw [hu]
    rfl

noncomputable def g3 (v : Coord 3) : ℕ := pk (clsK (enc3 v))

theorem step3_spec (p : Pattern) (k₀ m₀ s : ZMod (2 ^ 3 - 1)) (b sc : ℕ)
    (hsc : (if b = 1 then 6 else 1) = sc)
    (h1 : ∀ v : Coord 3, smK sc (enc3 v) = enc3 (s • v))
    (h5 : ∀ v : Coord 3, smK (5 * sc) (enc3 v) = enc3 (cen 3 • s • v))
    (l : ℤ) (mm lo : ℕ) (hlo : (lo : ℤ) = l + 2 * ((p.J : ℤ) + 1)) :
    ((Pattern.contrib k₀ m₀ s l (p.dropAt l mm)).map g3).sum =
      step3K k₀.val m₀.val (p.J + 1) p.s2 p.s1 p.l1 mm lo b := by
  unfold step3K Pattern.contrib Pattern.dropAt
  simp only [brec_beq', hsc, dSK_eq, dLK_eq]
  by_cases hl : Even l
  · have h0 : Nat.mod lo 2 = 0 := by
      obtain ⟨k, hk⟩ := hl
      change lo % 2 = 0
      omega
    have hw : pwK k₀.val m₀.val (p.J + 1) (Nat.div lo 2) (Nat.add 7 m₀.val) =
        enc3 (mPow k₀ m₀ (l / 2) (psi m₀)) := by
      rw [← pwK_enc k₀ m₀ (p.J + 1) (lo / 2) (psi m₀) (l / 2) (by obtain ⟨k, hk⟩ := hl; omega),
        enc_psi]
      rfl
    simp only [hl, h0, ↓reduceIte, hw]
    split_ifs <;> simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.sum_cons, Multiset.sum_singleton, Multiset.map_zero, Multiset.sum_zero, g3,
      Nat.mul_eq, Nat.add_eq, h1, h5, add_zero]
  · have h0 : Nat.mod lo 2 = 1 := by
      rw [Int.not_even_iff_odd] at hl
      obtain ⟨k, hk⟩ := hl
      change lo % 2 = 1
      omega
    have hw : pwK k₀.val m₀.val (p.J + 1) (Nat.div lo 2) (Nat.add (Nat.mul 7 k₀.val) 1) =
        enc3 (mPow k₀ m₀ ((l - 1) / 2) (chi k₀)) := by
      rw [← pwK_enc k₀ m₀ (p.J + 1) (lo / 2) (chi k₀) ((l - 1) / 2) (by
        rw [Int.not_even_iff_odd] at hl
        obtain ⟨k, hk⟩ := hl
        omega), enc_chi]
      rfl
    simp only [hl, h0, ↓reduceIte, hw, Nat.one_ne_zero]
    split_ifs <;> simp only [Multiset.map_singleton, Multiset.sum_singleton, Multiset.map_zero,
      Multiset.sum_zero, g3, h1]

theorem sum_map_sum' {α ι : Type*} (S : Finset ι) (M : ι → Multiset α) (G : α → ℕ) :
    ((∑ i ∈ S, M i).map G).sum = ∑ i ∈ S, ((M i).map G).sum := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons a S ha ih => simp [Finset.sum_cons, ih]

theorem winOK3_of (p : Pattern) (k₀ m₀ : ZMod (2 ^ 3 - 1)) (i d : ℕ) (hd : d ≤ p.J)
    (heq : ((p.chainR k₀ m₀ i (i + d)).map g3).sum = ((p.chainL k₀ m₀ i (i + d)).map g3).sum) :
    winOK (step3K k₀.val m₀.val (p.J + 1) p.s2 p.s1 p.l1) p.J (2 * (p.J + 1)) i d = true := by
  have hR : ∑ k ∈ Finset.range (p.J - d),
      step3K k₀.val m₀.val (p.J + 1) p.s2 p.s1 p.l1 (d + 1 + k)
        (i + d + (k + 1) + 2 * (p.J + 1)) 0 = ((p.chainR k₀ m₀ i (i + d)).map g3).sum := by
    unfold Pattern.chainR
    have hs : (i : ℤ) + p.J = (i + d : ℤ) + ((p.J - d : ℕ) : ℤ) := by omega
    rw [sum_map_sum', hs, sum_Ioc_shift]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [step3_spec p k₀ m₀ 1 0 1 (by simp) smK1_enc smK5_enc ((i : ℤ) + d + 1 + k) _
      (i + d + (k + 1) + 2 * (p.J + 1)) (by push_cast; ring)]
    have hm : ((i : ℤ) + d + 1 + k - i).toNat = d + 1 + k := by omega
    rw [hm]
  have hL : ∑ k ∈ Finset.range (p.J - d),
      step3K k₀.val m₀.val (p.J + 1) p.s2 p.s1 p.l1 (d + 1 + k)
        (i + 2 * (p.J + 1) - (k + 1)) 1 = ((p.chainL k₀ m₀ i (i + d)).map g3).sum := by
    unfold Pattern.chainL
    have hs : (i : ℤ) + d - p.J = (i : ℤ) - ((p.J - d : ℕ) : ℤ) := by omega
    rw [sum_map_sum', hs, sum_Ico_shift]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [step3_spec p k₀ m₀ (-1) 1 6 (by simp) smK6_enc smK30_enc ((i : ℤ) - 1 - k) _
      (i + 2 * (p.J + 1) - (k + 1)) (by omega)]
    have hm : ((i : ℤ) + d - (i - 1 - k)).toNat = d + 1 + k := by omega
    rw [hm]
  unfold winOK
  rw [beq_dec', decide_eq_true_eq, natRec_sum, natRec_sum]
  exact hR.trans (heq.trans hL.symm)

theorem allWin3_of (p : Pattern) (k₀ m₀ : ZMod (2 ^ 3 - 1))
    (hpa : passAllConc (n := 3) p k₀ m₀ = true) :
    allWin (step3K k₀.val m₀.val (p.J + 1) p.s2 p.s1 p.l1) p.J = true := by
  unfold passAllConc at hpa
  rw [List.all_eq_true] at hpa
  have hw : ∀ i : ℕ, i ≤ 1 → ∀ d ≤ p.J,
      ((p.chainR k₀ m₀ i (i + d)).map g3).sum = ((p.chainL k₀ m₀ i (i + d)).map g3).sum := by
    intro i hi d hd
    have hi' : (i : ℤ) ∈ [(0 : ℤ), 1] := by
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp
    have h := List.all_eq_true.mp (hpa (i : ℤ) hi') d (List.mem_range.mpr (by omega))
    rw [decide_eq_true_eq] at h
    have h' := congrArg (fun M => (M.map fun S => pk (keyS S)).sum) h
    simp only [Multiset.map_map, Function.comp_def, keyS_cls] at h'
    exact h'
  change allBelow (p.J + 1) (fun d => Bool.rec false
    (winOK (step3K k₀.val m₀.val (p.J + 1) p.s2 p.s1 p.l1) p.J (2 * (p.J + 1)) 1 d)
    (winOK (step3K k₀.val m₀.val (p.J + 1) p.s2 p.s1 p.l1) p.J (2 * (p.J + 1)) 0 d)) = true
  rw [allBelow_eq_true]
  intro d hd
  rw [brec_false', Bool.and_eq_true]
  exact ⟨winOK3_of p k₀ m₀ 0 d (by omega) (hw 0 (by omega) d (by omega)),
    winOK3_of p k₀ m₀ 1 d (by omega) (hw 1 le_rfl d (by omega))⟩

theorem okThreeK_eq (p : Pattern) (k m : ℕ) (hk : k < 6) (hm : m < 6) :
    okThreeK p (k + 1) (m + 1) =
      okThree p ((k + 1 : ℕ) : ZMod (2 ^ 3 - 1)) ((m + 1 : ℕ) : ZMod (2 ^ 3 - 1)) := by
  have hT : ∀ c : ℕ, c < 7 →
      ((4 * ((k + 1 : ℕ) : ZMod (2 ^ 3 - 1)) * ((m + 1 : ℕ) : ZMod (2 ^ 3 - 1)) - 2 = c) ↔
        (4 * ((k + 1) * (m + 1)) + 5) % 7 = c) := by
    intro c hc
    have h : (4 * ((k + 1 : ℕ) : ZMod (2 ^ 3 - 1)) * ((m + 1 : ℕ) : ZMod (2 ^ 3 - 1)) - 2) =
        ((4 * ((k + 1) * (m + 1)) + 5 : ℕ) : ZMod (2 ^ 3 - 1)) := by
      have h7 : ((7 : ℕ) : ZMod (2 ^ 3 - 1)) = 0 := ZMod.natCast_self _
      push_cast at h7 ⊢
      linear_combination (-1 : ZMod (2 ^ 3 - 1)) * h7
    rw [h, ZMod.natCast_eq_natCast_iff']
    have h7 : (2 ^ 3 - 1 : ℕ) = 7 := rfl
    rw [h7, Nat.mod_eq_of_lt hc]
  have hT0 := hT 0 (by norm_num)
  have hT1 := hT 1 (by norm_num)
  rw [Nat.cast_zero] at hT0
  rw [Nat.cast_one] at hT1
  unfold okThreeK okThree
  simp only [brec_false', brec_or', beq_dec', isP_eq, Nat.add_eq, Nat.mul_eq, nat_mod3]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, hT0, hT1]
  simp only [Pattern.p16, Pattern.p17, Pattern.p18, Pattern.p20, Pattern.p73, Pattern.target]
  tauto

theorem threeCheck_of_threeK (h : threeK = true) : threeCheck () = true := by
  unfold threeCheck admissibleList
  rw [List.all_eq_true]
  intro p hp
  rw [List.mem_filter] at hp
  obtain ⟨hp, hadm⟩ := hp
  simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hp
  obtain ⟨s1, hs1, s2, hs2, l1, hl1, rfl⟩ := hp
  have hc :=
    allBelow_eq_true.mp (allBelow_eq_true.mp (allBelow_eq_true.mp h s1 hs1) s2 hs2) l1 hl1
  rw [admK_of _ hadm] at hc
  change chk3K ⟨s2, s1, l1⟩ = true at hc
  generalize (⟨s2, s1, l1⟩ : Pattern) = p at hc ⊢
  rw [List.all_eq_true]
  intro k hk
  rw [List.all_eq_true]
  intro m hm
  rw [List.mem_range] at hk hm
  have h1 := allBelow_eq_true.mp (allBelow_eq_true.mp hc k hk) m hm
  rw [Bool.or_eq_true, Bool.not_eq_true']
  by_cases hpa : passAllConc (n := 3) p ((k + 1 : ℕ) : ZMod (2 ^ 3 - 1))
      ((m + 1 : ℕ) : ZMod (2 ^ 3 - 1)) = true
  · right
    have hw := allWin3_of p _ _ hpa
    have hk' : ((k + 1 : ℕ) : ZMod (2 ^ 3 - 1)).val = k + 1 := by
      rw [ZMod.val_natCast]
      exact Nat.mod_eq_of_lt (by norm_num; omega)
    have hm' : ((m + 1 : ℕ) : ZMod (2 ^ 3 - 1)).val = m + 1 := by
      rw [ZMod.val_natCast]
      exact Nat.mod_eq_of_lt (by norm_num; omega)
    rw [hk', hm'] at hw
    rw [← okThreeK_eq p k m hk hm]
    exact brec_true_of h1 hw
  · left
    simpa using hpa

end CFSG.Quasithin.Stroth.G5.K

end
