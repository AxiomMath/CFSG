module

public import Certificates.Data.Kernel.E6TT.Cover
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TableTBridge

public section

namespace CFSG.KC.E6TT

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
open CFSG.KC.Enum (strictN strictB)
open Certificates.Data.E6TableT (Vec reps genAct cartan)
open CFSG.StandardType.TablePThreeKG (vecZ repZ genActZ)

theorem strictN_eqC (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem strictB_eqC (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem nIf_eqC (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem bIf_eqC (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem bAnd_trueC {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a <;> simp_all

theorem bitN_eqC (s c : Nat) : bitN s c = s.testBit c := by
  change Nat.beq ((s >>> c) &&& 1) 1 = _
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (s / 2 ^ c) with h | h
  · rw [h]
    rfl
  · rw [h]
    rfl

theorem testBit_lor_one_shiftLeft (s c i : Nat) :
    (Nat.lor s (Nat.shiftLeft 1 c)).testBit i = (s.testBit i || decide (c = i)) := by
  change (s ||| 1 <<< c).testBit i = _
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem natDiv_eqC (a b : Nat) : Nat.div a b = a / b := rfl

theorem natMod_eqC (a b : Nat) : Nat.mod a b = a % b := rfl

theorem dec_enc {w : Vec} (hl : w.length = 6) (hw : ∀ x ∈ w, 0 ≤ x ∧ x < 3) :
    dec (enc w) = w := by
  match w, hl with
  | [a, b, c, d, e, f], _ =>
    obtain ⟨a', rfl⟩ := Int.eq_ofNat_of_zero_le (hw a (by simp)).1
    obtain ⟨b', rfl⟩ := Int.eq_ofNat_of_zero_le (hw b (by simp)).1
    obtain ⟨c', rfl⟩ := Int.eq_ofNat_of_zero_le (hw c (by simp)).1
    obtain ⟨d', rfl⟩ := Int.eq_ofNat_of_zero_le (hw d (by simp)).1
    obtain ⟨e', rfl⟩ := Int.eq_ofNat_of_zero_le (hw e (by simp)).1
    obtain ⟨f', rfl⟩ := Int.eq_ofNat_of_zero_le (hw f (by simp)).1
    have ha := (hw _ (by simp : ((a' : ℤ)) ∈ [(a' : ℤ), b', c', d', e', f'])).2
    have hb := (hw _ (by simp : ((b' : ℤ)) ∈ [(a' : ℤ), b', c', d', e', f'])).2
    have hc := (hw _ (by simp : ((c' : ℤ)) ∈ [(a' : ℤ), b', c', d', e', f'])).2
    have hd := (hw _ (by simp : ((d' : ℤ)) ∈ [(a' : ℤ), b', c', d', e', f'])).2
    have he := (hw _ (by simp : ((e' : ℤ)) ∈ [(a' : ℤ), b', c', d', e', f'])).2
    have hf := (hw _ (by simp : ((f' : ℤ)) ∈ [(a' : ℤ), b', c', d', e', f'])).2
    have hE : enc [(a' : ℤ), b', c', d', e', f'] =
        a' + 3 * (b' + 3 * (c' + 3 * (d' + 3 * (e' + 3 * (f' + 3 * 0))))) := rfl
    have ha' : a' < 3 := by omega
    have hb' : b' < 3 := by omega
    have hc' : c' < 3 := by omega
    have hd' : d' < 3 := by omega
    have he' : e' < 3 := by omega
    have hf' : f' < 3 := by omega
    change [dg _ 1, dg _ 3, dg _ 9, dg _ 27, dg _ 81, dg _ 243] = _
    rw [hE]
    simp only [dg, natDiv_eqC, natMod_eqC, List.cons.injEq, and_true, Int.ofNat_eq_coe,
      Nat.cast_inj]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem enc_lt : ∀ w : Vec, (∀ x ∈ w, 0 ≤ x ∧ x < 3) → enc w < 3 ^ w.length
  | [], _ => by decide
  | x :: xs, hw => by
    have hx := hw x (by simp)
    have ih := enc_lt xs (fun y hy => hw y (List.mem_cons_of_mem _ hy))
    have hx' : Int.toNat x < 3 := by omega
    change Int.toNat x + 3 * enc xs < 3 ^ (xs.length + 1)
    rw [pow_succ]
    omega

theorem genAct_dec_spec (j p : Nat) :
    (genAct j (dec p)).length = 6 ∧ ∀ x ∈ genAct j (dec p), 0 ≤ x ∧ x < 3 := by
  unfold genAct
  split_ifs
  · refine ⟨by simp, fun x hx => ?_⟩
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
    exact ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
  · refine ⟨rfl, fun x hx => ?_⟩
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    exact ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩

theorem vecZ_dec_enc_rep (k : Fin 5) : vecZ (dec (enc (reps.getD k []))) = repZ k := by
  have h : dec (enc (reps.getD k [])) = reps.getD k [] := by
    fin_cases k <;> decide
  rw [h]
  rfl

theorem cartan_eq_sixC (i k : Fin Tag.E6.rank) :
    Tag.E6.cartan i k = (cartan.getD i.val []).getD k.val 0 := by
  fin_cases i <;> fin_cases k <;> decide +kernel

theorem option_map_getD_neg_modC (o : Option Int) :
    (o.map (fun x => -x % 3)).getD 0 = (-(o.getD 0)) % 3 := by
  cases o <;> simp

theorem zmod3_intCastC (a : Int) : ((a % 3 : ℤ) : ZMod 3) = (a : ZMod 3) :=
  ZMod.intCast_mod a 3

theorem getD?_eq_getDC {α : Type} (l : List α) (n : Nat) (d : α) :
    (l[n]?).getD d = l.getD n d :=
  rfl

theorem vecZ_genActC (j : Fin 7) (x : Vec) :
    vecZ (genAct j.val x) = genActZ j (vecZ x) := by
  funext k
  fin_cases j <;> fin_cases k <;>
    simp [vecZ, genAct, genActZ, option_map_getD_neg_modC] <;>
    rw [zmod3_intCastC] <;>
    push_cast <;>
    (try rw [cartan_eq_sixC]) <;>
    simp only [getD?_eq_getDC, Fin.val_zero] <;>
    rfl

@[expose] def Reached (c : Nat) : Prop :=
  ∃ k : Fin 5, Relation.ReflTransGen (fun a b => ∃ j : Fin 7, b = genActZ j a) (repZ k)
    (vecZ (dec c))

@[expose] def CoverInv (seen : Nat) : Prop :=
  seen.testBit 0 = true ∨ ∀ c, seen.testBit c = true → Reached c

@[expose] noncomputable def coverStepF (c j p seen : Nat) : Nat :=
  nIf(bIf(Nat.ble (nat_lit 7) j,
      Nat.beq c (enc (reps.getD (Nat.sub j (nat_lit 7)) [])),
      bAnd(bitN seen p, Nat.beq c (enc (genAct j (dec p))))),
    Nat.lor seen (Nat.shiftLeft (nat_lit 1) c),
    Nat.lor seen (nat_lit 1))

theorem coverStep_eqF (e seen : Nat) :
    coverStep e seen = coverStepF (Nat.land e 1023) (Nat.shiftRight e 20)
      fld(e, 10, 1023) seen := by
  unfold coverStep
  rw [strictN_eqC, strictN_eqC, strictB_eqC]
  rfl

theorem coverInv_lor {seen : Nat} (h : seen.testBit 0 = true) (x : Nat) :
    CoverInv (Nat.lor seen x) := by
  left
  change (seen ||| x).testBit 0 = true
  rw [Nat.testBit_or, h]
  rfl

theorem coverInv_stepF (c j p seen : Nat) (h : CoverInv seen) : CoverInv (coverStepF c j p seen) := by
  rcases h with h0 | hall
  · unfold coverStepF
    rw [nIf_eqC]
    split_ifs
    · exact coverInv_lor h0 _
    · exact coverInv_lor h0 _
  have hadd : Reached c → CoverInv (Nat.lor seen (Nat.shiftLeft 1 c)) := fun hc => by
    right
    intro i hi
    rw [testBit_lor_one_shiftLeft, Bool.or_eq_true] at hi
    rcases hi with hi | hi
    · exact hall i hi
    · rw [decide_eq_true_eq] at hi
      rw [← hi]
      exact hc
  unfold coverStepF
  rw [nIf_eqC]
  split_ifs with hcond
  · rw [bIf_eqC] at hcond
    split_ifs at hcond with hj
    · have hc := Nat.eq_of_beq_eq_true hcond
      by_cases hk : j - 7 < 5
      · refine hadd ⟨⟨j - 7, hk⟩, ?_⟩
        have e : vecZ (dec (enc (reps.getD (j - 7) []))) = repZ ⟨j - 7, hk⟩ :=
          vecZ_dec_enc_rep ⟨j - 7, hk⟩
        change c = enc (reps.getD (j - 7) []) at hc
        have hz : vecZ (dec c) = repZ ⟨j - 7, hk⟩ := by rw [hc, e]
        exact hz ▸ Relation.ReflTransGen.refl
      · have hnil : reps.getD (j - 7) [] = [] :=
          List.getD_eq_default _ _ (by change 5 ≤ j - 7; omega)
        change c = enc (reps.getD (j - 7) []) at hc
        rw [hnil] at hc
        change c = 0 at hc
        subst hc
        left
        rw [testBit_lor_one_shiftLeft]
        simp
    · obtain ⟨hp, hc⟩ := bAnd_trueC hcond
      have hc := Nat.eq_of_beq_eq_true hc
      rw [bitN_eqC] at hp
      obtain ⟨k, hk⟩ := hall p hp
      have hj7 : j < 7 := by
        by_contra hc7
        exact hj (Nat.ble_eq_true_of_le (Nat.le_of_not_lt hc7))
      refine hadd ⟨k, Relation.ReflTransGen.tail hk ⟨⟨j, hj7⟩, ?_⟩⟩
      obtain ⟨hl, hw⟩ := genAct_dec_spec j p
      rw [hc, dec_enc hl hw]
      exact vecZ_genActC ⟨j, hj7⟩ (dec p)
  · left
    change (seen ||| 1).testBit 0 = true
    rw [Nat.testBit_or]
    simp

theorem coverInv_run : ∀ (CT : List Nat) (seen : Nat), CoverInv seen → CoverInv (coverRun CT seen)
  | [], _, h => h
  | e :: es, seen, h => by
    change CoverInv (strictN (coverStep e seen) (coverRun es))
    rw [strictN_eqC, coverStep_eqF]
    exact coverInv_run es _ (coverInv_stepF _ _ _ _ h)

theorem beq_full_eq {x n : Nat}
    (h : Nat.beq x (Nat.sub (Nat.shiftLeft 1 (n + 1)) 2) = true) : x = 2 ^ 1 * (2 ^ n - 1) + 0 := by
  have e : x = 1 <<< (n + 1) - 2 := Nat.eq_of_beq_eq_true h
  have hpos : 0 < (2 : Nat) ^ n := by positivity
  rw [e, pow_one, Nat.add_zero, Nat.one_shiftLeft, pow_succ]
  omega

theorem e6_cover_of_coverK {CT : List Nat} (hCT : coverK CT = true)
    (v : Fin Tag.E6.rank → ZMod 3) (hv : v ≠ 0) :
    ∃ k : Fin 5, Relation.ReflTransGen (fun a b => ∃ j : Fin 7, b = genActZ j a) (repZ k) v := by
  have hrun : coverRun CT 0 = 2 ^ 1 * (2 ^ 728 - 1) + 0 := beq_full_eq hCT
  have hinv := coverInv_run CT 0 (Or.inr (fun c hc => by simp at hc))
  rw [hrun] at hinv
  have hbit : ∀ i, (2 ^ 1 * (2 ^ 728 - 1) + 0).testBit i = decide (1 ≤ i ∧ i < 729) := by
    intro i
    rw [Nat.testBit_two_pow_mul_add _ (by norm_num), Nat.testBit_two_pow_sub_one]
    by_cases h : i < 1
    · rw [if_pos h, Nat.zero_testBit, eq_comm, decide_eq_false_iff_not]
      omega
    · rw [if_neg h, decide_eq_decide]
      constructor
      · intro h'
        omega
      · intro h'
        omega
  rcases hinv with h0 | hall
  · rw [hbit] at h0
    simp at h0
  let w : Vec := List.ofFn fun i => ((v i).val : ℤ)
  have hl : w.length = 6 := List.length_ofFn
  have hw : ∀ x ∈ w, 0 ≤ x ∧ x < 3 := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact ⟨Int.natCast_nonneg _, by exact_mod_cast ZMod.val_lt (v i)⟩
  have hvw : vecZ w = v := by
    funext i
    simp only [vecZ, w]
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact i.isLt)]
    simp only [List.getElem_ofFn]
    push_cast
    exact ZMod.natCast_zmod_val (v i)
  have hdec := dec_enc hl hw
  have hlt := enc_lt w hw
  rw [hl] at hlt
  have hne : enc w ≠ 0 := by
    intro h0
    apply hv
    rw [← hvw, ← hdec, h0]
    funext i
    fin_cases i <;> rfl
  obtain ⟨k, hk⟩ := hall (enc w) (by
    rw [hbit]
    simp only [decide_eq_true_eq]
    omega)
  rw [hdec, hvw] at hk
  exact ⟨k, hk⟩

end CFSG.KC.E6TT

end
