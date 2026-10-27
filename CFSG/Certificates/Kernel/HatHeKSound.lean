module

public import Certificates.Data.Kernel.HatHeK
public import CFSG.Certificates.Kernel.SporSch.PairJ3CntSound
import CFSG.Certificates.Kernel.Misc.PermClosOrbit
import CFSG.Certificates.Kernel.Misc.PermClosProof
import CFSG.Certificates.Kernel.LocalQTPermSound
public import Mathlib.Data.Nat.Bitwise

namespace CFSG.KC.HatHe

open CFSG.Sporadic.Schreier CFSG.KS.SporSch Equiv
open CFSG.KC.Misc.Clos (treeAt closedAt sortAt sortAt_spec orbit_card_proved)

noncomputable def enc5 (x : Fin 5 → Fin 8330) : ℕ :=
  (x 0 : ℕ) + 16384 * x 1 + 268435456 * x 2 + 4398046511104 * x 3 + 72057594037927936 * x 4

def bas : Fin 5 → Fin 8330 := fun i => ⟨i, lt_trans i.2 (by norm_num)⟩

theorem enc5_bas : enc5 bas = B0 := rfl

theorem fld_eq (t o : ℕ) : fld(t, o, 16383) = t / 2 ^ o % 16384 := by
  change (t >>> o) &&& (2 ^ 14 - 1) = t / 2 ^ o % 2 ^ 14
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem land_eq (t : ℕ) : Nat.land t 16383 = t % 16384 := by
  change t &&& (2 ^ 14 - 1) = t % 2 ^ 14
  exact Nat.and_two_pow_sub_one_eq_mod t 14

theorem shr_eq (t : ℕ) : Nat.shiftRight t 56 = t / 72057594037927936 := by
  change t >>> 56 = t / 2 ^ 56
  exact Nat.shiftRight_eq_div_pow t 56

theorem enc5_lane (x : Fin 5 → Fin 8330) :
    enc5 x % 16384 = x 0 ∧ enc5 x / 16384 % 16384 = x 1 ∧ enc5 x / 268435456 % 16384 = x 2 ∧
      enc5 x / 4398046511104 % 16384 = x 3 ∧ enc5 x / 72057594037927936 = x 4 := by
  have h0 := (x 0).2
  have h1 := (x 1).2
  have h2 := (x 2).2
  have h3 := (x 3).2
  have h4 := (x 4).2
  unfold enc5
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem enc5_inj : Function.Injective enc5 := by
  intro x y h
  have hx := enc5_lane x
  have hy := enc5_lane y
  rw [h] at hx
  funext i
  apply Fin.ext
  fin_cases i
  · exact hx.1.symm.trans hy.1
  · exact hx.2.1.symm.trans hy.2.1
  · exact hx.2.2.1.symm.trans hy.2.2.1
  · exact hx.2.2.2.1.symm.trans hy.2.2.2.1
  · exact hx.2.2.2.2.symm.trans hy.2.2.2.2

theorem enc5_fld (x : Fin 5 → Fin 8330) {b : ℕ} (hb : b < 5) :
    fld(enc5 x, Nat.mul 14 b, 16383) = x ⟨b, hb⟩ := by
  rw [fld_eq]
  obtain ⟨l0, l1, l2, l3, l4⟩ := enc5_lane x
  have h4 := (x 4).2
  change enc5 x / 2 ^ (14 * b) % 16384 = _
  interval_cases b
  · rw [Nat.mul_zero, Nat.pow_zero, Nat.div_one]
    exact l0
  · exact l1
  · exact l2
  · exact l3
  · have e : (2 : ℕ) ^ (14 * 4) = 72057594037927936 := by norm_num
    rw [e, l4]
    exact Nat.mod_eq_of_lt (by omega)

theorem en_or {x y k : ℕ} (hx : x < 2 ^ k) (hy : 2 ^ k ∣ y) : x ||| y = x + y := by
  obtain ⟨q, rfl⟩ := hy
  rw [Nat.lor_comm, Nat.mul_comm, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hx,
    Nat.add_comm]

theorem pack5 {a0 a1 a2 a3 a4 : ℕ} (h0 : a0 < 16384) (h1 : a1 < 16384) (h2 : a2 < 16384)
    (h3 : a3 < 16384) :
    Nat.lor a0 (Nat.lor (Nat.shiftLeft a1 14) (Nat.lor (Nat.shiftLeft a2 28)
      (Nat.lor (Nat.shiftLeft a3 42) (Nat.shiftLeft a4 56)))) =
      a0 + 16384 * a1 + 268435456 * a2 + 4398046511104 * a3 + 72057594037927936 * a4 := by
  change a0 ||| (a1 <<< 14 ||| (a2 <<< 28 ||| (a3 <<< 42 ||| a4 <<< 56))) = _
  simp only [Nat.shiftLeft_eq, Nat.reducePow]
  have e3 : a3 * 4398046511104 ||| a4 * 72057594037927936 =
      a3 * 4398046511104 + a4 * 72057594037927936 :=
    en_or (k := 56) (by simp only [Nat.reducePow]; omega) (by simp only [Nat.reducePow]; omega)
  rw [e3]
  have e2 : a2 * 268435456 ||| (a3 * 4398046511104 + a4 * 72057594037927936) =
      a2 * 268435456 + (a3 * 4398046511104 + a4 * 72057594037927936) :=
    en_or (k := 42) (by simp only [Nat.reducePow]; omega) (by simp only [Nat.reducePow]; omega)
  rw [e2]
  have e1 : a1 * 16384 ||| (a2 * 268435456 + (a3 * 4398046511104 + a4 * 72057594037927936)) =
      a1 * 16384 + (a2 * 268435456 + (a3 * 4398046511104 + a4 * 72057594037927936)) :=
    en_or (k := 28) (by simp only [Nat.reducePow]; omega) (by simp only [Nat.reducePow]; omega)
  rw [e1]
  have e0 : a0 ||| (a1 * 16384 + (a2 * 268435456 + (a3 * 4398046511104 +
      a4 * 72057594037927936))) = a0 + (a1 * 16384 + (a2 * 268435456 + (a3 * 4398046511104 +
      a4 * 72057594037927936))) :=
    en_or (k := 14) (by simp only [Nat.reducePow]; omega) (by simp only [Nat.reducePow]; omega)
  rw [e0]
  ring

theorem lt16384 (y : Fin 8330) : (y : ℕ) < 16384 := lt_trans y.2 (by norm_num)

theorem actT_enc {P : ℕ} {σ : Perm (Fin 8330)} (h : RepF 8330 (ap P) σ) (x : Fin 5 → Fin 8330) :
    actT P (enc5 x) = enc5 (σ • x) := by
  obtain ⟨l0, l1, l2, l3, l4⟩ := enc5_lane x
  have e0 : Nat.land (enc5 x) 16383 = x 0 := by rw [land_eq]; exact l0
  have e1 : fld(enc5 x, 14, 16383) = x 1 := by rw [fld_eq]; exact l1
  have e2 : fld(enc5 x, 28, 16383) = x 2 := by rw [fld_eq]; exact l2
  have e3 : fld(enc5 x, 42, 16383) = x 3 := by rw [fld_eq]; exact l3
  have e4 : Nat.shiftRight (enc5 x) 56 = x 4 := by rw [shr_eq]; exact l4
  unfold actT
  rw [e0, e1, e2, e3, e4, h _ (x 0).2, h _ (x 1).2, h _ (x 2).2, h _ (x 3).2, h _ (x 4).2,
    pack5 (lt16384 _) (lt16384 _) (lt16384 _) (lt16384 _)]
  rfl

theorem actW_enc {G : ℕ → ℕ} {c : ℕ → Perm (Fin 8330)}
    (hG : ∀ j < 9, RepF 8330 (ap (G j)) (c j)) :
    ∀ w : List ℕ, (∀ l ∈ w, l < 9) → ∀ x, actW G w (enc5 x) = enc5 ((w.map c).prod • x)
  | [], _, x => by
    change enc5 x = enc5 (([].map c).prod • x)
    rw [List.map_nil, List.prod_nil, one_smul]
  | l :: w, hw, x => by
    change actT (G l) (actW G w (enc5 x)) = _
    rw [actW_enc hG w (fun l' h' => hw l' (List.mem_cons_of_mem _ h')) x,
      actT_enc (hG l (hw l List.mem_cons_self)), List.map_cons, List.prod_cons, mul_smul]

theorem apW_rep {G : ℕ → ℕ} {c : ℕ → Perm (Fin 8330)}
    (hG : ∀ j < 9, RepF 8330 (ap (G j)) (c j)) :
    ∀ w : List ℕ, (∀ l ∈ w, l < 9) → RepF 8330 (apW G w) (w.map c).prod
  | [], _ => fun _ _ => rfl
  | l :: w, hw => by
    have h := RepF.comp (hG l (hw l List.mem_cons_self))
      (apW_rep hG w fun l' h' => hw l' (List.mem_cons_of_mem _ h'))
    rw [List.map_cons, List.prod_cons]
    exact h

noncomputable def tEl (gs : ℕ → Perm (Fin 8330)) (PA : ℕ → ℕ) : ℕ → Perm (Fin 8330)
  | 0 => 1
  | k + 1 =>
    if h : par PA (k + 1) < k + 1 then gs (lab PA (k + 1)) * tEl gs PA (par PA (k + 1)) else 1
termination_by k => k

theorem tEl_zero (gs : ℕ → Perm (Fin 8330)) (PA : ℕ → ℕ) : tEl gs PA 0 = 1 := by
  rw [tEl]

theorem tEl_succ (gs : ℕ → Perm (Fin 8330)) (PA : ℕ → ℕ) (k : ℕ) :
    tEl gs PA (k + 1) =
      if h : par PA (k + 1) < k + 1 then gs (lab PA (k + 1)) * tEl gs PA (par PA (k + 1))
      else 1 := by
  rw [tEl]

theorem tree_spec {gs : ℕ → Perm (Fin 8330)} {M : ℕ → ℕ → ℕ} {nG N : ℕ} {E PA : ℕ → ℕ}
    (y0 : Fin 5 → Fin 8330) (hM : ∀ j < nG, ∀ x, M (enc5 x) j = enc5 (gs j • x))
    (ht : ∀ k < N, treeAt M (enc5 y0) (fun j => j) nG E PA k = true) :
    ∀ k < N, E k = enc5 (tEl gs PA k • y0) ∧ (0 < k → par PA k < k ∧ lab PA k < nG) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    cases k with
    | zero =>
      have h : Nat.beq (E 0) (enc5 y0) = true := ht 0 hk
      refine ⟨?_, fun h => absurd h (lt_irrefl 0)⟩
      rw [Nat.eq_of_beq_eq_true h, tEl_zero, one_smul]
    | succ k =>
      have h : CFSG.KC.LQT.P.letB (PA (k + 1)) (fun r =>
          CFSG.KC.LQT.P.letB (Nat.land r 16777215) fun p =>
          CFSG.KC.LQT.P.letB (Nat.shiftRight r 24) fun l => CFSG.KC.Ord.andB (Nat.blt p (k + 1))
            (CFSG.KC.Ord.andB (Nat.blt l nG) (Nat.beq (E (k + 1)) (M (E p) ((fun j => j) l))))) =
          true := ht (k + 1) hk
      rw [CFSG.KC.LQT.P.letB_eq, CFSG.KC.LQT.P.letB_eq, CFSG.KC.LQT.P.letB_eq] at h
      obtain ⟨hp, h⟩ := CFSG.KC.LQT.P.andB_iff.1 h
      obtain ⟨hl, h⟩ := CFSG.KC.LQT.P.andB_iff.1 h
      have hp' : par PA (k + 1) < k + 1 := Nat.blt_eq.mp hp
      have hl' : lab PA (k + 1) < nG := Nat.blt_eq.mp hl
      have hE : E (k + 1) = M (E (par PA (k + 1))) (lab PA (k + 1)) := Nat.eq_of_beq_eq_true h
      obtain ⟨he, -⟩ := ih _ hp' (by omega)
      refine ⟨?_, fun _ => ⟨hp', hl'⟩⟩
      rw [hE, he, hM _ hl', tEl_succ, dif_pos hp', mul_smul]

theorem tEl_mem {gs : ℕ → Perm (Fin 8330)} {PA : ℕ → ℕ} {nG N : ℕ}
    {S : Subgroup (Perm (Fin 8330))} (hg : ∀ j < nG, gs j ∈ S)
    (hpl : ∀ k < N, 0 < k → par PA k < k ∧ lab PA k < nG) : ∀ k < N, tEl gs PA k ∈ S := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    cases k with
    | zero => rw [tEl_zero]; exact S.one_mem
    | succ k =>
      obtain ⟨hp, hl⟩ := hpl _ hk (Nat.succ_pos k)
      rw [tEl_succ, dif_pos hp]
      exact S.mul_mem (hg _ hl) (ih _ hp (by omega))

theorem trV_rep {G : ℕ → ℕ} {c : ℕ → Perm (Fin 8330)}
    (hG : ∀ j < 9, RepF 8330 (ap (G j)) (c j)) {W : ℕ → List ℕ} {nG N : ℕ}
    (hW : ∀ j < nG, ∀ l ∈ W j, l < 9) {PA : ℕ → ℕ}
    (hpl : ∀ k < N, 0 < k → par PA k < k ∧ lab PA k < nG) :
    ∀ f k, k < N → rootK PA f k = true →
      RepF 8330 (trV G W PA f k) (tEl (fun j => ((W j).map c).prod) PA k)
  | 0, k, _, h => by
    have : k = 0 := Nat.eq_of_beq_eq_true h
    subst this
    rw [tEl_zero]
    exact fun _ _ => rfl
  | f + 1, k, hk, h => by
    cases k with
    | zero =>
      rw [tEl_zero]
      exact fun _ _ => rfl
    | succ k =>
      have h' : rootK PA f (par PA (k + 1)) = true := h
      obtain ⟨hp, hl⟩ := hpl _ hk (Nat.succ_pos k)
      have ih := trV_rep hG hW hpl f _ (by omega) h'
      rw [tEl_succ, dif_pos hp]
      exact (apW_rep hG _ (hW _ hl)).comp ih

theorem memRow_bit {k : ℕ} : ∀ (c : List ℕ) (acc : ℕ),
    (List.rec (motive := fun _ => ℕ) acc (fun x _ a => Nat.lor (Nat.shiftLeft 1 x) a) c).testBit k
      = true → k ∈ c ∨ acc.testBit k = true
  | [], _, h => Or.inr h
  | x :: r, acc, h => by
    have h' : ((1 <<< x) ||| (List.rec (motive := fun _ => ℕ) acc
        (fun x _ a => Nat.lor (Nat.shiftLeft 1 x) a) r)).testBit k = true := h
    rw [Nat.testBit_or, Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow, Bool.or_eq_true,
      decide_eq_true_iff] at h'
    rcases h' with rfl | h'
    · exact Or.inl List.mem_cons_self
    · rcases memRow_bit r acc h' with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr h

theorem memMask_bit {k : ℕ} : ∀ CL : List (List ℕ), (memMask CL).testBit k = true →
    ∃ cl ∈ CL, k ∈ cl
  | [], h => by
    have h' : (0 : ℕ).testBit k = true := h
    simp at h'
  | c :: CL, h => by
    rcases memRow_bit c (memMask CL) h with h | h
    · exact ⟨c, List.mem_cons_self, h⟩
    · obtain ⟨cl, hcl, hk⟩ := memMask_bit CL h
      exact ⟨cl, List.mem_cons_of_mem _ hcl, hk⟩

theorem bit_of {m k : ℕ} (h : Nat.beq (Nat.land (Nat.shiftRight m k) 1) 1 = true) :
    m.testBit k = true := by
  have h1 : (m >>> k) &&& 1 = 1 := Nat.eq_of_beq_eq_true h
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow] at h1
  simp [Nat.testBit_eq_decide_div_mod_eq, h1]

theorem ncRec {A B : ℕ → ℕ} : ∀ m, Nat.rec (motive := fun _ => Bool) false
    (fun b ih => bIf(Nat.beq (A b) (B b), ih, true)) m = true → ∃ b < m, A b ≠ B b
  | 0, h => (Bool.false_ne_true h).elim
  | m + 1, h => by
    change Bool.rec (motive := fun _ => Bool) true (Nat.rec (motive := fun _ => Bool) false
      (fun b ih => bIf(Nat.beq (A b) (B b), ih, true)) m) (Nat.beq (A m) (B m)) = true at h
    cases hb : Nat.beq (A m) (B m)
    · exact ⟨m, by omega, Nat.ne_of_beq_eq_false hb⟩
    · rw [hb] at h
      obtain ⟨b, hb', hne⟩ := ncRec m h
      exact ⟨b, by omega, hne⟩

theorem allL_rec {Q : List ℕ → Bool} : ∀ CL : List (List ℕ),
    List.rec (motive := fun _ => Bool) true (fun c _ ih => bAnd(Q c, ih)) CL = true →
      ∀ c ∈ CL, Q c = true
  | [], _, c, hc => by simp at hc
  | c :: CL, h, c', hc' => by
    obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    rcases List.mem_cons.1 hc' with rfl | hc'
    · exact h1
    · exact allL_rec CL h2 c' hc'

theorem inner_rec {R : ℕ → ℕ → Bool} {x : ℕ} : ∀ r : List ℕ,
    List.rec (motive := fun _ => Bool) true (fun y _ ih2 => bAnd(R x y, ih2)) r = true →
      ∀ y ∈ r, R x y = true
  | [], _, y, hy => by simp at hy
  | y :: r, h, y', hy' => by
    obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    rcases List.mem_cons.1 hy' with rfl | hy'
    · exact h1
    · exact inner_rec r h2 y' hy'

theorem cls_pair {R : ℕ → ℕ → Bool} : ∀ c : List ℕ,
    List.rec (motive := fun _ => Bool) true (fun x r ih => bAnd(List.rec (motive := fun _ => Bool)
      true (fun y _ ih2 => bAnd(R x y, ih2)) r, ih)) c = true →
      ∀ a ∈ c, ∀ b ∈ c, a ≠ b → R a b = true ∨ R b a = true
  | [], _, a, ha, _, _, _ => by simp at ha
  | x :: r, h, a, ha, b, hb, hab => by
    obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    have hin := inner_rec r h1
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd rfl hab
      · exact Or.inl (hin b hb')
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact Or.inr (hin a ha')
      · exact cls_pair r h2 a ha' b hb' hab

theorem sort_lt {N : ℕ} {E SG : ℕ → ℕ} (hs : ∀ i < N, sortAt N E SG i = true) :
    ∀ i j, i < j → j < N → E (SG i) < E (SG j) := by
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | rfl
    · exact (ih h (by omega)).trans ((sortAt_spec (hs j (by omega))).2 hj)
    · exact (sortAt_spec (hs i (by omega))).2 hj

theorem sort_surj {N : ℕ} {E SG : ℕ → ℕ} (hs : ∀ i < N, sortAt N E SG i = true) :
    ∀ m < N, ∃ i < N, SG i = m := by
  let F : Fin N → Fin N := fun i => ⟨SG i, (sortAt_spec (hs i i.2)).1⟩
  have finj : Function.Injective F := by
    intro a b hab
    have e : SG a = SG b := congrArg Fin.val hab
    by_contra hne
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · exact absurd (congrArg E e) (sort_lt hs a b h b.2).ne
    · exact absurd (congrArg E e).symm (sort_lt hs b a h a.2).ne
  intro m hm
  obtain ⟨i, hi⟩ := (Finite.injective_iff_surjective.1 finj) ⟨m, hm⟩
  exact ⟨i, i.2, congrArg Fin.val hi⟩

theorem not_gap {N : ℕ} {E SG : ℕ → ℕ} (hs : ∀ i < N, sortAt N E SG i = true) {u b : ℕ}
    (hu : ∃ m < N, E m = u) (h1 : Nat.ble b N = true)
    (h2 : bIf(Nat.beq b 0, true, Nat.blt (E (SG (Nat.sub b 1))) u) = true)
    (h3 : bIf(Nat.beq b N, true, Nat.blt u (E (SG b))) = true) : False := by
  have hb : b ≤ N := Nat.le_of_ble_eq_true h1
  have h2' : b = 0 ∨ E (SG (b - 1)) < u := by
    cases e : Nat.beq b 0
    · rw [e] at h2
      exact Or.inr (Nat.blt_eq.mp h2)
    · exact Or.inl (Nat.eq_of_beq_eq_true e)
  have h3' : b = N ∨ u < E (SG b) := by
    cases e : Nat.beq b N
    · rw [e] at h3
      exact Or.inr (Nat.blt_eq.mp h3)
    · exact Or.inl (Nat.eq_of_beq_eq_true e)
  obtain ⟨m, hm, rfl⟩ := hu
  obtain ⟨i, hi, rfl⟩ := sort_surj hs m hm
  rcases Nat.lt_or_ge i b with hib | hib
  · rcases h2' with rfl | h2'
    · omega
    · rcases Nat.lt_or_ge i (b - 1) with h | h
      · have := sort_lt hs i (b - 1) h (by omega)
        omega
      · have e : i = b - 1 := by omega
        rw [e] at h2'
        omega
  · rcases h3' with rfl | h3'
    · omega
    · rcases Nat.lt_or_ge b i with h | h
      · have := sort_lt hs b i h hi
        omega
      · have e : i = b := by omega
        rw [e] at h3'
        omega

end CFSG.KC.HatHe

public section

namespace CFSG.KC.HatHe

open CFSG.Sporadic.Schreier CFSG.KS.SporSch Equiv
open CFSG.KC.Misc.Clos (treeAt closedAt sortAt orbit_card_proved)

theorem grpK_sound {K : Subgroup (Equiv.Perm (Fin 8330))} (hK : BaseFaithful K [0, 1, 2, 3, 4])
    {c : ℕ → Equiv.Perm (Fin 8330)} (hcK : ∀ j < 9, c j ∈ K) {G GI : ℕ → ℕ}
    (hG : ∀ j < 9, RepF 8330 (ap (G j)) (c j)) (hGI : ∀ j < 9, RepF 8330 (ap (GI j)) (c j)⁻¹)
    {W : ℕ → List ℕ} {nG N : ℕ} (hW : ∀ j < nG, ∀ l ∈ W j, l < 9) {dW dR : List ℕ}
    (hdW : ∀ l ∈ dW, l < 9) (hdR : dR = dW.reverse) {E Z PA SG CT MB : ℕ → ℕ}
    {CL : List (List ℕ)} {f : ℕ} (hN : 0 < N)
    (h : grpK G GI W nG N dW dR E Z PA SG CT MB CL f = true) :
    Nat.card (Subgroup.closure {g | g ∈ (List.range nG).map fun j => ((W j).map c).prod}) = N ∧
      ∀ A : Subgroup (Equiv.Perm (Fin 8330)),
        A ≤ Subgroup.closure {g | g ∈ (List.range nG).map fun j => ((W j).map c).prod} →
        A ≤ (Subgroup.closure {g | g ∈ (List.range nG).map fun j => ((W j).map c).prod}).map
          (MulAut.conj (dW.map c).prod).toMonoidHom →
        (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → Nat.card A ≤ CL.length := by
  classical
  set gs : ℕ → Perm (Fin 8330) := fun j => ((W j).map c).prod with hgs
  set d : Perm (Fin 8330) := (dW.map c).prod with hd
  set Hp := Subgroup.closure {g | g ∈ (List.range nG).map gs} with hHp
  unfold grpK at h
  obtain ⟨hZ0, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  rw [CFSG.KS.SporSch.strictB_val] at h
  obtain ⟨hrec, hclsCL⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  have hrec' := CFSG.KS.allN_spec hrec
  have hR : ∀ k < N, treeAt (fun t j => actW G (W j) t) B0 (fun j => j) nG E PA k = true ∧
      treeAt (fun t j => actW G (W j) t) (Z 0) (fun j => j) nG Z PA k = true ∧
      closedAt (fun t j => actW G (W j) t) (fun j => j) nG N E CT k = true ∧
      sortAt N E SG k = true ∧ rootK PA f k = true ∧
      memAt GI dR N E Z SG MB (memMask CL) k = true := by
    intro k hk
    have h := hrec' k hk
    unfold recK at h
    obtain ⟨h1, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    obtain ⟨h2, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    obtain ⟨h3, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    obtain ⟨h4, h⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    obtain ⟨h5, h6⟩ := (CFSG.KS.bAnd_iff _ _).1 h
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  have hs : ∀ i < N, sortAt N E SG i = true := fun i hi => (hR i hi).2.2.2.1
  have hgsK : ∀ j < nG, gs j ∈ K := fun j hj => list_prod_mem (fun x hx => by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
    exact hcK l (hW j hj l hl))
  have hgsP : ∀ j < nG, gs j ∈ Hp := fun j hj =>
    Subgroup.subset_closure (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)
  have hPK : Hp ≤ K := (Subgroup.closure_le K).2 (by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hg
    exact hgsK j (List.mem_range.1 hj))
  have hlen : ((List.range nG).map gs).length = nG := by simp
  have hgetD : ∀ j < nG, ((List.range nG).map gs).getD j 1 = gs j := by
    intro j hj
    simp [List.getD_eq_getElem?_getD, hj]
  have hM : ∀ j < nG, ∀ x, actW G (W j) (enc5 x) = enc5 (gs j • x) :=
    fun j hj x => actW_enc hG (W j) (hW j hj) x
  obtain ⟨-, hall, hcard⟩ := orbit_card_proved (H := Perm (Fin 8330)) enc5_inj
    ((List.range nG).map gs) (M := fun t j => actW G (W j) t) (G := fun j => j)
    (fun j hj x => by
      rw [hlen] at hj
      rw [hgetD j hj]
      exact (hM j hj x).symm) bas hN
    (by rw [hlen, enc5_bas]; exact fun k hk => (hR k hk).1) hs
    (by rw [hlen]; exact fun k hk => (hR k hk).2.2.1)
  have hfaith : ∀ g ∈ K, ∀ g' ∈ K, g • bas = g' • bas → g = g' := by
    intro g hg g' hg' e
    have h1 := hK (g'⁻¹ * g) (K.mul_mem (K.inv_mem hg') hg) (fun x hx => by
      have hx5 : (x : ℕ) < 5 := by
        simp at hx
        omega
      have e2 := congrFun e ⟨x, hx5⟩
      rw [Perm.mul_apply, Perm.inv_eq_iff_eq]
      exact e2)
    exact (inv_mul_eq_one.1 h1).symm
  have hcardP : Nat.card Hp = N := by
    rw [← hcard]
    refine Nat.card_eq_of_bijective (fun g : Hp => (⟨(g : Perm (Fin 8330)) • bas, g, g.2, rfl⟩ :
      {y // ∃ g ∈ Hp, g • bas = y})) ⟨?_, ?_⟩
    · intro a b hab
      exact Subtype.ext (hfaith _ (hPK a.2) _ (hPK b.2) (congrArg Subtype.val hab))
    · rintro ⟨y, g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  refine ⟨hcardP, ?_⟩
  intro A hAP hAd hcomm
  have hM' : ∀ j < nG, ∀ x, (fun t j => actW G (W j) t) (enc5 x) j = enc5 (gs j • x) := hM
  have hEt := tree_spec (gs := gs) bas hM' (by rw [enc5_bas]; exact fun k hk => (hR k hk).1)
  have hZ0' : Z 0 = enc5 (d • bas) := by
    rw [Nat.eq_of_beq_eq_true hZ0, ← enc5_bas, actW_enc hG dW hdW bas]
  have hZt := tree_spec (gs := gs) (d • bas) hM'
    (by rw [← hZ0']; exact fun k hk => (hR k hk).2.1)
  have hpl : ∀ k < N, 0 < k → par PA k < k ∧ lab PA k < nG := fun k hk => (hEt k hk).2
  have htP : ∀ k < N, tEl gs PA k ∈ Hp := tEl_mem hgsP hpl
  have hTr : ∀ k < N, RepF 8330 (trV G W PA f k) (tEl gs PA k) :=
    fun k hk => trV_rep hG hW hpl f k hk (hR k hk).2.2.2.2.1
  have hrec_a : ∀ a ∈ A, ∃ k < N, a = tEl gs PA k := by
    intro a ha
    obtain ⟨k, hk, hek⟩ := hall a (hAP ha)
    refine ⟨k, hk, hfaith _ (hPK (hAP ha)) _ (hPK (htP k hk)) (enc5_inj ?_)⟩
    rw [hek, (hEt k hk).1]
  choose! ka hkaN hka using hrec_a
  have hdR' : ∀ l ∈ dR, l < 9 := by
    rw [hdR]
    intro l hl
    exact hdW l (List.mem_reverse.1 hl)
  have hXd : (dR.map fun j => (c j)⁻¹).prod = d⁻¹ := by
    rw [hdR, hd, List.prod_inv_reverse, List.map_map, List.map_reverse]
    rfl
  have hcl : ∀ a ∈ A, ∃ i : Fin CL.length, ka a ∈ CL[(i : ℕ)] := by
    intro a ha
    have hk := hkaN a ha
    obtain ⟨p, hp, hpa⟩ := Subgroup.mem_map.1 (hAd ha)
    have hpa' : d * p * d⁻¹ = a := by simpa using hpa
    have hpa'' : d⁻¹ * a * d = p := by
      rw [← hpa']
      group
    have hu : ∃ m < N, E m = actW GI dR (Z (ka a)) := by
      rw [(hZt _ hk).1, actW_enc hGI dR hdR', ← hka a ha, ← mul_smul, ← mul_smul, hXd, hpa'']
      obtain ⟨m, hm, hme⟩ := hall p hp
      exact ⟨m, hm, hme.symm⟩
    have hm := (hR (ka a) hk).2.2.2.2.2
    unfold memAt at hm
    simp only [CFSG.KS.SporSch.strictB_val] at hm
    cases hodd : Nat.beq (Nat.land (MB (ka a)) 1) 1
    · rw [hodd] at hm
      obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 hm
      obtain ⟨h2, h3⟩ := (CFSG.KS.bAnd_iff _ _).1 h2
      exact (not_gap hs hu h1 h2 h3).elim
    · rw [hodd] at hm
      obtain ⟨-, hm⟩ := (CFSG.KS.bAnd_iff _ _).1 hm
      obtain ⟨-, hm⟩ := (CFSG.KS.bAnd_iff _ _).1 hm
      obtain ⟨cl, hcl, hkcl⟩ := memMask_bit CL (bit_of hm)
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hcl
      exact ⟨⟨i, hi⟩, hkcl⟩
  choose cls hcls using hcl
  have hclsK := allL_rec (Q := clsK G W PA E f) CL hclsCL
  have hnc : ∀ x < N, ∀ y < N, ncK G W PA E f x y = true →
      tEl gs PA x * tEl gs PA y ≠ tEl gs PA y * tEl gs PA x := by
    intro x hx y hy hxy e
    obtain ⟨b, hb, hne⟩ := ncRec (A := fun b => trV G W PA f x (fld(E y, Nat.mul 14 b, 16383)))
      (B := fun b => trV G W PA f y (fld(E x, Nat.mul 14 b, 16383))) 5 hxy
    apply hne
    beta_reduce
    rw [(hEt y hy).1, (hEt x hx).1, enc5_fld _ hb, enc5_fld _ hb, hTr x hx _ (Fin.isLt _),
      hTr y hy _ (Fin.isLt _)]
    have e2 := congrArg (fun σ : Perm (Fin 8330) => (σ (bas ⟨b, hb⟩) : ℕ)) e
    simp only [Perm.mul_apply] at e2
    exact e2
  have hinj : Function.Injective fun a : A => cls a a.2 := by
    intro a b hab
    by_contra hne
    have hne' : (a : Perm (Fin 8330)) ≠ b := fun h => hne (Subtype.ext h)
    have hk : ka a ≠ ka b := fun h => hne' (by rw [hka a a.2, hka b b.2, h])
    have ha := hcls a a.2
    have hb := hcls b b.2
    have hab' : cls a a.2 = cls b b.2 := hab
    rw [hab'] at ha
    have hc := hclsK _ (List.getElem_mem (cls b b.2).2)
    have hab2 := hcomm a a.2 b b.2
    rcases cls_pair (R := ncK G W PA E f) _ hc _ ha _ hb hk with h | h
    · refine hnc _ (hkaN a a.2) _ (hkaN b b.2) h ?_
      rw [← hka a a.2, ← hka b b.2]
      exact hab2
    · refine hnc _ (hkaN b b.2) _ (hkaN a a.2) h ?_
      rw [← hka a a.2, ← hka b b.2]
      exact hab2.symm
  calc Nat.card A ≤ Nat.card (Fin CL.length) := Nat.card_le_card_of_injective _ hinj
    _ = CL.length := Nat.card_fin _

end CFSG.KC.HatHe

end
