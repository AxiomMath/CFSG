module

public import Certificates.Data.Kernel.LocalQT.Syl
public import CFSG.Certificates.Kernel.LocalQTWordSound
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1MathieuGen

import CFSG.Certificates.Kernel.LocalQTTab2KSound

public section

namespace CFSG.KC.LQT.Syl.Pf

open Equiv CFSG.QuasithinUnique.Setup.X1 CFSG.KC.LQT.W CFSG.KC.LQT.Syl

section Codes

variable {n : ℕ} (H : Subgroup (Perm (Fin n)))

@[expose] noncomputable def cH (x : H) : ℕ := P.code (x : Perm (Fin n))

variable {H}

theorem cH_inj (hn : n ≤ 32) : Function.Injective (cH H) :=
  fun _ _ h => Subtype.ext (P.code_inj hn h)

theorem cH_mul (hn : n ≤ 32) (x y : H) : P.mul n (cH H x) (cH H y) = cH H (x * y) :=
  P.code_mul hn _ _

theorem cH_one : P.one n = cH H 1 := P.code_one

theorem cH_inv (hn : n ≤ 32) (x : H) : P.inv n (cH H x) = cH H x⁻¹ := P.code_inv hn _

theorem cH_pow (hn : n ≤ 32) (x : H) (k : ℕ) : P.pow n (cH H x) k = cH H (x ^ k) :=
  P.code_pow hn _ k

theorem cH_conj (hn : n ≤ 32) (c t : H) :
    P.conj n (cH H c) (cH H t) = cH H (c * t * c⁻¹) := P.conj_code hn _ _

theorem beq_cH (hn : n ≤ 32) (x y : H) : Nat.beq (cH H x) (cH H y) = true ↔ x = y := by
  rw [P.beq_iff]
  exact (cH_inj hn).eq_iff

theorem comm_cH (hn : n ≤ 32) (x y : H) :
    P.comm n (cH H x) (cH H y) = true ↔ x * y = y * x := by
  rw [P.comm, cH_mul hn, cH_mul hn, beq_cH hn]

theorem mem_map_cH (hn : n ≤ 32) (x : H) (L : List H) : cH H x ∈ L.map (cH H) ↔ x ∈ L :=
  List.mem_map_of_injective (cH_inj hn)

private theorem getD_val (L : List H) (i : ℕ) :
    (L.map Subtype.val).getD i 1 = ((L.getD i 1 : H) : Perm (Fin n)) :=
  List.getD_map (l := L) (n := i) (d := (1 : H)) Subtype.val

private theorem evalG_val (L : List H) (w : List ℤ) :
    ((evalG L w : H) : Perm (Fin n)) = evalG (L.map Subtype.val) w := by
  induction w with
  | nil => rfl
  | cons z w ih =>
    by_cases h : 0 < z
    · simp only [evalG, h, ↓reduceIte, Subgroup.coe_mul, ih, getD_val]
    · simp only [evalG, h, ↓reduceIte, Subgroup.coe_mul, Subgroup.coe_inv, ih, getD_val]

private theorem hev (hn : n ≤ 32) (L : List (Perm (Fin n))) (w : List ℤ) :
    evalZK n (L.map codeP) w = P.code (evalG L w) := by
  have hc : (codeP : Perm (Fin n) → ℕ) = P.code := rfl
  induction w with
  | nil => exact P.code_one
  | cons z w ih =>
    change P.mul n (letZ n (L.map codeP) z) (evalZK n (L.map codeP) w) = _
    rw [ih, evalG]
    have hz : letZ n (L.map codeP) z = P.code (if 0 < z then L.getD (z.toNat - 1) 1
        else (L.getD ((-z).toNat - 1) 1)⁻¹) := by
      rcases z with (_ | k) | k
      · change P.inv n (genAt n (L.map codeP) 0) = _
        rw [genAt_map, P.code_inv hn]
        rfl
      · change genAt n (L.map codeP) k = _
        rw [genAt_map]
        congr 1
        have h0 : (0 : ℤ) < Int.ofNat (k + 1) := Int.ofNat_lt.2 (Nat.succ_pos k)
        rw [ite_eq_left h0]
        simp
      · change P.inv n (genAt n (L.map codeP) k) = _
        rw [genAt_map, P.code_inv hn]
        congr 1
    rw [hz, P.code_mul hn]

theorem evalZK_H (hn : n ≤ 32) (L : List H) (w : List ℤ) :
    evalZK n (L.map (cH H)) w = cH H (evalG L w) := by
  have h1 : L.map (cH H) = (L.map Subtype.val).map codeP := by
    simp only [List.map_map]
    rfl
  rw [h1, hev hn, ← evalG_val]
  rfl

private theorem genAt_H (L : List H) (i : ℕ) : genAt n (L.map (cH H)) i = cH H (L.getD i 1) := by
  have h1 : L.map (cH H) = (L.map Subtype.val).map codeP := by
    simp only [List.map_map]
    rfl
  rw [h1, genAt_map, getD_val]
  rfl

private theorem evalWK_H (hn : n ≤ 32) (L : List H) (w : List ℕ) :
    evalWK n (L.map (cH H)) w = cH H (prodWord L w) := by
  induction w with
  | nil => exact cH_one
  | cons i w ih =>
    change P.mul n (genAt n (L.map (cH H)) i) (evalWK n (L.map (cH H)) w) = _
    rw [genAt_H, ih, cH_mul hn]
    simp [prodWord]

end Codes

section Sylow

open CFSG.KC.Ord

variable {n : ℕ} {H : Subgroup (Perm (Fin n))} (gA gB : H) {cA cB : ℕ}

theorem zk_eq (hn : n ≤ 32) (hA : codeP (gA : Perm (Fin n)) = cA)
    (hB : codeP (gB : Perm (Fin n)) = cB) (w : List ℤ) :
    evalZK n [cA, cB] w = cH H (evalN H [gA, gB] w) := by
  have h : [cA, cB] = [gA, gB].map (cH H) := by
    subst hA hB
    rfl
  rw [h, evalZK_H hn, evalN, normH_eq]

theorem gens_eq (hn : n ≤ 32) (hA : codeP (gA : Perm (Fin n)) = cA)
    (hB : codeP (gB : Perm (Fin n)) = cB) (rgw : List (List ℤ)) :
    rgw.map (evalZK n [cA, cB]) = (sylowGens H gA gB rgw).map (cH H) := by
  rw [sylowGens, List.map_map]
  exact List.map_congr_left fun w _ => zk_eq gA gB hn hA hB w

theorem rlK_eq (hn : n ≤ 32) (hA : codeP (gA : Perm (Fin n)) = cA)
    (hB : codeP (gB : Perm (Fin n)) = cB) (rgw rwords : List (List ℤ)) :
    rlK n cA cB rgw rwords = (sylowList H gA gB rgw rwords).map (cH H) := by
  rw [rlK, gens_eq gA gB hn hA hB, sylowList, List.map_map]
  refine List.map_congr_left fun w _ => ?_
  rw [Function.comp_apply, evalZK_H hn, evalN, normH_eq]

theorem sylBase_le {a : ℕ} {RL : List ℕ} (h : sylBase n a RL = true) : n ≤ 32 := by
  unfold sylBase at h
  simp only [CFSG.KC.LQT.S.allBs_cons, CFSG.KC.LQT.S.allBs_nil, P.andB_iff] at h
  exact Nat.le_of_ble_eq_true h.1

theorem sylBase_sound (hn : n ≤ 32) (Rl : List H) (a : ℕ)
    (h : sylBase n a (Rl.map (cH H)) = true) :
    Rl.length = 2 ^ a ∧ Rl.Nodup ∧ (1 : H) ∈ Rl ∧ ∀ x ∈ Rl, x ^ (2 ^ a) = 1 := by
  unfold sylBase at h
  simp only [CFSG.KC.LQT.S.allBs_cons, CFSG.KC.LQT.S.allBs_nil, P.andB_iff] at h
  obtain ⟨-, h2, h3, h4, h5, -⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [P.beq_iff, CFSG.KC.LQT.S.lenL_eq, List.length_map] at h2
    exact h2
  · exact List.Nodup.of_map _ (CFSG.KC.LQT.T2.nodup_of_distinctS h3)
  · rw [CFSG.KC.LQT.S.memL_iff, cH_one, mem_map_cH hn] at h4
    exact h4
  · intro x hx
    have := (P.allL_iff _ _).1 h5 (cH H x) (List.mem_map_of_mem hx)
    rw [cH_pow hn, cH_one, beq_cH hn] at this
    exact this

theorem syl_sound' (hA : codeP (gA : Perm (Fin n)) = cA) (hB : codeP (gB : Perm (Fin n)) = cB)
    (rgw rwords : List (List ℤ)) (a : ℕ) (h : sylK n a (rlK n cA cB rgw rwords) = true) :
    (sylowList H gA gB rgw rwords).length = 2 ^ a ∧ (sylowList H gA gB rgw rwords).Nodup ∧
      (1 : H) ∈ sylowList H gA gB rgw rwords ∧
      (∀ x ∈ sylowList H gA gB rgw rwords, ∀ y ∈ sylowList H gA gB rgw rwords,
        x * y ∈ sylowList H gA gB rgw rwords) ∧
      (∀ x ∈ sylowList H gA gB rgw rwords, x ^ (2 ^ a) = 1) := by
  unfold sylK at h
  rw [P.andB_iff] at h
  have hn : n ≤ 32 := sylBase_le h.1
  rw [rlK_eq gA gB hn hA hB] at h
  obtain ⟨hb, hc⟩ := h
  obtain ⟨h1, h2, h3, h4⟩ := sylBase_sound hn _ a hb
  refine ⟨h1, h2, h3, ?_, h4⟩
  intro x hx y hy
  have := (P.allL_iff _ _).1 hc (cH H x) (List.mem_map_of_mem hx)
  have := (P.allL_iff _ _).1 this (cH H y) (List.mem_map_of_mem hy)
  rw [CFSG.KC.LQT.S.memL_iff, cH_mul hn, mem_map_cH hn] at this
  exact this

theorem sylG_sound' (hA : codeP (gA : Perm (Fin n)) = cA) (hB : codeP (gB : Perm (Fin n)) = cB)
    (rgw rwords : List (List ℤ)) (a : ℕ)
    (h : sylGK n a (rlK n cA cB rgw rwords) (List.map (evalZK n [cA, cB]) rgw) = true) :
    (sylowList H gA gB rgw rwords).length = 2 ^ a ∧ (sylowList H gA gB rgw rwords).Nodup ∧
      (1 : H) ∈ sylowList H gA gB rgw rwords ∧
      (∀ x ∈ sylowList H gA gB rgw rwords, ∀ g ∈ sylowGens H gA gB rgw,
        x * g ∈ sylowList H gA gB rgw rwords) ∧
      (∀ x ∈ sylowList H gA gB rgw rwords, x ^ (2 ^ a) = 1) := by
  unfold sylGK at h
  rw [P.andB_iff] at h
  have hn : n ≤ 32 := sylBase_le h.1
  rw [rlK_eq gA gB hn hA hB, gens_eq gA gB hn hA hB] at h
  obtain ⟨hb, hc⟩ := h
  obtain ⟨h1, h2, h3, h4⟩ := sylBase_sound hn _ a hb
  refine ⟨h1, h2, h3, ?_, h4⟩
  intro x hx g hg
  have := (P.allL_iff _ _).1 hc (cH H x) (List.mem_map_of_mem hx)
  have := (P.allL_iff _ _).1 this (cH H g) (List.mem_map_of_mem hg)
  rw [CFSG.KC.LQT.S.memL_iff, cH_mul hn, mem_map_cH hn] at this
  exact this

theorem invK_eq (hn : n ≤ 32) (Rl : List H) :
    invK n (Rl.map (cH H)) = (invG Rl).map (cH H) := by
  rw [invK, CFSG.KC.LQT.T2.filtL_eqT, List.filter_map, invG]
  congr 1
  refine List.filter_congr fun x _ => ?_
  show andB (notB (Nat.beq (cH H x) (P.one n))) (Nat.beq (P.mul n (cH H x) (cH H x)) (P.one n))
    = _
  rw [Bool.eq_iff_iff, P.andB_iff, P.notB_iff, decide_eq_true_iff, cH_one, cH_mul hn, beq_cH hn,
    beq_cH hn]

private theorem pairInner (hn : n ≤ 32) (x : H) : ∀ I : List H,
    (List.rec (motive := fun _ => List (ℕ × ℕ)) []
      (fun y _ ih => Bool.rec (motive := fun _ => List (ℕ × ℕ)) ih (List.cons (cH H x, y) ih)
        (andB (notB (Nat.beq (cH H x) y)) (P.comm n (cH H x) y))) (I.map (cH H))) =
    (I.filterMap fun y => if x ≠ y ∧ x * y = y * x then some (x, y) else none).map
      (Prod.map (cH H) (cH H))
  | [] => rfl
  | y :: I => by
    rw [List.map_cons]
    dsimp only
    rw [pairInner hn x I]
    by_cases hc : x ≠ y ∧ x * y = y * x
    · have : andB (notB (Nat.beq (cH H x) (cH H y))) (P.comm n (cH H x) (cH H y)) = true := by
        rw [P.andB_iff, P.notB_iff, beq_cH hn, comm_cH hn]
        exact hc
      rw [this]
      dsimp only
      simp [List.filterMap_cons, hc]
    · have : andB (notB (Nat.beq (cH H x) (cH H y))) (P.comm n (cH H x) (cH H y)) = false := by
        rw [← Bool.not_eq_true, P.andB_iff, P.notB_iff, beq_cH hn, comm_cH hn]
        exact hc
      rw [this]
      dsimp only
      simp [List.filterMap_cons, hc]

theorem pairK_eq (hn : n ≤ 32) (I : List H) :
    pairK n (I.map (cH H)) = (pairG I).map (Prod.map (cH H) (cH H)) := by
  rw [pairK, List.map_map]
  refine Eq.trans (congrArg List.flatten (List.map_congr_left fun x _ => pairInner hn x I)) ?_
  rw [pairG, List.map_flatMap]
  rfl

end Sylow

section Rank

open CFSG.KC.Ord

theorem eqL_iff : ∀ l m : List ℕ, eqL l m = true ↔ l = m
  | [], [] => by simp [eqL]
  | [], _ :: _ => by simp [eqL]
  | _ :: _, [] => by simp [eqL]
  | x :: l, y :: m => by
    change andB (Nat.beq x y) (eqL l m) = true ↔ _
    rw [P.andB_iff, P.beq_iff, eqL_iff l m, List.cons.injEq]

private noncomputable def ddStep (L : List ℕ) (acc : List (List ℕ)) : List (List ℕ) :=
  Bool.rec (motive := fun _ => List (List ℕ)) (List.cons L acc) acc
    (List.rec (motive := fun _ => Bool) false (fun M _ ih2 => orB (eqL L M) ih2) acc)

private noncomputable def ddGo (Ls : List (List ℕ)) : List (List ℕ) → List (List ℕ) :=
  List.rec (motive := fun _ => List (List ℕ) → List (List ℕ)) (fun acc => acc)
    (fun L _ ih acc => ih (ddStep L acc)) Ls

private theorem ddGo_nil (acc : List (List ℕ)) : ddGo [] acc = acc := rfl

private theorem ddGo_cons (L : List ℕ) (Ls acc : List (List ℕ)) :
    ddGo (L :: Ls) acc = ddGo Ls (ddStep L acc) := rfl

private theorem anyEq (L : List ℕ) : ∀ acc : List (List ℕ),
    List.rec (motive := fun _ => Bool) false (fun M _ ih2 => orB (eqL L M) ih2) acc = true ↔
      ∃ M ∈ acc, eqL L M = true
  | [] => by dsimp only; simp
  | M :: acc => by
    dsimp only
    rw [P.orB_iff, anyEq L acc]
    simp

private theorem mem_ddStep {x L : List ℕ} {acc : List (List ℕ)} (h : x = L ∨ x ∈ acc) :
    x ∈ ddStep L acc := by
  unfold ddStep
  cases hb : (List.rec (motive := fun _ => Bool) false (fun M _ ih2 => orB (eqL L M) ih2) acc) with
  | false =>
    dsimp only
    rcases h with rfl | h
    · simp
    · simp [h]
  | true =>
    dsimp only
    obtain ⟨M, hM, hE⟩ := (anyEq L acc).1 hb
    rcases h with rfl | h
    · rw [(eqL_iff _ _).1 hE]
      exact hM
    · exact h

private theorem ddGo_mem (x : List ℕ) :
    ∀ (Ls acc : List (List ℕ)), (x ∈ Ls ∨ x ∈ acc) → x ∈ ddGo Ls acc
  | [], acc, h => by
    rcases h with h | h
    · simp at h
    · exact h
  | L :: Ls, acc, h => by
    rw [ddGo_cons]
    apply ddGo_mem x Ls
    rcases h with h | h
    · rcases List.mem_cons.1 h with rfl | h
      · exact Or.inr (mem_ddStep (Or.inl rfl))
      · exact Or.inl h
    · exact Or.inr (mem_ddStep (Or.inr h))

private noncomputable def lvl (n : ℕ) (I : List ℕ) (j : ℕ) : List (List ℕ) :=
  Nat.rec (motive := fun _ => List (List ℕ)) [[P.one n]] (fun _ ih => extK n I ih) j

private theorem lvl_succ (n : ℕ) (I : List ℕ) (j : ℕ) : lvl n I (j + 1) = extK n I (lvl n I j) :=
  rfl

private theorem lvl_zero (n : ℕ) (I : List ℕ) : lvl n I 0 = [[P.one n]] := rfl

private theorem rankK_nil {n : ℕ} {I : List ℕ} {k : ℕ} (h : rankK n I k = true) :
    lvl n I k = [] := by
  have h' : (List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) (lvl n I k)) = true := h
  cases hl : lvl n I k with
  | nil => rfl
  | cons a t =>
    rw [hl] at h'
    exact absurd h' (by simp)

variable {n : ℕ} {H : Subgroup (Perm (Fin n))} (gA gB : H) {cA cB : ℕ}

private theorem mem_extK (I : List ℕ) (Es : List (List ℕ)) (E : List ℕ) (hE : E ∈ Es) (x : ℕ)
    (hx : x ∈ I) (hc : andB (P.allL E fun e => P.comm n x e) (notB (CFSG.KC.LQT.S.memL x E)) = true) :
    CFSG.KC.LQT.T2.sortK (List.append E (List.map (P.mul n x) E)) ∈ extK n I Es := by
  unfold extK
  show _ ∈ ddGo _ []
  apply ddGo_mem
  left
  rw [List.mem_flatten]
  refine ⟨_, List.mem_map.2 ⟨E, hE, rfl⟩, ?_⟩
  rw [List.mem_flatten]
  refine ⟨_, List.mem_map.2 ⟨x, hx, rfl⟩, ?_⟩
  rw [hc]
  simp

section Subprods

variable {S : Type*} [Group S]

private theorem mem_subprods_of_mem {l : List S} {y : S} (hy : y ∈ l) : y ∈ subprods l := by
  induction l with
  | nil => simp at hy
  | cons z l ih =>
    simp only [subprods, List.mem_append, List.mem_map]
    rcases List.mem_cons.1 hy with rfl | hy
    · exact Or.inr ⟨1, one_mem_subprods l, mul_one _⟩
    · exact Or.inl (ih hy)

private theorem commute_subprods {x : S} {l : List S} (h : ∀ y ∈ l, x * y = y * x) :
    ∀ s ∈ subprods l, x * s = s * x := by
  induction l with
  | nil =>
    intro s hs
    simp only [subprods, List.mem_singleton] at hs
    subst hs
    simp
  | cons z l ih =>
    intro s hs
    simp only [subprods, List.mem_append, List.mem_map] at hs
    have hl : ∀ y ∈ l, x * y = y * x := fun y hy => h y (List.mem_cons_of_mem z hy)
    rcases hs with hs | ⟨t, ht, rfl⟩
    · exact ih hl s hs
    · calc x * (z * t) = (x * z) * t := (mul_assoc _ _ _).symm
        _ = (z * x) * t := by rw [h z List.mem_cons_self]
        _ = z * (x * t) := mul_assoc _ _ _
        _ = z * (t * x) := by rw [ih hl t ht]
        _ = z * t * x := (mul_assoc _ _ _).symm

end Subprods

private theorem rank_step (hn : n ≤ 32) (Rinv : List H) (I : List ℕ) (hI : I = Rinv.map (cH H))
    (l : List H) (L : List ℕ) (Ls : List (List ℕ)) (hL : L ∈ Ls)
    (hs : ∀ c, c ∈ L ↔ c ∈ (subprods l).map (cH H)) (x : H) (hx : x ∈ indepExt Rinv l) :
    ∃ L' ∈ extK n I Ls, ∀ c, c ∈ L' ↔ c ∈ (subprods (x :: l)).map (cH H) := by
  simp only [indepExt, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not] at hx
  obtain ⟨hxR, hcomm, hnot⟩ := hx
  refine ⟨_, mem_extK I Ls L hL (cH H x) (hI ▸ List.mem_map_of_mem hxR) ?_, ?_⟩
  · rw [P.andB_iff, P.allL_iff, P.notB_iff, CFSG.KC.LQT.S.memL_iff]
    constructor
    · intro e he
      obtain ⟨s, hs', rfl⟩ := List.mem_map.1 ((hs e).1 he)
      exact (comm_cH hn x s).2 (commute_subprods hcomm s hs')
    · intro hmem
      obtain ⟨s, hs', hxs⟩ := List.mem_map.1 ((hs _).1 hmem)
      exact hnot (cH_inj hn hxs ▸ hs')
  · intro c
    rw [(CFSG.KC.LQT.T2.sortK_perm _).mem_iff]
    show c ∈ L ++ _ ↔ _
    simp only [subprods, List.map_append, List.mem_append, List.mem_map, hs]
    refine or_congr Iff.rfl ⟨?_, ?_⟩
    · rintro ⟨a, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨x * b, ⟨b, hb, rfl⟩, (cH_mul hn x b).symm⟩
    · rintro ⟨a, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨cH H b, ⟨b, hb, rfl⟩, cH_mul hn x b⟩

private theorem rank_forall (hn : n ≤ 32) (Rinv : List H) (I : List ℕ)
    (hI : I = Rinv.map (cH H)) : ∀ (k j : ℕ) (l : List H),
    (∃ L ∈ lvl n I j, ∀ c, c ∈ L ↔ c ∈ (subprods l).map (cH H)) → lvl n I (j + k) = [] →
      forallIndep Rinv (fun _ => false) k l = true
  | 0, j, l, ⟨L, hL, _⟩, h => by
    rw [Nat.add_zero] at h
    rw [h] at hL
    simp at hL
  | k + 1, j, l, ⟨L, hL, hs⟩, h => by
    rw [forallIndep, List.all_eq_true]
    intro x hx
    obtain ⟨L', hL', hs'⟩ := rank_step hn Rinv I hI l L (lvl n I j) hL hs x hx
    refine rank_forall hn Rinv I hI k (j + 1) (x :: l) ⟨L', hL', hs'⟩ ?_
    rw [show j + 1 + k = j + (k + 1) by omega]
    exact h

theorem rank_sound' (hA : codeP (gA : Perm (Fin n)) = cA) (hB : codeP (gB : Perm (Fin n)) = cB)
    (rgw rwords : List (List ℤ)) (k : ℕ) (hn : n ≤ 32)
    (h : rankK n (invK n (rlK n cA cB rgw rwords)) k = true) :
    forallIndep (invG (sylowList H gA gB rgw rwords)) (fun _ => false) k [] = true := by
  rw [rlK_eq gA gB hn hA hB, invK_eq hn] at h
  have hnil := rankK_nil h
  refine rank_forall hn _ _ rfl k 0 [] ⟨[P.one n], ?_, ?_⟩ (by rw [Nat.zero_add]; exact hnil)
  · rw [lvl_zero]
    simp
  · intro c
    simp [subprods, cH_one]
    rw [cH_one]

end Rank

section Tables

open CFSG.KC.Ord

theorem lenK_eq {α : Type} (l : List α) : lenK l = l.length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change Nat.succ (lenK l) = _
    rw [ih]
    rfl

theorem getK_eq {α : Type} (l : List α) (i : ℕ) (d : α) : getK l i d = l.getD i d := by
  induction l generalizing i with
  | nil => simp [getK]
  | cons x l ih =>
    cases i with
    | zero => rfl
    | succ i =>
      change getK l i d = _
      rw [ih]
      rfl

theorem getD_mem {α : Type} (l : List α) (i : ℕ) (d : α) (h : i < l.length) :
    l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

theorem recAnd {α : Type} (P' : α → Bool) : ∀ G : List α,
    List.rec (motive := fun _ => Bool) true (fun e _ ih => andB (P' e) ih) G = true ↔
      ∀ e ∈ G, P' e = true
  | [] => by dsimp only; simp
  | e :: G => by
    dsimp only
    rw [P.andB_iff, recAnd P' G]
    simp

private theorem zipAll_spec {α : Type} (f : α → ℕ × ℕ → Bool) :
    ∀ (l : List α) (h : List (ℕ × ℕ)), zipAll l h f = true → ∀ x ∈ l, ∃ q ∈ h, f x q = true
  | [], _, _, x, hx => by simp at hx
  | y :: l, h, hz, x, hx => by
    cases h with
    | nil =>
      have : zipAll (y :: l) [] f = false := rfl
      rw [this] at hz
      exact absurd hz (by simp)
    | cons q qs =>
      have hz' : andB (f y q) (zipAll l qs f) = true := hz
      rw [P.andB_iff] at hz'
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨q, List.mem_cons_self, hz'.1⟩
      · obtain ⟨q', hq', hf⟩ := zipAll_spec f l qs hz'.2 x hx
        exact ⟨q', List.mem_cons_of_mem _ hq', hf⟩

variable {n : ℕ} {H : Subgroup (Perm (Fin n))} (gA gB : H) {cA cB : ℕ}

theorem getK_H (Rl : List H) (i : ℕ) :
    getK (Rl.map (cH H)) i (P.one n) = cH H (Rl.getD i 1) := by
  rw [getK_eq, cH_one]
  exact List.getD_map (l := Rl) (n := i) (d := (1 : H)) (cH H)

theorem zks_eq (hn : n ≤ 32) (hA : codeP (gA : Perm (Fin n)) = cA)
    (hB : codeP (gB : Perm (Fin n)) = cB) (ws : List (List ℤ)) :
    ws.map (evalZK n [cA, cB]) = (ws.map (evalN H [gA, gB])).map (cH H) := by
  rw [List.map_map]
  exact List.map_congr_left fun w _ => zk_eq gA gB hn hA hB w

private theorem flat_eq (hn : n ≤ 32) (Ts : List H) :
    ∀ CJ : List H, List.flatten (List.map (fun c => List.map (P.conj n c) (Ts.map (cH H)))
        (CJ.map (cH H))) =
      (CJ.flatMap fun c => Ts.map fun t => c * t * c⁻¹).map (cH H)
  | [] => rfl
  | c :: CJ => by
    rw [List.map_cons, List.map_cons, List.flatten_cons, flat_eq hn Ts CJ, List.flatMap_cons,
      List.map_append, List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun t _ => ?_
    exact cH_conj hn c t

theorem witK_iff (hn : n ≤ 32) (Ts CJ : List H) (w : List ℕ) (p : ℕ) :
    witK n (Ts.map (cH H)) (CJ.map (cH H)) w p = true ↔
      (prodWord (conjGens Ts CJ) w ^ p = 1 ∧ prodWord (conjGens Ts CJ) w ≠ 1) := by
  unfold witK
  rw [P.letB_eq]
  have hc : List.append (Ts.map (cH H)) (List.flatten (List.map
      (fun c => List.map (P.conj n c) (Ts.map (cH H))) (CJ.map (cH H)))) =
      (conjGens Ts CJ).map (cH H) := by
    rw [flat_eq hn, conjGens, List.map_append]
    rfl
  rw [hc, evalWK_H hn, P.andB_iff, P.notB_iff, cH_pow hn, cH_one, beq_cH hn, beq_cH hn]

theorem g1ok_sound' (hA : codeP (gA : Perm (Fin n)) = cA) (hB : codeP (gB : Perm (Fin n)) = cB)
    (rgw rwords : List (List ℤ)) (G1 : List (ℕ × List (List ℤ) × List ℕ)) (p : ℕ) (hn : n ≤ 32)
    (h : g1okK n cA cB (rlK n cA cB rgw rwords) G1 p = true) :
    g1ok (sylowList H gA gB rgw rwords) (fun ws => ws.map (evalN H [gA, gB])) G1 p = true := by
  rw [rlK_eq gA gB hn hA hB] at h
  unfold g1okK at h
  have hall := (recAnd _ G1).1 h
  unfold g1ok
  rw [List.all_eq_true]
  intro e he
  have h1 := hall e he
  rw [P.andB_iff, P.beq_iff, lenK_eq, getK_H, zks_eq gA gB hn hA hB] at h1
  rw [Bool.and_eq_true]
  refine ⟨by simpa using h1.1, ?_⟩
  have := (witK_iff hn [sylowList H gA gB rgw rwords |>.getD e.1 1]
    (e.2.1.map (evalN H [gA, gB])) e.2.2 p).1 h1.2
  simpa [witOK] using this

theorem g2ok_sound' (hA : codeP (gA : Perm (Fin n)) = cA) (hB : codeP (gB : Perm (Fin n)) = cB)
    (rgw rwords : List (List ℤ)) (G2 : List (ℕ × ℕ × List (List ℤ) × List ℕ)) (p : ℕ)
    (hn : n ≤ 32) (h : g2okK n cA cB (rlK n cA cB rgw rwords) G2 p = true) :
    g2ok (sylowList H gA gB rgw rwords) (fun ws => ws.map (evalN H [gA, gB])) G2 p = true := by
  rw [rlK_eq gA gB hn hA hB] at h
  unfold g2okK at h
  have hall := (recAnd _ G2).1 h
  unfold g2ok
  rw [List.all_eq_true]
  intro e he
  have h1 := hall e he
  rw [P.andB_iff, P.beq_iff, lenK_eq, getK_H, getK_H, zks_eq gA gB hn hA hB] at h1
  rw [Bool.and_eq_true]
  refine ⟨by simpa using h1.1, ?_⟩
  have := (witK_iff hn [(sylowList H gA gB rgw rwords).getD e.1 1,
    (sylowList H gA gB rgw rwords).getD e.2.1 1]
    (e.2.2.1.map (evalN H [gA, gB])) e.2.2.2 p).1 h1.2
  simpa [witOK] using this

theorem g1cov_sound' (hA : codeP (gA : Perm (Fin n)) = cA) (hB : codeP (gB : Perm (Fin n)) = cB)
    (rgw rwords : List (List ℤ)) (G1 : List (ℕ × List (List ℤ) × List ℕ)) (hs : List (ℕ × ℕ))
    (hn : n ≤ 32) (h : g1covK n (rlK n cA cB rgw rwords) G1 hs = true) :
    g1cover (sylowList H gA gB rgw rwords) G1 = true := by
  rw [rlK_eq gA gB hn hA hB] at h
  unfold g1covK at h
  rw [invK_eq hn] at h
  have hz := zipAll_spec _ _ _ h
  unfold g1cover
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨q, -, hf⟩ := hz (cH H x) (List.mem_map_of_mem hx)
  rw [P.andB_iff, P.andB_iff, P.blt_iff, P.blt_iff, lenK_eq, CFSG.KC.LQT.S.lenL_eq,
    List.length_map] at hf
  obtain ⟨h1, h2, h3⟩ := hf
  have hg1 : getK ((sylowList H gA gB rgw rwords).map (cH H)) q.2 (P.one n) =
      cH H ((sylowList H gA gB rgw rwords).getD q.2 1) := getK_H _ _
  have hg2 : getK ((sylowList H gA gB rgw rwords).map (cH H))
      (getK G1 q.1 ((0, [], []) : ℕ × List (List ℤ) × List ℕ)).1 (P.one n) =
      cH H ((sylowList H gA gB rgw rwords).getD
        (G1.getD q.1 ((0, [], []) : ℕ × List (List ℤ) × List ℕ)).1 1) := by
    rw [getK_eq G1 q.1 ((0, [], []) : ℕ × List (List ℤ) × List ℕ)]
    exact getK_H _ _
  rw [hg1, hg2, cH_conj hn, beq_cH hn] at h3
  refine List.any_eq_true.2 ⟨G1.getD q.1 ((0, [], []) : ℕ × List (List ℤ) × List ℕ),
    getD_mem _ _ _ h1, List.any_eq_true.2 ⟨_, getD_mem _ q.2 1 h2, (decide_eq_true h3)⟩⟩

theorem g2cov_sound' (hA : codeP (gA : Perm (Fin n)) = cA) (hB : codeP (gB : Perm (Fin n)) = cB)
    (rgw rwords : List (List ℤ)) (G2 : List (ℕ × ℕ × List (List ℤ) × List ℕ))
    (hs : List (ℕ × ℕ)) (hn : n ≤ 32) (h : g2covK n (rlK n cA cB rgw rwords) G2 hs = true) :
    g2cover (sylowList H gA gB rgw rwords) G2 = true := by
  rw [rlK_eq gA gB hn hA hB] at h
  unfold g2covK at h
  rw [invK_eq hn, pairK_eq hn] at h
  have hz := zipAll_spec _ _ _ h
  unfold g2cover
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨q, -, hf⟩ := hz (Prod.map (cH H) (cH H) x) (List.mem_map_of_mem hx)
  have e1 : (Prod.map (cH H) (cH H) x).1 = cH H x.1 := rfl
  have e2 : (Prod.map (cH H) (cH H) x).2 = cH H x.2 := rfl
  rw [e1, e2] at hf
  rw [P.andB_iff, P.andB_iff, P.andB_iff, P.blt_iff, P.blt_iff, lenK_eq, CFSG.KC.LQT.S.lenL_eq,
    List.length_map] at hf
  obtain ⟨h1, h2, h3, h4⟩ := hf
  have hg1 : getK ((sylowList H gA gB rgw rwords).map (cH H)) q.2 (P.one n) =
      cH H ((sylowList H gA gB rgw rwords).getD q.2 1) := getK_H _ _
  have hg2 : getK ((sylowList H gA gB rgw rwords).map (cH H))
      (getK G2 q.1 ((0, 0, [], []) : ℕ × ℕ × List (List ℤ) × List ℕ)).1 (P.one n) =
      cH H ((sylowList H gA gB rgw rwords).getD
        (G2.getD q.1 ((0, 0, [], []) : ℕ × ℕ × List (List ℤ) × List ℕ)).1 1) := by
    rw [getK_eq G2 q.1 ((0, 0, [], []) : ℕ × ℕ × List (List ℤ) × List ℕ)]
    exact getK_H _ _
  have hg3 : getK ((sylowList H gA gB rgw rwords).map (cH H))
      (getK G2 q.1 ((0, 0, [], []) : ℕ × ℕ × List (List ℤ) × List ℕ)).2.1 (P.one n) =
      cH H ((sylowList H gA gB rgw rwords).getD
        (G2.getD q.1 ((0, 0, [], []) : ℕ × ℕ × List (List ℤ) × List ℕ)).2.1 1) := by
    rw [getK_eq G2 q.1 ((0, 0, [], []) : ℕ × ℕ × List (List ℤ) × List ℕ)]
    exact getK_H _ _
  rw [hg1, hg2, cH_conj hn, beq_cH hn] at h3
  rw [hg1, hg3, cH_conj hn, beq_cH hn] at h4
  refine List.any_eq_true.2 ⟨G2.getD q.1 ((0, 0, [], []) : ℕ × ℕ × List (List ℤ) × List ℕ),
    getD_mem _ _ _ h1, List.any_eq_true.2 ⟨_, getD_mem _ q.2 1 h2, ?_⟩⟩
  rw [Bool.and_eq_true]
  exact ⟨(decide_eq_true h3), (decide_eq_true h4)⟩

theorem g1covL_sound' (hA : codeP (gA : Perm (Fin n)) = cA) (hB : codeP (gB : Perm (Fin n)) = cB)
    (rgw rwords : List (List ℤ)) (G1 : List (ℕ × List (List ℤ) × List ℕ)) (hs : List (ℕ × ℕ))
    (hn : n ≤ 32) (h : g1covK n (rlK n cA cB rgw rwords) G1 hs = true) :
    ((invList H (sylowList H gA gB rgw rwords)).all fun x => G1.any fun e =>
      (sylowList H gA gB rgw rwords).any fun r =>
        r * x * r⁻¹ == (sylowList H gA gB rgw rwords).getD e.1 1) = true := by
  have hc := g1cov_sound' gA gB hA hB rgw rwords G1 hs hn h
  unfold g1cover at hc
  rw [List.all_eq_true] at hc ⊢
  intro x hx
  obtain ⟨e, he, hr⟩ := List.any_eq_true.1 (hc x hx)
  obtain ⟨r, hr', hrx⟩ := List.any_eq_true.1 hr
  exact List.any_eq_true.2 ⟨e, he, List.any_eq_true.2 ⟨r, hr', beq_iff_eq.2 (of_decide_eq_true hrx)⟩⟩

theorem g2covL_sound' (hA : codeP (gA : Perm (Fin n)) = cA) (hB : codeP (gB : Perm (Fin n)) = cB)
    (rgw rwords : List (List ℤ)) (G2 : List (ℕ × ℕ × List (List ℤ) × List ℕ))
    (hs : List (ℕ × ℕ)) (hn : n ≤ 32) (h : g2covK n (rlK n cA cB rgw rwords) G2 hs = true) :
    ((pairList H (invList H (sylowList H gA gB rgw rwords))).all fun p => G2.any fun e =>
      (sylowList H gA gB rgw rwords).any fun r =>
        r * p.1 * r⁻¹ == (sylowList H gA gB rgw rwords).getD e.1 1 &&
          r * p.2 * r⁻¹ == (sylowList H gA gB rgw rwords).getD e.2.1 1) = true := by
  have hc := g2cov_sound' gA gB hA hB rgw rwords G2 hs hn h
  unfold g2cover at hc
  rw [List.all_eq_true] at hc ⊢
  intro x hx
  obtain ⟨e, he, hr⟩ := List.any_eq_true.1 (hc x hx)
  obtain ⟨r, hr', hrx⟩ := List.any_eq_true.1 hr
  rw [Bool.and_eq_true] at hrx
  refine List.any_eq_true.2 ⟨e, he, List.any_eq_true.2 ⟨r, hr', ?_⟩⟩
  rw [Bool.and_eq_true]
  exact ⟨beq_iff_eq.2 (of_decide_eq_true hrx.1), beq_iff_eq.2 (of_decide_eq_true hrx.2)⟩

end Tables

end CFSG.KC.LQT.Syl.Pf

end
