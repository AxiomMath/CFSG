module

public import Certificates.Data.Kernel.LocalQT.Syl24
public import CFSG.Certificates.Kernel.LocalQTWordSound
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PairCover

import CFSG.Certificates.Kernel.LocalQTSylProved
import CFSG.Certificates.Kernel.LocalQTTab2KSound

public section

namespace CFSG.KC.LQT.Syl.Pf24

open Equiv CFSG.QuasithinUnique.Setup.X1 CFSG.KC.LQT.W CFSG.KC.LQT.Syl CFSG.KC.LQT.Syl.Pf

section Cover

variable {S : Type} [Group S] [DecidableEq S]

private theorem zipIdx_getD {α : Type} {l : List α} {x : α × ℕ} (d : α) (hx : x ∈ l.zipIdx) :
    x.2 < l.length ∧ l.getD x.2 d = x.1 := by
  rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff] at hx
  obtain ⟨h, e⟩ := hx
  exact ⟨h, by rw [List.getD_eq_getElem _ _ h, e]⟩

private theorem mem_zipIdx_getD {α : Type} {l : List α} {i : ℕ} (d : α) (h : i < l.length) :
    (l.getD i d, i) ∈ l.zipIdx := by
  rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
  exact ⟨h, (List.getD_eq_getElem _ _ h).symm⟩

private theorem fold_mono {β : Type} (A B : β → ℕ × ℕ) (L : List β) :
    ∀ (m0 : Std.HashMap (ℕ × ℕ) (ℕ × ℕ)) (k : ℕ × ℕ), k ∈ m0 →
      k ∈ L.foldl (fun m b => m.insertIfNew (A b) (B b)) m0 := by
  induction L with
  | nil => intro m0 k hk; exact hk
  | cons b L ih =>
    intro m0 k hk
    rw [List.foldl_cons]
    exact ih _ _ (Std.HashMap.mem_insertIfNew.2 (Or.inr hk))

private theorem fold_mem {β : Type} (A B : β → ℕ × ℕ) (L : List β) :
    ∀ (m0 : Std.HashMap (ℕ × ℕ) (ℕ × ℕ)) (b : β), b ∈ L →
      A b ∈ L.foldl (fun m b => m.insertIfNew (A b) (B b)) m0 := by
  induction L with
  | nil => intro m0 b hb; simp at hb
  | cons c L ih =>
    intro m0 b hb
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hb with rfl | hb
    · exact fold_mono A B L _ _ (Std.HashMap.mem_insertIfNew.2 (Or.inl (by simp)))
    · exact ih _ _ hb

private theorem fold_inv {β : Type} (A B : β → ℕ × ℕ) (Q : ℕ × ℕ → ℕ × ℕ → Prop) (L : List β)
    (hL : ∀ b ∈ L, Q (A b) (B b)) :
    ∀ (m0 : Std.HashMap (ℕ × ℕ) (ℕ × ℕ)), (∀ a v, m0[a]? = some v → Q a v) →
      ∀ a v, (L.foldl (fun m b => m.insertIfNew (A b) (B b)) m0)[a]? = some v → Q a v := by
  induction L with
  | nil => intro m0 h0; exact h0
  | cons c L ih =>
    intro m0 h0
    rw [List.foldl_cons]
    refine ih (fun b hb => hL b (List.mem_cons_of_mem _ hb)) _ ?_
    intro a v hv
    rw [Std.HashMap.getElem?_insertIfNew] at hv
    split_ifs at hv with hc
    · cases hv
      have : A c = a := by simpa using hc.1
      subst this
      exact hL c List.mem_cons_self
    · exact h0 a v hv


private def innerStep (key : S → ℕ) (Rl : List S) (tk : (S × S) × ℕ)
    (m : Std.HashMap (ℕ × ℕ) (ℕ × ℕ)) : Std.HashMap (ℕ × ℕ) (ℕ × ℕ) :=
  Rl.zipIdx.foldl (fun m rr =>
    m.insertIfNew (key (rr.1⁻¹ * tk.1.1 * rr.1), key (rr.1⁻¹ * tk.1.2 * rr.1)) (tk.2, rr.2)) m

private theorem coverMapG_eq (key : S → ℕ) (Rl : List S) (reps : List (S × S)) :
    coverMapG key Rl reps = reps.zipIdx.foldl (fun m tk => innerStep key Rl tk m) {} := rfl

private theorem outer_mono (key : S → ℕ) (Rl : List S) (T : List ((S × S) × ℕ)) :
    ∀ (m0 : Std.HashMap (ℕ × ℕ) (ℕ × ℕ)) (k : ℕ × ℕ), k ∈ m0 →
      k ∈ T.foldl (fun m tk => innerStep key Rl tk m) m0 := by
  induction T with
  | nil => intro m0 k hk; exact hk
  | cons tk T ih =>
    intro m0 k hk
    rw [List.foldl_cons]
    exact ih _ _ (fold_mono _ _ _ _ _ hk)

private theorem outer_mem (key : S → ℕ) (Rl : List S) (T : List ((S × S) × ℕ)) :
    ∀ (m0 : Std.HashMap (ℕ × ℕ) (ℕ × ℕ)), ∀ tk ∈ T, ∀ rr ∈ Rl.zipIdx,
      (key (rr.1⁻¹ * tk.1.1 * rr.1), key (rr.1⁻¹ * tk.1.2 * rr.1)) ∈
        T.foldl (fun m tk => innerStep key Rl tk m) m0 := by
  induction T with
  | nil => intro m0 tk htk; simp at htk
  | cons c T ih =>
    intro m0 tk htk rr hrr
    rw [List.foldl_cons]
    rcases List.mem_cons.1 htk with rfl | htk
    · exact outer_mono key Rl T _ _ (fold_mem
        (fun rr : S × ℕ => (key (rr.1⁻¹ * tk.1.1 * rr.1), key (rr.1⁻¹ * tk.1.2 * rr.1)))
        (fun rr : S × ℕ => (tk.2, rr.2)) _ _ rr hrr)
    · exact ih _ tk htk rr hrr

private theorem outer_inv (key : S → ℕ) (Rl : List S) (reps : List (S × S))
    (Q : ℕ × ℕ → ℕ × ℕ → Prop) (T : List ((S × S) × ℕ))
    (hT : ∀ tk ∈ T, ∀ rr ∈ Rl.zipIdx,
      Q (key (rr.1⁻¹ * tk.1.1 * rr.1), key (rr.1⁻¹ * tk.1.2 * rr.1)) (tk.2, rr.2)) :
    ∀ (m0 : Std.HashMap (ℕ × ℕ) (ℕ × ℕ)), (∀ a v, m0[a]? = some v → Q a v) →
      ∀ a v, (T.foldl (fun m tk => innerStep key Rl tk m) m0)[a]? = some v → Q a v := by
  induction T with
  | nil => intro m0 h0; exact h0
  | cons c T ih =>
    intro m0 h0
    rw [List.foldl_cons]
    refine ih (fun tk htk => hT tk (List.mem_cons_of_mem _ htk)) _ ?_
    exact fold_inv _ _ Q _ (fun rr hrr => hT c List.mem_cons_self rr hrr) m0 h0

private theorem coveredG_of_inj (key : S → ℕ) (hk : Function.Injective key) (Rl : List S)
    (reps : List (S × S)) (x : S × S) {i j : ℕ} (hi : i < reps.length) (hj : j < Rl.length)
    (h1 : Rl.getD j 1 * x.1 * (Rl.getD j 1)⁻¹ = (reps.getD i (1, 1)).1)
    (h2 : Rl.getD j 1 * x.2 * (Rl.getD j 1)⁻¹ = (reps.getD i (1, 1)).2) :
    coveredG key Rl reps (coverMapG key Rl reps) x = true := by
  have hmem := outer_mem key Rl reps.zipIdx {} (reps.getD i (1, 1), i)
    (mem_zipIdx_getD _ hi) (Rl.getD j 1, j) (mem_zipIdx_getD _ hj)
  have hx1 : x.1 = (Rl.getD j 1)⁻¹ * (reps.getD i (1, 1)).1 * Rl.getD j 1 := by
    rw [← h1]; group
  have hx2 : x.2 = (Rl.getD j 1)⁻¹ * (reps.getD i (1, 1)).2 * Rl.getD j 1 := by
    rw [← h2]; group
  have hkey : (key x.1, key x.2) ∈ coverMapG key Rl reps := by
    rw [coverMapG_eq, hx1, hx2]
    exact hmem
  obtain ⟨⟨k, ri⟩, hv⟩ := Option.isSome_iff_exists.1 (Std.HashMap.isSome_getElem?_iff_mem.2 hkey)
  have hinv := outer_inv key Rl reps
    (fun a v => ∃ k ri, k < reps.length ∧ ri < Rl.length ∧ v = (k, ri) ∧
      a = (key ((Rl.getD ri 1)⁻¹ * (reps.getD k (1, 1)).1 * Rl.getD ri 1),
        key ((Rl.getD ri 1)⁻¹ * (reps.getD k (1, 1)).2 * Rl.getD ri 1))) reps.zipIdx
    (fun tk htk rr hrr => by
      obtain ⟨h1, h2⟩ := zipIdx_getD (1, 1) htk
      obtain ⟨h3, h4⟩ := zipIdx_getD 1 hrr
      exact ⟨tk.2, rr.2, h1, h3, rfl, by rw [h2, h4]⟩) {}
    (fun a v hv => by simp at hv)
  obtain ⟨k', ri', hk', hri', hv', ha'⟩ := hinv _ _ (by rw [coverMapG_eq] at hv; exact hv)
  simp only [Prod.mk.injEq] at hv' ha'
  obtain ⟨rfl, rfl⟩ := hv'
  have e1 := hk ha'.1
  have e2 := hk ha'.2
  simp only [coveredG, hv, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨⟨hk', hri'⟩, ?_⟩, ?_⟩
  · rw [e1]; group
  · rw [e2]; group


section Key

private theorem foldl_digits (n : ℕ) (l : List ℕ) :
    l.foldl (fun acc d => acc * n + d) 0 = Nat.ofDigits n l.reverse := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l d ih =>
    rw [List.foldl_append, ih, List.foldl_cons, List.foldl_nil, List.reverse_append,
      List.reverse_singleton, List.singleton_append, Nat.ofDigits_cons]
    ring

private theorem key_inj {n : ℕ} (x y : Equiv.Perm (Fin n))
    (h : (List.finRange n).foldl (fun acc i => acc * n + (x i).val) 0 =
      (List.finRange n).foldl (fun acc i => acc * n + (y i).val) 0) : x = y := by
  rcases Nat.lt_or_ge 1 n with hn | hn
  · have e1 : ∀ z : Equiv.Perm (Fin n), (List.finRange n).foldl (fun acc i => acc * n + (z i).val) 0 =
        ((List.finRange n).map fun i => (z i).val).foldl (fun acc d => acc * n + d) 0 := by
      intro z; rw [List.foldl_map]
    rw [e1, e1, foldl_digits, foldl_digits] at h
    have := Nat.ofDigits_inj_of_len_eq hn (by simp) (by simp)
      (by simp) h
    rw [List.reverse_inj, List.map_inj_left] at this
    ext i
    exact this i (List.mem_finRange i)
  · have : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.2 (by omega)
    ext i
    exact congrArg Fin.val (Subsingleton.elim _ _)

end Key


end Cover

section Count

private theorem letN_eq (y : ℕ) (k : ℕ → ℕ) : letN y k = k y := by cases y <;> rfl

private noncomputable def bd (f : ℕ × ℕ → ℕ × ℕ → ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ) → ℕ → ℕ :=
  List.rec (motive := fun _ => List (ℕ × ℕ) → ℕ → ℕ)
    (fun h acc => List.rec (motive := fun _ => ℕ) acc (fun _ _ _ => Nat.add acc 1099511627776) h)
    (fun x _ ih h acc => List.rec (motive := fun _ => ℕ) (Nat.add acc 1099511627776)
      (fun q qs _ => letN (Nat.add acc (f x q)) (ih qs)) h)

private theorem bd_nil_cons (f : ℕ × ℕ → ℕ × ℕ → ℕ) (q : ℕ × ℕ) (qs : List (ℕ × ℕ)) (acc : ℕ) :
    bd f [] (q :: qs) acc = acc + 1099511627776 := rfl

private theorem bd_cons_nil (f : ℕ × ℕ → ℕ × ℕ → ℕ) (x : ℕ × ℕ) (xs : List (ℕ × ℕ)) (acc : ℕ) :
    bd f (x :: xs) [] acc = acc + 1099511627776 := rfl

private theorem bd_cons_cons (f : ℕ × ℕ → ℕ × ℕ → ℕ) (x : ℕ × ℕ) (xs : List (ℕ × ℕ)) (q : ℕ × ℕ)
    (qs : List (ℕ × ℕ)) (acc : ℕ) :
    bd f (x :: xs) (q :: qs) acc = bd f xs qs (acc + f x q) := by
  show letN (Nat.add acc (f x q)) (bd f xs qs) = _
  rw [letN_eq]
  rfl

private theorem bd_ge (f : ℕ × ℕ → ℕ × ℕ → ℕ) (xs : List (ℕ × ℕ)) :
    ∀ (hs : List (ℕ × ℕ)) (acc : ℕ), acc ≤ bd f xs hs acc := by
  induction xs with
  | nil =>
    intro hs acc
    cases hs with
    | nil => exact le_rfl
    | cons q qs => rw [bd_nil_cons]; omega
  | cons x xs ih =>
    intro hs acc
    cases hs with
    | nil => rw [bd_cons_nil]; omega
    | cons q qs =>
      rw [bd_cons_cons]
      exact le_trans (Nat.le_add_right _ _) (ih qs _)

private theorem bd_spec (f : ℕ × ℕ → ℕ × ℕ → ℕ) (xs : List (ℕ × ℕ)) :
    ∀ (hs : List (ℕ × ℕ)) (acc : ℕ), bd f xs hs acc < 1099511627776 →
      hs.length = xs.length ∧
        bd f xs hs acc = acc + ((xs.zip hs).map fun p => f p.1 p.2).sum := by
  induction xs with
  | nil =>
    intro hs acc h
    cases hs with
    | nil => exact ⟨rfl, by simp [show bd f [] [] acc = acc from rfl]⟩
    | cons q qs => rw [bd_nil_cons] at h; omega
  | cons x xs ih =>
    intro hs acc h
    cases hs with
    | nil => rw [bd_cons_nil] at h; omega
    | cons q qs =>
      rw [bd_cons_cons] at h ⊢
      obtain ⟨h1, h2⟩ := ih qs _ h
      refine ⟨by simp [h1], ?_⟩
      rw [h2, List.zip_cons_cons, List.map_cons, List.sum_cons]
      dsimp only
      omega

private theorem filter_len_le {α : Type} (B : α → Bool) (g : α → ℕ × ℕ → ℕ) (X : List α) :
    ∀ (hs : List (ℕ × ℕ)), hs.length = X.length →
      (∀ x q, (x, q) ∈ X.zip hs → g x q = 0 → B x = false) →
      (X.filter B).length ≤ ((X.zip hs).map fun p => g p.1 p.2).sum := by
  induction X with
  | nil => intro hs _ _; simp
  | cons x X ih =>
    intro hs hlen hcov
    cases hs with
    | nil => simp at hlen
    | cons q qs =>
      have hlen' : qs.length = X.length := by simpa using hlen
      have hz : (x :: X).zip (q :: qs) = (x, q) :: X.zip qs := rfl
      have ih' := ih qs hlen' (fun y r hyr => hcov y r (by
        rw [hz]; exact List.mem_cons_of_mem _ hyr))
      rw [hz, List.map_cons, List.sum_cons, List.filter_cons]
      by_cases hB : B x = true
      · have hg : g x q ≠ 0 := fun h0 => by
          have := hcov x q (by rw [hz]; exact List.mem_cons_self) h0
          rw [hB] at this; exact absurd this (by simp)
        simp only [hB, if_true, List.length_cons]
        omega
      · have hB' : B x = false := by simpa using hB
        simp only [hB', Bool.false_eq_true, ↓reduceIte]
        have := Nat.zero_le (g x q)
        omega

end Count

section Main

variable {n : ℕ} {H : Subgroup (Perm (Fin n))} (gA gB : H) {cA cB : ℕ}

private theorem sqK_succ (n x a : ℕ) : sqK n x (a + 1) = sqK n (P.mul n x x) a := by
  have : sqK n x (a + 1) = letN (P.mul n x x) (fun y => sqK n y a) := rfl
  rw [this, letN_eq]

private theorem sqK_H (hn : n ≤ 32) (a : ℕ) : ∀ x : H, sqK n (cH H x) a = cH H (x ^ (2 ^ a)) := by
  induction a with
  | zero => intro x; show cH H x = cH H (x ^ 2 ^ 0); rw [pow_zero, pow_one]
  | succ a ih =>
    intro x
    rw [sqK_succ, cH_mul hn, ih, ← pow_two, ← pow_mul, pow_succ, mul_comm]

theorem sylG2_sound' (hA : codeP (gA : Perm (Fin n)) = cA) (hB : codeP (gB : Perm (Fin n)) = cB)
    (rgw rwords : List (List ℤ)) (a : ℕ)
    (h : sylG2K n a (rlK n cA cB rgw rwords) (List.map (evalZK n [cA, cB]) rgw) = true) :
    (sylowList H gA gB rgw rwords).length = 2 ^ a ∧ (sylowList H gA gB rgw rwords).Nodup ∧
      (1 : H) ∈ sylowList H gA gB rgw rwords ∧
      (∀ x ∈ sylowList H gA gB rgw rwords, ∀ g ∈ sylowGens H gA gB rgw,
        x * g ∈ sylowList H gA gB rgw rwords) ∧
      (∀ x ∈ sylowList H gA gB rgw rwords, x ^ (2 ^ a) = 1) := by
  unfold sylG2K at h
  have hn : n ≤ 32 := by
    simp only [CFSG.KC.LQT.S.allBs_cons, CFSG.KC.LQT.S.allBs_nil, P.andB_iff] at h
    exact Nat.le_of_ble_eq_true h.1
  rw [rlK_eq gA gB hn hA hB, gens_eq gA gB hn hA hB] at h
  simp only [CFSG.KC.LQT.S.allBs_cons, CFSG.KC.LQT.S.allBs_nil, P.andB_iff] at h
  obtain ⟨-, h2, h3, h4, h5, h6, -⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [P.beq_iff, CFSG.KC.LQT.S.lenL_eq, List.length_map] at h2
    exact h2
  · exact List.Nodup.of_map _ (CFSG.KC.LQT.T2.nodup_of_distinctS h3)
  · rw [CFSG.KC.LQT.S.memL_iff, cH_one, mem_map_cH hn] at h4
    exact h4
  · intro x hx g hg
    have := (P.allL_iff _ _).1 h6 (cH H g) (List.mem_map_of_mem hg)
    rw [eqL_iff] at this
    have hm : cH H (x * g) ∈ List.map (fun y => P.mul n y (cH H g)) (List.map (cH H) (sylowList H gA gB rgw rwords)) := by
      rw [List.mem_map]
      exact ⟨cH H x, List.mem_map_of_mem hx, cH_mul hn x g⟩
    rw [← (CFSG.KC.LQT.T2.sortK_perm _).mem_iff, this, (CFSG.KC.LQT.T2.sortK_perm _).mem_iff,
      mem_map_cH hn] at hm
    exact hm
  · intro x hx
    have := (P.allL_iff _ _).1 h5 (cH H x) (List.mem_map_of_mem hx)
    rw [sqK_H hn, cH_one, beq_cH hn] at this
    exact this

theorem pairLen_sound' (hA : codeP (gA : Perm (Fin n)) = cA) (hB : codeP (gB : Perm (Fin n)) = cB)
    (rgw rwords : List (List ℤ)) (c : ℕ) (hn : n ≤ 32)
    (h : lenIs (pairK n (invK n (rlK n cA cB rgw rwords))) c = true) :
    (pairG (invG (sylowList H gA gB rgw rwords))).length = c := by
  rw [rlK_eq gA gB hn hA hB, invK_eq hn, pairK_eq hn] at h
  unfold lenIs at h
  rw [P.beq_iff, lenK_eq, List.length_map] at h
  exact h

private theorem toNatK_eq (z : ℤ) : toNatK z = z.toNat := by
  rcases z with m | m <;> rfl

private theorem recHead (w : List ℤ) :
    List.rec (motive := fun _ => ℤ) 0 (fun z _ _ => z) w = w.headD 0 := by
  cases w <;> rfl

private theorem conjP_eq (Ps : List H) (ws : List (List ℤ)) :
    conjP n (Ps.map (cH H)) ws = (ws.map fun w => Ps.getD (w.headD 0).toNat 1).map (cH H) := by
  unfold conjP
  rw [List.map_map]
  refine List.map_congr_left fun w _ => ?_
  simp only [Function.comp_apply]
  rw [recHead, toNatK_eq, getK_H]

theorem g1okP_sound' (hA : codeP (gA : Perm (Fin n)) = cA) (hB : codeP (gB : Perm (Fin n)) = cB)
    (rgw rwords poolW : List (List ℤ)) (G1 : List (ℕ × List (List ℤ) × List ℕ)) (p : ℕ)
    (hn : n ≤ 32)
    (h : g1okPK n (List.map (evalZK n [cA, cB]) poolW) (rlK n cA cB rgw rwords) G1 p = true) :
    g1ok (sylowList H gA gB rgw rwords)
      (fun ws => ws.map fun w => (poolW.map (evalN H [gA, gB])).getD (w.headD 0).toNat 1) G1 p =
        true := by
  rw [rlK_eq gA gB hn hA hB, zks_eq gA gB hn hA hB poolW] at h
  unfold g1okPK at h
  have hall := (recAnd _ G1).1 h
  unfold g1ok
  rw [List.all_eq_true]
  intro e he
  have h1 := hall e he
  rw [P.andB_iff, P.beq_iff, lenK_eq, getK_H, conjP_eq] at h1
  rw [Bool.and_eq_true]
  refine ⟨by simpa using h1.1, ?_⟩
  have := (witK_iff hn [(sylowList H gA gB rgw rwords).getD e.1 1]
    (e.2.1.map fun w : List ℤ => (poolW.map (evalN H [gA, gB])).getD (w.headD 0).toNat 1) e.2.2 p).1 h1.2
  simpa [witOK] using this

theorem g2okP_sound' (hA : codeP (gA : Perm (Fin n)) = cA) (hB : codeP (gB : Perm (Fin n)) = cB)
    (rgw rwords poolW : List (List ℤ)) (G2 : List (ℕ × ℕ × List (List ℤ) × List ℕ)) (p : ℕ)
    (hn : n ≤ 32)
    (h : g2okPK n (List.map (evalZK n [cA, cB]) poolW) (rlK n cA cB rgw rwords) G2 p = true) :
    g2ok (sylowList H gA gB rgw rwords)
      (fun ws => ws.map fun w => (poolW.map (evalN H [gA, gB])).getD (w.headD 0).toNat 1) G2 p =
        true := by
  rw [rlK_eq gA gB hn hA hB, zks_eq gA gB hn hA hB poolW] at h
  unfold g2okPK at h
  have hall := (recAnd _ G2).1 h
  unfold g2ok
  rw [List.all_eq_true]
  intro e he
  have h1 := hall e he
  rw [P.andB_iff, P.beq_iff, lenK_eq, getK_H, getK_H, conjP_eq] at h1
  rw [Bool.and_eq_true]
  refine ⟨by simpa using h1.1, ?_⟩
  have := (witK_iff hn [(sylowList H gA gB rgw rwords).getD e.1 1,
    (sylowList H gA gB rgw rwords).getD e.2.1 1]
    (e.2.2.1.map fun w : List ℤ => (poolW.map (evalN H [gA, gB])).getD (w.headD 0).toNat 1) e.2.2.2 p).1
    h1.2
  simpa [witOK] using this

private theorem badOne_zero {n : ℕ} {RL : List ℕ} {RP : List (ℕ × ℕ)} {m : ℕ} {x q : ℕ × ℕ}
    (h : badOne n RL RP m x q = 0) :
    Nat.blt q.1 m = true ∧ Nat.blt q.2 (CFSG.KC.LQT.S.lenL RL) = true ∧
      Nat.beq (P.conj n (getK RL q.2 (P.one n)) x.1) (getK RP q.1 (0, 0)).1 = true ∧
      Nat.beq (P.conj n (getK RL q.2 (P.one n)) x.2) (getK RP q.1 (0, 0)).2 = true := by
  unfold badOne at h
  cases hb1 : Nat.blt q.1 m
  · rw [hb1] at h
    change (1 : ℕ) = 0 at h
    omega
  · rw [hb1] at h
    dsimp only at h
    cases hb2 : CFSG.KC.Ord.andB (Nat.blt q.2 (CFSG.KC.LQT.S.lenL RL))
        (P.letB (getK RL q.2 (P.one n)) fun r =>
          CFSG.KC.Ord.andB (Nat.beq (P.conj n r x.1) (getK RP q.1 (0, 0)).1)
            (Nat.beq (P.conj n r x.2) (getK RP q.1 (0, 0)).2))
    · rw [hb2] at h
      change (1099511627776 : ℕ) = 0 at h
      omega
    · rw [P.andB_iff, P.letB_eq, P.andB_iff] at hb2
      exact ⟨rfl, hb2.1, hb2.2.1, hb2.2.2⟩

private theorem RP_get (Rl : List H) (G2 : List (ℕ × ℕ × List (List ℤ) × List ℕ)) {i : ℕ}
    (hi : i < G2.length) :
    getK (G2.map fun e => (getK (Rl.map (cH H)) e.1 (P.one n), getK (Rl.map (cH H)) e.2.1 (P.one n)))
        i (0, 0) =
      Prod.map (cH H) (cH H) ((G2.map fun e => (Rl.getD e.1 1, Rl.getD e.2.1 1)).getD i (1, 1)) := by
  rw [getK_eq, List.getD_eq_getElem _ _ (by simpa using hi),
    List.getD_eq_getElem _ _ (by simpa using hi)]
  simp [getK_H]

theorem bad_sound' (hA : codeP (gA : Perm (Fin n)) = cA) (hB : codeP (gB : Perm (Fin n)) = cB)
    (rgw rwords : List (List ℤ)) (G2 : List (ℕ × ℕ × List (List ℤ) × List ℕ))
    (hs : List (ℕ × ℕ)) (c : ℕ) (hc : c < 2 ^ 40) (hn : n ≤ 32)
    (h : atMost (badK n (rlK n cA cB rgw rwords) G2 hs) c = true) :
    (g2coverBad
      (fun x : H => (List.finRange n).foldl (fun acc i => acc * n + ((x : Perm (Fin n)) i).val) 0)
      (sylowList H gA gB rgw rwords) G2).length ≤ c := by
  rw [rlK_eq gA gB hn hA hB] at h
  generalize sylowList H gA gB rgw rwords = Rl at h ⊢
  have hle : badK n (Rl.map (cH H)) G2 hs ≤ c := Nat.le_of_ble_eq_true h
  have e : badK n (Rl.map (cH H)) G2 hs = bd (badOne n (Rl.map (cH H))
      (G2.map fun e => (getK (Rl.map (cH H)) e.1 (P.one n), getK (Rl.map (cH H)) e.2.1 (P.one n)))
      (lenK G2)) (pairK n (invK n (Rl.map (cH H)))) hs 0 := rfl
  rw [e, invK_eq hn, pairK_eq hn] at hle
  obtain ⟨hlen, hsum⟩ := bd_spec _ _ _ _ (lt_of_le_of_lt hle hc)
  rw [List.length_map] at hlen
  rw [zero_add, List.zip_map_left, List.map_map] at hsum
  have hkey : Function.Injective (fun x : H =>
      (List.finRange n).foldl (fun acc i => acc * n + ((x : Perm (Fin n)) i).val) 0) :=
    fun x y hxy => Subtype.ext (key_inj _ _ hxy)
  rw [hsum] at hle
  unfold g2coverBad
  dsimp only
  refine le_trans (filter_len_le _ (fun x q => badOne n (Rl.map (cH H))
      (G2.map fun e : ℕ × ℕ × List (List ℤ) × List ℕ =>
        (getK (Rl.map (cH H)) e.1 (P.one n), getK (Rl.map (cH H)) e.2.1 (P.one n)))
      (lenK G2) (Prod.map (cH H) (cH H) x) q) _ hs hlen ?_) hle
  intro x q _ h0
  obtain ⟨h1, h2, h3, h4⟩ := badOne_zero h0
  rw [P.blt_iff, lenK_eq] at h1
  rw [P.blt_iff, CFSG.KC.LQT.S.lenL_eq, List.length_map] at h2
  simp only [Prod.map_fst, Prod.map_snd] at h3 h4
  rw [getK_H, RP_get Rl G2 h1] at h3 h4
  simp only [Prod.map_fst, Prod.map_snd] at h3 h4
  rw [cH_conj hn, beq_cH hn] at h3 h4
  have hcov := coveredG_of_inj _ hkey Rl (G2.map fun e => (Rl.getD e.1 1, Rl.getD e.2.1 1)) x
    (i := q.1) (j := q.2) (by simpa using h1) h2 h3 h4
  rw [hcov]
  rfl

end Main

end CFSG.KC.LQT.Syl.Pf24

end
