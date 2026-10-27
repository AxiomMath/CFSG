module

public import Certificates.Data.Kernel.Sym6Sq
public import Certificates.Certificate4137
public import Certificates.Certificate24864
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResSqCheck
public import CFSG.Certificates.Kernel.LocalQTSylLSound

public section

namespace CFSG.KC.Sym6Sq

open Equiv CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.W CFSG.KC.LQT.Syl
  CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint
  CFSG.EvenSporadicStandard.M24Std CFSG.EvenSporadicStandard.M24Std.Sym6

theorem strictA_eq {α : Type} (y : ℕ) (k : ℕ → α) : strictA y k = k y := by
  cases y <;> rfl

theorem forceA_eq {α : Type} (L : List ℕ) (k : List ℕ → α) : forceA L k = k L := by
  unfold forceA
  induction L generalizing k with
  | nil => rfl
  | cons x L ih =>
    rw [← ih (fun L' => k (x :: L'))]
    exact strictA_eq x _

theorem revApp_eq : ∀ (l r : List (ℕ × ℕ)), revApp l r = l.reverse ++ r
  | [], _ => rfl
  | x :: l, r => by
    rw [List.reverse_cons, List.append_assoc]
    exact revApp_eq l (x :: r)

theorem lenK_len {α : Type} : ∀ l : List α, lenK l = l.length
  | [] => rfl
  | _ :: l => congrArg Nat.succ (lenK_len l)

theorem cmS (x y : S24) : mul 24 (codeP (x : Perm (Fin 24))) (codeP (y : Perm (Fin 24))) =
    codeP ((x * y : S24) : Perm (Fin 24)) := LQT.P.code_mul (by norm_num) _ _

theorem ciS (x : S24) : inv 24 (codeP (x : Perm (Fin 24))) = codeP ((x⁻¹ : S24) : Perm (Fin 24)) :=
  LQT.P.code_inv (by norm_num) _

theorem c1S : one 24 = codeP ((1 : S24) : Perm (Fin 24)) := LQT.P.code_one

theorem cinjS {x y : S24} (h : codeP (x : Perm (Fin 24)) = codeP (y : Perm (Fin 24))) : x = y :=
  Subtype.ext (LQT.P.code_inj (by norm_num) h)

theorem cm6 (σ τ : Perm (Fin 6)) : mul 6 (codeP σ) (codeP τ) = codeP (σ * τ) :=
  LQT.P.code_mul (by norm_num) σ τ

theorem c16 : one 6 = codeP (1 : Perm (Fin 6)) := LQT.P.code_one

theorem idxK_cons (a : ℕ) (L : List ℕ) (x : ℕ) :
    idxK (a :: L) x = Bool.rec (motive := fun _ => ℕ) (Nat.succ (idxK L x)) 0 (Nat.beq a x) := rfl

theorem idxK_map (L : List S24) (z : S24) :
    idxK (L.map fun x : S24 => codeP (x : Perm (Fin 24))) (codeP (z : Perm (Fin 24))) =
      L.idxOf z := by
  induction L with
  | nil => simp [idxK]
  | cons a L ih =>
    have key : Nat.beq (codeP (a : Perm (Fin 24))) (codeP (z : Perm (Fin 24))) = (a == z) := by
      rw [Bool.eq_iff_iff, beq_iff_eq, LQT.P.beq_iff]
      exact ⟨cinjS, fun h => h ▸ rfl⟩
    rw [List.map_cons, idxK_cons, key, List.idxOf_cons, ih]
    cases a == z <;> rfl

@[expose] def cpair (p : S24 × Perm (Fin 6)) : ℕ × ℕ := (codeP (p.1 : Perm (Fin 24)), codeP p.2)

theorem key6_eq (c : ℕ) : key6 c = ∑ i ∈ Finset.range 6, img c i * 6 ^ i :=
  LQT.P.rec_sum (fun i => img c i * 6 ^ i) 6

theorem key6_code (σ : Perm (Fin 6)) : key6 (codeP σ) = ∑ i : Fin 6, (σ i : ℕ) * 6 ^ (i : ℕ) := by
  rw [key6_eq, ← Fin.sum_univ_eq_sum_range (fun i => img (codeP σ) i * 6 ^ i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : img (codeP σ) i = σ i := LQT.P.img_code (by norm_num) σ i
  rw [e]

theorem digits6 (a b : Fin 6 → ℕ) (ha : ∀ i, a i < 6) (hb : ∀ i, b i < 6)
    (h : ∑ i : Fin 6, a i * 6 ^ (i : ℕ) = ∑ i : Fin 6, b i * 6 ^ (i : ℕ)) : a = b := by
  rw [Fin.sum_univ_six, Fin.sum_univ_six] at h
  have a0 := ha 0
  have a1 := ha 1
  have a2 := ha 2
  have a3 := ha 3
  have a4 := ha 4
  have a5 := ha 5
  have b0 := hb 0
  have b1 := hb 1
  have b2 := hb 2
  have b3 := hb 3
  have b4 := hb 4
  have b5 := hb 5
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at h
  norm_num at h
  have e0 : a 0 = b 0 := by omega
  have e1 : a 1 = b 1 := by omega
  have e2 : a 2 = b 2 := by omega
  have e3 : a 3 = b 3 := by omega
  have e4 : a 4 = b 4 := by omega
  have e5 : a 5 = b 5 := by omega
  funext i
  fin_cases i
  exacts [e0, e1, e2, e3, e4, e5]

theorem key6_inj {σ τ : Perm (Fin 6)} (h : key6 (codeP σ) = key6 (codeP τ)) : σ = τ := by
  rw [key6_code, key6_code] at h
  have := digits6 (fun i => (σ i : ℕ)) (fun i => (τ i : ℕ)) (fun i => (σ i).isLt)
    (fun i => (τ i).isLt) h
  exact Equiv.ext fun i => Fin.ext (congrFun this i)

theorem symStep_eq (st : List (S24 × Perm (Fin 6)) × List (S24 × Perm (Fin 6))) :
    symStep st = ((st.2.flatMap fun p => symGens.map fun g => (g.1 * p.1, g.2 * p.2)).foldl
      addNew st.1, ((st.2.flatMap fun p => symGens.map fun g => (g.1 * p.1, g.2 * p.2)).foldl
      addNew st.1).drop st.1.length) := by
  simp only [symStep, normH_eq, tab_eq]

@[expose] def MK (M : ℕ) (acc : List (S24 × Perm (Fin 6))) : Prop :=
  ∀ σ : Perm (Fin 6), M.testBit (key6 (codeP σ)) = true ↔ ∃ q ∈ acc, q.2 = σ

@[expose] def Rel (acc0 acc : List (S24 × Perm (Fin 6)))
    (st : List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ) : Prop :=
  ∃ M, st = ((acc.map cpair).reverse, ((acc.drop acc0.length).map cpair).reverse, M) ∧
    MK M acc ∧ acc0.length ≤ acc.length

theorem shl1 (v : ℕ) : Nat.shiftLeft 1 v = 2 ^ v := by
  change 1 <<< v = _
  rw [Nat.one_shiftLeft]

theorem shl1' (v : ℕ) : Nat.shiftLeft (nat_lit 1) v = 2 ^ v := shl1 v

theorem addK_eq (a b : ℕ) (A N : List (ℕ × ℕ)) (M : ℕ) :
    addK a b (A, N, M) = strictA (Nat.shiftLeft 1 (key6 b)) fun bit =>
      Bool.rec (motive := fun _ => List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ)
        (strictA (Nat.lor M bit) fun m => ((a, b) :: A, (a, b) :: N, m))
        (A, N, M) (Nat.blt 0 (Nat.land M bit)) := rfl

theorem addK_if (a b : ℕ) (A N : List (ℕ × ℕ)) (M : ℕ) :
    addK a b (A, N, M) = if M.testBit (key6 b) = true then (A, N, M)
      else ((a, b) :: A, (a, b) :: N, M ||| 2 ^ key6 b) := by
  rw [addK_eq]
  simp only [strictA_eq]
  rw [LQT.P.bit_eq, LQT.P.lor_eq]
  cases M.testBit (key6 b) <;> simp

theorem addK_rel {acc0 acc : List (S24 × Perm (Fin 6))}
    {st : List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ} (h : Rel acc0 acc st) (x : S24 × Perm (Fin 6)) :
    Rel acc0 (addNew acc x) (addK (cpair x).1 (cpair x).2 st) := by
  obtain ⟨M, rfl, hM, hl⟩ := h
  rw [addK_if]
  have hiff : M.testBit (key6 (cpair x).2) = true ↔
      (acc.any fun q => decide (q.2 = x.2)) = true := by
    rw [List.any_eq_true]
    exact (hM x.2).trans (by simp)
  by_cases hb : M.testBit (key6 (cpair x).2) = true
  · rw [if_pos hb, addNew, if_pos (hiff.1 hb)]
    exact ⟨M, rfl, hM, hl⟩
  · rw [if_neg hb, addNew, if_neg fun e => hb (hiff.2 e)]
    refine ⟨M ||| 2 ^ key6 (cpair x).2, ?_, ?_, ?_⟩
    · rw [List.drop_append_of_le_length hl]
      simp
    · intro σ
      rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, hM σ, decide_eq_true_iff]
      constructor
      · rintro (⟨q, hq, e⟩ | e)
        · exact ⟨q, List.mem_append_left _ hq, e⟩
        · exact ⟨x, List.mem_append_right _ (List.mem_singleton.2 rfl), key6_inj e⟩
      · rintro ⟨q, hq, e⟩
        rcases List.mem_append.1 hq with hq | hq
        · exact Or.inl ⟨q, hq, e⟩
        · rw [List.mem_singleton.1 hq] at e
          exact Or.inr (by rw [← e]; rfl)
    · simp only [List.length_append, List.length_singleton]
      omega

theorem genK_cons (g : ℕ × ℕ) (gs : List (ℕ × ℕ)) (p : ℕ × ℕ)
    (st : List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ) :
    genK (g :: gs) p st = strictA (mul 24 g.1 p.1) fun a => strictA (mul 6 g.2 p.2) fun b =>
      genK gs p (addK a b st) := rfl

theorem frK_cons (gs : List (ℕ × ℕ)) (p : ℕ × ℕ) (fr : List (ℕ × ℕ))
    (st : List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ) :
    frK gs (p :: fr) st = frK gs fr (genK gs p st) := rfl

theorem stepK_eq (gs : List (ℕ × ℕ)) (A F : List (ℕ × ℕ)) (M : ℕ) :
    stepK gs (A, F, M) = ((frK gs F (A, [], M)).1, revApp (frK gs F (A, [], M)).2.1 [],
      (frK gs F (A, [], M)).2.2) := rfl

theorem cpair_mul1 (g p : S24 × Perm (Fin 6)) :
    mul 24 (cpair g).1 (cpair p).1 = (cpair (g.1 * p.1, g.2 * p.2)).1 := cmS g.1 p.1

theorem cpair_mul2 (g p : S24 × Perm (Fin 6)) :
    mul 6 (cpair g).2 (cpair p).2 = (cpair (g.1 * p.1, g.2 * p.2)).2 := cm6 g.2 p.2

theorem genK_rel (acc0 : List (S24 × Perm (Fin 6))) (p : S24 × Perm (Fin 6)) :
    ∀ (Gs acc : List (S24 × Perm (Fin 6))) (st : List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ),
      Rel acc0 acc st → Rel acc0 ((Gs.map fun g => (g.1 * p.1, g.2 * p.2)).foldl addNew acc)
        (genK (Gs.map cpair) (cpair p) st)
  | [], _, _, h => h
  | g :: Gs, acc, st, h => by
    rw [List.map_cons, List.map_cons, List.foldl_cons, genK_cons]
    simp only [strictA_eq]
    rw [cpair_mul1, cpair_mul2]
    exact genK_rel acc0 p Gs _ _ (addK_rel h _)

theorem frK_rel (acc0 Gs : List (S24 × Perm (Fin 6))) :
    ∀ (fr acc : List (S24 × Perm (Fin 6))) (st : List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ),
      Rel acc0 acc st →
        Rel acc0 ((fr.flatMap fun p => Gs.map fun g => (g.1 * p.1, g.2 * p.2)).foldl addNew acc)
          (frK (Gs.map cpair) (fr.map cpair) st)
  | [], _, _, h => h
  | p :: fr, acc, st, h => by
    rw [List.flatMap_cons, List.foldl_append, List.map_cons, frK_cons]
    exact frK_rel acc0 Gs fr _ _ (genK_rel acc0 p Gs acc st h)

theorem stepK_inv (acc fr : List (S24 × Perm (Fin 6))) (M : ℕ) (hM : MK M acc) :
    ∃ M', stepK (symGens.map cpair) ((acc.map cpair).reverse, fr.map cpair, M) =
      (((symStep (acc, fr)).1.map cpair).reverse, (symStep (acc, fr)).2.map cpair, M') ∧
      MK M' (symStep (acc, fr)).1 := by
  have h0 : Rel acc acc ((acc.map cpair).reverse, [], M) := ⟨M, by simp, hM, le_rfl⟩
  obtain ⟨M', e, hM', -⟩ := frK_rel acc symGens fr acc _ h0
  rw [stepK_eq, e, symStep_eq]
  refine ⟨M', ?_, hM'⟩
  simp only [revApp_eq, List.reverse_reverse, List.append_nil]

theorem gens_eq : gens (codeP (sxS : Perm (Fin 24))) (codeP (sxT : Perm (Fin 24))) =
    symGens.map cpair := by
  have h1 : codeP (Equiv.swap (0 : Fin 6) 1) = 172066817 := by decide +kernel
  have h2 : codeP (finRotate 6) = 5377089 := by decide +kernel
  change [(codeP (sxS : Perm (Fin 24)), 172066817), (codeP (sxT : Perm (Fin 24)), 5377089)] = _
  simp only [symGens, List.map_cons, List.map_nil, cpair, h1, h2]

theorem iter_inv : ∀ n : ℕ, ∃ M, (Nat.rec (motive := fun _ => List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ)
      ([(one 24, one 6)], [(one 24, one 6)], Nat.shiftLeft (nat_lit 1) (key6 (one 6)))
      (fun _ st => stepK (gens (codeP (sxS : Perm (Fin 24))) (codeP (sxT : Perm (Fin 24)))) st)
      n) = (((symStep^[n] ([(1, 1)], [(1, 1)])).1.map cpair).reverse,
        (symStep^[n] ([(1, 1)], [(1, 1)])).2.map cpair, M) ∧
      MK M (symStep^[n] ([(1, 1)], [(1, 1)])).1
  | 0 => by
    refine ⟨Nat.shiftLeft (nat_lit 1) (key6 (one 6)), ?_, ?_⟩
    · have e : cpair (1, 1) = (one 24, one 6) := Prod.ext c1S.symm c16.symm
      simp [e]
    · intro σ
      rw [shl1', Nat.testBit_two_pow, decide_eq_true_iff, c16]
      simp only [Function.iterate_zero, id_eq, List.mem_singleton, exists_eq_left]
      exact ⟨fun h => key6_inj h, fun h => by rw [h]⟩
  | n + 1 => by
    obtain ⟨M, e, hM⟩ := iter_inv n
    obtain ⟨M', e', hM'⟩ := stepK_inv _ _ M hM
    refine ⟨M', ?_, ?_⟩
    · change stepK _ (Nat.rec (motive := fun _ => List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ)
        ([(one 24, one 6)], [(one 24, one 6)], Nat.shiftLeft (nat_lit 1) (key6 (one 6)))
        (fun _ st => stepK (gens (codeP (sxS : Perm (Fin 24))) (codeP (sxT : Perm (Fin 24)))) st)
        n) = _
      rw [e, gens_eq, e', Function.iterate_succ_apply']
    · rw [Function.iterate_succ_apply']
      exact hM'

theorem bfsK_eq : bfsK (codeP (sxS : Perm (Fin 24))) (codeP (sxT : Perm (Fin 24))) =
    (sym6T.map cpair).reverse := by
  obtain ⟨M, e, -⟩ := iter_inv (nat_lit 20)
  unfold bfsK
  rw [e]
  rfl

theorem foldl_addNew_good {Q : S24 × Perm (Fin 6) → Prop} :
    ∀ (L acc : List (S24 × Perm (Fin 6))), (∀ x ∈ acc, Q x) → (acc.map Prod.snd).Nodup →
      (∀ x ∈ L, Q x) → (∀ x ∈ L.foldl addNew acc, Q x) ∧ ((L.foldl addNew acc).map Prod.snd).Nodup
  | [], _, h1, h2, _ => ⟨h1, h2⟩
  | c :: L, acc, h1, h2, h3 => by
    rw [List.foldl_cons]
    refine foldl_addNew_good L _ ?_ ?_ fun x hx => h3 x (List.mem_cons_of_mem _ hx)
    · unfold addNew
      split_ifs
      · exact h1
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact h1 x hx
        · rw [List.mem_singleton.1 hx]
          exact h3 c List.mem_cons_self
    · unfold addNew
      split_ifs with hc
      · exact h2
      · have hnot : c.2 ∉ acc.map Prod.snd := fun hm => by
          obtain ⟨q, hq, e⟩ := List.mem_map.1 hm
          exact hc (List.any_eq_true.2 ⟨q, hq, by simp [e]⟩)
        rw [List.map_append, List.nodup_append]
        refine ⟨h2, List.nodup_singleton _, fun a ha b hb => ?_⟩
        rw [List.map_singleton, List.mem_singleton] at hb
        rintro rfl
        exact hnot (hb ▸ ha)

theorem good_iter : ∀ n : ℕ,
    (∀ x ∈ (symStep^[n] ([(1, 1)], [(1, 1)])).1, QdNorm x.1) ∧
      (∀ x ∈ (symStep^[n] ([(1, 1)], [(1, 1)])).2, QdNorm x.1) ∧
      ((symStep^[n] ([(1, 1)], [(1, 1)])).1.map Prod.snd).Nodup
  | 0 => by
    have h1 : QdNorm (1 : S24) := fun s => by simp
    refine ⟨fun x hx => ?_, fun x hx => ?_, by simp⟩
    · rw [Function.iterate_zero, id_eq, List.mem_singleton] at hx
      rw [hx]
      exact h1
    · rw [Function.iterate_zero, id_eq, List.mem_singleton] at hx
      rw [hx]
      exact h1
  | n + 1 => by
    obtain ⟨h1, h2, h3⟩ := good_iter n
    rw [Function.iterate_succ_apply', symStep_eq]
    have hS : QdNorm sxS := Certificates.certificate24864.2.2.2.2.2.1.norm
    have hT : QdNorm sxT := Certificates.certificate24864.2.2.2.2.2.2.1.norm
    have hL : ∀ x ∈ (symStep^[n] ([(1, 1)], [(1, 1)])).2.flatMap
        (fun p => symGens.map fun g => (g.1 * p.1, g.2 * p.2)), QdNorm x.1 := by
      intro x hx
      obtain ⟨p, hp, hx⟩ := List.mem_flatMap.1 hx
      obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hx
      have hg1 : QdNorm g.1 := by
        simp only [symGens, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl
        exacts [hS, hT]
      exact hg1.mul (h2 p hp)
    obtain ⟨k1, k2⟩ := foldl_addNew_good _ _ h1 h3 hL
    exact ⟨k1, fun x hx => k1 x (List.mem_of_mem_drop hx), k2⟩

def rP : List S24 → ℕ → S24
  | [], _ => 1
  | b :: L, d => (if d.testBit 0 then b else 1) * rP L (d / 2)

theorem elt_rP (B : List S24) (m : ℕ) : ∀ (k : ℕ) (acc : S24) (j : ℕ), j + k ≤ B.length →
    (List.range' j k).foldl (fun acc i => if m.testBit i then acc * B.getD i 1 else acc) acc =
      acc * rP ((B.drop j).take k) (m / 2 ^ j) := by
  intro k
  induction k with
  | zero => intro acc j _; simp [rP]
  | succ k ih =>
    intro acc j hj
    rw [List.range'_succ, List.foldl_cons, ih _ _ (by omega)]
    have hjl : j < B.length := by omega
    have hd : m / 2 ^ j / 2 = m / 2 ^ (j + 1) := by rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
    have ht : (m / 2 ^ j).testBit 0 = m.testBit j := by
      rw [Nat.testBit_zero, Nat.testBit_eq_decide_div_mod_eq]
    rw [List.drop_eq_getElem_cons hjl, List.take_succ_cons, rP, hd, ht,
      List.getD_eq_getElem _ _ hjl]
    split_ifs <;> simp [mul_assoc]

theorem elt_eq_rP {B : List S24} (hB : B.length = 6) (m : ℕ) : m24Elt B m = rP B m := by
  have h := elt_rP B m 6 1 0 (by omega)
  rw [Nat.pow_zero, Nat.div_one, List.drop_zero, List.take_of_length_le (by omega), one_mul,
    ← List.range_eq_range'] at h
  exact h

section Grp

variable {E : List S24} (hE1 : (1 : S24) ∈ E) (hmul : ∀ x ∈ E, ∀ y ∈ E, x * y ∈ E)
  (hsq : ∀ x ∈ E, x * x = 1) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)

include hE1 hmul in
theorem rP_mem {L : List S24} (hL : ∀ b ∈ L, b ∈ E) : ∀ d, rP L d ∈ E := by
  induction L with
  | nil => exact fun _ => hE1
  | cons b L ih =>
    intro d
    refine hmul _ ?_ _ (ih (fun x hx => hL x (List.mem_cons_of_mem _ hx)) _)
    split_ifs
    exacts [hL b List.mem_cons_self, hE1]

theorem xor_div_two (a b : ℕ) : (a ^^^ b) / 2 = a / 2 ^^^ b / 2 :=
  Nat.eq_of_testBit_eq fun i => by
    rw [Nat.testBit_div_two, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_div_two,
      Nat.testBit_div_two]

include hE1 hmul hsq hcomm in
theorem rP_xor {L : List S24} (hL : ∀ b ∈ L, b ∈ E) : ∀ a b, rP L (a ^^^ b) = rP L a * rP L b := by
  induction L with
  | nil => intro a b; simp [rP]
  | cons x L ih =>
    intro a b
    have hx : x ∈ E := hL x List.mem_cons_self
    have hL' : ∀ y ∈ L, y ∈ E := fun y hy => hL y (List.mem_cons_of_mem _ hy)
    simp only [rP]
    rw [xor_div_two, ih hL', Nat.testBit_xor]
    have hc : (if b.testBit 0 = true then x else 1) * rP L (a / 2) =
        rP L (a / 2) * (if b.testBit 0 = true then x else 1) := by
      refine hcomm _ ?_ _ (rP_mem hE1 hmul hL' _)
      split_ifs
      exacts [hx, hE1]
    have ht : (if (a.testBit 0 ^^ b.testBit 0) = true then x else 1) =
        (if a.testBit 0 = true then x else 1) * (if b.testBit 0 = true then x else 1) := by
      cases a.testBit 0 <;> cases b.testBit 0 <;> simp [hsq x hx]
    rw [ht]
    simp only [mul_assoc]
    rw [← mul_assoc (if b.testBit 0 = true then x else 1), hc, mul_assoc]

end Grp

theorem rP_zero : ∀ L : List S24, rP L 0 = 1
  | [] => rfl
  | _ :: L => by simp [rP, rP_zero L]

theorem rP_conj (h : S24) : ∀ (L : List S24) (d : ℕ),
    h * rP L d * h⁻¹ = rP (L.map fun b => h * b * h⁻¹) d
  | [], _ => by simp [rP]
  | b :: L, d => by
    simp only [rP, List.map_cons]
    rw [← rP_conj h L]
    split_ifs <;> group

theorem linK_cons (a : ℕ) (y : List ℕ) (d : ℕ) :
    linK (a :: y) d = (if d.testBit 0 = true then a else 0) ^^^ linK y (d / 2) := by
  have e : linK (a :: y) d =
      (Bool.rec (motive := fun _ => ℕ) 0 a (Nat.beq (d % 2) 1)) ^^^ linK y (d / 2) := rfl
  rw [e, Nat.testBit_zero]
  by_cases h : d % 2 = 1
  · rw [LQT.P.beq_iff.2 h, if_pos (decide_eq_true h)]
  · rw [Bool.eq_false_iff.2 fun e => h (LQT.P.beq_iff.1 e), if_neg (by simpa using h)]

theorem linK_lt : ∀ (y : List ℕ), (∀ a ∈ y, a < 64) → ∀ d, linK y d < 64
  | [], _, _ => by
    change (0 : ℕ) < 64
    norm_num
  | a :: y, hy, d => by
    rw [linK_cons]
    have h1 : (if d.testBit 0 = true then a else 0) < 2 ^ 6 := by
      split_ifs
      · exact hy a List.mem_cons_self
      · norm_num
    have h2 : linK y (d / 2) < 2 ^ 6 :=
      linK_lt y (fun b hb => hy b (List.mem_cons_of_mem _ hb)) _
    exact Nat.xor_lt_two_pow h1 h2

theorem fixL_eq (y : List ℕ) :
    fixL y = ((List.range 64).filter fun m => decide (linK y m = m)).length := by
  have key : ∀ n, Nat.rec (motive := fun _ => ℕ) 0 (fun m acc => Nat.add acc
      (Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.beq (linK y m) m))) n =
      ((List.range n).filter fun m => decide (linK y m = m)).length := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      change Nat.add (Nat.rec (motive := fun _ => ℕ) 0 (fun m acc => Nat.add acc
        (Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.beq (linK y m) m))) n) _ = _
      rw [ih, List.range_succ, List.filter_append, List.length_append]
      by_cases h : linK y n = n
      · rw [LQT.P.beq_iff.2 h]
        simp [h]
      · rw [Bool.eq_false_iff.2 fun e => h (LQT.P.beq_iff.1 e)]
        simp [h]
  exact key 64

theorem count_eq (h : S24)
    (hlt : ∀ b ∈ m24E1B, m24E1l.idxOf (h * b * h⁻¹) < 64) :
    (m24E1l.filter fun x => decide (h * x * h⁻¹ = x)).length =
      ((List.range 64).filter fun m =>
        decide (linK (m24E1B.map fun b => m24E1l.idxOf (h * b * h⁻¹)) m = m)).length := by
  obtain ⟨hlen, hnd, h1, hmul, hsq, hcomm, hbas⟩ := Certificates.certificate4137.1
  have hB6 : m24E1B.length = 6 := by
    rw [m24E1B, m24Bas, List.length_map]
    rfl
  have hf : ∀ m, m24Elt m24E1B m = rP m24E1B m := elt_eq_rP hB6
  have hEl : m24E1l = (List.range 64).map (m24Elt m24E1B) := rfl
  have hget : ∀ i (hi : i < m24E1l.length), m24E1l[i] = m24Elt m24E1B i := by
    intro i hi
    simp [m24E1l, m24Lst]
  have hconj : m24E1B.map (fun b => h * b * h⁻¹) =
      (m24E1B.map fun b => m24E1l.idxOf (h * b * h⁻¹)).map (rP m24E1B) := by
    rw [List.map_map]
    refine List.map_congr_left fun b hb => ?_
    have hl : m24E1l.idxOf (h * b * h⁻¹) < m24E1l.length := hlen ▸ hlt b hb
    have e := List.getElem_idxOf hl
    rw [hget, hf] at e
    exact e.symm
  have hy : ∀ a ∈ m24E1B.map (fun b => m24E1l.idxOf (h * b * h⁻¹)), a < 64 := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
    exact hlt b hb
  have hinj : ∀ a < 64, ∀ b < 64, rP m24E1B a = rP m24E1B b → a = b := by
    intro a ha b hb e
    rw [← hf, ← hf] at e
    rw [hEl] at hnd
    exact List.inj_on_of_nodup_map hnd (List.mem_range.2 ha) (List.mem_range.2 hb) e
  have hBE : ∀ b ∈ m24E1B, b ∈ m24E1l := hbas
  rw [hEl, List.filter_map, List.length_map]
  congr 1
  refine List.filter_congr fun m hm => ?_
  have hm' := List.mem_range.1 hm
  simp only [Function.comp_apply]
  rw [hf, rP_conj, hconj]
  have hlin : ∀ (y : List ℕ) (d : ℕ), rP (y.map (rP m24E1B)) d = rP m24E1B (linK y d) := by
    intro y
    induction y with
    | nil => intro d; exact (rP_zero m24E1B).symm
    | cons a y ih =>
      intro d
      rw [linK_cons, rP_xor h1 hmul hsq hcomm hBE, ← ih]
      simp only [List.map_cons, rP]
      split_ifs
      · rfl
      · rw [rP_zero]
  rw [hlin]
  exact decide_eq_decide.2 ⟨fun e => hinj _ (linK_lt _ hy _) _ hm' e, fun e => congrArg _ e⟩

theorem coset {w s e : S24} (hw : QdNorm w) (hs : QdNorm s)
    (he : e ∈ m24E1l) :
    (w * e * s ∈ m24E1l ↔ w * s ∈ m24E1l) ∧
      (w * e * s * (w * e * s) ∈ m24E1l ↔ w * s * (w * s) ∈ m24E1l) ∧
      ∀ x ∈ m24E1l, w * e * s * x * (w * e * s)⁻¹ = w * s * x * (w * s)⁻¹ := by
  obtain ⟨-, -, -, hmul, hsq, hcomm, -⟩ := Certificates.certificate4137.1
  have hf : w * e * w⁻¹ ∈ m24E1l := (hw e).1 he
  have hh : QdNorm (w * s) := hw.mul hs
  have key : ∀ u ∈ m24E1l, ∀ z : S24, u * z ∈ m24E1l ↔ z ∈ m24E1l := by
    intro u hu z
    refine ⟨fun h => ?_, fun h => hmul u hu z h⟩
    have e1 : z = u * (u * z) := by rw [← mul_assoc, hsq u hu, one_mul]
    rw [e1]
    exact hmul u hu _ h
  refine ⟨?_, ?_, fun x hx => ?_⟩
  · have e1 : w * e * s = w * e * w⁻¹ * (w * s) := by group
    rw [e1]
    exact key _ hf _
  · have e1 : w * e * s * (w * e * s) =
        w * e * w⁻¹ * (w * s * (w * e * w⁻¹) * (w * s)⁻¹) * (w * s * (w * s)) := by group
    rw [e1]
    exact key _ (hmul _ hf _ ((hh _).1 hf)) _
  · have hz : w * s * x * (w * s)⁻¹ ∈ m24E1l := (hh x).1 hx
    have e1 : w * e * s * x * (w * e * s)⁻¹ =
        w * e * w⁻¹ * (w * s * x * (w * s)⁻¹) * (w * e * w⁻¹)⁻¹ := by group
    rw [e1, hcomm _ hf _ hz, mul_assoc, mul_inv_cancel, mul_one]

theorem sqRun_cons (E B W : List ℕ) (e o : ℕ) (p : ℕ × ℕ) (T : List (ℕ × ℕ)) :
    sqRun E B W e o (p :: T) = CFSG.KC.Ord.andB (impB (Nat.beq (mul 6 p.2 p.2) (one 6))
      (allL W fun w => strictA (mul 24 w p.1) fun h => liftK E B e o h p.2))
      (sqRun E B W e o T) := rfl

theorem sqRun_sound (E B W : List ℕ) (e o : ℕ) : ∀ T : List (ℕ × ℕ), sqRun E B W e o T = true →
    ∀ p ∈ T, mul 6 p.2 p.2 = one 6 → ∀ w ∈ W, liftK E B e o (mul 24 w p.1) p.2 = true
  | [], _ => by simp
  | p :: T, h => by
    rw [sqRun_cons, LQT.P.andB_iff, LQT.P.impB_iff, LQT.P.beq_iff, LQT.P.allL_iff] at h
    intro q hq hq2 w hw
    rcases List.mem_cons.1 hq with rfl | hq
    · have := h.1 hq2 w hw
      rwa [strictA_eq] at this
    · exact sqRun_sound E B W e o T h.2 q hq hq2 w hw

theorem cntK_eq (E B : List ℕ) (h hi c : ℕ) : cntK E B h hi c =
    CFSG.KC.Ord.andB (below64 (B.map fun b => idxK E (mul 24 (mul 24 h b) hi)))
      (Nat.beq (fixL (B.map fun b => idxK E (mul 24 (mul 24 h b) hi))) c) := by
  have e : ∀ B : List ℕ, List.rec (motive := fun _ => List ℕ) []
      (fun b _ ih => idxK E (mul 24 (mul 24 h b) hi) :: ih) B =
      B.map fun b => idxK E (mul 24 (mul 24 h b) hi) := by
    intro B
    induction B with
    | nil => rfl
    | cons b B ih =>
      rw [List.map_cons]
      exact congrArg _ ih
  unfold cntK
  rw [forceA_eq, e]

theorem mem_iff (z : S24) :
    idxK (m24E1l.map fun x : S24 => codeP (x : Perm (Fin 24))) (codeP (z : Perm (Fin 24))) < 64 ↔
      z ∈ m24E1l := by
  rw [idxK_map, ← Certificates.certificate4137.1.1, List.idxOf_lt_length_iff]

theorem lift_sound (h : S24) (σ : Perm (Fin 6)) (e o : ℕ)
    (hk : liftK (m24E1l.map fun x : S24 => codeP (x : Perm (Fin 24)))
      (m24E1B.map fun x : S24 => codeP (x : Perm (Fin 24))) e o (codeP (h : Perm (Fin 24)))
      (codeP σ) = true)
    (h2 : h * h ∈ m24E1l) (hn : h ∉ m24E1l) :
    (m24E1l.filter fun x => decide (h * x * h⁻¹ = x)).length =
      if Perm.sign σ = 1 then e else o := by
  unfold liftK at hk
  rw [LQT.P.impB_iff, LQT.P.andB_iff, LQT.P.notB_iff, LQT.P.blt_iff, LQT.P.blt_iff, cmS, mem_iff, mem_iff] at hk
  have hc := hk ⟨h2, hn⟩
  rw [cntK_eq, LQT.P.andB_iff, LQT.P.beq_iff, ciS, List.map_map] at hc
  simp only [Function.comp_def, cmS, idxK_map] at hc
  obtain ⟨hb, hf⟩ := hc
  unfold below64 at hb
  rw [LQT.P.allL_iff] at hb
  have hlt : ∀ b ∈ m24E1B, m24E1l.idxOf (h * b * h⁻¹) < 64 := fun b hb' =>
    LQT.P.blt_iff.1 (hb _ (List.mem_map_of_mem hb'))
  rw [count_eq h hlt, ← fixL_eq, hf]
  have hev : even 6 (codeP σ) = true ↔ Perm.sign σ = 1 := LQT.P.even_code (by norm_num) σ
  cases hb' : even 6 (codeP σ)
  · have : ¬ Perm.sign σ = 1 := fun e' => by
      have := hev.2 e'
      rw [hb'] at this
      exact Bool.false_ne_true this
    rw [if_neg this]
  · rw [if_pos (hev.1 hb')]

theorem codeW {G : List ℕ}
    (hG : [m24a, m24b].map (fun x : S24 => codeP (x : Perm (Fin 24))) = G) (w : List ℤ) :
    codeP ((m24Cj w : S24) : Perm (Fin 24)) = evalZK 24 G w := by
  have := codes_gens NativeSporadic.M24 (by decide) [m24a, m24b] hG [w]
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at this
  exact this

theorem codeS {G : List ℕ}
    (hG : [m24a, m24b].map (fun x : S24 => codeP (x : Perm (Fin 24))) = G) :
    codeP (sxS : Perm (Fin 24)) = evalZK 24 G wordSxS := codeW hG wordSxS

theorem codeT {G : List ℕ}
    (hG : [m24a, m24b].map (fun x : S24 => codeP (x : Perm (Fin 24))) = G) :
    codeP (sxT : Perm (Fin 24)) = evalZK 24 G wordSxT := codeW hG wordSxT

theorem codeO {G : List ℕ}
    (hG : [m24a, m24b].map (fun x : S24 => codeP (x : Perm (Fin 24))) = G) :
    codeP (qdOmega : Perm (Fin 24)) = evalZK 24 G wordQdOmega := codeW hG wordQdOmega

theorem codesB {G : List ℕ}
    (hG : [m24a, m24b].map (fun x : S24 => codeP (x : Perm (Fin 24))) = G) :
    m24E1B.map (fun x : S24 => codeP (x : Perm (Fin 24))) = rlGK 24 G m24RGens m24E1Bw :=
  codes_eval NativeSporadic.M24 (by decide) [m24a, m24b] hG m24RGens m24E1Bw

theorem codesE {G : List ℕ}
    (hG : [m24a, m24b].map (fun x : S24 => codeP (x : Perm (Fin 24))) = G) :
    m24E1l.map (fun x : S24 => codeP (x : Perm (Fin 24))) =
      lstK 24 6 (rlGK 24 G m24RGens m24E1Bw) :=
  lst_codes _ (codesB hG)

theorem normChk_sound {G : List ℕ}
    (hG : [m24a, m24b].map (fun x : S24 => codeP (x : Perm (Fin 24))) = G)
    (h : normChk G m24RGens m24E1Bw wordQdOmega = true) : QdNormChk qdOmega := by
  unfold normChk at h
  rw [forceA_eq, ← codesE hG, ← codeO hG] at h
  unfold CFSG.KC.Sym6Sq.normK at h
  rw [strictA_eq, ciS, LQT.P.allL_iff] at h
  intro x hx
  have := h _ (List.mem_map_of_mem hx)
  rw [LQT.P.andB_iff, LQT.P.blt_iff, LQT.P.blt_iff, cmS, cmS, cmS, cmS, mem_iff, mem_iff] at this
  exact this

theorem qdNorm_w (hΩ : QdNormChk qdOmega) {w : S24}
    (hw : w ∈ [1, qdOmega, qdOmega⁻¹]) : QdNorm w := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · exact fun s => by simp
  · exact hΩ.norm
  · refine QdNormChk.norm fun x hx => ?_
    rw [inv_inv]
    exact ⟨(hΩ x hx).2, (hΩ x hx).1⟩

theorem mem_sxK0 {k : S24} (hk : k ∈ sxK0) :
    ∃ w ∈ [1, qdOmega, qdOmega⁻¹], ∃ e ∈ m24E1l, k = w * e := by
  simp only [sxK0, List.mem_append, List.mem_map] at hk
  rcases hk with (hk | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩
  · exact ⟨1, by simp, k, hk, (one_mul k).symm⟩
  · exact ⟨qdOmega, by simp, e, he, rfl⟩
  · exact ⟨qdOmega⁻¹, by simp, e, he, rfl⟩

theorem sqChk_run {G : List ℕ}
    (hG : [m24a, m24b].map (fun x : S24 => codeP (x : Perm (Fin 24))) = G)
    (h : sqChk G m24RGens m24E1Bw wordSxS wordSxT wordQdOmega 16 8 = true) :
    ∀ p ∈ sym6T, p.2 * p.2 = 1 → ∀ w ∈ [1, qdOmega, qdOmega⁻¹],
      liftK (m24E1l.map fun x : S24 => codeP (x : Perm (Fin 24)))
        (m24E1B.map fun x : S24 => codeP (x : Perm (Fin 24))) 16 8
        (codeP ((w * p.1 : S24) : Perm (Fin 24))) (codeP p.2) = true := by
  unfold sqChk at h
  simp only [forceA_eq, strictA_eq] at h
  rw [← codesE hG, ← codesB hG, ← codeO hG, ← codeS hG, ← codeT hG, bfsK_eq] at h
  intro p hp hp2 w hw
  have hW : [one 24, codeP (qdOmega : Perm (Fin 24)), inv 24 (codeP (qdOmega : Perm (Fin 24)))] =
      [1, qdOmega, qdOmega⁻¹].map fun x : S24 => codeP (x : Perm (Fin 24)) := by
    rw [c1S, ciS]
    rfl
  have h2 : mul 6 (cpair p).2 (cpair p).2 = one 6 := by
    rw [cpair_mul2, c16]
    exact congrArg codeP hp2
  have := sqRun_sound _ _ _ 16 8 _ h (cpair p) (List.mem_reverse.2 (List.mem_map_of_mem hp)) h2
    (codeP (w : Perm (Fin 24))) (hW ▸ List.mem_map_of_mem hw)
  have e : mul 24 (codeP (w : Perm (Fin 24))) (cpair p).1 = codeP ((w * p.1 : S24) : Perm (Fin 24)) :=
    cmS w p.1
  rwa [e] at this

theorem sym6SqData_of {G : List ℕ}
    (hG : [m24a, m24b].map (fun x : S24 => codeP (x : Perm (Fin 24))) = G)
    (hom : normChk G m24RGens m24E1Bw wordQdOmega = true)
    (hsq : sqChk G m24RGens m24E1Bw wordSxS wordSxT wordQdOmega 16 8 = true) : Sym6SqData := by
  have hΩ := normChk_sound hG hom
  have hrun := sqChk_run hG hsq
  intro p hp hp2 k hk hk2 hkn
  obtain ⟨w, hw, e, he, rfl⟩ := mem_sxK0 hk
  have hs : QdNorm p.1 := (good_iter 20).1 p hp
  obtain ⟨ha, hb, hc⟩ := coset (qdNorm_w hΩ hw) hs he
  rw [List.filter_congr fun x hx => by rw [hc x hx]]
  exact lift_sound (w * p.1) p.2 16 8 (hrun p hp hp2 w hw) (hb.1 hk2) fun h' => hkn (ha.2 h')

theorem sym6InvData_of {G : List ℕ}
    (hG : [m24a, m24b].map (fun x : S24 => codeP (x : Perm (Fin 24))) = G)
    (hbfs : bfsChk G wordSxS wordSxT = true)
    (hom : normChk G m24RGens m24E1Bw wordQdOmega = true)
    (hsq : sqChk G m24RGens m24E1Bw wordSxS wordSxT wordQdOmega 16 8 = true) : Sym6InvData := by
  have hsd := sym6SqData_of hG hom hsq
  have h1 : (1 : S24) ∈ m24E1l := Certificates.certificate4137.1.2.2.1
  unfold bfsChk at hbfs
  simp only [strictA_eq] at hbfs
  rw [← codeS hG, ← codeT hG] at hbfs
  rw [bfsK_eq, LQT.P.andB_iff, LQT.P.beq_iff, LQT.P.beq_iff, lenK_len, List.length_reverse,
    List.length_map, cmS, c1S] at hbfs
  obtain ⟨hlen, hss⟩ := hbfs
  refine ⟨fun σ => ?_, fun p hp hp2 k hk hinv hn => hsd p hp hp2 k hk (hinv ▸ h1) hn, ?_⟩
  · have hnd : (sym6T.map Prod.snd).Nodup := (good_iter 20).2.2
    have hc : (sym6T.map Prod.snd).toFinset = Finset.univ := by
      refine Finset.eq_univ_of_card _ ?_
      rw [List.toFinset_card_of_nodup hnd, List.length_map, hlen, Fintype.card_perm,
        Fintype.card_fin]
      rfl
    have hσ : σ ∈ (sym6T.map Prod.snd).toFinset := hc ▸ Finset.mem_univ σ
    obtain ⟨p, hp, e⟩ := List.mem_map.1 (List.mem_toFinset.1 hσ)
    exact ⟨p, hp, e⟩
  · refine ⟨1, List.mem_append_left _ (List.mem_append_left _ h1), ?_⟩
    rw [one_mul]
    exact cinjS hss

end CFSG.KC.Sym6Sq

end
