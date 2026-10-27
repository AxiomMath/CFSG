module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuNEChecks
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuAsmAlign

public section

namespace CFSG.ComponentClassification.GMS78.RuNE

open Subgroup CFSG.CosetTable CFSG.ComponentClassification.GMS78.RuPi7
  CFSG.ComponentClassification.GMS78.RuAsm
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge.SurjD.Native

theorem pi7Word_cons (l : Fin 7 × Bool) (w : List (Fin 7 × Bool)) :
    pi7Word (l :: w) = pi7Word [l] * pi7Word w := by
  rw [← pi7Word_append]
  rfl

theorem pi7Word_flatten_replicate (u : List (Fin 7 × Bool)) (k : ℕ) :
    pi7Word (List.replicate k u).flatten = pi7Word u ^ k := by
  rw [pi7Word, mk_flatten_replicate, map_pow]
  rfl

theorem pi7Word_flatMap_mem {H : Subgroup Pi7} {β : Type*} (l : List β)
    (f : β → List (Fin 7 × Bool)) (h : ∀ j ∈ l, pi7Word (f j) ∈ H) :
    pi7Word (l.flatMap f) ∈ H := by
  induction l with
  | nil => rw [List.flatMap_nil, pi7Word_nil]; exact one_mem _
  | cons a l ih =>
    rw [List.flatMap_cons, pi7Word_append]
    exact mul_mem (h a (by simp)) (ih fun j hj => h j (by simp [hj]))

noncomputable def neW (u : List (Fin 7)) : Pi7 := pi7Word (posWord u)

theorem neW_nil : neW [] = 1 := pi7Word_nil

theorem neW_cons (i : Fin 7) (u : List (Fin 7)) :
    neW (i :: u) = PresentedGroup.of i * neW u := by
  rw [neW, posWord, List.map_cons, pi7Word_cons, pi7Word_letter]
  rfl

theorem neW_mem_letterSub {l u : List (Fin 7)} (hu : ∀ i ∈ u, i ∈ l) : neW u ∈ letterSub l :=
  pi7Word_mem_letterSub fun p hp => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hp
    exact hu i hi

theorem neW_w0 : neW [5, 0, 2, 6] =
    PresentedGroup.of 5 * PresentedGroup.of 0 * PresentedGroup.of 2 * PresentedGroup.of 6 := by
  rw [neW_cons, neW_cons, neW_cons, neW_cons, neW_nil, mul_one, mul_assoc, mul_assoc]

theorem getD_mem_or {α : Type*} (l : List α) (n : ℕ) (d : α) :
    l.getD n d ∈ l ∨ l.getD n d = d := by
  by_cases h : n < l.length
  · left
    rw [List.getD_eq_getElem _ _ h]
    exact List.getElem_mem h
  · right
    exact List.getD_eq_default _ _ (Nat.le_of_not_lt h)

theorem conj_mul_conj {G : Type*} [Group G] (a b t : G) :
    a * b * t * (a * b)⁻¹ = a * (b * t * b⁻¹) * a⁻¹ := by
  group

theorem ne_basis :
    ∀ p ∈ neBasisEqs, pi7Word p.1 = pi7Word p.2 :=
  fun p hp => pi7Word_eq_of_wordProd (ne_basisEqs p hp)

theorem ne_act :
    (∀ j < 6, ∀ i < 64,
      (neMulTab.getD j []).getD i 0 < 64 ∧ (neConjTab.getD j []).getD i 0 < 64) ∧
    (∀ k < 6, ∀ j < 64, ∃ i < 64, (neConjTab.getD k []).getD i 0 = j) ∧
    (∀ u ∈ neActWords, ∀ l ∈ u, l ∈ ([0, 1, 2, 3, 5] : List (Fin 7))) ∧
    (∀ u ∈ neOrbitWords, ∀ l ∈ u, l ∈ ([0, 1, 2, 3, 4, 5] : List (Fin 7))) ∧
    (neActWords.map neActPerm).Nodup ∧ neActWords.length = 192 ∧ neOrbitWords.length = 20 ∧
    ∀ k < 20, ∀ l < 20, k < l → ∃ t ∈ neOrbitWit, t.1 = k ∧ t.2.1 = l := by
  have h := ne_actCheck
  simp only [neActCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    List.any_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
    at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, fun k hk l hl hkl => ?_⟩
  rcases h8 k hk l hl with h | h
  · exact absurd hkl h
  · exact h

theorem ne_w0 :
    ∀ i < 64, (neActPerm [5, 0, 2, 6]).getD i 0 ≠ i ∨ i = 0 := by
  have h := ne_w0Check
  simp only [neW0Check, List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq] at h
  exact h

theorem mem_neBasis_comm {j k : ℕ} (hj : j < 6) (hk : k < 6) :
    (ruE0Words.getD j [] ++ ruE0Words.getD k [], ruE0Words.getD k [] ++ ruE0Words.getD j []) ∈
      neBasisEqs :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩⟩)))

theorem mem_neBasis_sq {j : ℕ} (hj : j < 6) :
    (ruE0Words.getD j [] ++ ruE0Words.getD j [], []) ∈ neBasisEqs :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)))

theorem mem_neBasis_conj {k j : ℕ} (hk : k < 6) (hj : j < 6) :
    ((neConjLetters.getD k 0, true) :: ruE0Words.getD j [] ++ [(neConjLetters.getD k 0, false)],
      neTWord ((neConjTab.getD k []).getD (2 ^ j) 0)) ∈ neBasisEqs :=
  List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨k, List.mem_range.2 hk,
    List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩⟩))

theorem mem_neBasis_w0 : ((List.replicate 7 neW0Word).flatten, []) ∈ neBasisEqs :=
  List.mem_append_right _ (List.mem_singleton.2 rfl)

theorem xor_lt_64 {a b : ℕ} (ha : a < 64) (hb : b < 64) : a ^^^ b < 64 :=
  Nat.xor_lt_two_pow (n := 6) ha hb

theorem two_pow_lt_64 {j : ℕ} (hj : j < 6) : 2 ^ j < 64 :=
  calc 2 ^ j < 2 ^ 6 := Nat.pow_lt_pow_right (by norm_num) hj
    _ = 64 := by norm_num

theorem testBit_xor_two_pow_ne {i m j : ℕ} (h : j ≠ m) : (i ^^^ 2 ^ m).testBit j = i.testBit j := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  simp [Ne.symm h]

theorem testBit_xor_two_pow_self (i m : ℕ) : (i ^^^ 2 ^ m).testBit m = !i.testBit m := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow_self]
  cases i.testBit m <;> rfl

@[expose] def xorBits (l : List ℕ) : ℕ := l.foldr (fun j acc => 2 ^ j ^^^ acc) 0

theorem testBit_xorBits : ∀ {L : List ℕ}, L.Nodup → ∀ k, (xorBits L).testBit k = decide (k ∈ L)
  | [], _, k => by simp [xorBits]
  | j :: L, hL, k => by
    rw [List.nodup_cons] at hL
    have ih := testBit_xorBits hL.2 k
    change (2 ^ j ^^^ xorBits L).testBit k = _
    rw [Nat.testBit_xor, Nat.testBit_two_pow, ih]
    by_cases hk : k = j
    · subst hk
      simp [hL.1]
    · simp [hk, Ne.symm hk]

theorem xorBits_bits {a : ℕ} (ha : a < 64) :
    xorBits ((List.range 6).filter fun j => a.testBit j) = a := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_xorBits ((List.nodup_range).filter _)]
  by_cases hk : k < 6
  · simp [List.mem_filter, hk]
  · have h1 : a.testBit k = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (by
        calc 64 = 2 ^ 6 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [List.mem_filter, hk, h1]

noncomputable def neT (i : ℕ) : Pi7 := pi7Word (neTWord i)

noncomputable def neE (j : ℕ) : Pi7 := pi7Word (ruE0Words.getD j [])

theorem neT_zero : neT 0 = 1 := by
  rw [neT, show neTWord 0 = [] by decide, pi7Word_nil]

theorem neE_mem (j : ℕ) : neE j ∈ ruE0 := by
  rcases getD_mem_or ruE0Words j [] with h | h
  · exact subset_closure ⟨_, h, rfl⟩
  · rw [neE, h, pi7Word_nil]
    exact one_mem _

theorem neT_mem (i : ℕ) : neT i ∈ ruE0 :=
  pi7Word_flatMap_mem _ _ fun j _ => neE_mem j

theorem exists_neE {y : Pi7} (hy : y ∈ pi7Word '' {w | w ∈ ruE0Words}) : ∃ j < 6, neE j = y := by
  obtain ⟨w, hw, rfl⟩ := hy
  have hw' : w ∈ ruE0Words := hw
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw'
  exact ⟨j, hj, by rw [neE, List.getD_eq_getElem _ _ hj]⟩

theorem pi7Word_flatMap {β : Type*} (l : List β) (f : β → List (Fin 7 × Bool)) :
    pi7Word (l.flatMap f) = (l.map fun x => pi7Word (f x)).prod := by
  induction l with
  | nil => rw [List.flatMap_nil, pi7Word_nil, List.map_nil, List.prod_nil]
  | cons a l ih => rw [List.flatMap_cons, pi7Word_append, ih, List.map_cons, List.prod_cons]

noncomputable def neP (n i : ℕ) : Pi7 := (((List.range n).filter fun j => i.testBit j).map neE).prod

theorem neT_eq_neP (i : ℕ) : neT i = neP 6 i := by
  rw [neT, neTWord, pi7Word_flatMap]
  rfl

theorem neP_succ (n i : ℕ) : neP (n + 1) i = neP n i * (if i.testBit n then neE n else 1) := by
  simp only [neP, List.range_succ, List.filter_append, List.map_append, List.prod_append]
  congr 1
  by_cases h : i.testBit n <;> simp [h]

theorem neP_xor_high {n m : ℕ} (hm : n ≤ m) (i : ℕ) : neP n (i ^^^ 2 ^ m) = neP n i := by
  unfold neP
  congr 2
  refine List.filter_congr fun j hj => ?_
  rw [testBit_xor_two_pow_ne (by have := List.mem_range.1 hj; omega)]

section Facts

theorem neE_comm {j k : ℕ} (hj : j < 6) (hk : k < 6) : neE j * neE k = neE k * neE j := by
  have h := ne_basis _ (mem_neBasis_comm hj hk)
  rw [pi7Word_append, pi7Word_append] at h
  exact h

theorem neE_mul_self {j : ℕ} (hj : j < 6) : neE j * neE j = 1 := by
  have h := ne_basis _ (mem_neBasis_sq hj)
  rw [pi7Word_append, pi7Word_nil] at h
  exact h

theorem conj_neE_tab {k j : ℕ} (hk : k < 6) (hj : j < 6) :
    PresentedGroup.of (neConjLetters.getD k 0) * neE j *
        (PresentedGroup.of (neConjLetters.getD k 0))⁻¹ =
      neT ((neConjTab.getD k []).getD (2 ^ j) 0) := by
  have h := ne_basis _ (mem_neBasis_conj hk hj)
  rw [pi7Word_append, pi7Word_cons, pi7Word_letter, pi7Word_letter_inv] at h
  exact h

theorem w0_pow_seven :
    (PresentedGroup.of 5 * PresentedGroup.of 0 * PresentedGroup.of 2 * PresentedGroup.of 6 :
      Pi7) ^ 7 = 1 := by
  have h := ne_basis _ mem_neBasis_w0
  rw [pi7Word_flatten_replicate, pi7Word_nil] at h
  rw [← neW_w0]
  exact h

theorem neE_comm_neP {j : ℕ} (hj : j < 6) (i : ℕ) :
    ∀ {n : ℕ}, n ≤ 6 → neE j * neP n i = neP n i * neE j
  | 0, _ => by simp [neP]
  | n + 1, hn => by
    rw [neP_succ, ← mul_assoc, neE_comm_neP hj i (by omega), mul_assoc, mul_assoc]
    congr 1
    split_ifs
    · exact neE_comm hj (by omega)
    · rw [mul_one, one_mul]

theorem neE_mul_neP : ∀ {n : ℕ}, n ≤ 6 → ∀ {j : ℕ} (i : ℕ), j < n →
    neE j * neP n i = neP n (i ^^^ 2 ^ j)
  | 0, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, hn, j, i, hj => by
    rw [neP_succ, neP_succ, ← mul_assoc]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · rw [neE_mul_neP (by omega) i hj, testBit_xor_two_pow_ne (by omega)]
    · rw [neE_comm_neP (by omega) i (by omega), neP_xor_high le_rfl, testBit_xor_two_pow_self,
        mul_assoc]
      congr 1
      cases h : i.testBit j
      · simp
      · simp [neE_mul_self (j := j) (by omega)]

theorem neE_mul_neT {j : ℕ} (hj : j < 6) (i : ℕ) : neE j * neT i = neT (i ^^^ 2 ^ j) := by
  rw [neT_eq_neP, neT_eq_neP]
  exact neE_mul_neP le_rfl i hj

theorem neT_mul {a : ℕ} (ha : a < 64) (b : ℕ) : neT a * neT b = neT (a ^^^ b) := by
  have h : ∀ L : List ℕ, (∀ j ∈ L, j < 6) → ((L.map neE).prod * neT b = neT (xorBits L ^^^ b)) := by
    intro L hL
    induction L with
    | nil => simp [xorBits]
    | cons j L ih =>
      rw [List.map_cons, List.prod_cons, mul_assoc,
        ih fun j' hj' => hL j' (List.mem_cons_of_mem _ hj'), neE_mul_neT (hL j List.mem_cons_self)]
      change neT _ = neT ((2 ^ j ^^^ xorBits L) ^^^ b)
      rw [Nat.xor_assoc, Nat.xor_comm (2 ^ j), Nat.xor_assoc, Nat.xor_comm b]
  have h2 := h ((List.range 6).filter fun j => a.testBit j) fun j hj =>
    List.mem_range.1 (List.mem_of_mem_filter hj)
  rw [xorBits_bits ha] at h2
  rw [neT_eq_neP a]
  exact h2

theorem ruE0_comm {x y : Pi7} (hx : x ∈ ruE0) (hy : y ∈ ruE0) : x * y = y * x := by
  have hcomm : ∀ a ∈ pi7Word '' {w | w ∈ ruE0Words}, ∀ b ∈ pi7Word '' {w | w ∈ ruE0Words},
      a * b = b * a := by
    intro a ha b hb
    obtain ⟨j, hj, rfl⟩ := exists_neE ha
    obtain ⟨k, hk, rfl⟩ := exists_neE hb
    exact neE_comm hj hk
  have h1 : closure (pi7Word '' {w | w ∈ ruE0Words}) ≤
      centralizer (pi7Word '' {w | w ∈ ruE0Words}) :=
    (closure_le _).2 fun a ha => mem_centralizer_iff.2 fun b hb => hcomm b hb a ha
  exact (mem_centralizer_iff.1 (closure_le_centralizer_centralizer _ hx) y (h1 hy)).symm

theorem conj_neT_tab {k i : ℕ} (hk : k < 6) (hi : i < 64) :
    PresentedGroup.of (neConjLetters.getD k 0) * neT i *
        (PresentedGroup.of (neConjLetters.getD k 0))⁻¹ =
      neT ((neConjTab.getD k []).getD i 0) := by
  set g : Pi7 := PresentedGroup.of (neConjLetters.getD k 0)
  set c : ℕ → ℕ := fun j => (neConjTab.getD k []).getD (2 ^ j) 0 with hc
  set L := (List.range 6).filter fun j => i.testBit j with hL
  have hL6 : ∀ j ∈ L, j < 6 := fun j hj => List.mem_range.1 (List.mem_of_mem_filter hj)
  have hconj : g * (L.map neE).prod * g⁻¹ = (L.map fun j => neT (c j)).prod := by
    have e := map_list_prod (MulAut.conj g) (L.map neE)
    simp only [MulAut.conj_apply, List.map_map] at e
    rw [e]
    congr 1
    refine List.map_congr_left fun j hj => ?_
    simp only [Function.comp_apply]
    exact conj_neE_tab hk (hL6 j hj)
  have hfold : ∀ L' : List ℕ, (∀ j ∈ L', j < 6) → ∀ a < 64,
      neT a * (L'.map fun j => neT (c j)).prod = neT (L'.foldl (fun a j => a ^^^ c j) a) := by
    intro L' hL'
    induction L' with
    | nil => intro a _; simp
    | cons j L' ih =>
      intro a ha
      have hcj : c j < 64 := (ne_act.1 k hk (2 ^ j) (two_pow_lt_64 (hL' j List.mem_cons_self))).2
      rw [List.map_cons, List.prod_cons, ← mul_assoc, neT_mul ha,
        ih (fun j' hj' => hL' j' (List.mem_cons_of_mem _ hj')) _ (xor_lt_64 ha hcj)]
      rfl
  rw [ne_conjLin k hk i hi, neT_eq_neP i]
  change g * (L.map neE).prod * g⁻¹ = neT (L.foldl (fun a j => a ^^^ c j) 0)
  rw [hconj, ← one_mul (List.prod _), ← neT_zero]
  exact hfold L hL6 0 (by norm_num)

theorem neT_injective {i k : ℕ} (hi : i < 64) (hk : k < 64) (h : neT i = neT k) : i = k := by
  by_contra hne
  have h0 : i ^^^ k ≠ 0 := fun e => hne (xor_eq_zero_iff.mp e)
  apply pi7Word_ne_of_wordProd (u := neTWord (i ^^^ k)) (v := []) (ne_tNe _ (xor_lt_64 hi hk) h0)
  rw [pi7Word_nil]
  change neT (i ^^^ k) = 1
  rw [← neT_mul hi, h, neT_mul hk, Nat.xor_self, neT_zero]

theorem mem_ruE0_iff {x : Pi7} : x ∈ ruE0 ↔ ∃ i < 64, neT i = x := by
  refine ⟨fun hx => ?_, fun ⟨i, _, hi⟩ => hi ▸ neT_mem i⟩
  replace hx : x ∈ closure (pi7Word '' {w | w ∈ ruE0Words}) := hx
  induction hx using Subgroup.closure_induction_left with
  | one => exact ⟨0, by norm_num, neT_zero⟩
  | mul_left y hy z _ ih =>
    obtain ⟨j, hj, rfl⟩ := exists_neE hy
    obtain ⟨i, hi, rfl⟩ := ih
    exact ⟨_, xor_lt_64 hi (two_pow_lt_64 hj), (neE_mul_neT hj i).symm⟩
  | inv_mul_cancel y hy z _ ih =>
    obtain ⟨j, hj, rfl⟩ := exists_neE hy
    obtain ⟨i, hi, rfl⟩ := ih
    rw [inv_eq_of_mul_eq_one_right (neE_mul_self hj)]
    exact ⟨_, xor_lt_64 hi (two_pow_lt_64 hj), (neE_mul_neT hj i).symm⟩

theorem orbitX_not_mem {t : ℕ × ℕ × ℕ} (ht : t ∈ neOrbitWit) : pi7Word (neOrbitX t) ∉ ruE0 := by
  intro hx
  obtain ⟨j, hj⟩ := ne_orbitComm t ht
  apply pi7Word_ne_of_wordProd hj
  rw [pi7Word_append, pi7Word_append]
  exact ruE0_comm hx (neE_mem j)

end Facts

theorem ruE0_le_ruB0 : ruE0 ≤ ruB0 := by
  refine (closure_le _).2 ?_
  rintro _ ⟨w, hw, rfl⟩
  have h : ∀ w ∈ ruE0Words, ∀ p ∈ w, p.1 ∈ ([0, 1, 2, 3] : List (Fin 7)) := by decide
  exact pi7Word_mem_letterSub (h w hw)

theorem ruB0_le_ruM1 : ruB0 ≤ ruM1 := letterSub_mono (by decide)

theorem ruB0_le_ruM2 : ruB0 ≤ ruM2 := letterSub_mono (by decide)

theorem ruM13_le_ruM1 : ruM13 ≤ ruM1 := letterSub_mono (by decide)

theorem ruZ0_mem_ruE0 : ruZ0 ∈ ruE0 := by
  have h : ruZ0Word = ruE0Words.getD 0 [] := rfl
  rw [ruZ0, h]
  exact neE_mem 0

theorem ruE0_le_ruM1 : ruE0 ≤ ruM1 := ruE0_le_ruB0.trans ruB0_le_ruM1

theorem neConjLetters_spec : ∀ l ∈ neConjLetters,
    neConjLetters.idxOf l < 6 ∧ neConjLetters.getD (neConjLetters.idxOf l) 0 = l := by
  decide

theorem conj_neT
    {l : Fin 7}
    (hl : l ∈ neConjLetters) {i : ℕ} (hi : i < 64) :
    PresentedGroup.of l * neT i * (PresentedGroup.of l)⁻¹ = neT (neConjPerm l i) ∧
      neConjPerm l i < 64 := by
  obtain ⟨hk, hkl⟩ := neConjLetters_spec l hl
  have h := conj_neT_tab hk hi
  rw [hkl] at h
  exact ⟨h, (ne_act.1 _ hk i hi).2⟩

theorem conj_neW
    {u : List (Fin 7)}
    (hu : ∀ l ∈ u, l ∈ neConjLetters) {i : ℕ} (hi : i < 64) :
    neW u * neT i * (neW u)⁻¹ = neT (u.foldr neConjPerm i) ∧ u.foldr neConjPerm i < 64 := by
  induction u with
  | nil => exact ⟨by rw [neW_nil, one_mul, inv_one, mul_one]; rfl, hi⟩
  | cons l u ih =>
    obtain ⟨h1, h2⟩ := ih fun l' hl' => hu l' (List.mem_cons_of_mem _ hl')
    obtain ⟨h3, h4⟩ := conj_neT (hu l (by simp)) h2
    refine ⟨?_, h4⟩
    rw [neW_cons, conj_mul_conj, h1, h3]
    rfl

theorem of_mem_normalizer
    {l : Fin 7}
    (hl : l ∈ neConjLetters) : (PresentedGroup.of l : Pi7) ∈ normalizer (ruE0 : Set Pi7) := by
  refine mem_normalizer_iff.2 fun h => ⟨fun hh => ?_, fun hh => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := mem_ruE0_iff.1 hh
    rw [(conj_neT hl hi).1]
    exact neT_mem _
  · obtain ⟨j, hj, hjh⟩ := mem_ruE0_iff.1 hh
    obtain ⟨hk, -⟩ := neConjLetters_spec l hl
    obtain ⟨i, hi, hij⟩ := ne_act.2.1 _ hk j hj
    have e : PresentedGroup.of l * neT i * (PresentedGroup.of l)⁻¹ =
        PresentedGroup.of l * h * (PresentedGroup.of l)⁻¹ := by
      rw [(conj_neT hl hi).1, ← hjh]
      exact congrArg neT hij
    rw [mul_right_cancel_iff, mul_left_cancel_iff] at e
    exact e ▸ neT_mem i

theorem ruM13_le_normalizer :
    ruM13 ≤ normalizer (ruE0 : Set Pi7) := by
  refine (closure_le _).2 ?_
  rintro _ ⟨i, hi, rfl⟩
  have h : ∀ i : Fin 7, i ∈ ([0, 1, 2, 3, 5] : List (Fin 7)) → i ∈ neConjLetters := by decide
  exact of_mem_normalizer (h i hi)

noncomputable def neM (k : ℕ) : Pi7 := neW (neOrbitWords.getD k [])

noncomputable def neA (r : ℕ) : Pi7 := neW (neActWords.getD r [])

theorem neM_mem (k : ℕ) : neM k ∈ ruM1 := by
  rcases getD_mem_or neOrbitWords k [] with h | h
  · exact neW_mem_letterSub (ne_act.2.2.2.1 _ h)
  · rw [neM, h, neW_nil]
    exact one_mem _

theorem neA_mem (r : ℕ) : neA r ∈ ruM13 := by
  rcases getD_mem_or neActWords r [] with h | h
  · exact neW_mem_letterSub (ne_act.2.2.1 _ h)
  · rw [neA, h, neW_nil]
    exact one_mem _

theorem neM_inv_mul_not_mem
    {k l : ℕ} (hkl : k < l)
    (hl : l < 20) : (neM l)⁻¹ * neM k ∉ normalizer (ruE0 : Set Pi7) := by
  intro hn
  obtain ⟨t, ht, rfl, rfl⟩ := ne_act.2.2.2.2.2.2.2 k (hkl.trans hl) l hl hkl
  apply orbitX_not_mem ht
  have e : pi7Word (neOrbitX t) =
      (neM t.2.1)⁻¹ * neM t.1 * neE t.2.2 * ((neM t.2.1)⁻¹ * neM t.1)⁻¹ := by
    rw [neOrbitX, pi7Word_append, pi7Word_append, pi7Word_append, pi7Word_append,
      pi7Word_invWord, pi7Word_invWord]
    simp only [neM, neW, neE]
    group
  rw [e]
  exact (mem_normalizer_iff.1 hn _).1 (neE_mem _)

theorem neM_eq_of_mem
    {k l : ℕ} (hk : k < 20)
    (hl : l < 20) (h : (neM k)⁻¹ * neM l ∈ normalizer (ruE0 : Set Pi7)) : k = l := by
  rcases lt_trichotomy k l with hkl | hkl | hkl
  · have h' := inv_mem h
    rw [mul_inv_rev, inv_inv] at h'
    exact absurd h' (neM_inv_mul_not_mem hkl hl)
  · exact hkl
  · exact absurd h (neM_inv_mul_not_mem hkl hk)

theorem neA_eq
    {r r' : ℕ} (hr : r < 192)
    (hr' : r' < 192)
    (h : ∀ i < 64, neA r * neT i * (neA r)⁻¹ = neA r' * neT i * (neA r')⁻¹) : r = r' := by
  obtain ⟨-, -, hlet, -, hnd, hlen, -⟩ := ne_act
  have hsub : ∀ i : Fin 7, i ∈ ([0, 1, 2, 3, 5] : List (Fin 7)) → i ∈ neConjLetters := by
    decide
  have hu : ∀ s < 192, ∀ l ∈ neActWords.getD s [], l ∈ neConjLetters := by
    intro s hs l hl
    rw [List.getD_eq_getElem _ _ (hlen ▸ hs)] at hl
    exact hsub l (hlet _ (List.getElem_mem _) l hl)
  have hp : neActPerm (neActWords.getD r []) = neActPerm (neActWords.getD r' []) := by
    simp only [neActPerm]
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.1 hi
    obtain ⟨e1, b1⟩ := conj_neW (hu r hr) hi'
    obtain ⟨e2, b2⟩ := conj_neW (hu r' hr') hi'
    exact neT_injective b1 b2 (e1.symm.trans ((h i hi').trans e2))
  rw [List.getD_eq_getElem _ _ (hlen ▸ hr), List.getD_eq_getElem _ _ (hlen ▸ hr')] at hp
  have hr2 : r < (neActWords.map neActPerm).length := by rw [List.length_map, hlen]; exact hr
  have hr2' : r' < (neActWords.map neActPerm).length := by rw [List.length_map, hlen]; exact hr'
  exact (hnd.getElem_inj_iff (hi := hr2) (hj := hr2')).1
    (by rw [List.getElem_map, List.getElem_map]; exact hp)

theorem ruM1_eq_genSub :
    ruM1 = genSub {r : FreeGroup (Fin 7) | r ∈ pi7Rels.map FreeGroup.mk} sub1 := by
  have h : {i : Fin 7 | i ∈ ([0, 1, 2, 3, 4, 5] : List (Fin 7))} = {x | x ∈ sub1} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    revert x
    decide
  rw [ruM1, letterSub, h]

theorem card_ruM1_le : Nat.card ruM1 ≤ 245760 := by
  obtain ⟨hfin1, hcard1⟩ := card_relsM1
  have h := (card_genSub_le pi7Rels sub1).2
  rw [ruM1_eq_genSub]
  exact h.trans hcard1

theorem index_centralizer_ge :
    20 * 192 ≤ ((centralizer (ruE0 : Set Pi7)).subgroupOf ruM1).index := by
  have := card_pi7_le.1
  have hA : ∀ s, neA s ∈ normalizer (ruE0 : Set Pi7) := fun s => ruM13_le_normalizer (neA_mem s)
  have hf : Function.Injective fun p : Fin 20 × Fin 192 =>
      (QuotientGroup.mk ⟨neM p.1 * neA p.2, mul_mem (neM_mem _) (ruM13_le_ruM1 (neA_mem _))⟩ :
        ↥ruM1 ⧸ (centralizer (ruE0 : Set Pi7)).subgroupOf ruM1) := by
    rintro ⟨k, r⟩ ⟨k', r'⟩ hkr
    have hc : (neM k * neA r)⁻¹ * (neM k' * neA r') ∈ centralizer (ruE0 : Set Pi7) :=
      mem_subgroupOf.1 (QuotientGroup.eq.1 hkr)
    have hk : (neM k)⁻¹ * neM k' ∈ normalizer (ruE0 : Set Pi7) := by
      have e : (neM k)⁻¹ * neM k' =
          neA r * ((neM k * neA r)⁻¹ * (neM k' * neA r')) * (neA r')⁻¹ := by group
      rw [e]
      exact mul_mem (mul_mem (hA r) (centralizer_le_normalizer _ hc)) (inv_mem (hA r'))
    have e1 : k = k' := Fin.ext (neM_eq_of_mem k.2 k'.2 hk)
    subst e1
    have hc' : (neA r)⁻¹ * neA r' ∈ centralizer (ruE0 : Set Pi7) := by
      have e : (neA r)⁻¹ * neA r' = (neM k * neA r)⁻¹ * (neM k * neA r') := by group
      rw [e]
      exact hc
    have e2 : (r : ℕ) = r' := neA_eq r.2 r'.2 fun i _ => by
      have hcom := mem_centralizer_iff.1 hc' (neT i) (neT_mem i)
      calc neA r * neT i * (neA r)⁻¹
          = neA r * (neT i * ((neA r)⁻¹ * neA r')) * ((neA r)⁻¹ * neA r')⁻¹ * (neA r)⁻¹ := by
            group
        _ = neA r * (((neA r)⁻¹ * neA r') * neT i) * ((neA r)⁻¹ * neA r')⁻¹ * (neA r)⁻¹ := by
            rw [hcom]
        _ = neA r' * neT i * (neA r')⁻¹ := by group
    exact Prod.ext rfl (Fin.ext e2)
  have h := Nat.card_le_card_of_injective _ hf
  rwa [Nat.card_prod, Nat.card_fin, Nat.card_fin] at h

theorem card_centralizer_le :
    Nat.card ((centralizer (ruE0 : Set Pi7)).subgroupOf ruM1) ≤ 64 := by
  have h : Nat.card ((centralizer (ruE0 : Set Pi7)).subgroupOf ruM1) * (20 * 192) ≤
      64 * (20 * 192) :=
    calc _ ≤ Nat.card ((centralizer (ruE0 : Set Pi7)).subgroupOf ruM1) *
          ((centralizer (ruE0 : Set Pi7)).subgroupOf ruM1).index :=
          Nat.mul_le_mul_left _ index_centralizer_ge
      _ = Nat.card ruM1 := card_mul_index _
      _ ≤ 64 * (20 * 192) := card_ruM1_le.trans (by norm_num)
  exact Nat.le_of_mul_le_mul_right h (by norm_num)

theorem mem_ruE0_of_mem_centralizer
    {m : Pi7} (hm : m ∈ ruM1) (hc : m ∈ centralizer (ruE0 : Set Pi7)) : m ∈ ruE0 := by
  have := card_pi7_le.1
  have hle : ruE0.subgroupOf ruM1 ≤ (centralizer (ruE0 : Set Pi7)).subgroupOf ruM1 := fun x hx =>
    mem_subgroupOf.2 (mem_centralizer_iff.2 fun h hh => ruE0_comm hh (mem_subgroupOf.1 hx))
  have hf : Function.Injective fun i : Fin 64 =>
      (⟨⟨neT i, ruE0_le_ruM1 (neT_mem i)⟩, mem_subgroupOf.2 (neT_mem i)⟩ :
        ↥(ruE0.subgroupOf ruM1)) := by
    intro i k hik
    exact Fin.ext (neT_injective i.2 k.2
      (congrArg (fun x : ↥(ruE0.subgroupOf ruM1) => ((x : ↥ruM1) : Pi7)) hik))
  have hcard := Nat.card_le_card_of_injective _ hf
  rw [Nat.card_fin] at hcard
  have heq := eq_of_le_of_card_ge hle (card_centralizer_le.trans hcard)
  have hx : (⟨m, hm⟩ : ↥ruM1) ∈ (centralizer (ruE0 : Set Pi7)).subgroupOf ruM1 :=
    mem_subgroupOf.2 hc
  rw [← heq] at hx
  exact mem_subgroupOf.1 hx

theorem eq_one_of_commute_w0
    {e : Pi7} (he : e ∈ ruE0)
    (hc : PresentedGroup.of 5 * PresentedGroup.of 0 * PresentedGroup.of 2 * PresentedGroup.of 6 *
        e = e * (PresentedGroup.of 5 * PresentedGroup.of 0 * PresentedGroup.of 2 *
          PresentedGroup.of 6)) :
    e = 1 := by
  rw [← neW_w0] at hc
  obtain ⟨i, hi, rfl⟩ := mem_ruE0_iff.1 he
  obtain ⟨h1, h2⟩ := conj_neW (u := [5, 0, 2, 6]) (by decide) hi
  have h3 : neT ([5, 0, 2, 6].foldr neConjPerm i) = neT i := by
    rw [← h1, hc, mul_inv_cancel_right]
  have h4 := neT_injective h2 hi h3
  rcases ne_w0 i hi with h5 | h5
  · refine absurd ?_ h5
    have hl : i < (neActPerm [5, 0, 2, 6]).length := by simp [neActPerm, hi]
    rw [List.getD_eq_getElem _ _ hl]
    simp only [neActPerm, List.getElem_map, List.getElem_range]
    exact h4
  · rw [h5, neT_zero]

end CFSG.ComponentClassification.GMS78.RuNE
