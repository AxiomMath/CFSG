module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThLocalData
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCentSound
public import CFSG.Sporadic.Th.Max3.AllConjFinal
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThLocalCheck

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThLocal

open CFSG.RankThree.PartTwo.Sec4.Item434SporTh CFSG.RankThree.PartTwo.Sec4.Item434SporE81
open CFSG.Sporadic.Th.Native CFSG.Monster.B.Fischer
open CFSG.RankThree.PartTwo.Sec4.Item434SporLy (wordG wordG_mem)
open CFSG.Assembly (IsElemAbelian)

theorem getElem!_set!_of_lt (a : Array ℕ) (k r v : ℕ) (hr : r < a.size) :
    (a.set! k v)[r]! = if k = r then v else a[r]! := by
  rw [Array.set!_eq_setIfInBounds, getElem!_pos (a.setIfInBounds k v) r (by simpa using hr),
    Array.getElem_setIfInBounds hr, getElem!_pos a r hr]

theorem size_set! (a : Array ℕ) (k v : ℕ) : (a.set! k v).size = a.size := by
  rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

section Table

variable {W : Type*} [Group W] {p : ℕ → W} {m N : ℕ} {g : ℕ → W} {edges : Array (Array ℕ)}
  {par lab : Array ℕ}

theorem mulIdxN_spec (hT : IsTable p m N g edges par lab) :
    ∀ f i, i ≤ f → i < N → ∀ j < N, mulIdxN edges par lab f i j < N ∧
      g (mulIdxN edges par lab f i j) = g i * g j := by
  intro f
  induction f with
  | zero =>
    intro i hi hiN j hj
    have h0 : i = 0 := by omega
    subst h0
    simp [mulIdxN, hT.g0, hj]
  | succ f ih =>
    intro i hi hiN j hj
    by_cases h0 : i = 0
    · subst h0
      simp [mulIdxN, hT.g0, hj]
    · obtain ⟨hp, hl, hg⟩ := hT.tree i hiN (Nat.pos_of_ne_zero h0)
      obtain ⟨h1, h2⟩ := ih (par[i]!) (by omega) (by omega) j hj
      obtain ⟨h3, h4⟩ := hT.edge _ h1 lab[i]! hl
      simp only [mulIdxN, h0, ite_false]
      refine ⟨h3, ?_⟩
      rw [h4, h2, hg, mul_assoc]

theorem powIdx_spec (hT : IsTable p m N g edges par lab) {i : ℕ} (hi : i < N) :
    ∀ e, powIdx (mulIdxN edges par lab N) i e < N ∧
      g (powIdx (mulIdxN edges par lab N) i e) = g i ^ e
  | 0 => ⟨hT.pos, by rw [powIdx, hT.g0, pow_zero]⟩
  | e + 1 => by
    obtain ⟨h1, h2⟩ := powIdx_spec hT hi e
    obtain ⟨h3, h4⟩ := mulIdxN_spec hT N i hi.le hi _ h1
    exact ⟨h3, by rw [powIdx, h4, h2, pow_succ']⟩

theorem mul_spec (hT : IsTable p m N g edges par lab) {i j : ℕ} (hi : i < N) (hj : j < N) :
    mulIdxN edges par lab N i j < N ∧ g (mulIdxN edges par lab N i j) = g i * g j :=
  mulIdxN_spec hT N i hi.le hi j hj

@[expose] def QConj (Q : Subgroup W) (x y : W) : Prop := ∃ q ∈ Q, x = q * y * q⁻¹

theorem QConj.refl (Q : Subgroup W) (x : W) : QConj Q x x := ⟨1, Q.one_mem, by group⟩

@[expose] def ClassInv (Q : Subgroup W) (g : ℕ → W) (reps : List ℕ) (arr : Array ℕ) : Prop :=
  arr.size = qN ∧ ∀ i < qN, arr[i]! < qN → arr[i]! ∈ reps ∧ QConj Q (g i) (g arr[i]!)

theorem initRep_inv (Q : Subgroup W) (g : ℕ → W) (reps : List ℕ) :
    ClassInv Q g reps (initRep reps) := by
  have key : ∀ (l : List ℕ) (a : Array ℕ), a.size = qN → (∀ r ∈ l, r ∈ reps) →
      (∀ i < qN, a[i]! < qN → a[i]! = i ∧ i ∈ reps) →
      (l.foldl (fun a r => a.set! r r) a).size = qN ∧
        ∀ i < qN, (l.foldl (fun a r => a.set! r r) a)[i]! < qN →
          (l.foldl (fun a r => a.set! r r) a)[i]! = i ∧ i ∈ reps := by
    intro l
    induction l with
    | nil => intro a ha _ h; exact ⟨ha, h⟩
    | cons r l ih =>
      intro a ha hl h
      rw [List.foldl_cons]
      refine ih _ (by rw [size_set!, ha]) (fun r' hr' => hl r' (List.mem_cons_of_mem _ hr')) ?_
      intro i hi hlt
      rw [getElem!_set!_of_lt _ _ _ _ (by rw [ha]; exact hi)] at hlt ⊢
      by_cases hri : r = i
      · subst hri
        rw [ite_eq_left rfl]
        exact ⟨rfl, hl _ List.mem_cons_self⟩
      · rw [ite_eq_right hri] at hlt ⊢
        exact h i hi hlt
  obtain ⟨hs, h⟩ := key reps (Array.replicate qN qN) (by simp) (fun r hr => hr) (fun i hi hlt => by
    rw [getElem!_pos _ i (by simpa using hi), Array.getElem_replicate] at hlt
    exact absurd hlt (lt_irrefl _))
  unfold initRep
  refine ⟨hs, fun i hi hlt => ?_⟩
  obtain ⟨e, hmem⟩ := h i hi hlt
  rw [e]
  exact ⟨hmem, QConj.refl Q _⟩

theorem stepFold_false (mul : ℕ → ℕ → ℕ) :
    ∀ (l : List (ℕ × ℕ × ℕ)) (arr : Array ℕ), (l.foldl (stepFold edges mul) (false, arr)).1 = false
  | [], _ => rfl
  | ⟨_, _, _⟩ :: l, arr => by
    rw [List.foldl_cons]
    exact stepFold_false mul l _

theorem classTable_inv (hT : IsTable p 10 qN g edges par lab) (X : ThLocalData)
    (h : (classTable edges (mulIdxN edges par lab qN) X).1 = true) :
    ClassInv (Subgroup.closure (p '' {k | k < 10})) g X.reps
      (classTable edges (mulIdxN edges par lab qN) X).2 := by
  set Q := Subgroup.closure (p '' {k | k < 10}) with hQ
  have hpQ : ∀ k < 10, p k ∈ Q := fun k hk => Subgroup.subset_closure ⟨k, hk, rfl⟩
  have key : ∀ (l : List (ℕ × ℕ × ℕ)) (st : Bool × Array ℕ), ClassInv Q g X.reps st.2 →
      (l.foldl (stepFold edges (mulIdxN edges par lab qN)) st).1 = true →
      ClassInv Q g X.reps (l.foldl (stepFold edges (mulIdxN edges par lab qN)) st).2 := by
    intro l
    induction l with
    | nil => intro st hst _; exact hst
    | cons y l ih =>
      intro st hst hfl
      obtain ⟨b, arr⟩ := st
      obtain ⟨i, p', k⟩ := y
      rw [List.foldl_cons] at hfl ⊢
      have hstep : stepFold edges (mulIdxN edges par lab qN) (b, arr) (i, p', k) =
          (b && decide (i < qN) && decide (p' < qN) && decide (k < 10) && decide (arr[p']! < qN) &&
            ((edges[p']!)[k]! == mulIdxN edges par lab qN i ((edges[0]!)[k]!)),
            arr.set! i arr[p']!) := rfl
      rw [hstep] at hfl ⊢
      by_cases hC : (b && decide (i < qN) && decide (p' < qN) && decide (k < 10) &&
          decide (arr[p']! < qN) &&
          ((edges[p']!)[k]! == mulIdxN edges par lab qN i ((edges[0]!)[k]!))) = true
      · refine ih _ ?_ hfl
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hC
        obtain ⟨⟨⟨⟨⟨-, hi⟩, hp'⟩, hk⟩, hv⟩, he⟩ := hC
        obtain ⟨hsz, hinv⟩ := hst
        refine ⟨by simp only [size_set!]; exact hsz, fun j hj hjlt => ?_⟩
        rw [getElem!_set!_of_lt _ _ _ _ (by rw [hsz]; exact hj)] at hjlt ⊢
        by_cases hij : i = j
        · subst hij
          rw [ite_eq_left rfl] at hjlt ⊢
          obtain ⟨hrep, q, hq, hgq⟩ := hinv p' hp' hjlt
          refine ⟨hrep, p k * q, Q.mul_mem (hpQ k hk) hq, ?_⟩
          obtain ⟨h1, h2⟩ := hT.edge p' hp' k hk
          obtain ⟨h3, h4⟩ := hT.edge 0 hT.pos k hk
          obtain ⟨h5, h6⟩ := mul_spec hT hi h3
          have e1 : g ((edges[p']!)[k]!) = g (mulIdxN edges par lab qN i ((edges[0]!)[k]!)) := by
            rw [he]
          rw [h2, h6, h4, hT.g0, mul_one] at e1
          have : g i = p k * g p' * (p k)⁻¹ := by
            rw [e1]; group
          rw [this, hgq]
          group
        · rw [ite_eq_right hij] at hjlt ⊢
          exact hinv j hj hjlt
      · have hC' : (b && decide (i < qN) && decide (p' < qN) && decide (k < 10) &&
            decide (arr[p']! < qN) &&
            ((edges[p']!)[k]! == mulIdxN edges par lab qN i ((edges[0]!)[k]!))) = false := by
          simpa using hC
        rw [hC', stepFold_false] at hfl
        exact absurd hfl (by decide)
  exact key _ _ (initRep_inv Q g X.reps) h

end Table

theorem matOf_spec {P : Array Mat} {p : ℕ → GL (Fin 248) (ZMod 2)} {m N : ℕ}
    {g : ℕ → GL (Fin 248) (ZMod 2)} {edges : Array (Array ℕ)} {par lab : Array ℕ}
    (hP : ∀ l < m, Rp P[l]! (p l)) (hT : IsTable p m N g edges par lab) :
    ∀ f i, i ≤ f → i < N → Rp (matOf P par lab f i) (g i) := by
  have hid : Rp idRows (g 0) := by
    unfold Rp
    rw [hT.g0, CFSG.Sporadic.Th.rowsMatrix_idRows, Units.val_one]
  intro f
  induction f with
  | zero =>
    intro i hi _
    have h0 : i = 0 := by omega
    subst h0
    exact hid
  | succ f ih =>
    intro i hi hiN
    by_cases h0 : i = 0
    · subst h0
      rw [matOf, ite_eq_left rfl]
      exact hid
    · obtain ⟨hp, hl, hg⟩ := hT.tree i hiN (Nat.pos_of_ne_zero h0)
      rw [matOf, ite_eq_right h0, hg]
      exact Rp.mul (hP _ hl) (ih _ (by omega) (by omega))

section Pair

variable {G : Type*} [Group G]

theorem pow_eq_pow_mod_three {x : G} (hx : x ^ 3 = 1) (n : ℕ) : x ^ n = x ^ (n % 3) := by
  conv_lhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hx, one_pow, mul_one]

@[expose] def pairProd (x y : G) (ij : Fin 3 × Fin 3) : G := x ^ ij.1.val * y ^ ij.2.val

theorem pairProd_mul {x y : G} (hxy : Commute x y) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (u v : Fin 3 × Fin 3) :
    pairProd x y u * pairProd x y v = pairProd x y
      (⟨(u.1.val + v.1.val) % 3, Nat.mod_lt _ (by norm_num)⟩,
        ⟨(u.2.val + v.2.val) % 3, Nat.mod_lt _ (by norm_num)⟩) := by
  unfold pairProd
  rw [← pow_eq_pow_mod_three hx, ← pow_eq_pow_mod_three hy, pow_add, pow_add]
  have hc : y ^ u.2.val * x ^ v.1.val = x ^ v.1.val * y ^ u.2.val :=
    ((hxy.pow_pow v.1.val u.2.val).eq).symm
  calc x ^ u.1.val * y ^ u.2.val * (x ^ v.1.val * y ^ v.2.val)
      = x ^ u.1.val * (y ^ u.2.val * x ^ v.1.val) * y ^ v.2.val := by group
    _ = x ^ u.1.val * (x ^ v.1.val * y ^ u.2.val) * y ^ v.2.val := by rw [hc]
    _ = x ^ u.1.val * x ^ v.1.val * (y ^ u.2.val * y ^ v.2.val) := by group

theorem inv_eq_sq {x : G} (hx : x ^ 3 = 1) : x⁻¹ = x ^ 2 := by
  rw [inv_eq_iff_mul_eq_one, ← pow_succ', hx]

@[expose] def pairSubgroup {x y : G} (hxy : Commute x y) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) :
    Subgroup G where
  carrier := Set.range (pairProd x y)
  mul_mem' := by
    rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
    exact ⟨_, (pairProd_mul hxy hx hy u v).symm⟩
  one_mem' := ⟨(0, 0), by simp [pairProd]⟩
  inv_mem' := by
    rintro _ ⟨⟨i, j⟩, rfl⟩
    refine ⟨(⟨(3 - i.val) % 3, Nat.mod_lt _ (by norm_num)⟩,
      ⟨(3 - j.val) % 3, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
    symm
    apply inv_eq_of_mul_eq_one_right
    rw [pairProd_mul hxy hx hy]
    have hi := i.isLt
    have hj := j.isLt
    have h1 : (i.val + (3 - i.val) % 3) % 3 = 0 := by omega
    have h2 : (j.val + (3 - j.val) % 3) % 3 = 0 := by omega
    simp only [pairProd, h1, h2, pow_zero, mul_one]

theorem closure_pair_eq_range {x y : G} (hxy : Commute x y) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) :
    (Subgroup.closure ({x, y} : Set G) : Set G) = Set.range (pairProd x y) := by
  apply le_antisymm
  · have hle : Subgroup.closure ({x, y} : Set G) ≤ pairSubgroup hxy hx hy := by
      rw [Subgroup.closure_le]
      intro v hv
      rcases hv with rfl | rfl
      · exact ⟨(1, 0), by simp [pairProd]⟩
      · exact ⟨(0, 1), by simp [pairProd]⟩
    exact fun v hv => hle hv
  · rintro _ ⟨⟨i, j⟩, rfl⟩
    have hx' : x ∈ Subgroup.closure ({x, y} : Set G) :=
      Subgroup.subset_closure (Set.mem_insert x _)
    have hy' : y ∈ Subgroup.closure ({x, y} : Set G) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem x (Set.mem_singleton y))
    show x ^ i.val * y ^ j.val ∈ Subgroup.closure ({x, y} : Set G)
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hx' _) (Subgroup.pow_mem _ hy' _)

theorem card_closure_pair {x y : G} (hxy : Commute x y) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hinj : Function.Injective (pairProd x y)) :
    Nat.card (Subgroup.closure ({x, y} : Set G)) = 9 := by
  have e : Nat.card (Subgroup.closure ({x, y} : Set G)) = Nat.card (Set.range (pairProd x y)) := by
    rw [← closure_pair_eq_range hxy hx hy, SetLike.coe_sort_coe]
  rw [e, Nat.card_range_of_injective hinj]
  simp

theorem isElemAbelian_closure_pair {x y : G} (hxy : Commute x y) (hx : x ^ 3 = 1)
    (hy : y ^ 3 = 1) : IsElemAbelian 3 (Subgroup.closure ({x, y} : Set G)) := by
  refine isElemAbelian_closure_of_comm ?_ ?_
  · intro u hu v hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact Commute.refl _
    · exact hxy
    · exact hxy.symm
    · exact Commute.refl _
  · intro u hu
    rcases hu with rfl | rfl
    · exact hx
    · exact hy

end Pair

section Main


theorem mem_centralizer_J {x t : CFSG.Sporadic.Th.J} :
    x ∈ Subgroup.centralizer ({t} : Set CFSG.Sporadic.Th.J) ↔
      (x : GL (Fin 248) (ZMod 2)) * t = t * x := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subtype.ext_iff, Subgroup.coe_mul,
    Subgroup.coe_mul]

theorem isConj_J {x y c : CFSG.Sporadic.Th.J}
    (h : (x : GL (Fin 248) (ZMod 2)) = c * y * (c : GL (Fin 248) (ZMod 2))⁻¹) : IsConj x y := by
  refine isConj_iff.2 ⟨c⁻¹, Subtype.ext ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, h]
  group

theorem factorization_J :
    (Nat.card CFSG.Sporadic.Th.J).factorization 3 = 10 := by
  rw [CFSG.Sporadic.Th.Max3.natCard_J,
    show (90745943887872000 : ℕ) = 3 ^ 10 * 1536790528000 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply, Nat.factorization_pow,
    Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_three,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  rfl

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent in
theorem thLocalChecks_sound
    {E : ThE81Data} {X : ThLocalData} {A B Z : Mat} {gs P : Array Mat} {c : ArrCert}
    (hA : Rp A CFSG.Sporadic.Th.gA) (hB : Rp B CFSG.Sporadic.Th.gB)
    (hZ : Rp Z ((zJ : CFSG.Sporadic.Th.J) : GL (Fin 248) (ZMod 2)))
    (hgs : gs = #[evalWord #[A, B] E.w61, evalWord #[A, B] E.w62])
    (hP : P = E.pW.map (evalWord gs))
    (h : thLocalChecks E X A B Z gs P c = true) :
    ∃ Q : Subgroup CFSG.Sporadic.Th.J, Nat.card Q = 3 ^ 10 ∧ zJ ∈ Q ∧ zJ ^ 3 = 1 ∧
      (∀ q ∈ Q, q * zJ = zJ * q) ∧ (∃ u : CFSG.Sporadic.Th.J, orderOf u = 2 ∧ u * zJ = zJ * u) ∧
      ∀ s ∈ Q, orderOf s = 3 → ∃ t : CFSG.Sporadic.Th.J, IsConj s t ∧
        3 ^ 7 ≤ Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set CFSG.Sporadic.Th.J)) ∧
        ∃ E : Subgroup CFSG.Sporadic.Th.J,
          E ≤ Subgroup.centralizer ({t} : Set CFSG.Sporadic.Th.J) ∧ IsElemAbelian 3 E ∧
            Nat.card E = 9 ∧ ∀ x ∈ E, x ≠ 1 → IsConj x zJ ∨ IsConj x (zJ ^ 2) := by
  set JG := CFSG.Sporadic.Th.J with hJG
  have : Finite JG := Nat.finite_of_card_ne_zero
    (by rw [CFSG.Sporadic.Th.Max3.natCard_J]; norm_num)
  have hJ := factorization_J
  unfold thLocalChecks at h
  simp only [Bool.and_eq_true, and_assoc] at h
  obtain ⟨hl1, hl2, hl3, hpc, horb, hloc, hfus, hrc, hinvl, hip1, hip2, hU2, hUne, hUz, hMz⟩ := h
  unfold localTableChecks at hloc
  simp only [Bool.and_eq_true, and_assoc] at hloc
  obtain ⟨he09, hz2, hz3, hzc, hreps, hct, hcov, htg⟩ := hloc
  set gA := CFSG.Sporadic.Th.gA with hgA
  set gB := CFSG.Sporadic.Th.gB with hgB
  have ha : gA ∈ JG := Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : gB ∈ JG := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  let cd0 : ℕ → GL (Fin 248) (ZMod 2) := fun l => if l = 0 then gA else gB
  have hcd0J : ∀ l, cd0 l ∈ JG := fun l => by
    by_cases hl : l = 0
    · simp only [cd0, hl, ite_true]; exact ha
    · simp only [cd0, hl, ite_false]; exact hb
  have hAB : ∀ l < 2, Rp (#[A, B] : Array Mat)[l]! (cd0 l) := by
    intro l hl
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · exact hA
    · exact hB
  have hletters1 : ∀ x ∈ E.w61, x.1 < 2 := fun x hx =>
    of_decide_eq_true (List.all_eq_true.1 hl1 x hx)
  have hletters2 : ∀ x ∈ E.w62, x.1 < 2 := fun x hx =>
    of_decide_eq_true (List.all_eq_true.1 hl2 x hx)
  have hx61 : Rp (evalWord #[A, B] E.w61) (wordG cd0 E.w61) :=
    rowsMatrix_evalWord_eq fun x hx => hAB x.1 (hletters1 x hx)
  have hx62 : Rp (evalWord #[A, B] E.w62) (wordG cd0 E.w62) :=
    rowsMatrix_evalWord_eq fun x hx => hAB x.1 (hletters2 x hx)
  have hx61J : wordG cd0 E.w61 ∈ JG := wordG_mem fun x _ => hcd0J x.1
  have hx62J : wordG cd0 E.w62 ∈ JG := wordG_mem fun x _ => hcd0J x.1
  let cd1 : ℕ → GL (Fin 248) (ZMod 2) := fun l =>
    if l = 0 then wordG cd0 E.w61 else wordG cd0 E.w62
  have hcd1J : ∀ l, cd1 l ∈ JG := fun l => by
    by_cases hl : l = 0
    · simp only [cd1, hl, ite_true]; exact hx61J
    · simp only [cd1, hl, ite_false]; exact hx62J
  have hgs1 : ∀ l < 2, Rp gs[l]! (cd1 l) := by
    intro l hl
    rw [hgs]
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · exact hx61
    · exact hx62
  have hsize : P.size = 10 := pcCheck_size hpc
  have hpWsize : E.pW.size = 10 := by rw [hP, Array.size_map] at hsize; exact hsize
  have hletters : ∀ k < 10, ∀ x ∈ E.pW[k]!, x.1 < 2 := by
    intro k hk x hx
    have := List.all_eq_true.1 hl3 (E.pW[k]!) (by
      rw [getElem!_pos E.pW k (by omega)]
      exact Array.getElem_mem_toList (by omega))
    exact of_decide_eq_true (List.all_eq_true.1 this x hx)
  let g : ℕ → GL (Fin 248) (ZMod 2) := fun k => wordG cd1 (E.pW[k]!)
  have hg : ∀ l < 10, Rp P[l]! (g l) := by
    intro l hl
    have hPl : P[l]! = evalWord gs E.pW[l]! := by
      rw [hP, getElem!_map_of_lt E.pW (evalWord gs) (by omega)]
    rw [hPl]
    exact rowsMatrix_evalWord_eq fun x hx => hgs1 x.1 (hletters l hl x hx)
  have hgJ : ∀ k, g k ∈ JG := fun k => wordG_mem fun x _ => hcd1J x.1
  obtain ⟨hcube, hconj⟩ := pc_sound hg hpc
  have hQp : IsPGroup 3 (tailGroup g 10 0) := isPGroup_tailGroup g 10 hcube hconj 0
  have hQeq : tailGroup g 10 0 = Subgroup.closure (g '' {k | k < 10}) := by
    have hs : ({l | 0 ≤ l ∧ l < 10} : Set ℕ) = {k | k < 10} := by
      ext l
      simp
    unfold tailGroup
    rw [hs]
  rw [hQeq] at hQp
  set Q := Subgroup.closure (g '' {k | k < 10}) with hQdef
  have hQJ : Q ≤ JG := by
    rw [hQdef, Subgroup.closure_le]
    rintro _ ⟨k, -, rfl⟩
    exact hgJ k
  have hle : Nat.card Q ≤ 59049 := by
    have := card_le_of_isPGroup hQJ hQp
    rw [hJ] at this
    simpa using this
  obtain ⟨⟨gi, hT⟩, hQN⟩ := orbit_table hsize hg hle horb
  have hgiQ : ∀ i < qN, gi i ∈ Q := g_mem hT
  have hgiJ : ∀ i < qN, gi i ∈ JG := fun i hi => hQJ (hgiQ i hi)
  obtain ⟨mul, hmul⟩ : ∃ m, m = mulIdxN c.edges c.par c.lab qN := ⟨_, rfl⟩
  rw [← hmul] at hz2 hz3 hzc hct hcov htg
  have hmulS : ∀ {i j : ℕ}, i < qN → j < qN → mul i j < qN ∧ gi (mul i j) = gi i * gi j := by
    intro i j hi hj
    rw [hmul]
    exact mul_spec hT hi hj
  have hpowS : ∀ {i : ℕ}, i < qN → ∀ e, powIdx mul i e < qN ∧ gi (powIdx mul i e) = gi i ^ e := by
    intro i hi e
    rw [hmul]
    exact powIdx_spec hT hi e
  have hM : ∀ i < qN, Rp (matOf P c.par c.lab qN i) (gi i) := fun i hi =>
    matOf_spec hg hT qN i hi.le hi
  have hz10 : gi 10 = g 9 := by
    obtain ⟨-, h2⟩ := hT.edge 0 hT.pos 9 (by norm_num)
    rw [beq_iff_eq.1 he09, hT.g0, mul_one] at h2
    exact h2
  have hzJ : gi 10 = (zJ : GL (Fin 248) (ZMod 2)) := by
    have h1 : Rp Z (gi 10) := by
      rw [← beq_iff_eq.1 hMz]
      exact hM 10 (by norm_num)
    exact h1.eq_of_eq hZ rfl
  have hz94 : gi 94 = gi 10 * gi 10 := by
    obtain ⟨-, h2⟩ := hmulS (i := 10) (j := 10) (by norm_num) (by norm_num)
    rw [← beq_iff_eq.1 hz2]
    exact h2
  have hzcomm : ∀ q ∈ Q, q * gi 10 = gi 10 * q := by
    have hle' : Q ≤ Subgroup.centralizer {gi 10} := by
      rw [hQdef, Subgroup.closure_le]
      rintro _ ⟨k, hk, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      obtain ⟨h1, h2⟩ := hT.edge 10 (by norm_num) k hk
      obtain ⟨h3, h4⟩ := hT.edge 0 hT.pos k hk
      obtain ⟨h5, h6⟩ := hmulS (i := 10) (by norm_num) h3
      have e1 : gi ((c.edges[10]!)[k]!) = gi (mul 10 ((c.edges[0]!)[k]!)) := by
        rw [beq_iff_eq.1 (List.all_eq_true.1 hzc k (List.mem_range.2 hk))]
      rw [h2, h6, h4, hT.g0, mul_one] at e1
      exact e1
    intro q hq
    have hq' := hle' hq
    rw [Subgroup.mem_centralizer_singleton_iff] at hq'
    exact hq'
  have hQJcard : Nat.card (Q.subgroupOf JG) = 3 ^ 10 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQJ).toEquiv, hQN]
    norm_num
  have hzQJ : zJ ∈ Q.subgroupOf JG := by
    rw [Subgroup.mem_subgroupOf, ← hzJ]
    exact hgiQ 10 (by norm_num)
  let cd4 : ℕ → GL (Fin 248) (ZMod 2) := fun l =>
    if l = 0 then gA else if l = 1 then gB else if l = 2 then wordG cd0 E.w61
    else wordG cd0 E.w62
  have hcd4J : ∀ l, cd4 l ∈ JG := fun l => by
    simp only [cd4]
    split_ifs
    · exact ha
    · exact hb
    · exact hx61J
    · exact hx62J
  have hgs4 : ∀ l < 4, Rp (#[A, B, gs[0]!, gs[1]!] : Array Mat)[l]!
      (cd4 l) := by
    intro l hl
    rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
    · exact hA
    · exact hB
    · have e : cd4 2 = cd1 0 := by
        simp only [cd4, cd1, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, if_false, if_true]
      rw [e]
      exact hgs1 0 (by norm_num)
    · have e : cd4 3 = cd1 1 := by
        simp only [cd4, cd1, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, one_ne_zero, if_false]
        rfl
      rw [e]
      exact hgs1 1 (by norm_num)
  have hword4 : ∀ w : List (ℕ × ℕ), (∀ x ∈ w, x.1 < 4) →
      Rp (evalWord #[A, B, gs[0]!, gs[1]!] w) (wordG cd4 w) ∧
        wordG cd4 w ∈ JG := fun w hw =>
    ⟨rowsMatrix_evalWord_eq fun x hx => hgs4 x.1 (hw x hx), wordG_mem fun x _ => hcd4J x.1⟩
  have hfusG : ∀ f ∈ X.fus, f.2.1 < qN ∧ (∃ y ∈ X.tgts, y.1 = f.2.1) ∧ ∃ w ∈ JG,
      gi f.2.1 = w * gi f.1 * w⁻¹ := by
    intro f hf
    have hff := List.all_eq_true.1 hfus f hf
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem, List.any_eq_true,
      beq_iff_eq] at hff
    obtain ⟨⟨⟨⟨hr, ht⟩, hwl⟩, ⟨y, hy, hyt⟩⟩, hWM⟩ := hff
    have hrq : f.1 < qN := of_decide_eq_true (List.all_eq_true.1 hreps f.1 hr)
    obtain ⟨hW, hWJ⟩ := hword4 f.2.2 fun x hx => of_decide_eq_true (List.all_eq_true.1 hwl x hx)
    refine ⟨ht, ⟨y, hy, hyt⟩, wordG cd4 f.2.2, hWJ, ?_⟩
    have e := (hW.mul (hM f.1 hrq)).eq_of_eq ((hM f.2.1 ht).mul hW) hWM
    rw [e]
    group
  have hinv := classTable_inv hT X (by rw [← hmul]; exact hct)
  rw [← hmul] at hinv
  obtain ⟨hU, hUJ⟩ := hword4 X.invW fun x hx => of_decide_eq_true (List.all_eq_true.1 hinvl x hx)
  set uG := wordG cd4 X.invW with huG
  have hu2 : uG * uG = 1 := by
    have hid : Rp idRows (1 : GL (Fin 248) (ZMod 2)) := by
      unfold Rp
      rw [CFSG.Sporadic.Th.rowsMatrix_idRows, Units.val_one]
    exact (hU.mul hU).eq_of_eq hid (beq_iff_eq.1 hU2)
  have hu1 : uG ≠ 1 := by
    intro h1
    have hm : CFSG.Sporadic.Th.rowsMatrix (evalWord #[A, B, gs[0]!, gs[1]!]
        X.invW) = 1 := by
      rw [hU, h1, Units.val_one]
    have hi1 : X.invPos.1 < 248 := of_decide_eq_true hip1
    have hi2 : X.invPos.2 < 248 := of_decide_eq_true hip2
    have := congrFun (congrFun hm ⟨X.invPos.1, hi1⟩) ⟨X.invPos.2, hi2⟩
    rw [CFSG.Sporadic.Th.rowsMatrix_apply, Matrix.one_apply] at this
    simp only [CFSG.Sporadic.Th.Native.V4.toVec, Fin.mk.injEq] at this
    have hne := hUne
    simp only [bne_iff_ne, ne_eq] at hne
    by_cases hij : X.invPos.1 = X.invPos.2
    · rw [ite_eq_left hij] at this
      have hb' : ((evalWord #[A, B, gs[0]!, gs[1]!] X.invW)[X.invPos.1]?.getD
          V4.zero).testBit X.invPos.2 = false := by
        have : (X.invPos.1 == X.invPos.2) = true := beq_iff_eq.2 hij
        rw [this] at hne
        simpa using hne
      rw [hb'] at this
      exact absurd this (by decide)
    · rw [ite_eq_right hij] at this
      have hb' : ((evalWord #[A, B, gs[0]!, gs[1]!] X.invW)[X.invPos.1]?.getD
          V4.zero).testBit X.invPos.2 = true := by
        have : (X.invPos.1 == X.invPos.2) = false := by simpa using hij
        rw [this] at hne
        simpa using hne
      rw [hb'] at this
      exact absurd this (by decide)
  have huz : uG * gi 10 = gi 10 * uG :=
    (hU.mul (hM 10 (by norm_num))).eq_of_eq ((hM 10 (by norm_num)).mul hU) (beq_iff_eq.1 hUz)
  have hz3J : zJ ^ 3 = 1 := by
    apply Subtype.ext
    obtain ⟨-, h2⟩ := hpowS (i := 10) (by norm_num) 3
    rw [beq_iff_eq.1 hz3, hT.g0, hzJ] at h2
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    exact h2.symm
  refine ⟨Q.subgroupOf JG, hQJcard, hzQJ, hz3J, ?_, ?_, ?_⟩
  · intro q hq
    rw [Subgroup.mem_subgroupOf] at hq
    apply Subtype.ext
    simp only [Subgroup.coe_mul, ← hzJ]
    exact hzcomm q hq
  · refine ⟨⟨uG, hUJ⟩, orderOf_eq_prime (Subtype.ext (by
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [pow_two]; exact hu2)) (fun h1 => hu1 (by
        have h' := congrArg Subtype.val h1
        rwa [Subgroup.coe_one] at h')), Subtype.ext ?_⟩
    simp only [Subgroup.coe_mul, ← hzJ]
    exact huz
  · intro s hs hs3
    rw [Subgroup.mem_subgroupOf] at hs
    obtain ⟨i, hi, hgis⟩ := hT.surj _ hs
    have hs1 : (s : GL (Fin 248) (ZMod 2)) ≠ 1 := by
      intro h1
      have : s = 1 := Subtype.ext (by rw [h1, Subgroup.coe_one])
      rw [this, orderOf_one] at hs3
      exact absurd hs3 (by norm_num)
    have hs3' : (s : GL (Fin 248) (ZMod 2)) ^ 3 = 1 := by
      have := pow_orderOf_eq_one s
      rw [hs3] at this
      have h' := congrArg Subtype.val this
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at h'
    have hi0 : i ≠ 0 := by
      rintro rfl
      rw [hT.g0] at hgis
      exact hs1 hgis.symm
    have hpow : powIdx mul i 3 = 0 := by
      obtain ⟨h1, h2⟩ := hpowS hi 3
      rw [hgis, hs3', ← hT.g0] at h2
      exact hT.inj _ h1 _ hT.pos h2
    have hcr : (classTable c.edges mul X).2[i]! < qN := by
      have := List.all_eq_true.1 hcov i (List.mem_range.2 hi)
      simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at this
      rcases this with (h0 | h0) | h0
      · exact absurd h0 hi0
      · exact absurd hpow h0
      · exact h0
    obtain ⟨hrep, q, hq, hqs⟩ := hinv.2 i hi hcr
    set r := (classTable c.edges mul X).2[i]! with hr
    obtain ⟨y, hy, t, hyt, w, hwJ, htw⟩ : ∃ y ∈ X.tgts, ∃ t, y.1 = t ∧ ∃ w ∈ JG,
        gi t = w * gi r * w⁻¹ := by
      have := List.all_eq_true.1 hrc r hrep
      simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq] at this
      rcases this with ⟨f, hf, hfr⟩ | ⟨y, hy, hyr⟩
      · obtain ⟨-, ⟨y, hy, hyt⟩, w, hwJ, hw⟩ := hfusG f hf
        exact ⟨y, hy, f.2.1, hyt, w, hwJ, by rw [hw, hfr]⟩
      · exact ⟨y, hy, r, hyr, 1, JG.one_mem, by group⟩
    have hty := List.all_eq_true.1 htg y hy
    unfold tgtOK at hty
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] at hty
    obtain ⟨ht, he1, he2, hcnt, hte1, hte2, he12, hp1, hp2, hdist, hR86⟩ := hty
    rw [hyt] at ht hcnt hte1 hte2
    set tJ : JG := ⟨gi t, hgiJ t ht⟩ with htJ
    refine ⟨tJ, ?_, ?_, ?_⟩
    ·
      refine isConj_J (c := ⟨q * w⁻¹, JG.mul_mem (hQJ hq) (JG.inv_mem hwJ)⟩) ?_
      simp only [htJ]
      rw [← hgis, hqs, htw]
      group
    ·
      set S := ((List.range qN).filter fun j => mul t j == mul j t).toFinset with hS
      have hScard : 2187 ≤ S.card := by
        rw [hS, List.toFinset_card_of_nodup (List.nodup_range.filter _),
          ← List.countP_eq_length_filter]
        exact hcnt
      have hmemS : ∀ j ∈ S, j < qN ∧ mul t j = mul j t := by
        intro j hj
        simp only [hS, List.mem_toFinset, List.mem_filter, List.mem_range, beq_iff_eq] at hj
        exact hj
      have hFm : ∀ j : S, (⟨gi j, hgiJ j (hmemS j j.2).1⟩ : JG) ∈
          Q.subgroupOf JG ⊓ Subgroup.centralizer ({tJ} : Set JG) := by
        intro j
        refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · rw [Subgroup.mem_subgroupOf]
          exact hgiQ j (hmemS j j.2).1
        · rw [mem_centralizer_J]
          obtain ⟨hjN, hj⟩ := hmemS j j.2
          obtain ⟨-, h1⟩ := hmulS ht hjN
          obtain ⟨-, h2⟩ := hmulS hjN ht
          show gi j * gi t = gi t * gi j
          rw [← h1, ← h2, hj]
      let F : S → ↥(Q.subgroupOf JG ⊓ Subgroup.centralizer ({tJ} : Set JG)) := fun j =>
        ⟨⟨gi j, hgiJ j (hmemS j j.2).1⟩, hFm j⟩
      have hF : Function.Injective F := by
        intro j k hjk
        have e1 := congrArg Subtype.val (congrArg Subtype.val hjk)
        exact Subtype.ext (hT.inj _ (hmemS j j.2).1 _ (hmemS k k.2).1 e1)
      calc 3 ^ 7 = 2187 := by norm_num
        _ ≤ S.card := hScard
        _ = Nat.card S := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
        _ ≤ _ := Nat.card_le_card_of_injective F hF
    ·
      obtain ⟨-, hge1⟩ := hpowS he1 3
      obtain ⟨-, hge2⟩ := hpowS he2 3
      rw [hp1, hT.g0] at hge1
      rw [hp2, hT.g0] at hge2
      set e1J : JG := ⟨gi y.2.1, hgiJ _ he1⟩ with he1J
      set e2J : JG := ⟨gi y.2.2, hgiJ _ he2⟩ with he2J
      have hcube1 : e1J ^ 3 = 1 := Subtype.ext (by
        simp only [he1J, Subgroup.coe_pow, Subgroup.coe_one]; exact hge1.symm)
      have hcube2 : e2J ^ 3 = 1 := Subtype.ext (by
        simp only [he2J, Subgroup.coe_pow, Subgroup.coe_one]; exact hge2.symm)
      have hcomm12 : Commute e1J e2J := by
        show e1J * e2J = e2J * e1J
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        obtain ⟨-, h1⟩ := hmulS he1 he2
        obtain ⟨-, h2⟩ := hmulS he2 he1
        show gi y.2.1 * gi y.2.2 = gi y.2.2 * gi y.2.1
        rw [← h1, ← h2, he12]
      have he9 : ∀ u : Fin 3 × Fin 3, e9Idx mul y.2.1 y.2.2 (3 * u.1.val + u.2.val) < qN ∧
          gi (e9Idx mul y.2.1 y.2.2 (3 * u.1.val + u.2.val)) =
            ((pairProd e1J e2J u : JG) : GL (Fin 248) (ZMod 2)) := by
        intro u
        have hd : (3 * u.1.val + u.2.val) / 3 = u.1.val := by omega
        have hm : (3 * u.1.val + u.2.val) % 3 = u.2.val := by omega
        unfold e9Idx
        rw [hd, hm]
        obtain ⟨h1, h2⟩ := hpowS he1 u.1.val
        obtain ⟨h3, h4⟩ := hpowS he2 u.2.val
        obtain ⟨h5, h6⟩ := hmulS h1 h3
        refine ⟨h5, ?_⟩
        rw [h6, h2, h4]
        simp only [pairProd, he1J, he2J, Subgroup.coe_mul, Subgroup.coe_pow]
      have hinj : Function.Injective (pairProd e1J e2J) := by
        intro u v huv
        by_contra hne
        have hab : 3 * u.1.val + u.2.val ≠ 3 * v.1.val + v.2.val := by
          intro hab
          apply hne
          have h1 : u.1.val = v.1.val := by omega
          have h2 : u.2.val = v.2.val := by omega
          exact Prod.ext (Fin.ext h1) (Fin.ext h2)
        have hd := List.all_eq_true.1 (List.all_eq_true.1 hdist _
          (List.mem_range.2 (by omega : 3 * u.1.val + u.2.val < 9)))
          _ (List.mem_range.2 (by omega : 3 * v.1.val + v.2.val < 9))
        simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hd
        rcases hd with hd | hd
        · exact hab hd
        · apply hd
          obtain ⟨hu1, hu2⟩ := he9 u
          obtain ⟨hv1, hv2⟩ := he9 v
          refine hT.inj _ hu1 _ hv1 ?_
          rw [hu2, hv2, huv]
      refine ⟨Subgroup.closure ({e1J, e2J} : Set JG), ?_,
        isElemAbelian_closure_pair hcomm12 hcube1 hcube2,
        card_closure_pair hcomm12 hcube1 hcube2 hinj, ?_⟩
      · rw [Subgroup.closure_le]
        intro x hx
        rcases hx with rfl | rfl
        · rw [SetLike.mem_coe, mem_centralizer_J]
          obtain ⟨-, h1⟩ := hmulS he1 ht
          obtain ⟨-, h2⟩ := hmulS ht he1
          show gi y.2.1 * gi t = gi t * gi y.2.1
          rw [← h1, ← h2, hte1]
        · rw [SetLike.mem_coe, mem_centralizer_J]
          obtain ⟨-, h1⟩ := hmulS he2 ht
          obtain ⟨-, h2⟩ := hmulS ht he2
          show gi y.2.2 * gi t = gi t * gi y.2.2
          rw [← h1, ← h2, hte2]
      · intro x hx hx1
        have e : ((Subgroup.closure ({e1J, e2J} : Set JG) : Set JG)) =
            Set.range (pairProd e1J e2J) := closure_pair_eq_range hcomm12 hcube1 hcube2
        have hxr : x ∈ Set.range (pairProd e1J e2J) := by
          rw [← e]
          exact hx
        obtain ⟨u, rfl⟩ := hxr
        have hu0 : 3 * u.1.val + u.2.val ≠ 0 := by
          intro h0
          apply hx1
          have h1 : u.1.val = 0 := by omega
          have h2 : u.2.val = 0 := by omega
          simp [pairProd, h1, h2]
        have hR := List.all_eq_true.1 hR86 _
          (List.mem_range.2 (by omega : 3 * u.1.val + u.2.val < 9))
        simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hR
        rcases hR with h0 | ⟨hcr', hR'⟩
        · exact absurd h0 hu0
        obtain ⟨hmN, hmg⟩ := he9 u
        set m := e9Idx mul y.2.1 y.2.2 (3 * u.1.val + u.2.val) with hm
        obtain ⟨-, q', hq', hq'm⟩ := hinv.2 m hmN hcr'
        set r' := (classTable c.edges mul X).2[m]! with hr'
        have hr86 : ∃ w ∈ JG, gi 10 = w * gi r' * w⁻¹ ∨ gi 94 = w * gi r' * w⁻¹ := by
          unfold isR86 at hR'
          simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Bool.and_eq_true] at hR'
          rcases hR' with (h10 | h94) | ⟨f, hf, hfr, hft⟩
          · exact ⟨1, JG.one_mem, Or.inl (by rw [h10]; group)⟩
          · exact ⟨1, JG.one_mem, Or.inr (by rw [h94]; group)⟩
          · obtain ⟨-, -, w, hwJ, hw⟩ := hfusG f hf
            rw [hfr] at hw
            rcases hft with h10 | h94
            · exact ⟨w, hwJ, Or.inl (by rw [← h10]; exact hw)⟩
            · exact ⟨w, hwJ, Or.inr (by rw [← h94]; exact hw)⟩
        obtain ⟨w', hw'J, hw'⟩ := hr86
        have hcJ : q' * w'⁻¹ ∈ JG := JG.mul_mem (hQJ hq') (JG.inv_mem hw'J)
        rcases hw' with hw' | hw'
        · left
          refine isConj_J (c := ⟨q' * w'⁻¹, hcJ⟩) ?_
          rw [← hmg, hq'm, ← hzJ, hw']
          dsimp only
          group
        · right
          refine isConj_J (c := ⟨q' * w'⁻¹, hcJ⟩) ?_
          have : ((zJ ^ 2 : JG) : GL (Fin 248) (ZMod 2)) = gi 94 := by
            rw [hz94, hzJ, pow_two, Subgroup.coe_mul]
          rw [← hmg, hq'm, this, hw']
          dsimp only
          group

theorem rp_seedA : Rp (rowsOf seedA) CFSG.Sporadic.Th.gA := by
  show CFSG.Sporadic.Th.rowsMatrix _ = _
  rw [CFSG.Sporadic.Th.rowsMatrix_rowsOf_seedA]
  rfl

theorem rp_seedB : Rp (rowsOf seedB) CFSG.Sporadic.Th.gB := by
  show CFSG.Sporadic.Th.rowsMatrix _ = _
  rw [CFSG.Sporadic.Th.rowsMatrix_rowsOf_seedB]
  rfl

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent in
theorem thLocal_sound
    (h : thLocalCheck thLocal (rowsOf seedA) (rowsOf seedB) = true) :
    ∃ Q : Subgroup CFSG.Sporadic.Th.J, Nat.card Q = 3 ^ 10 ∧ zJ ∈ Q ∧ zJ ^ 3 = 1 ∧
      (∀ q ∈ Q, q * zJ = zJ * q) ∧ (∃ u : CFSG.Sporadic.Th.J, orderOf u = 2 ∧ u * zJ = zJ * u) ∧
      ∀ s ∈ Q, orderOf s = 3 → ∃ t : CFSG.Sporadic.Th.J, IsConj s t ∧
        3 ^ 7 ≤ Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set CFSG.Sporadic.Th.J)) ∧
        ∃ E : Subgroup CFSG.Sporadic.Th.J,
          E ≤ Subgroup.centralizer ({t} : Set CFSG.Sporadic.Th.J) ∧ IsElemAbelian 3 E ∧
            Nat.card E = 9 ∧ ∀ x ∈ E, x ≠ 1 → IsConj x zJ ∨ IsConj x (zJ ^ 2) := by
  unfold thLocalCheck at h
  dsimp only at h
  exact thLocalChecks_sound rp_seedA rp_seedB rowsMatrix_zRows rfl rfl h

end Main

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThLocal
