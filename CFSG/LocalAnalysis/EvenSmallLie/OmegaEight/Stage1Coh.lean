module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1CohCheck
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Bits
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1

open Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar

abbrev Mat6 := Matrix (Fin 6) (Fin 6) (ZMod 2)

@[expose] def diagM6 (B : Mat6) : Mat6 := Matrix.of fun r c => if r = c then B r c else 0

@[expose] def outerM6 (u w : V6) : Mat6 := Matrix.of fun a b => u a * w b

@[expose] def rowM6 (B : Mat6) (g : ℕ) : V6 := fun b => if h : g < 6 then B ⟨g, h⟩ b else 0

theorem toMat_diag6 (B : Array ℕ) : toMat 6 6 (diag6 B) = diagM6 (toMat 6 6 B) := by
  ext r c
  rw [toMat_apply, diag6, getD_ofFn, Nat.testBit_and, Nat.testBit_two_pow, diagM6, Matrix.of_apply,
    toMat_apply]
  by_cases h : r = c
  · subst h; simp
  · have : (r : ℕ) ≠ c := Fin.val_ne_of_ne h
    simp [h, this]

theorem toMat_outer6 (u w : ℕ) : toMat 6 6 (outer6 u w) = outerM6 (toVec 6 u) (toVec 6 w) := by
  ext a b
  rw [toMat_apply, outer6, getD_ofFn, outerM6, Matrix.of_apply, toVec, toVec]
  cases u.testBit a <;> simp

theorem rowM6_toMat (B : Array ℕ) {g : ℕ} (hg : g < 6) :
    rowM6 (toMat 6 6 B) g = toVec 6 (B.getD g 0) := by
  ext b
  rw [rowM6, dite_eq_left hg, toMat_apply, toVec]

theorem toMat_combo6 (row : ℕ) (C : ℕ → Array ℕ) (k : ℕ) :
    toMat 6 6 (combo6 row C k) = ∑ d ∈ Finset.range k, bz (row.testBit d) • toMat 6 6 (C d) := by
  induction k with
  | zero =>
    rw [combo6, Finset.range_zero, Finset.sum_empty]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  | succ k ih =>
    rw [combo6, Finset.sum_range_succ, ← ih]
    split_ifs with h
    · rw [toMat_bxor, h, bz_true, one_smul]
    · rw [Bool.not_eq_true] at h
      rw [h, bz_false, zero_smul, add_zero]

@[expose] def gamBlockM (ε : Eps) (C : ℕ → Mat6) (k : ℕ) : Mat6 :=
  if k < 6 then C k + (C k)ᵀ
  else if k < 12 then diagM6 (C (k - 6))
  else
    (∑ d : Fin 6, toVec 6 ((genRows ε ((k - 12) / 6)).getD ((k - 12) % 6) 0) d • C d +
        (genMat ε ((k - 12) / 6))ᵀ * C ((k - 12) % 6) * genMat ε ((k - 12) / 6)) +
      (outerM6 (rowM6 (C 6) ((k - 12) / 6))
          (toVec 6 ((genRows ε ((k - 12) / 6)).getD ((k - 12) % 6) 0)) +
        outerM6 (toVec 6 ((genRows ε ((k - 12) / 6)).getD ((k - 12) % 6) 0))
          (rowM6 (C 6) ((k - 12) / 6)))

theorem toMat_gamBlock (ε : Eps) (C : ℕ → Array ℕ) {k : ℕ} (hk : k < 48) :
    toMat 6 6 (gamBlock ε C k) = gamBlockM ε (fun s => toMat 6 6 (C s)) k := by
  unfold gamBlock gamBlockM
  split_ifs with h1 h2
  · rw [toMat_bxor, toMat_btr]
  · rw [toMat_diag6]
  · have hg : (k - 12) / 6 < 6 := by omega
    rw [toMat_bxor, toMat_bxor, toMat_bxor, toMat_combo6, toMat_bmul, toMat_bmul, toMat_btr,
      toMat_outer6, toMat_outer6, rowM6_toMat _ hg, genMat, mul_assoc]
    rw [← Fin.sum_univ_eq_sum_range (fun d => bz (((genRows ε ((k - 12) / 6)).getD
      ((k - 12) % 6) 0).testBit d) • toMat 6 6 (C d)) 6]
    rfl

theorem gamBlockM_congr (ε : Eps) {C C' : ℕ → Mat6} (h : ∀ s < 7, C s = C' s) {k : ℕ}
    (hk : k < 48) : gamBlockM ε C k = gamBlockM ε C' k := by
  unfold gamBlockM
  split_ifs with h1 h2
  · rw [h k (by omega)]
  · rw [h (k - 6) (by omega)]
  · have hsum : (∑ d : Fin 6, toVec 6 ((genRows ε ((k - 12) / 6)).getD ((k - 12) % 6) 0) d •
        C d) = ∑ d : Fin 6, toVec 6 ((genRows ε ((k - 12) / 6)).getD ((k - 12) % 6) 0) d • C' d :=
      Finset.sum_congr rfl fun d _ => by rw [h d (by omega)]
    rw [hsum, h ((k - 12) % 6) (by omega), h 6 (by omega)]

theorem gamBlockM_add (ε : Eps) (C C' : ℕ → Mat6) (k : ℕ) :
    gamBlockM ε (C + C') k = gamBlockM ε C k + gamBlockM ε C' k := by
  unfold gamBlockM
  split_ifs
  · simp only [Pi.add_apply, transpose_add]; abel
  · ext r c; simp only [diagM6, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]; split_ifs <;> simp
  · have hrow : ∀ g, rowM6 (C 6 + C' 6) g = rowM6 (C 6) g + rowM6 (C' 6) g := by
      intro g; ext b; simp only [rowM6, Pi.add_apply, Matrix.add_apply]; split_ifs <;> simp
    have hout1 : ∀ u w w' : V6, outerM6 (w + w') u = outerM6 w u + outerM6 w' u := by
      intro u w w'; ext a b; simp [outerM6, add_mul]
    have hout2 : ∀ u w w' : V6, outerM6 u (w + w') = outerM6 u w + outerM6 u w' := by
      intro u w w'; ext a b; simp [outerM6, mul_add]
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib, mul_add, add_mul, hrow, hout1,
      hout2]
    abel

theorem gamBlockM_smul (ε : Eps) (a : ZMod 2) (C : ℕ → Mat6) (k : ℕ) :
    gamBlockM ε (a • C) k = a • gamBlockM ε C k := by
  unfold gamBlockM
  split_ifs
  · simp only [Pi.smul_apply, transpose_smul, smul_add]
  · ext r c; simp only [diagM6, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply]
    split_ifs <;> simp
  · have hrow : ∀ g, rowM6 (a • C 6) g = a • rowM6 (C 6) g := by
      intro g; ext b; simp only [rowM6, Pi.smul_apply, Matrix.smul_apply]; split_ifs <;> simp
    have hout1 : ∀ u w : V6, outerM6 (a • w) u = a • outerM6 w u := by
      intro u w; ext i j; simp [outerM6, mul_assoc]
    have hout2 : ∀ u w : V6, outerM6 u (a • w) = a • outerM6 u w := by
      intro u w; ext i j; simp [outerM6]; ring
    simp only [Pi.smul_apply, hrow, hout1, hout2, smul_add, Finset.smul_sum, mul_smul_comm,
      smul_mul_assoc]
    congr 2
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [smul_comm]

@[expose] def gamLin (ε : Eps) : (Fin 7 → Mat6) →ₗ[ZMod 2] (Fin 48 → Mat6) where
  toFun C k := gamBlockM ε (fun s => if h : s < 7 then C ⟨s, h⟩ else 0) k
  map_add' C C' := by
    ext1 k
    rw [Pi.add_apply, ← gamBlockM_add]
    congr 1
    ext1 s
    by_cases hs : s < 7 <;> simp [hs]
  map_smul' a C := by
    ext1 k
    rw [Pi.smul_apply, RingHom.id_apply, ← gamBlockM_smul]
    congr 1
    ext1 s
    by_cases hs : s < 7 <;> simp [hs]

@[expose] def gamF (ε : Eps) : (Fin (7 * (6 * 6)) → ZMod 2) →ₗ[ZMod 2] (Fin (48 * (6 * 6)) → ZMod 2) :=
  (blocksEquivN 6 48).symm.toLinearMap ∘ₗ gamLin ε ∘ₗ (blocksEquivN 6 7).toLinearMap

theorem toVec_gamFb (ε : Eps) (v : ℕ) :
    toVec (48 * (6 * 6)) (gamFb ε v) = gamF ε (toVec (7 * (6 * 6)) v) := by
  rw [gamFb, toVec_packN]
  simp only [gamF, LinearMap.comp_apply, LinearEquiv.coe_coe, blocksEquivN_symm_apply,
    blocksEquivN_apply, gamLin, LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  ext1 k
  rw [toMat_gamBlock ε _ k.isLt]
  refine gamBlockM_congr ε (fun s hs => ?_) k.isLt
  rw [dite_eq_left hs]
  exact toMat_unpackN 6 7 v ⟨s, hs⟩

theorem toMat_transpose_mulVec6 (n m : ℕ) (A : Array ℕ) (e : Fin n → ZMod 2) :
    (toMat n m A)ᵀ *ᵥ e = ∑ c : Fin n, e c • toVec m (A.getD c 0) := by
  ext i
  simp only [mulVec, dotProduct, transpose_apply, toMat_apply, Finset.sum_apply, Pi.smul_apply,
    toVec, smul_eq_mul, mul_comm]

theorem gamSol_entry : ∀ a b c m : Fin 6, toMat 6 6 (Array.ofFn (n := 6) fun r =>
    (if (r : ℕ) = c then 2 ^ (m : ℕ) else 0) ^^^ (if (r : ℕ) = m then 2 ^ (c : ℕ) else 0)) a b =
      (if a = c ∧ b = m then 1 else 0) + (if a = m ∧ b = c then 1 else 0) := by
  decide

theorem exists_mu_of_gamma (ε : Eps) (Γ : Fin 6 → Mat6) (Λ : Mat6)
    (halt : ∀ c, Γ c + (Γ c)ᵀ = 0) (hdiag : ∀ c a, Γ c a a = 0)
    (heq : ∀ g c : Fin 6, ((∑ d : Fin 6, genMat ε g c d • Γ d) +
        (genMat ε g)ᵀ * Γ c * genMat ε g) +
      (outerM6 (fun a => Λ g a) (fun b => genMat ε g c b) +
        outerM6 (fun b => genMat ε g c b) (fun a => Λ g a)) = 0) :
    ∃ μ : V6, ∀ c a b, Γ c a b = (if a = c then μ b else 0) + (if b = c then μ a else 0) := by
  set C : Fin 7 → Mat6 := fun s => if h : (s : ℕ) < 6 then Γ ⟨s, h⟩ else Λ with hC
  set C' : ℕ → Mat6 := fun s => if h : s < 6 then Γ ⟨s, h⟩ else Λ with hC'
  have hCC' : ∀ s < 7, (fun s => if h : s < 7 then C ⟨s, h⟩ else 0) s = C' s := by
    intro s hs
    simp only [hC, hC', dite_eq_left hs]
  have hC'Γ : ∀ s (h : s < 6), C' s = Γ ⟨s, h⟩ := fun s h => by simp only [hC', dite_eq_left h]
  have hC'6 : C' 6 = Λ := by simp only [hC']; rfl
  have hblock : ∀ k < 48, gamBlockM ε C' k = 0 := by
    intro k hk
    unfold gamBlockM
    split_ifs with h1 h2
    · rw [hC'Γ k h1]
      exact halt ⟨k, h1⟩
    · have h4 : k - 6 < 6 := by omega
      rw [hC'Γ _ h4]
      ext r c
      simp only [diagM6, Matrix.of_apply, Matrix.zero_apply]
      split_ifs with h3
      · subst h3
        exact hdiag ⟨k - 6, h4⟩ r
      · rfl
    · have hg : (k - 12) / 6 < 6 := by omega
      have hc : (k - 12) % 6 < 6 := Nat.mod_lt _ (by norm_num)
      have h := heq ⟨_, hg⟩ ⟨_, hc⟩
      have hrow : rowM6 (C' 6) ((k - 12) / 6) = fun a => Λ ⟨_, hg⟩ a := by
        ext a
        rw [hC'6, rowM6, dite_eq_left hg]
      have hsum : (∑ d : Fin 6, toVec 6 ((genRows ε ((k - 12) / 6)).getD ((k - 12) % 6) 0) d •
          C' d) = ∑ d : Fin 6, genMat ε ((k - 12) / 6) ⟨(k - 12) % 6, hc⟩ d • Γ d :=
        Finset.sum_congr rfl fun d _ => by rw [hC'Γ d d.isLt]; rfl
      have hm : toVec 6 ((genRows ε ((k - 12) / 6)).getD ((k - 12) % 6) 0) =
          fun b => genMat ε ((k - 12) / 6) ⟨(k - 12) % 6, hc⟩ b := rfl
      rw [hrow, hC'Γ _ hc, hsum, hm]
      exact h
  have hlin : gamLin ε C = 0 := by
    ext1 k
    simp only [gamLin, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
    rw [gamBlockM_congr ε hCC' k.isLt]
    exact hblock k k.isLt
  have hR : toMat (48 * (6 * 6)) (7 * (6 * 6)) (linBits (7 * (6 * 6)) (48 * (6 * 6)) (gamFb ε)) *ᵥ
      vecOfN 6 7 C = 0 := by
    rw [toMat_linBits_mulVec (gamFb ε) (gamF ε) (fun j => by rw [toVec_gamFb, toVec_two_pow])]
    simp only [gamF, LinearMap.comp_apply, LinearEquiv.coe_coe, blocksEquivN_apply,
      blocksOfN_vecOfN, hlin, blocksEquivN_symm_apply]
    ext i
    simp [vecOfN]
  obtain ⟨e, he⟩ := (cohChecks ε).2.1 _ hR
  rw [toMat_transpose_mulVec6] at he
  refine ⟨e, fun c a b => ?_⟩
  have h1 := congrArg (fun y => (blocksEquivN 6 7) y ⟨c, by omega⟩ a b) he
  simp only [blocksEquivN_apply, blocksOfN_vecOfN, hC, c.isLt, dite_true, map_sum,
    map_smul, Finset.sum_apply, Pi.smul_apply, Matrix.sum_apply, Matrix.smul_apply] at h1
  have hm : ∀ m : Fin 6, blocksOfN 6 7 (toVec (7 * 36) ((Array.ofFn (n := 6) fun m =>
      gamSol ε m).getD m 0)) ⟨c, by omega⟩ a b =
        (if a = c ∧ b = m then 1 else 0) + (if a = m ∧ b = c then 1 else 0) := by
    intro m
    rw [getD_ofFn, gamSol, blocksOfN_packN]
    have hc6 : ((⟨c, by omega⟩ : Fin 7) : ℕ) < 6 := c.isLt
    simp only [hc6, ite_true]
    exact gamSol_entry a b c m
  simp only [hm] at h1
  rw [h1]
  simp only [smul_eq_mul, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
  congr 1
  · by_cases hac : a = c
    · simp [hac]
    · simp [hac]
  · by_cases hbc : b = c
    · simp [hbc]
    · simp [hbc]

@[expose] def urMat6 (ε : Eps) (C : ℕ → Mat6) : List ℕ → Mat6 × Mat6
  | [] => (1, 0)
  | s :: w => (genMat ε s * (urMat6 ε C w).1, genMat ε s * (urMat6 ε C w).2 + C s * (urMat6 ε C w).1)

theorem toMat_id6' : toMat 6 6 id6 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem toMat_zero6 : toMat 6 6 zero6 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem toMat_urPair6 (ε : Eps) (C : ℕ → Array ℕ) (w : List ℕ) :
    toMat 6 6 (urPair6 ε C w).1 = (urMat6 ε (fun s => toMat 6 6 (C s)) w).1 ∧
      toMat 6 6 (urPair6 ε C w).2 = (urMat6 ε (fun s => toMat 6 6 (C s)) w).2 := by
  induction w with
  | nil => exact ⟨toMat_id6', toMat_zero6⟩
  | cons s w ih =>
    simp only [urPair6, urMat6, toMat_bmul, toMat_bxor, ih.1, ih.2, genMat, and_self]

theorem urMat6_fst (ε : Eps) (C C' : ℕ → Mat6) (w : List ℕ) :
    (urMat6 ε C w).1 = (urMat6 ε C' w).1 := by
  induction w with
  | nil => rfl
  | cons s w ih => simp only [urMat6, ih]

theorem urMat6_congr (ε : Eps) {C C' : ℕ → Mat6} (w : List ℕ) (h : ∀ s ∈ w, C s = C' s) :
    (urMat6 ε C w).2 = (urMat6 ε C' w).2 := by
  induction w with
  | nil => rfl
  | cons s w ih =>
    simp only [urMat6, urMat6_fst ε C C' w, ih (fun x hx => h x (List.mem_cons_of_mem _ hx)),
      h s List.mem_cons_self]

theorem urMat6_add (ε : Eps) (C C' : ℕ → Mat6) (w : List ℕ) :
    (urMat6 ε (C + C') w).2 = (urMat6 ε C w).2 + (urMat6 ε C' w).2 := by
  induction w with
  | nil => simp [urMat6]
  | cons s w ih =>
    simp only [urMat6, ih, Pi.add_apply, urMat6_fst ε (C + C') C w, urMat6_fst ε C' C w]
    noncomm_ring

theorem urMat6_smul (ε : Eps) (c : ZMod 2) (C : ℕ → Mat6) (w : List ℕ) :
    (urMat6 ε (c • C) w).2 = c • (urMat6 ε C w).2 := by
  induction w with
  | nil => simp [urMat6]
  | cons s w ih =>
    simp only [urMat6, ih, Pi.smul_apply, urMat6_fst ε (c • C) C w, smul_add, mul_smul_comm,
      smul_mul_assoc]

@[expose] def extC (C : Fin 6 → Mat6) (s : ℕ) : Mat6 := if h : s < 6 then C ⟨s, h⟩ else 0

@[expose] def urLin6 (ε : Eps) : (Fin 6 → Mat6) →ₗ[ZMod 2] (Fin (nRels ε) → Mat6) where
  toFun C k := (urMat6 ε (extC C) ((extRels ε).getD k [])).2
  map_add' C C' := by
    ext1 k
    rw [Pi.add_apply, ← urMat6_add]
    congr 2
    ext1 s
    by_cases hs : s < 6 <;> simp [extC, hs]
  map_smul' c C := by
    ext1 k
    rw [Pi.smul_apply, RingHom.id_apply, ← urMat6_smul]
    congr 2
    ext1 s
    by_cases hs : s < 6 <;> simp [extC, hs]

@[expose] def extF (ε : Eps) :
    (Fin (6 * (6 * 6)) → ZMod 2) →ₗ[ZMod 2] (Fin (nRels ε * (6 * 6)) → ZMod 2) :=
  (blocksEquivN 6 (nRels ε)).symm.toLinearMap ∘ₗ urLin6 ε ∘ₗ (blocksEquivN 6 6).toLinearMap

@[expose] def cobLin6 (ε : Eps) : Mat6 →ₗ[ZMod 2] (Fin 6 → Mat6) where
  toFun X s := genMat ε s * X + X * genMat ε s
  map_add' X X' := by ext1 s; simp only [Pi.add_apply]; noncomm_ring
  map_smul' c X := by ext1 s; simp [smul_add]

@[expose] def cobF6 (ε : Eps) : (Fin (1 * (6 * 6)) → ZMod 2) →ₗ[ZMod 2] (Fin (6 * (6 * 6)) → ZMod 2) :=
  (blocksEquivN 6 6).symm.toLinearMap ∘ₗ cobLin6 ε ∘ₗ
    (LinearMap.proj 0 ∘ₗ (blocksEquivN 6 1).toLinearMap)

theorem extRels_lt (ε : Eps) {k s : ℕ} (hs : s ∈ (extRels ε).getD k []) : s < 6 := by
  have h : ∀ w ∈ extRels ε, ∀ s ∈ w, s < 6 := by
    have hb : ((extRels ε).all fun w => w.all fun s => decide (s < 6)) = true := by
      cases ε <;> decide
    simp only [List.all_eq_true, decide_eq_true_eq] at hb
    exact hb
  by_cases hk : k < (extRels ε).length
  · rw [List.getD_eq_getElem _ _ hk] at hs
    exact h _ (List.getElem_mem hk) s hs
  · rw [List.getD_eq_default _ _ (not_lt.mp hk)] at hs
    simp at hs

theorem toVec_extFb (ε : Eps) (v : ℕ) :
    toVec (nRels ε * (6 * 6)) (extFb ε v) = extF ε (toVec (6 * (6 * 6)) v) := by
  rw [extFb, toVec_packN]
  simp only [extF, LinearMap.comp_apply, LinearEquiv.coe_coe, blocksEquivN_symm_apply,
    blocksEquivN_apply]
  congr 1
  ext1 k
  rw [(toMat_urPair6 _ _ _).2]
  simp only [urLin6, LinearMap.coe_mk, AddHom.coe_mk]
  refine urMat6_congr ε _ fun s hs => ?_
  have hs6 := extRels_lt ε hs
  rw [extC, dite_eq_left hs6]
  exact toMat_unpackN 6 6 v ⟨s, hs6⟩

theorem toVec_cobFb6 (ε : Eps) (v : ℕ) :
    toVec (6 * (6 * 6)) (cobFb6 ε v) = cobF6 ε (toVec (1 * (6 * 6)) v) := by
  rw [cobFb6, toVec_packN]
  simp only [cobF6, LinearMap.comp_apply, LinearEquiv.coe_coe, blocksEquivN_symm_apply,
    blocksEquivN_apply, LinearMap.proj_apply]
  congr 1
  ext1 s
  simp only [toMat_bxor, toMat_bmul, cobLin6, LinearMap.coe_mk, AddHom.coe_mk, genMat]
  rw [← toMat_unpackN 6 1 v 0]
  rfl

theorem exists_coboundary6 (ε : Eps) (C : Fin 6 → Mat6)
    (hC : ∀ w ∈ extRels ε, (urMat6 ε (extC C) w).2 = 0) :
    ∃ X : Mat6, ∀ s : Fin 6, C s = genMat ε s * X + X * genMat ε s := by
  have hF : extF ε (vecOfN 6 6 C) = 0 := by
    simp only [extF, LinearMap.comp_apply, LinearEquiv.coe_coe, blocksEquivN_apply,
      blocksOfN_vecOfN, blocksEquivN_symm_apply]
    have : urLin6 ε C = 0 := by
      ext1 k
      simp only [urLin6, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
      by_cases hk : (k : ℕ) < (extRels ε).length
      · rw [List.getD_eq_getElem _ _ hk]
        exact hC _ (List.getElem_mem hk)
      · rw [List.getD_eq_default _ _ (not_lt.mp hk)]
        rfl
    rw [this]
    ext i
    simp [vecOfN]
  have hR : toMat (nRels ε * (6 * 6)) (6 * (6 * 6)) (linBits (6 * (6 * 6)) (nRels ε * (6 * 6))
      (extFb ε)) *ᵥ vecOfN 6 6 C = 0 := by
    rw [toMat_linBits_mulVec (extFb ε) (extF ε) (fun j => by rw [toVec_extFb, toVec_two_pow]),
      hF]
  obtain ⟨e, he⟩ := (cohChecks ε).2.2 _ hR
  have hB : (toMat 36 (6 * (6 * 6)) (Array.ofFn (n := 36) fun j => cobFb6 ε (2 ^ (j : ℕ))))ᵀ *ᵥ e =
      cobF6 ε e := by
    rw [← toMat_btr]
    exact toMat_linBits_mulVec (cobFb6 ε) (cobF6 ε) (fun j => by rw [toVec_cobFb6, toVec_two_pow]) e
  rw [hB] at he
  refine ⟨blocksOfN 6 1 e 0, fun s => ?_⟩
  have := congrArg (fun y => blocksOfN 6 6 y s) he
  simp only [cobF6, LinearMap.comp_apply, LinearEquiv.coe_coe, blocksEquivN_apply,
    blocksEquivN_symm_apply, LinearMap.proj_apply, blocksOfN_vecOfN] at this
  exact this

end CFSG.EvenSmallLie.OmegaEight.Stage1
