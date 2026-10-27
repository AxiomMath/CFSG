module

public import Certificates.Data.Kernel.Misc.A6C5Cent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CPair

public section

namespace CFSG.KS.A6C5

open CFSG.KC.A6C5 CFSG.OddStandard.SmallF3.Omega Subgroup

abbrev M5 := Matrix (Fin 5) (Fin 5) (ZMod 3)

@[expose] def toM (x : List ℕ) : M5 := Matrix.of fun i j => ((en x i j : ℕ) : ZMod 3)

def Cn (x : List ℕ) : Prop := x.length = 25 ∧ ∀ e ∈ x, e < 3

theorem idx_div (i j : Fin 5) : (5 * (i : ℕ) + j) / 5 = i := by omega

theorem idx_mod (i j : Fin 5) : (5 * (i : ℕ) + j) % 5 = j := by omega

theorem en_map (f : ℕ → ℕ) (i j : Fin 5) : en ((List.range 25).map f) i j = f (5 * i + j) := by
  have h : 5 * (i : ℕ) + j < 25 := by omega
  simp [en, List.getD_eq_getElem?_getD, List.getElem?_range h]

theorem cn_map (f : ℕ → ℕ) (hf : ∀ p, f p < 3) : Cn ((List.range 25).map f) := by
  refine ⟨by simp, fun e he => ?_⟩
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp he
  exact hf p

theorem cn_of_cnB {x : List ℕ} (h : cnB x = true) : Cn x := by
  simp only [cnB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  exact h

theorem en_lt {x : List ℕ} (hx : Cn x) (i j : ℕ) : en x i j < 3 := by
  unfold en
  rw [List.getD_eq_getElem?_getD]
  rcases h : x[5 * i + j]? with _ | e
  · simp
  · simp only [Option.getD_some]
    exact hx.2 e (List.mem_of_getElem? h)

theorem eq_of_cn {x : List ℕ} (hx : Cn x) :
    x = (List.range 25).map fun p => en x (p / 5) (p % 5) := by
  refine List.ext_getElem (by simp [hx.1]) fun p h1 _ => ?_
  rw [List.getElem_map, List.getElem_range]
  unfold en
  rw [Nat.div_add_mod, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]

theorem toM_inj {x y : List ℕ} (hx : Cn x) (hy : Cn y) (h : toM x = toM y) : x = y := by
  rw [eq_of_cn hx, eq_of_cn hy]
  refine List.map_congr_left fun p hp => ?_
  have hp' : p < 25 := List.mem_range.mp hp
  have e := congrFun (congrFun h ⟨p / 5, by omega⟩) ⟨p % 5, by omega⟩
  simp only [toM, Matrix.of_apply] at e
  have e' := congrArg ZMod.val e
  rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (en_lt hx _ _),
    Nat.mod_eq_of_lt (en_lt hy _ _)] at e'
  exact e'

theorem toM_mulL (x y : List ℕ) : toM (mulL x y) = toM x * toM y := by
  ext i j
  simp only [mulL, toM, Matrix.of_apply, en_map, idx_div, idx_mod, Matrix.mul_apply,
    Fin.sum_univ_five, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul]
  rfl

theorem toM_addL (x y : List ℕ) : toM (addL x y) = toM x + toM y := by
  ext i j
  simp only [addL, toM, Matrix.of_apply, en_map, idx_div, idx_mod, Matrix.add_apply,
    ZMod.natCast_mod, Nat.cast_add]

theorem toM_trL (x : List ℕ) : toM (trL x) = (toM x).transpose := by
  ext i j
  simp only [trL, toM, Matrix.of_apply, en_map, idx_div, idx_mod, Matrix.transpose_apply]

theorem toM_negL (x : List ℕ) : toM (negL x) = -toM x := by
  ext i j
  have h2 : ((2 : ℕ) : ZMod 3) = -1 := by decide
  simp only [negL, toM, Matrix.of_apply, en_map, idx_div, idx_mod, Matrix.neg_apply,
    ZMod.natCast_mod, Nat.cast_mul, h2, neg_one_mul]

theorem toM_idL : toM idL = 1 := by
  ext i j
  simp only [idL, toM, Matrix.of_apply, en_map, idx_div, idx_mod, Matrix.one_apply, Fin.val_inj]
  split_ifs <;> simp

theorem toM_powL (x : List ℕ) (k : ℕ) : toM (powL x k) = toM x ^ k := by
  induction k with
  | zero => exact toM_idL
  | succ k ih =>
    change toM (mulL x (powL x k)) = _
    rw [toM_mulL, ih, pow_succ']

theorem cn_mulL (x y : List ℕ) : Cn (mulL x y) := cn_map _ fun _ => Nat.mod_lt _ (by norm_num)

theorem cn_negL (x : List ℕ) : Cn (negL x) := cn_map _ fun _ => Nat.mod_lt _ (by norm_num)

theorem cn_idL : Cn idL := cn_map _ fun p => by split_ifs <;> norm_num

theorem toM_colL (X : M5) :
    toM (colL (X 0 0).val (X 1 0).val (X 2 0).val (X 3 0).val (X 4 0).val) =
      X * toM (colL 1 0 0 0 0) := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_five]
  fin_cases i <;> fin_cases j <;> simp [toM, en, colL]

theorem eqS_iff {x y : List ℕ} : eqS x y = true ↔ x = y ∨ x = negL y := by
  simp [eqS]

theorem sim_of_simL {x : List ℕ} (h : simL x = true) : A6CSimMat (toM x) := by
  unfold simL at h
  rcases eqS_iff.mp h with h | h
  · left
    have e := congrArg toM h
    rwa [toM_mulL, toM_trL, toM_idL] at e
  · right
    have e := congrArg toM h
    rwa [toM_mulL, toM_trL, toM_negL, toM_idL] at e

theorem simL_of_sim {x : List ℕ} (hs : A6CSimMat (toM x)) : simL x = true := by
  unfold simL
  rw [eqS_iff]
  rcases hs with h | h
  · left
    refine toM_inj (cn_mulL _ _) cn_idL ?_
    rw [toM_mulL, toM_trL, toM_idL]
    exact h
  · right
    refine toM_inj (cn_mulL _ _) (cn_negL _) ?_
    rw [toM_mulL, toM_trL, toM_negL, toM_idL]
    exact h

theorem eq_of_comm (G X P Bi : M5) (E : ℕ → M5)
    (hB : (G ^ 0 * P * E 0 + (G ^ 1 * P * E 1 + (G ^ 2 * P * E 2 + (G ^ 3 * P * E 3 +
      G ^ 4 * P * E 4)))) * Bi = 1) (hX : X * G = G * X) :
    X = (G ^ 0 * (X * P) * E 0 + (G ^ 1 * (X * P) * E 1 + (G ^ 2 * (X * P) * E 2 +
      (G ^ 3 * (X * P) * E 3 + G ^ 4 * (X * P) * E 4)))) * Bi := by
  have key : ∀ (k : ℕ) (F : M5), X * (G ^ k * P * F) = G ^ k * (X * P) * F := by
    intro k F
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, (Commute.pow_right hX k).eq,
      Matrix.mul_assoc (G ^ k) X P]
  calc X = X * ((G ^ 0 * P * E 0 + (G ^ 1 * P * E 1 + (G ^ 2 * P * E 2 + (G ^ 3 * P * E 3 +
        G ^ 4 * P * E 4)))) * Bi) := by rw [hB, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, Matrix.mul_add, Matrix.mul_add, Matrix.mul_add,
        Matrix.mul_add, key, key, key, key, key]

theorem anti_false (G X : M5) (h5 : G ^ 5 = 1) (hX : X * G = -(G * X)) (hs : A6CSimMat X) :
    False := by
  have h2 : X * G ^ 2 = G ^ 2 * X := by
    rw [pow_two, ← Matrix.mul_assoc, hX, Matrix.neg_mul, Matrix.mul_assoc, hX, Matrix.mul_neg,
      neg_neg, ← Matrix.mul_assoc]
  have hG : (G ^ 2) ^ 3 = G := by
    rw [← pow_mul, pow_succ, h5, Matrix.one_mul]
  have hc : X * G = G * X := by
    have h := (Commute.pow_right h2 3).eq
    rw [hG] at h
    exact h
  have h0 : G * X = 0 := by
    have e : G * X = -(G * X) := hc.symm.trans hX
    ext i j
    have h := congrFun (congrFun e i) j
    rw [Matrix.neg_apply] at h
    rw [Matrix.zero_apply]
    generalize (G * X) i j = t at h ⊢
    revert t
    decide
  have e5 : G ^ 4 * G = 1 := by
    rw [← pow_succ]
    exact h5
  have hX0 : X = 0 := by
    calc X = G ^ 4 * (G * X) := by rw [← Matrix.mul_assoc, e5, Matrix.one_mul]
      _ = 0 := by rw [h0, Matrix.mul_zero]
  have hne : (1 : M5) ≠ 0 := one_ne_zero
  rw [hX0] at hs
  rcases hs with h | h
  · rw [Matrix.zero_mul] at h
    exact hne h.symm
  · rw [Matrix.zero_mul, eq_comm, neg_eq_zero] at h
    exact hne h

theorem toM_kryl (W : List ℕ) : toM (kryl W) =
    toM g0L ^ 0 * toM W * toM (eU 0) + (toM g0L ^ 1 * toM W * toM (eU 1) +
      (toM g0L ^ 2 * toM W * toM (eU 2) + (toM g0L ^ 3 * toM W * toM (eU 3) +
        toM g0L ^ 4 * toM W * toM (eU 4)))) := by
  simp only [kryl, kt, toM_addL, toM_mulL, toM_powL]

theorem basic_parts (h : basic = true) :
    cnB g0L = true ∧ cnB zL = true ∧ cnB nL = true ∧ simL g0L = true ∧ eqS g0L idL = false ∧
      powL g0L 5 = idL ∧ simL zL = true ∧ commL zL g0L = true ∧ eqS (mulL zL zL) idL = true ∧
      mulL (kryl (colL 1 0 0 0 0)) bInv = idL ∧ pwB els = true ∧ simL nL = true ∧
      eqS (mulL nL g0L) (mulL (mulL g0L g0L) nL) = true := by
  unfold basic at h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

theorem mem3 {b : ℕ} (hb : b < 3) : b ∈ [0, 1, 2] := by
  interval_cases b <;> simp

theorem cand_all (h0 : candA 0 = true) (h1 : candA 1 = true) (h2 : candA 2 = true) {a b c d e : ℕ}
    (ha : a < 3) (hb : b < 3) (hc : c < 3) (hd : d < 3) (he : e < 3) :
    candOK a b c d e = true := by
  have h : candA a = true := by
    interval_cases a
    exacts [h0, h1, h2]
  simp only [candA, List.all_eq_true] at h
  exact h b (mem3 hb) c (mem3 hc) d (mem3 hd) e (mem3 he)

theorem cand_of_comm (hb : basic = true) {X : M5} (hX : X * toM g0L = toM g0L * X) :
    X = toM (cand (X 0 0).val (X 1 0).val (X 2 0).val (X 3 0).val (X 4 0).val) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hB, -, -, -⟩ := basic_parts hb
  have hB' := congrArg toM hB
  rw [toM_mulL, toM_kryl, toM_idL] at hB'
  rw [cand, toM_mulL, toM_kryl, toM_colL]
  exact eq_of_comm _ X _ _ (fun j => toM (eU j)) hB' hX

theorem els_form {y : List ℕ} (hy : y ∈ els) : ∃ i < 5, ∃ j < 2, y = el i j := by
  simp only [els, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    exact ⟨_, by norm_num, _, by norm_num, rfl⟩

variable {Γ : Type} [Group Γ] (m : A6CModel 5 Γ)

theorem e_of_eqS {x y : List ℕ} (hy : A6CSimMat (toM y)) (h : eqS x y = true) :
    m.ofMat (toM x) = m.ofMat (toM y) := by
  rcases eqS_iff.mp h with rfl | rfl
  · rfl
  · rw [toM_negL]
    exact m.ofMat_neg hy

theorem eqS_of_e {x y : List ℕ} (hx : Cn x) (hy : Cn y) (sx : A6CSimMat (toM x))
    (sy : A6CSimMat (toM y)) (h : m.ofMat (toM x) = m.ofMat (toM y)) : eqS x y = true := by
  rw [eqS_iff]
  rcases (m.ofMat_eq _ _ sx sy).mp h with h | h
  · exact Or.inl (toM_inj hx hy h)
  · refine Or.inr (toM_inj hx (cn_negL _) ?_)
    rw [toM_negL]
    exact h

theorem e_mulL {x y : List ℕ} (sx : A6CSimMat (toM x)) (sy : A6CSimMat (toM y)) :
    m.ofMat (toM (mulL x y)) = m.ofMat (toM x) * m.ofMat (toM y) := by
  rw [toM_mulL]
  exact m.ofMat_mul _ _ sx sy

section basic

variable (hb : basic = true)
include hb

theorem sG : A6CSimMat (toM g0L) := sim_of_simL (basic_parts hb).2.2.2.1

theorem sZ : A6CSimMat (toM zL) := sim_of_simL (basic_parts hb).2.2.2.2.2.2.1

theorem sN : A6CSimMat (toM nL) := sim_of_simL (basic_parts hb).2.2.2.2.2.2.2.2.2.2.2.1

theorem sim_el (i j : ℕ) : A6CSimMat (toM (el i j)) := by
  rw [el, toM_mulL, toM_powL, toM_powL]
  exact ((sG hb).pow i).mul ((sZ hb).pow j)

theorem e_el (i j : ℕ) :
    m.ofMat (toM (el i j)) = m.ofMat (toM g0L) ^ i * m.ofMat (toM zL) ^ j := by
  rw [el, toM_mulL, toM_powL, toM_powL, m.ofMat_mul _ _ ((sG hb).pow i) ((sZ hb).pow j),
    m.ofMat_pow (sG hb), m.ofMat_pow (sZ hb)]

theorem zg_comm : m.ofMat (toM zL) * m.ofMat (toM g0L) = m.ofMat (toM g0L) * m.ofMat (toM zL) := by
  have h := (basic_parts hb).2.2.2.2.2.2.2.1
  unfold commL at h
  rw [← e_mulL m (sZ hb) (sG hb), ← e_mulL m (sG hb) (sZ hb)]
  exact e_of_eqS m (by rw [toM_mulL]; exact (sG hb).mul (sZ hb)) h

theorem zz : m.ofMat (toM zL) * m.ofMat (toM zL) = 1 := by
  have h := (basic_parts hb).2.2.2.2.2.2.2.2.1
  rw [← e_mulL m (sZ hb) (sZ hb), e_of_eqS m (by rw [toM_idL]; exact A6CSimMat.one) h, toM_idL,
    m.ofMat_one]

theorem g5 : m.ofMat (toM g0L) ^ 5 = 1 := by
  rw [← m.ofMat_pow (sG hb), ← toM_powL, (basic_parts hb).2.2.2.2.2.1, toM_idL, m.ofMat_one]

theorem g1 : m.ofMat (toM g0L) ≠ 1 := by
  intro h
  rw [← m.ofMat_one, ← toM_idL] at h
  have e := eqS_of_e m (cn_of_cnB (basic_parts hb).1) cn_idL (sG hb)
    (by rw [toM_idL]; exact A6CSimMat.one) h
  rw [(basic_parts hb).2.2.2.2.1] at e
  exact Bool.false_ne_true e

theorem nconj : m.ofMat (toM nL) * m.ofMat (toM g0L) * (m.ofMat (toM nL))⁻¹ =
    m.ofMat (toM g0L) ^ 2 := by
  have h := (basic_parts hb).2.2.2.2.2.2.2.2.2.2.2.2
  have sGG : A6CSimMat (toM (mulL g0L g0L)) := by rw [toM_mulL]; exact (sG hb).mul (sG hb)
  have e := e_of_eqS m (by rw [toM_mulL]; exact sGG.mul (sN hb)) h
  rw [e_mulL m (sN hb) (sG hb), e_mulL m sGG (sN hb), e_mulL m (sG hb) (sG hb)] at e
  rw [e, pow_two, mul_inv_cancel_right]

theorem nodup_of_pwB : ∀ L : List (List ℕ), (∀ x ∈ L, Cn x ∧ A6CSimMat (toM x)) →
    pwB L = true → (L.map fun x => m.ofMat (toM x)).Nodup
  | [], _, _ => List.nodup_nil
  | x :: xs, hs, h => by
    simp only [pwB, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_of_pwB xs (fun y hy => hs y (List.mem_cons_of_mem _ hy)) h.2⟩
    obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hm
    have hx := hs x List.mem_cons_self
    have hy' := hs y (List.mem_cons_of_mem _ hy)
    have e := eqS_of_e m hx.1 hy'.1 hx.2 hy'.2 hxy.symm
    rw [h.1 y hy] at e
    exact Bool.false_ne_true e

theorem cent_sub (h0 : candA 0 = true) (h1 : candA 1 = true) (h2 : candA 2 = true) {c : Γ}
    (hc : m.ofMat (toM g0L) * c = c * m.ofMat (toM g0L)) :
    ∃ y ∈ els, m.ofMat (toM y) = c := by
  obtain ⟨X, hXs, rfl⟩ := m.ofMat_surj c
  have hG := sG hb
  rw [← m.ofMat_mul _ _ hG hXs, ← m.ofMat_mul _ _ hXs hG] at hc
  have hG5 : toM g0L ^ 5 = 1 := by
    rw [← toM_powL, (basic_parts hb).2.2.2.2.2.1, toM_idL]
  rcases (m.ofMat_eq _ _ (hG.mul hXs) (hXs.mul hG)).mp hc with hc | hc
  swap
  · exact (anti_false _ X hG5 (neg_eq_iff_eq_neg.mp hc.symm) hXs).elim
  have hX := cand_of_comm hb hc.symm
  have hok := cand_all h0 h1 h2 (ZMod.val_lt (X 0 0)) (ZMod.val_lt (X 1 0))
    (ZMod.val_lt (X 2 0)) (ZMod.val_lt (X 3 0)) (ZMod.val_lt (X 4 0))
  unfold candOK at hok
  have hcn := cn_mulL (kryl (colL (X 0 0).val (X 1 0).val (X 2 0).val (X 3 0).val (X 4 0).val))
    bInv
  rw [← cand] at hcn
  generalize cand (X 0 0).val (X 1 0).val (X 2 0).val (X 3 0).val (X 4 0).val = y0 at hX hok hcn
  subst hX
  rw [simL_of_sim hXs] at hok
  simp only [Bool.not_true, Bool.false_or, List.any_eq_true] at hok
  obtain ⟨y, hy, hey⟩ := hok
  obtain ⟨i, -, j, -, rfl⟩ := els_form hy
  exact ⟨_, hy, (e_of_eqS m (sim_el hb i j) hey).symm⟩

end basic

theorem a6c5_facts (hb : basic = true) (h0 : candA 0 = true) (h1 : candA 1 = true)
    (h2 : candA 2 = true) (Γ : Type) [Group Γ] (m : A6CModel 5 Γ) :
    A6CPairFacts Γ (fun _ => True) 10 2 := by
  classical
  set g : Γ := m.ofMat (toM g0L) with hg
  set z : Γ := m.ofMat (toM zL) with hz
  have hzg : z * g = g * z := zg_comm m hb
  have hzz : z * z = 1 := zz m hb
  have hg5 : g ^ 5 = 1 := g5 m hb
  have hg1 : g ≠ 1 := g1 m hb
  have hcent : ∀ c : Γ, g * c = c * g → ∃ i < 5, ∃ j < 2, c = g ^ i * z ^ j := by
    intro c hc
    obtain ⟨y, hy, rfl⟩ := cent_sub m hb h0 h1 h2 hc
    obtain ⟨i, hi, j, hj, rfl⟩ := els_form hy
    exact ⟨i, hi, j, hj, e_el m hb i j⟩
  have hmemC : ∀ c : Γ, c ∈ centralizer ({g} : Set Γ) ↔ g * c = c * g := by
    intro c
    rw [Subgroup.mem_centralizer_iff]
    simp
  refine ⟨g, m.ofMat (toM nL), hg5, hg1, nconj m hb, ?_, ?_⟩
  ·
    set L := els.map fun x => m.ofMat (toM x) with hL
    have hnd : L.Nodup := nodup_of_pwB m hb els
      (fun x hx => by
        obtain ⟨i, -, j, -, rfl⟩ := els_form hx
        exact ⟨cn_mulL _ _, sim_el hb i j⟩) (basic_parts hb).2.2.2.2.2.2.2.2.2.2.1
    have hset : (centralizer ({g} : Set Γ) : Set Γ) = ↑L.toFinset := by
      ext c
      rw [SetLike.mem_coe, hmemC, Finset.mem_coe, List.mem_toFinset]
      constructor
      · intro hc
        obtain ⟨y, hy, rfl⟩ := cent_sub m hb h0 h1 h2 hc
        exact List.mem_map.mpr ⟨y, hy, rfl⟩
      · intro hc
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hc
        obtain ⟨i, -, j, -, rfl⟩ := els_form hy
        rw [e_el m hb i j, ← hg, ← hz]
        have hc' : Commute g (g ^ i * z ^ j) :=
          ((Commute.refl g).pow_right i).mul_right ((Commute.symm hzg).pow_right j)
        exact hc'.eq
    change Nat.card ((centralizer ({g} : Set Γ) : Set Γ)) = 10
    rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, hL,
      List.length_map]
    rfl
  · intro a _ ha2 hag _
    have hsub : ∀ c ∈ centralizer ({a, g} : Set Γ), c = 1 ∨ c = z := by
      intro c hc
      rw [Subgroup.mem_centralizer_iff] at hc
      have hca : a * c = c * a := hc a (by simp)
      obtain ⟨i, hi, j, hj, rfl⟩ := hcent _ (hc g (by simp))
      have hsq : g ^ i * z ^ j * (g ^ i * z ^ j) = g ^ (2 * i) := by
        have hczg : Commute z g := hzg
        have hcz : Commute (z ^ j) (g ^ i) := hczg.pow_pow j i
        rw [mul_assoc, ← mul_assoc (z ^ j), hcz.eq, mul_assoc, ← mul_assoc, ← pow_add,
          ← pow_add, ← two_mul, ← two_mul, pow_mul z, pow_two, hzz, one_pow, mul_one]
      have hasq : Commute a (g ^ (2 * i)) := by
        rw [← hsq]
        exact (Commute.mul_right hca hca)
      have hi0 : i = 0 := by
        by_contra hne
        have hgen : ∃ k : ℕ, (g ^ (2 * i)) ^ k = g := by
          have hp : ∀ n : ℕ, g ^ n = g ^ (n % 5) := fun n => pow_eq_pow_mod n hg5
          interval_cases i
          · exact absurd rfl hne
          · exact ⟨3, by rw [← pow_mul, hp]; simp⟩
          · exact ⟨4, by rw [← pow_mul, hp]; simp⟩
          · exact ⟨1, by rw [← pow_mul, hp]; simp⟩
          · exact ⟨2, by rw [← pow_mul, hp]; simp⟩
        obtain ⟨k, hk⟩ := hgen
        have hag' : Commute a g := by
          rw [← hk]
          exact hasq.pow_right k
        have h4 : g ^ 4 = 1 := by
          have ha4 : a ^ 4 = 1 := by
            rw [pow_succ, pow_succ, pow_succ, pow_one, ha2, one_mul, ha2]
          rw [← hag, hag'.mul_pow, ha4, one_mul]
        apply hg1
        rw [← hg5, pow_succ, h4, one_mul]
      subst hi0
      interval_cases j
      · left
        simp
      · right
        simp
    constructor
    · have hss : (centralizer ({a, g} : Set Γ) : Set Γ) ⊆ ({1, z} : Set Γ) := by
        intro c hc
        rcases hsub c hc with rfl | rfl <;> simp
      change Nat.card ((centralizer ({a, g} : Set Γ) : Set Γ)) ≤ 2
      rw [Nat.card_coe_set_eq]
      calc _ ≤ ({1, z} : Set Γ).ncard := Set.ncard_le_ncard hss (Set.toFinite _)
        _ ≤ 2 := by
          refine (Set.ncard_insert_le _ _).trans ?_
          rw [Set.ncard_singleton]
    · intro c hc
      rcases hsub c hc with rfl | rfl
      · exact one_mul 1
      · exact hzz

end CFSG.KS.A6C5
