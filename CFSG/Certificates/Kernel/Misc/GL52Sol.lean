module

public import CFSG.Certificates.Kernel.Misc.GL52Elim
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.KC.Misc.GLM.Ech

open CFSG.KC.Misc.GLM Module

abbrev M5 := Matrix (Fin 5) (Fin 5) (ZMod 2)

@[expose] def mat (v : Fin 25 → ZMod 2) : M5 := fun i j => v ⟨5 * i + j, by omega⟩

@[expose] def vec (M : M5) : Fin 25 → ZMod 2 := fun q => M ⟨q / 5, by omega⟩ ⟨q % 5, by omega⟩

theorem mat_vec (M : M5) : mat (vec M) = M := by
  ext i j
  change M ⟨(5 * i + j) / 5, _⟩ ⟨(5 * i + j) % 5, _⟩ = M i j
  congr 1 <;> ext <;> simp only <;> omega

theorem vec_inj {M N : M5} (h : vec M = vec N) : M = N := by
  rw [← mat_vec M, ← mat_vec N, h]

theorem mat_add (v w : Fin 25 → ZMod 2) : mat (v + w) = mat v + mat w := rfl

theorem mat_smul (c : ZMod 2) (v : Fin 25 → ZMod 2) : mat (c • v) = c • mat v := rfl

@[expose] def blk (p : M5 × M5) (v : Fin 25 → ZMod 2) : M5 := mat v * p.1 + p.2 * mat v

theorem blk_add (p : M5 × M5) (v w : Fin 25 → ZMod 2) : blk p (v + w) = blk p v + blk p w := by
  unfold blk
  rw [mat_add, Matrix.add_mul, Matrix.mul_add]
  abel

theorem blk_smul (p : M5 × M5) (c : ZMod 2) (v : Fin 25 → ZMod 2) :
    blk p (c • v) = c • blk p v := by
  unfold blk
  rw [mat_smul, Matrix.smul_mul, Matrix.mul_smul, smul_add]

theorem div25_lt {L : ℕ} (p : Fin (25 * L)) : (p : ℕ) / 25 < L := by
  have := p.isLt
  omega

@[expose] noncomputable def Lps (ps : List (M5 × M5)) :
    (Fin 25 → ZMod 2) →ₗ[ZMod 2] (Fin (25 * ps.length) → ZMod 2) where
  toFun v p := vec (blk (ps.get ⟨(p : ℕ) / 25, div25_lt p⟩) v) ⟨p % 25, by omega⟩
  map_add' v w := by
    funext p
    rw [blk_add]
    rfl
  map_smul' c v := by
    funext p
    rw [blk_smul]
    rfl

theorem Lps_apply (ps : List (M5 × M5)) (v : Fin 25 → ZMod 2) (p : Fin (25 * ps.length)) :
    Lps ps v p = vec (blk (ps.get ⟨(p : ℕ) / 25, div25_lt p⟩) v) ⟨p % 25, by omega⟩ := rfl

theorem add_eq_zero_iff2 (x y : ZMod 2) : x + y = 0 ↔ x = y := by
  revert x y
  decide

theorem Lps_eq_zero (ps : List (M5 × M5)) (v : Fin 25 → ZMod 2) :
    Lps ps v = 0 ↔ ∀ p ∈ ps, mat v * p.1 = p.2 * mat v := by
  constructor
  · intro h p hp
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    ext a b
    have ha := a.isLt
    have hb := b.isLt
    have e := congrFun h ⟨25 * i + (5 * a + b), by omega⟩
    rw [Lps_apply, Pi.zero_apply] at e
    have e1 : ps.get ⟨(25 * i + (5 * (a : ℕ) + b)) / 25, by omega⟩ = ps[i] := by
      rw [List.get_eq_getElem]
      congr 1
      dsimp only
      omega
    rw [e1] at e
    change blk ps[i] v ⟨(25 * i + (5 * (a : ℕ) + b)) % 25 / 5, _⟩
      ⟨(25 * i + (5 * (a : ℕ) + b)) % 25 % 5, _⟩ = 0 at e
    have e3 : (⟨(25 * i + (5 * (a : ℕ) + b)) % 25 / 5, by omega⟩ : Fin 5) = a :=
      Fin.ext (by simp only; omega)
    have e4 : (⟨(25 * i + (5 * (a : ℕ) + b)) % 25 % 5, by omega⟩ : Fin 5) = b :=
      Fin.ext (by simp only; omega)
    rw [e3, e4] at e
    unfold blk at e
    rw [Matrix.add_apply, add_eq_zero_iff2] at e
    exact e
  · intro h
    funext p
    rw [Lps_apply, Pi.zero_apply]
    have hp := h _ (List.get_mem ps ⟨(p : ℕ) / 25, div25_lt p⟩)
    unfold blk
    rw [hp]
    have z : ∀ x : ZMod 2, x + x = 0 := by decide
    change (_ + _ : M5) _ _ = 0
    rw [Matrix.add_apply, z]

@[expose] noncomputable def bk (idx : ℕ) (p : ℕ × ℕ) : ℕ :=
  Nat.xor (mmulK (Nat.shiftLeft 1 idx) p.1) (mmulK p.2 (Nat.shiftLeft 1 idx))

@[expose] noncomputable def imgGo (idx : ℕ) (L : List (ℕ × ℕ)) (sh : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun p _ ih sh => Prod.rec (motive := fun _ => ℕ)
      (fun A B => Nat.lor (Nat.shiftLeft (Nat.xor (mmulK (Nat.shiftLeft 1 idx) A)
        (mmulK B (Nat.shiftLeft 1 idx))) sh) (ih (Nat.add sh 25))) p) L sh

theorem imgK_eq (P : List (ℕ × ℕ)) (idx : ℕ) : imgK P idx = imgGo idx P 0 := rfl

theorem imgGo_cons (idx : ℕ) (p : ℕ × ℕ) (L : List (ℕ × ℕ)) (sh : ℕ) :
    imgGo idx (p :: L) sh = Nat.lor (Nat.shiftLeft (bk idx p) sh) (imgGo idx L (sh + 25)) := by
  rcases p with ⟨A, B⟩
  rfl

theorem shl_testBit (x sh v : ℕ) :
    (Nat.shiftLeft x sh).testBit v = (decide (sh ≤ v) && x.testBit (v - sh)) := by
  change (x <<< sh).testBit v = _
  rw [Nat.testBit_shiftLeft]

theorem lor_testBit (x y v : ℕ) : (Nat.lor x y).testBit v = (x.testBit v || y.testBit v) :=
  Nat.testBit_or x y v

theorem imgGo_low (idx : ℕ) : ∀ (L : List (ℕ × ℕ)) (sh v : ℕ), v < sh →
    (imgGo idx L sh).testBit v = false
  | [], _, v, _ => Nat.zero_testBit v
  | p :: L, sh, v, hv => by
    rw [imgGo_cons, lor_testBit, shl_testBit, decide_eq_false (by omega), Bool.false_and,
      imgGo_low idx L (sh + 25) v (by omega), Bool.false_or]

theorem imgGo_lt (idx : ℕ) : ∀ (L : List (ℕ × ℕ)) (sh : ℕ), (∀ p ∈ L, bk idx p < 2 ^ 25) →
    imgGo idx L sh < 2 ^ (sh + 25 * L.length)
  | [], sh, _ => Nat.two_pow_pos _
  | p :: L, sh, hb => by
    rw [imgGo_cons]
    have h1 := imgGo_lt idx L (sh + 25) fun q hq => hb q (List.mem_cons_of_mem _ hq)
    have hp := hb p (List.mem_cons_self ..)
    have e : sh + 25 * (p :: L).length = sh + 25 + 25 * L.length := by
      rw [List.length_cons]
      ring
    rw [e]
    apply Nat.or_lt_two_pow
    · change bk idx p <<< sh < _
      rw [Nat.shiftLeft_eq, pow_add, pow_add]
      calc bk idx p * 2 ^ sh < 2 ^ 25 * 2 ^ sh := Nat.mul_lt_mul_of_pos_right hp (Nat.two_pow_pos _)
        _ = 2 ^ sh * 2 ^ 25 := Nat.mul_comm _ _
        _ ≤ 2 ^ sh * 2 ^ 25 * 2 ^ (25 * L.length) := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
    · exact h1

theorem imgGo_bit (idx : ℕ) : ∀ (L : List (ℕ × ℕ)) (sh i q : ℕ), (∀ p ∈ L, bk idx p < 2 ^ 25) →
    (hi : i < L.length) → q < 25 → (imgGo idx L sh).testBit (sh + 25 * i + q) = (bk idx L[i]).testBit q
  | [], _, _, _, _, hi, _ => by simp at hi
  | p :: L, sh, i, q, hb, hi, hq => by
    have hp := hb p (List.mem_cons_self ..)
    rw [imgGo_cons, lor_testBit, shl_testBit, decide_eq_true (by omega), Bool.true_and]
    rcases i with _ | i
    · rw [imgGo_low idx L (sh + 25) _ (by omega), Bool.or_false]
      congr 1
      omega
    · have e : sh + 25 * (i + 1) + q = (sh + 25) + 25 * i + q := by ring
      rw [e, imgGo_bit idx L (sh + 25) i q (fun r hr => hb r (List.mem_cons_of_mem _ hr))
        (by simpa using hi) hq]
      have h0 : (bk idx p).testBit (sh + 25 + 25 * i + q - sh) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hp (Nat.pow_le_pow_right (by norm_num) (by omega)))
      rw [h0, Bool.false_or]
      rfl

theorem vec_mat (v : Fin 25 → ZMod 2) : vec (mat v) = v := by
  funext q
  change v ⟨5 * ((q : ℕ) / 5) + (q : ℕ) % 5, _⟩ = v q
  congr 1
  ext
  simp only
  omega

theorem isUnit_iff_rank5 (A : M5) : IsUnit A ↔ A.rank = 5 := by
  constructor
  · intro h
    rw [Matrix.rank_of_isUnit A h, Fintype.card_fin]
  · intro h
    rw [← Matrix.isUnit_toLin'_iff, LinearMap.isUnit_iff_range_eq_top, Matrix.toLin'_apply']
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    exact h

open scoped Classical in
theorem sol_count (cd : M5 → ℕ) (hlt : ∀ M, cd M < 2 ^ 25) (hbv : ∀ M, bvo 25 0 (cd M) = vec M)
    (hrk : ∀ M, rankK (cd M) = M.rank) (hmul : ∀ M N, mmulK (cd M) (cd N) = cd (M * N))
    (hadd : ∀ M N, Nat.xor (cd M) (cd N) = cd (M + N))
    (hunit : ∀ idx < 25, Nat.shiftLeft 1 idx = cd (mat (bvo 25 0 (2 ^ idx))))
    (ps : List (M5 × M5)) :
    Nat.card {g : GL (Fin 5) (ZMod 2) // ∀ p ∈ ps, (g : M5) * p.1 = p.2 * (g : M5)} =
      unitCntK (elimK (ps.map fun p => (cd p.1, cd p.2)) (25 * ps.length) 25).2 := by
  set P := ps.map fun p => (cd p.1, cd p.2) with hP
  have hPl : P.length = ps.length := List.length_map _
  have hbk : ∀ idx < 25, ∀ p : M5 × M5, bk idx (cd p.1, cd p.2) = cd (blk p (bvo 25 0 (2 ^ idx))) := by
    intro idx hidx p
    unfold bk blk
    rw [hunit idx hidx, hmul, hmul, hadd]
  have hbk_lt : ∀ idx < 25, ∀ q ∈ P, bk idx q < 2 ^ 25 := by
    intro idx hidx q hq
    rw [hP, List.mem_map] at hq
    obtain ⟨p, -, rfl⟩ := hq
    rw [hbk idx hidx p]
    exact hlt _
  have hlt' : ∀ idx < 25, imgK P idx < 2 ^ (25 * ps.length) := by
    intro idx hidx
    have h := imgGo_lt idx P 0 (hbk_lt idx hidx)
    rw [Nat.zero_add, hPl] at h
    rw [imgK_eq]
    exact h
  have hL : ∀ idx < 25, bvo (25 * ps.length) 0 (imgK P idx) = Lps ps (bvo 25 0 (2 ^ idx)) := by
    intro idx hidx
    funext p
    have hi := div25_lt p
    have hq : (p : ℕ) % 25 < 25 := Nat.mod_lt _ (by norm_num)
    rw [Lps_apply]
    change (if (imgK P idx).testBit (p + 0) then (1 : ZMod 2) else 0) = _
    have e : (p : ℕ) + 0 = 0 + 25 * ((p : ℕ) / 25) + (p : ℕ) % 25 := by omega
    rw [e, imgK_eq, imgGo_bit idx P 0 _ _ (hbk_lt idx hidx) (by rw [hPl]; exact hi) hq]
    have e2 : P[(p : ℕ) / 25]'(by rw [hPl]; exact hi) =
        (cd (ps.get ⟨(p : ℕ) / 25, hi⟩).1, cd (ps.get ⟨(p : ℕ) / 25, hi⟩).2) := by
      simp only [hP, List.getElem_map, List.get_eq_getElem]
    rw [e2, hbk idx hidx]
    have h3 := congrFun (hbv (blk (ps.get ⟨(p : ℕ) / 25, hi⟩) (bvo 25 0 (2 ^ idx)))) ⟨(p : ℕ) % 25, hq⟩
    change (if (cd _).testBit ((p : ℕ) % 25 + 0) then (1 : ZMod 2) else 0) = _ at h3
    rw [Nat.add_zero] at h3
    exact h3
  rw [elim_count (25 * ps.length) P (Lps ps) hlt' hL]
  have e1 : Nat.card {g : GL (Fin 5) (ZMod 2) // ∀ p ∈ ps, (g : M5) * p.1 = p.2 * (g : M5)} =
      Nat.card {M : M5 // IsUnit M ∧ ∀ p ∈ ps, M * p.1 = p.2 * M} := by
    refine Nat.card_congr
      { toFun := fun g => ⟨g.1.val, g.1.isUnit, g.2⟩
        invFun := fun M => ⟨M.2.1.unit, M.2.2⟩
        left_inv := fun g => ?_
        right_inv := fun M => rfl }
    apply Subtype.ext
    apply Units.ext
    rfl
  rw [e1, Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine Finset.card_bij (fun M _ => cd M) (fun M hM => ?_) (fun M _ N _ e => ?_) (fun c hc => ?_)
  · rw [Finset.mem_filter] at hM ⊢
    obtain ⟨-, hu, hs⟩ := hM
    refine ⟨Finset.mem_range.2 (hlt M), ?_, ?_⟩
    · rw [hbv, Lps_eq_zero, mat_vec]
      exact hs
    · rw [hrk, ← isUnit_iff_rank5]
      exact hu
  · apply vec_inj
    rw [← hbv, ← hbv, e]
  · rw [Finset.mem_filter, Finset.mem_range] at hc
    obtain ⟨hc25, hker, hc5⟩ := hc
    refine ⟨mat (bvo 25 0 c), ?_, ?_⟩
    · have hcd : cd (mat (bvo 25 0 c)) = c :=
        bvo25_inj (hlt _) hc25 (by rw [hbv, vec_mat])
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · rw [isUnit_iff_rank5, ← hrk, hcd]
        exact hc5
      · rw [← Lps_eq_zero]
        exact hker
    · exact bvo25_inj (hlt _) hc25 (by rw [hbv, vec_mat])

end CFSG.KC.Misc.GLM.Ech

end
