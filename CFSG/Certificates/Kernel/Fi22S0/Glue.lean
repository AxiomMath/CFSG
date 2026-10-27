
module

public import CFSG.Certificates.Kernel.Spor.ConjIndexSound
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Certificates.Kernel.LyS0.Sound
public import CFSG.HardMathSupport.Foote.E27.SporFi22Base
public import CFSG.HardMathSupport.Foote.E27.TableSylow

public section

namespace CFSG.KD.Fi22S0

open CFSG.Sporadic.Fi22 CFSG.Sporadic.Fi22.S0 CFSG.Sporadic.Fi22.Native CFSG.F3.Native
  CFSG.HardMathSupport.Foote.E27 CFSG.HardMathSupport.Foote.E27.Fi22S0

theorem shapeOK_of {oi oj pp pj : ℕ → ℕ} {lt : ℕ → ℕ → ℕ}
    (hops : ops () = Array.ofFn (n := 567) fun t => (oi (t.val + 3), oj (t.val + 3)))
    (hoi : ∀ k, 3 ≤ k → k < 570 → oi k < k ∧ oj k < k)
    (hpar : par () = Array.ofFn (n := 19683) fun i => (pp i.val, pj i.val))
    (htree : ∀ i < 19683, 0 < i → pp i < i ∧ pj i < 3)
    (hL : L () = Array.ofFn (n := 3) fun j => Array.ofFn (n := 19683) fun i => lt j.val i.val) :
    shapeOK () = true := by
  have hg : ((List.range gens.size).all fun j => decide (gens[j]! < 567 + 3)) = true ∧
      gens.size = 3 := by decide
  unfold shapeOK
  rw [hops, hpar, hL]
  simp only [Array.size_ofFn, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, Bool.or_eq_true]
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, fun t ht => ?_⟩, ?_⟩, fun i hi => ?_⟩
  · first | trivial | rfl
  · first | trivial | exact hg.2
  · first | trivial | rfl
  · first | trivial | rfl
  · rw [CFSG.KS.LyS0K.ofFnG (fun t => (oi (t + 3), oj (t + 3))) ht]
    exact hoi (t + 3) (by omega) (by omega)
  · have := hg.1
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at this
    exact this
  · by_cases h0 : i = 0
    · exact Or.inl h0
    · right
      have hi' : i < 19683 := by unfold nS at hi; exact hi
      rw [CFSG.KS.LyS0K.ofFnG (fun i => (pp i, pj i)) hi']
      exact htree i hi' (Nat.pos_of_ne_zero h0)

theorem shape_parts_of (h : shapeOK () = true) :
    (∀ t < ops.size, (ops[t]!).1 < t + 3 ∧ (ops[t]!).2 < t + 3) ∧
    (∀ j < gens.size, gens[j]! < ops.size + 3) ∧ ops.size = 567 ∧ gens.size = 3 ∧ par.size = nS ∧
    (∀ i < nS, i = 0 ∨ ((par[i]!).1 < i ∧ (par[i]!).2 < 3)) := by
  unfold shapeOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq, decide_eq_true_eq,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, -⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨fun t ht => h5 t ht, fun j hj => h6 j hj, h1, h2, h3, fun i hi => h7 i hi⟩

theorem regs_spec_of (hs : shapeOK () = true) :
    regsM.size = 3 + ops.size ∧ ∀ k < 3 + ops.size, (regsM[k]!).size = 77 ∧ RowsWF (regsM[k]!) ∧
      toMat 77 (regsM[k]!) = matJ (regJ k) := by
  obtain ⟨hops, -, -, -, -, -⟩ := shape_parts_of hs
  have h := buildN_inv (#[matA, matB, matBi] : Array (Array V))
    (fun acc k => mul 77 (acc[(ops[k - 3]!).1]!) (acc[(ops[k - 3]!).2]!))
    (fun k x => x.size = 77 ∧ RowsWF x ∧ toMat 77 x = matJ (regJ k)) ops.size ?_ ?_
  · exact h
  · intro k hk
    have hk3 : k < 3 := hk
    interval_cases k
    · refine ⟨matA_size, rowsWF_matA, ?_⟩
      change toMat 77 matA = matJ (regJ 0)
      rw [regJ_zero, toMat_matA]; rfl
    · refine ⟨matB_size, rowsWF_matB, ?_⟩
      change toMat 77 matB = matJ (regJ 1)
      rw [regJ_one, toMat_matB]; rfl
    · refine ⟨matBi_size, rowsWF_matBi, ?_⟩
      change toMat 77 matBi = matJ (regJ 2)
      rw [regJ_two]; exact b_inv_val.symm
  · intro n hn r hr hP
    have hrs : r.size = 3 + n := hr
    obtain ⟨hp1, hp2⟩ := hops n hn
    have e : r.size - 3 = n := by omega
    obtain ⟨hs1, hw1, ht1⟩ := hP _ (by omega : (ops[n]!).1 < r.size)
    obtain ⟨hs2, hw2, ht2⟩ := hP _ (by omega : (ops[n]!).2 < r.size)
    change (mul 77 (r[(ops[r.size - 3]!).1]!) (r[(ops[r.size - 3]!).2]!)).size = 77 ∧
      RowsWF (mul 77 (r[(ops[r.size - 3]!).1]!) (r[(ops[r.size - 3]!).2]!)) ∧
      toMat 77 (mul 77 (r[(ops[r.size - 3]!).1]!) (r[(ops[r.size - 3]!).2]!)) =
        matJ (regJ r.size)
    rw [e]
    refine ⟨by rw [mul_size, hs1], RowsWF.mul _ 77 hw1 hw2, ?_⟩
    rw [regJ_succ (k := r.size) ⟨by omega, by rw [e]; omega, by rw [e]; omega⟩, e,
      toMat_mul hs1 hw1 hw2, matJ_mul, ht1, ht2]

theorem genM_spec_of (hs : shapeOK () = true) {j : ℕ} (hj : j < 3) :
    (genM j).size = 77 ∧ RowsWF (genM j) ∧ toMat 77 (genM j) = matJ (gJ j) := by
  obtain ⟨-, hg, -, hgs, -, -⟩ := shape_parts_of hs
  have hj' : j < gens.size := by omega
  rw [gJ_eq]
  exact (regs_spec_of hs).2 (gens[j]!) (by have := hg j hj'; omega)

theorem elts_spec_of (hs : shapeOK () = true) :
    eltsM.size = nS ∧ ∀ i < nS, canonM 77 (eltsM[i]!) = true ∧
      toMat 77 (eltsM[i]!) = matJ (tabElt gJ par i) := by
  obtain ⟨-, -, -, -, -, hpar⟩ := shape_parts_of hs
  have h := buildN_inv (#[idM 77] : Array (Array V))
    (fun acc i => mul 77 (genM (par[i]!).2) (acc[(par[i]!).1]!))
    (fun k x => canonM 77 x = true ∧ toMat 77 x = matJ (tabElt gJ par k)) (nS - 1) ?_ ?_
  · have hs : 1 + (nS - 1) = nS := by unfold nS; omega
    have hsz : (#[idM 77] : Array (Array V)).size = 1 := rfl
    rw [hsz, hs] at h
    exact h
  · intro k hk
    have hk1 : k = 0 := by
      have : k < 1 := hk
      omega
    subst hk1
    refine ⟨canonM_idM 77, ?_⟩
    change toMat 77 (idM 77) = matJ (tabElt gJ par 0)
    rw [toMat_idM, tabElt_zero, matJ_one]
  · intro n hn r hr hP
    have hrs : r.size = 1 + n := hr
    have hnS : 1 + n < nS := by unfold nS at hn ⊢; omega
    rcases hpar (1 + n) hnS with h0 | ⟨hp, hj⟩
    · omega
    have hp' : (par[r.size]!).1 < r.size := by rw [hrs]; exact hp
    have hj' : (par[r.size]!).2 < 3 := by rw [hrs]; exact hj
    obtain ⟨hs1, hw1, ht1⟩ := genM_spec_of hs hj'
    obtain ⟨hc2, ht2⟩ := hP _ hp'
    change canonM 77 (mul 77 (genM (par[r.size]!).2) (r[(par[r.size]!).1]!)) = true ∧
      toMat 77 (mul 77 (genM (par[r.size]!).2) (r[(par[r.size]!).1]!)) =
        matJ (tabElt gJ par r.size)
    refine ⟨canonM_mul hs1 hw1 hc2, ?_⟩
    rw [tabElt_succ gJ par hp', toMat_mul hs1 hw1 (RowsWF.of_canonM hc2), matJ_mul, ht1, ht2]

theorem eqM_of_toMat {X Y : Array V} (hX : canonM 77 X = true) (hY : canonM 77 Y = true)
    (h : toMat 77 X = toMat 77 Y) : eqM 77 X Y = true := by
  cases e : eqM 77 X Y
  · exact absurd h (not_eqM_of_ne (canonM_spec hX).1 (canonM_spec hY).1 e hX hY)
  · rfl

theorem fi22S0Check_of (hs : shapeOK () = true) (hT : TabData gJ par L nS 3)
    (hk : killOK () = true) : fi22S0Check () = true := by
  obtain ⟨hesz, hE⟩ := elts_spec_of hs
  have hleft : leftOK () = true := by
    unfold leftOK
    simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
    intro j hj i hi
    obtain ⟨hlt, heq⟩ := hT.left j hj i hi
    refine ⟨hlt, ?_⟩
    obtain ⟨hs1, hw1, ht1⟩ := genM_spec_of hs hj
    obtain ⟨hc2, ht2⟩ := hE i hi
    obtain ⟨hc3, ht3⟩ := hE _ hlt
    refine eqM_of_toMat (canonM_mul hs1 hw1 hc2) hc3 ?_
    rw [toMat_mul hs1 hw1 (RowsWF.of_canonM hc2), ht1, ht2, ht3, ← matJ_mul, heq]
  have hcanon : canonOK () = true := by
    unfold canonOK
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
    exact ⟨hesz, fun i hi => (hE i hi).1⟩
  have hdist : distinctOK () = true := by
    unfold distinctOK
    simp only [List.all_eq_true, List.mem_range, Bool.not_eq_true']
    intro i hi k hk
    cases e : eqM 77 (eltsM[i]!) (eltsM[k]!)
    · rfl
    · have := toMat_eq_of_eqM e
      rw [(hE i hi).2, (hE k (by omega)).2] at this
      have := hT.inj i hi k (by omega) (matJ_injective this)
      omega
  unfold fi22S0Check
  rw [hs, hk, hcanon, hleft, hdist]
  rfl

end CFSG.KD.Fi22S0

end
