module

public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoPilotToral

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType
  CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.E6TwoMat CFSG.StandardType.E6TwoPilot

@[expose] def nLetters (i : Fin Tag.E6.rank) : List ℕ := [6 + i.val, 12 + 2 * i.val, 6 + i.val]

@[expose] def tWN : List ℕ := tWord.flatMap nLetters

@[expose] def xWord (a b : ℕ) (v : Fin 4 → ZMod 3) : List ℕ :=
  eWord v ++ wpow a sWord ++ wpow b tWN

theorem rootOf_nLetters : ∀ i : Fin Tag.E6.rank,
    rootOf (6 + i.val) = Pi.single i 1 ∧ rootOf (12 + 2 * i.val) = -Pi.single i 1 := by
  decide +kernel

section Words

variable {K : Type} [Field K] [CharP K 2]

theorem weylElt_eq_wordElt (i : Fin Tag.E6.rank) : weylElt .E6 K i 1 = wordElt K (nLetters i) := by
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul, nLetters, wordElt_cons, wordElt_cons,
    wordElt_cons, wordElt_nil, mul_one, (rootOf_nLetters i).1, (rootOf_nLetters i).2,
    pinnedX_single, pinnedX_neg_single]
  simp only [inv_one, Units.val_one, CharTwo.neg_eq, mul_assoc]

theorem prod_weylElt_eq_wordElt (l : List (Fin Tag.E6.rank)) :
    (l.map fun i => weylElt .E6 K i 1).prod = wordElt K (l.flatMap nLetters) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, List.flatMap_cons, wordElt_append, ih, weylElt_eq_wordElt]

theorem coe_tE6Two_eq_wordElt :
    ((tE6Two K : adjointGroup .E6 K) : ModGL .E6 K) = wordElt K tWN := by
  change canonicalRep (coxeterSystem .E6) K tWeyl = _
  rw [tWeyl, CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_wordProd_of_charTwo,
    prod_weylElt_eq_wordElt]
  rfl

end Words

section S

variable {K : Type} [Field K] [CharP K 2]

theorem coe_torus_mul_stHom_eq_wordElt (h2 : (2 : K) = 0) (v : Fin 4 → ZMod 3) (a b : ZMod 3) :
    ((torusE6Two h2 (.ofAdd v) * stHom K (.ofAdd a, .ofAdd b) : adjointGroup .E6 K) :
      ModGL .E6 K) = wordElt K (xWord a.val b.val v) := by
  rw [stHom_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow,
    coe_torusE6Two_eq_wordElt, coe_tE6Two_eq_wordElt, xWord, wordElt_append, wordElt_append,
    wordElt_wpow, wordElt_wpow, mul_assoc]
  rfl

theorem conj_eq_of_wordsAgree (h2 : (2 : K) = 0) {cw xw : List ℕ} {x : adjointGroup .E6 K}
    (hx : (x : ModGL .E6 K) = wordElt K xw) {v : Fin 4 → ZMod 3}
    (h : wordsAgree (cw ++ xw) (eWord v ++ cw) = true) :
    ∃ c : adjointGroup .E6 K, c * x * c⁻¹ = torusE6Two h2 (.ofAdd v) := by
  refine ⟨⟨wordElt K cw, wordElt_mem_adjointGroup cw⟩, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hx, coe_torusE6Two_eq_wordElt]
  change wordElt K cw * wordElt K xw = wordElt K (eWord v) * wordElt K cw
  rw [← wordElt_append, ← wordElt_append]
  exact wordElt_eq_of_wordsAgree h

theorem stHom_conj_ofAdd (h2 : (2 : K) = 0) (g : G9) (v : Fin 4 → ZMod 3) :
    stHom K g * torusE6Two h2 (.ofAdd v) * (stHom K g)⁻¹ = torusE6Two h2 (.ofAdd (actG g v)) := by
  rw [stHom_conj_torusE6Two, phiAct_eq_actG]
  rfl

theorem actG_neg (g : G9) (v : Fin 4 → ZMod 3) : actG g (-v) = -actG g v := by
  have h := map_inv (phiAct g) (Multiplicative.ofAdd v)
  rw [phiAct_eq_actG, phiAct_eq_actG] at h
  exact congrArg Multiplicative.toAdd h

theorem cube_torus_stHom (h2 : (2 : K) = 0) (g : G9) (v : Fin 4 → ZMod 3) :
    (torusE6Two h2 (.ofAdd v) * stHom K g) ^ 3 =
      torusE6Two h2 (.ofAdd (v + actG g v + actG g (actG g v))) := by
  have hg3 : stHom K g ^ 3 = 1 := by rw [← map_pow, g9_pow_three, map_one]
  have e1 := stHom_conj_ofAdd h2 g v
  have e2 := stHom_conj_ofAdd h2 g (actG g v)
  calc (torusE6Two h2 (.ofAdd v) * stHom K g) ^ 3 = torusE6Two h2 (.ofAdd v) *
        (stHom K g * torusE6Two h2 (.ofAdd v) * (stHom K g)⁻¹) *
        (stHom K g * (stHom K g * torusE6Two h2 (.ofAdd v) * (stHom K g)⁻¹) * (stHom K g)⁻¹) *
        stHom K g ^ 3 := by rw [pow_three, pow_three]; group
    _ = torusE6Two h2 (.ofAdd (v + actG g v + actG g (actG g v))) := by
        rw [e1, e2, hg3, mul_one, ← map_mul, ← map_mul]
        rfl

theorem inv_torus_stHom (h2 : (2 : K) = 0) (g : G9) (v : Fin 4 → ZMod 3) :
    (torusE6Two h2 (.ofAdd v) * stHom K g)⁻¹ =
      torusE6Two h2 (.ofAdd (-actG g⁻¹ v)) * stHom K g⁻¹ := by
  have e1 := stHom_conj_ofAdd h2 g⁻¹ (-v)
  rw [actG_neg] at e1
  have hinv : stHom K g⁻¹ = (stHom K g)⁻¹ := map_inv _ _
  rw [← e1, hinv]
  have hv : (torusE6Two h2 (.ofAdd v))⁻¹ = torusE6Two h2 (.ofAdd (-v)) := by
    rw [← map_inv]
    rfl
  rw [← hv]
  group

theorem conj_torus_stHom (h2 : (2 : K) = 0) (g h : G9) (v w : Fin 4 → ZMod 3) :
    (torusE6Two h2 (.ofAdd w) * stHom K h) * (torusE6Two h2 (.ofAdd v) * stHom K g) *
        (torusE6Two h2 (.ofAdd w) * stHom K h)⁻¹ =
      torusE6Two h2 (.ofAdd (w + actG h v - actG g w)) * stHom K g := by
  have e1 := stHom_conj_ofAdd h2 h v
  have e2 := stHom_conj_ofAdd h2 g (-w)
  rw [actG_neg] at e2
  have hc : stHom K h * stHom K g = stHom K g * stHom K h := by
    rw [← map_mul, ← map_mul, mul_comm]
  have hw : (torusE6Two h2 (.ofAdd w))⁻¹ = torusE6Two h2 (.ofAdd (-w)) := by
    rw [← map_inv]
    rfl
  calc (torusE6Two h2 (.ofAdd w) * stHom K h) * (torusE6Two h2 (.ofAdd v) * stHom K g) *
        (torusE6Two h2 (.ofAdd w) * stHom K h)⁻¹ =
      torusE6Two h2 (.ofAdd w) * (stHom K h * torusE6Two h2 (.ofAdd v) * (stHom K h)⁻¹) *
        (stHom K h * stHom K g * (stHom K h)⁻¹) * (torusE6Two h2 (.ofAdd w))⁻¹ := by group
    _ = torusE6Two h2 (.ofAdd w) * torusE6Two h2 (.ofAdd (actG h v)) *
        (stHom K g * torusE6Two h2 (.ofAdd (-w)) * (stHom K g)⁻¹) * stHom K g := by
        rw [e1, hc, mul_inv_cancel_right, hw]
        group
    _ = torusE6Two h2 (.ofAdd (w + actG h v - actG g w)) * stHom K g := by
        rw [e2, ← map_mul, ← map_mul, sub_eq_add_neg]
        rfl

@[expose] def negCoord (i : Fin 4) (v : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 :=
  fun j => if j = i then -v j else v j

@[expose] def bMove (k : Fin 6) (v : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 :=
  if k = 0 then msFun v else if k = 1 then mtFun v
  else negCoord ⟨k.val - 2, by omega⟩ v

@[expose] def applyMoves (ws : List (Fin 6)) (v : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 :=
  ws.foldl (fun v k => bMove k v) v

theorem sub_reflFun_eq_negCoord (i : Fin 4) (v : Fin 4 → ZMod 3) :
    v - reflFunE6Two i v • Pi.single i 1 = negCoord i v := by
  funext j
  simp only [Pi.sub_apply, Pi.smul_apply, reflFunE6Two_apply, negCoord, Pi.single_apply,
    smul_eq_mul]
  split_ifs with hj
  · subst hj
    ring_nf
    rfl
  · simp

theorem exists_conj_bMove (h2 : (2 : K) = 0) (k : Fin 6) :
    ∃ c : adjointGroup .E6 K, ∀ v, c * torusE6Two h2 (.ofAdd v) * c⁻¹ =
      torusE6Two h2 (.ofAdd (bMove k v)) := by
  by_cases h0 : k = 0
  · refine ⟨sE6Two K, fun v => ?_⟩
    rw [torusE6Two_msAut, msAut_ofAdd, bMove, ite_eq_left h0]
  by_cases h1 : k = 1
  · refine ⟨tE6Two K, fun v => ?_⟩
    rw [torusE6Two_mtAut, mtAut_ofAdd, bMove, ite_eq_right h0, ite_eq_left h1]
  · refine ⟨nE6Two ⟨k.val - 2, by omega⟩, fun v => ?_⟩
    rw [nE6Two_conj_torus, bMove, ite_eq_right h0, ite_eq_right h1, sub_reflFun_eq_negCoord]

theorem exists_conj_applyMoves (h2 : (2 : K) = 0) :
    ∀ (ws : List (Fin 6)) (v : Fin 4 → ZMod 3), ∃ c : adjointGroup .E6 K,
      c * torusE6Two h2 (.ofAdd v) * c⁻¹ = torusE6Two h2 (.ofAdd (applyMoves ws v))
  | [], v => ⟨1, by simp [applyMoves]⟩
  | k :: ws, v => by
    obtain ⟨c₁, hc₁⟩ := exists_conj_bMove (K := K) h2 k
    obtain ⟨c₂, hc₂⟩ := exists_conj_applyMoves h2 ws (bMove k v)
    refine ⟨c₂ * c₁, ?_⟩
    have e : applyMoves (k :: ws) v = applyMoves ws (bMove k v) := rfl
    rw [e, ← hc₂, ← hc₁ v]
    group

end S

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6
