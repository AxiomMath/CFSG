
module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22ThreeInputs
public import CFSG.HardMathSupport.Foote.E27.SporFi22Base
public import CFSG.Sporadic.Fi22.Centralizer
public import CFSG.HardMathSupport.Foote.E27.TableSylow

@[expose] public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Three

open CFSG.Sporadic.Fi22 CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.Fi22.S0 CFSG.HardMathSupport.Foote.E27
  CFSG.HardMathSupport.Foote.E27.Fi22S0 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Native
  CFSG.F3.Native
open scoped Pointwise

theorem getElem!_ofFn_any {α : Type*} [Inhabited α] {m : ℕ} (f : Fin m → α) {i : ℕ}
    (hi : i < m) : (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi), Array.getElem_ofFn]

theorem eq_of_rep_eqT {T T' : Table} {g h : J} (hT : Rep 3510 T g) (hT' : Rep 3510 T' h)
    (he : eqT T T' = true) : g = h := by
  apply eq_of_smul_eq_smul (α := Fin 3510)
  intro i
  have h1 := allIn_eq_true.1 he i.val (Nat.zero_le _) i.2
  rw [beq_iff_eq, hT i.val i.2, hT' i.val i.2, idx_of_lt g i.2, idx_of_lt h i.2] at h1
  exact Fin.ext h1

theorem genTables_neg_two (O : COrbit) : genTables O (-2) = invT 3510 O.beta := by
  unfold genTables
  simp

theorem rep_binv : Rep 3510 (invT 3510 orb.beta) b⁻¹ := by
  have h := rep_gen (-2)
  rw [genG_neg_two, genTables_neg_two] at h
  exact h

theorem regT_eq (O : COrbit) : regT O = buildN #[O.alpha, O.beta, invT 3510 O.beta]
    (fun acc k => compT 3510 (acc[(ops[k - 3]!).1]!) (acc[(ops[k - 3]!).2]!)) ops.size := rfl

theorem genOf_get (R : Array Table) {j : ℕ} (hj : j < 3) : (genOf R)[j]! = R[gens[j]!]! := by
  unfold genOf
  exact getElem!_ofFn_any _ hj

theorem eltT_eq (P : Array (ℕ × ℕ)) (G : Array Table) (i : ℕ) :
    eltT P G i = if 0 < i ∧ (P[i]!).1 < i then compT 3510 G[(P[i]!).2]! (eltT P G (P[i]!).1)
      else idT 3510 := by
  rw [eltT.eq_def]
  split_ifs <;> rfl

theorem rep_chainLetters :
    ∀ l < (chainLetters orb).size, Rep 3510 (chainLetters orb)[l]! (pairG gs l) := by
  have hc := chainOK_parts actionChecks_parts.2.2.2.2.2.2.2.1
  exact rep_pairG rep_letters hc.1 hc.2.1

theorem lettersT_nil (letters : Array Table) : lettersT letters [] = idT 3510 := by
  unfold lettersT
  exact List.foldr_nil

theorem lettersT_cons (letters : Array Table) (l : ℕ) (w : List ℕ) :
    lettersT letters (l :: w) = compT 3510 letters[l]! (lettersT letters w) := by
  unfold lettersT
  exact List.foldr_cons

theorem rep_lettersT_of {letters : Array Table}
    (hL : ∀ l < letters.size, Rep 3510 letters[l]! (pairG gs l)) :
    ∀ w : List ℕ, (∀ z ∈ w, z < letters.size) →
      Rep 3510 (lettersT letters w) (w.map (pairG gs)).prod
  | [], _ => by
    rw [lettersT_nil, List.map_nil, List.prod_nil]
    exact Rep.idT (by norm_num)
  | l :: w, hw => by
    have hl := hw l (List.mem_cons_self)
    have ih := rep_lettersT_of hL w fun z hz => hw z (List.mem_cons_of_mem _ hz)
    rw [lettersT_cons, List.map_cons, List.prod_cons]
    exact (hL l hl).compT ih

theorem rep_lettersT (w : List ℕ) (hw : ∀ z ∈ w, z < (chainLetters orb).size) :
    Rep 3510 (lettersT (chainLetters orb) w) (w.map (pairG gs)).prod :=
  rep_lettersT_of rep_chainLetters w hw

@[expose] noncomputable def xRep (k : ℕ) : J := tabElt gJ par (globRep[k]!)

theorem xRep_def (k : ℕ) : xRep k = tabElt gJ par (globRep[k]!) := rfl

theorem globRep_lt : ∀ m < 4, globRep[m]! < nS := by decide

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Three
