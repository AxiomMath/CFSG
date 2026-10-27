module

public import Certificates.Data.Kernel.PermCent.Sp6E4QuatTwin
public import CFSG.Certificates.Kernel.PermCent.Sp6E4Sound

public section

namespace CFSG.Certificates.Kernel.PkCV.Sp6E

open CFSG.EvenSmallLie.Sp6 CFSG.Sporadic.Schreier CFSG.ClassicalInvolution.Q3.TL4.E4Sp6
  CFSG.ClassicalInvolution.Q3.TL4.E4Sp6Data CFSG.ClassicalInvolution.Q3.TL4.E4C
  CFSG.Certificates.Kernel.PkCV.Sp6B

section Generic

variable {n : Nat} [Small n]

theorem drop_map' {α β : Type*} (f : α → β) : ∀ (L : List α) (k : Nat), (L.map f).drop k = (L.drop k).map f
  | [], k => by cases k <;> rfl
  | _ :: _, 0 => rfl
  | _ :: L, k + 1 => drop_map' f L k

theorem q8_ev (r i j : CV n) : q8Elems (ev r) (ev i) (ev j) = (q8C r i j).map ev := by
  simp only [q8Elems.eq_1, q8C.eq_1, List.map_cons, List.map_nil, ev_mul', one_eq_ev]

theorem normsN_ev (L : List (CV n)) (i j h : CV n) :
    norms (L.map ev) (ev i) (ev j) (ev h) = normsN L i j h := by
  rw [norms.eq_1, normsN.eq_1]
  simp only [ev_inv', ev_mul', decide_mem_map_ev]

theorem closedL_ev (L : List (CV n)) (i j : CV n) :
    closedL (L.map ev) (ev i) (ev j) = closedLC L i j := by
  simp only [closedL.eq_1, closedLC.eq_1, one_eq_ev, List.all_map, Function.comp_def, ev_inv',
    ev_mul', decide_mem_map_ev]

theorem letters_ev (G : List (CV n)) : letters (G.map ev) = (lettersC G).map ev := by
  simp only [letters.eq_1, lettersC.eq_1, List.map_append, List.map_map, Function.comp_def, ev_inv']

theorem memberCheck_ev (G L : List (CV n)) (i j : CV n) (W : List (CV n)) (σ : List (List ℕ)) :
    memberCheck (G.map ev) (L.map ev) (ev i) (ev j) (W.map ev) σ = memberCheckC G L i j W σ := by
  rw [memberCheck.eq_1, memberCheckC.eq_1, letters_ev]
  simp only [List.length_map, one_eq_ev, List.getD_map, decide_ev_eq, ev_inv', ev_mul', normsN_ev]

theorem treeStep_ev (L : List (CV n)) (i j u gp gk : CV n) (d : Bool) :
    treeStep (L.map ev) (ev i) (ev j) (ev u) (ev gp) (ev gk) d = treeStepC L i j u gp gk d := by
  simp only [treeStep.eq_1, treeStepC.eq_1, ev_inv', ev_mul', normsN_ev]

theorem treeCheck_ev (L U : List (CV n)) (i j : CV n) (W : List (CV n))
    (tree : List (ℕ × Bool × ℕ)) :
    treeCheck (L.map ev) (U.map ev) (ev i) (ev j) (W.map ev) tree = treeCheckC L U i j W tree := by
  rw [treeCheck.eq_1, treeCheckC.eq_1]
  simp only [List.all_map, Function.comp_def, List.length_map, one_eq_ev, List.getD_map,
    decide_mem_map_ev, ev_pow', decide_ev_eq, treeStep_ev]

theorem nbrCheck_ev (L : List (CV n)) (i j : CV n) (W : List (CV n)) (allowed : List ℕ) :
    nbrCheck (L.map ev) (ev i) (ev j) (W.map ev) allowed = nbrCheckC L i j W allowed := by
  rw [nbrCheck.eq_1, nbrCheckC.eq_1]
  simp only [List.length_map, one_eq_ev, List.getD_map, ev_inv', ev_mul', normsN_ev]

theorem edgeCheck_ev (L : List (CV n)) (i j g : CV n) :
    edgeCheck (L.map ev) (ev i) (ev j) (ev g) = edgeCheckC L i j g := by
  simp only [edgeCheck.eq_1, edgeCheckC.eq_1, ev_inv', ev_mul', normsN_ev]

theorem sameSet_ev (A B : List (CV n)) : sameSet (A.map ev) (B.map ev) = sameSetC A B := by
  simp only [sameSet.eq_1, sameSetC.eq_1, List.all_map, Function.comp_def, decide_mem_map_ev]

theorem violates_ev (T : List (CV n)) (i j c : CV n) :
    violates (T.map ev) (ev i) (ev j) (ev c) = violatesC T i j c := by
  simp only [violates.eq_1, violatesC.eq_1, List.any_map, List.any_cons, List.any_nil,
    Function.comp_def, ev_mul', ev_inv', decide_mem_map_ev, decide_ev_eq]

theorem identStep_ev (r ρ : CV n) (W L0 L1 : List (CV n)) (j : CV n) :
    identStep (ev r) (ev ρ) (W.map ev) (L0.map ev) (L1.map ev) (ev j) =
      identStepC r ρ W L0 L1 j := by
  simp only [identStep.eq_1, identStepC.eq_1, q8_ev, sameSet_ev, List.any_map, Function.comp_def,
    violates_ev, ev_mul', ev_inv', decide_ev_eq]

theorem identCheck_ev (r : CV n) (R C W L0 L1 : List (CV n)) :
    identCheck (ev r) (R.map ev) (C.map ev) (W.map ev) (L0.map ev) (L1.map ev) =
      identCheckC r R C W L0 L1 := by
  simp only [identCheck.eq_1, identCheckC.eq_1, List.all_map, Function.comp_def, tab_eq, ev_mul',
    decide_ev_eq, identStep_ev]

theorem nil_ev : ([] : List (Equiv.Perm (Fin n))) = ([] : List (CV n)).map ev := rfl

theorem singleton_ev (σ : Equiv.Perm (Fin n)) : [σ] = [cOf σ].map ev := by
  rw [List.map_cons, List.map_nil, ev_cOf]

end Generic

theorem gens_ev : sp6Gens = G.map ev := by rw [G.eq_1, map_cOf_ev]

theorem check_eq124 : check () = (decide (iC * iC = r2C) && closedLC L0C iC jC && p124i1 &&
    p124i2 && p124i3 && p124i4 && p124m && p124t && p124n &&
    edgeCheckC L0C iC jC (wsC.getD 11 1)) := by
  rw [check.eq_1, U.eq_1, W.eq_1, twin_ev, L1_ev, L0_ev, ws_ev, rho_ev, jay_ev, tab_eq,
    singleton_ev, tabs.eq_1, tabs.eq_1, tabs.eq_1, tabs.eq_1, map_tab, map_tab, map_tab, map_tab,
    ← map_cOf_ev sp6FourReps1, ← map_cOf_ev sp6FourReps2, ← map_cOf_ev sp6FourReps3,
    ← map_cOf_ev sp6FourReps4, E2_ev, enum_ev, enum_ev, enum_ev, gens_ev, drop_map']
  simp only [tab_eq]
  rw [rep2_ev, eq_ev_cOf sp6Rep1, eq_ev_cOf sp6Rep3, eq_ev_cOf sp6Rep4, nil_ev]
  rw [p124i1.eq_1, p124i2.eq_1, p124i3.eq_1, p124i4.eq_1, p124m.eq_1, p124t.eq_1, p124n.eq_1]
  simp only [ev_mul', decide_ev_eq, closedL_ev, identCheck_ev, memberCheck_ev, treeCheck_ev,
    nbrCheck_ev, edgeCheck_ev]

end CFSG.Certificates.Kernel.PkCV.Sp6E

end
