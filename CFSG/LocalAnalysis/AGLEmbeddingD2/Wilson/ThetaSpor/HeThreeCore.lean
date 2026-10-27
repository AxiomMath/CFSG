
module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.ThreeRestrict
public import CFSG.Sporadic.HeldB.InnerRestrict
public import CFSG.Sporadic.HeldB.FixCount
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThreeInputs

public section

namespace CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He

open CFSG.Sporadic.HeldB CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.LocalRank
open CFSG.AGLEmbeddingD2.Wilson.ThetaSpor
open scoped Pointwise

@[expose, irreducible] noncomputable def heThreeP (w : List ℤ) : Equiv.Perm (Fin 8330) :=
  evalSignedWord [heGenPerm 0, heGenPerm 1] w

theorem rep_heThreeP {w : List ℤ} (hw : lettersOK 2 w = true) :
    Rep 8330 (heThreeArr w) (heThreeP w) := by
  rw [heThreeArr, heThreeP]
  exact rep_wordA_evalSignedWord (fun h hh => (rep_heAB h hh).1) (fun h hh => (rep_heAB h hh).2) hw

theorem heThreeP_mem (w : List ℤ) : heThreeP w ∈ heP := by
  rw [heThreeP]
  refine evalSignedWord_mem heP (fun g hg => ?_) _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h <;> rw [h]
  · exact heGenPerm_mem (by norm_num)
  · exact heGenPerm_mem (by norm_num)

structure BigData (m k : ℕ) (ws : List (List ℤ)) (sigma : List (Array ℕ)) (delta : Array ℕ)
    (fx : ℕ) : Prop where
  letters0 : lettersOK 2 (ws.getD 0 []) = true
  chk0 : permChk 8330 (heThreeArr (ws.getD 0 [])) = true
  cube : eqA 8330 (compA 8330 (heThreeArr (ws.getD 0 []))
      (compA 8330 (heThreeArr (ws.getD 0 [])) (heThreeArr (ws.getD 0 [])))) (idA 8330) = true
  ne : eqA 8330 (heThreeArr (ws.getD 0 [])) (idA 8330) = false
  zero : (heThreeArr (ws.getD 0 []))[0]! = 0
  fixes : (List.range 8330).countP (fun i => (heThreeArr (ws.getD 0 []))[i]! == i) = fx
  len : ws.length = k
  gens : ∀ j < k, lettersOK 2 (ws.getD j []) = true ∧
      permChk 8330 (heThreeArr (ws.getD j [])) = true ∧
      eqA 8330 (compA 8330 (heThreeArr (ws.getD j [])) (heThreeArr (ws.getD 0 [])))
        (compA 8330 (heThreeArr (ws.getD 0 [])) (heThreeArr (ws.getD j []))) = true ∧
      permChk m (sigma.getD j #[]) = true ∧
      agreeOK m (heThreeArr (ws.getD j [])) delta (sigma.getD j #[]) = true
  deltaInc : incListOK 8330 m delta = true
  deltaFix : fixesOK m (heThreeArr (ws.getD 0 [])) delta = true

section Generic

variable {m k : ℕ} {ws : List (List ℤ)} {sigma : List (Array ℕ)} {delta : Array ℕ} {fx : ℕ}

@[expose] noncomputable def bOf (ws : List (List ℤ)) : Equiv.Perm (Fin 8330) :=
  heThreeP (ws.getD 0 [])

@[expose] noncomputable def cOf (ws : List (List ℤ)) (j : ℕ) : Equiv.Perm (Fin 8330) :=
  heThreeP (ws.getD j [])

theorem rep_bOf (hd : BigData m k ws sigma delta fx) :
    Rep 8330 (heThreeArr (ws.getD 0 [])) (bOf ws) := rep_heThreeP hd.letters0

theorem rep_cOf (hd : BigData m k ws sigma delta fx) {j : ℕ}
    (hj : j < k) : Rep 8330 (heThreeArr (ws.getD j [])) (cOf ws j) :=
  rep_heThreeP (hd.gens j hj).1

theorem bOf_mem : bOf ws ∈ heP := heThreeP_mem _

theorem cOf_mem (j : ℕ) : cOf ws j ∈ heP := heThreeP_mem _

theorem bOf_pow_three (hd : BigData m k ws sigma delta fx) :
    bOf ws ^ 3 = 1 := by
  have h := eq_of_eqA (rep_compA (rep_bOf hd) (rep_compA (rep_bOf hd) (rep_bOf hd)))
    rep_idA hd.cube
  rw [pow_succ', sq]
  exact h

theorem bOf_ne_one (hd : BigData m k ws sigma delta fx) :
    bOf ws ≠ 1 := by
  intro h
  have h' := (eqA_iff (rep_bOf hd) rep_idA).2 h
  rw [hd.ne] at h'
  exact absurd h' (by decide)

theorem orderOf_bOf (hd : BigData m k ws sigma delta fx) :
    orderOf (bOf ws) = 3 := orderOf_eq_prime (bOf_pow_three hd) (bOf_ne_one hd)

theorem fixCard_bOf (hd : BigData m k ws sigma delta fx) :
    fixCard (bOf ws) = fx :=
  (fixCard_eq_countP (rep_bOf hd)).trans hd.fixes

theorem cOf_comm (hd : BigData m k ws sigma delta fx) {j : ℕ}
    (hj : j < k) : cOf ws j * bOf ws = bOf ws * cOf ws j :=
  eq_of_eqA (rep_compA (rep_cOf hd hj) (rep_bOf hd)) (rep_compA (rep_bOf hd) (rep_cOf hd hj))
    (hd.gens j hj).2.2.1

theorem delta_lt (hd : BigData m k ws sigma delta fx) : ∀ i < m, delta[i]! < 8330 := by
  have h := hd.deltaInc
  simp only [incListOK, Bool.and_eq_true, allLt_iff, decide_eq_true_eq] at h
  exact h.1.2

theorem delta_injective (hd : BigData m k ws sigma delta fx) :
    Function.Injective (listPt 8330 delta (m := m)) := by
  have h := hd.deltaInc
  simp only [incListOK, Bool.and_eq_true, allLt_iff, decide_eq_true_eq] at h
  exact listPt_injective_of_inc h.1.2 h.2

theorem cOf_agree (hd : BigData m k ws sigma delta fx) {j : ℕ}
    (hj : j < k) (i : Fin m) :
    cOf ws j (listPt 8330 delta i) = listPt 8330 delta (permOrId m (sigma.getD j #[]) i) :=
  agreeOK_spec_of_lt (delta_lt hd) (rep_cOf hd hj)
    (permChk_spec (hd.gens j hj).2.2.2.1).1 (hd.gens j hj).2.2.2.2 i

theorem bOf_fix (hd : BigData m k ws sigma delta fx) (i : Fin m) :
    bOf ws (listPt 8330 delta i) = listPt 8330 delta i := by
  apply Fin.ext
  have h := hd.deltaFix
  simp only [fixesOK, allLt_iff, beq_iff_eq] at h
  rw [← rep_bOf hd, listPt_val_of_lt (delta_lt hd)]
  exact h i i.2

@[expose] noncomputable def grpOf (ws : List (List ℤ)) (k : ℕ) :
    Subgroup (Equiv.Perm (Fin 8330)) :=
  Subgroup.closure {g | ∃ j < k, cOf ws j = g}

theorem grpOf_le (hd : BigData m k ws sigma delta fx) :
    grpOf ws k ≤ centralizerIn heP (bOf ws) := by
  rw [grpOf, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact mem_centralizerIn.2 ⟨cOf_mem j, cOf_comm hd hj⟩

theorem b_mem_grpOf (hk : 0 < k) : bOf ws ∈ grpOf ws k :=
  Subgroup.subset_closure ⟨0, hk, rfl⟩

theorem grpOf_stab (hd : BigData m k ws sigma delta fx) :
    grpOf ws k ≤ MulAction.stabilizer (Equiv.Perm (Fin 8330))
      (Set.range (listPt 8330 delta (m := m))) := by
  rw [grpOf, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact mem_stabilizer_of_agree (cOf_agree hd hj)

theorem restrict_range (hd : BigData m k ws sigma delta fx)
    (Q : RawSchreierDatum m)
    (hQ : Q.originalSubgroup =
      Subgroup.closure {g | ∃ j < k, permOrId m (sigma.getD j #[]) = g}) :
    (restrictHom (delta_injective hd) (grpOf ws k) (grpOf_stab hd)).range = Q.originalSubgroup := by
  rw [restrictHom_range (delta_injective hd) (grpOf_stab hd) rfl, hQ]
  congr 1
  ext g
  constructor
  · rintro ⟨h, ⟨j, hj, hjh⟩, rfl⟩
    exact ⟨j, hj, (restrictHom_eq_of_agree (delta_injective hd) (grpOf_stab hd) h
      (by rw [← hjh]; exact cOf_agree hd hj)).symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨cOf ws j, Subgroup.subset_closure ⟨j, hj, rfl⟩⟩, ⟨j, hj, rfl⟩,
      restrictHom_eq_of_agree (delta_injective hd) (grpOf_stab hd) _ (cOf_agree hd hj)⟩

theorem heThree_theta (hd : BigData m k ws sigma delta fx)
    (hk : 0 < k) (Q : RawSchreierDatum m)
    (hQ : Q.originalSubgroup =
      Subgroup.closure {g | ∃ j < k, permOrId m (sigma.getD j #[]) = g})
    (hrad : ∀ K : Subgroup Q.originalSubgroup, K.Normal → Group.IsSolvable K → K = ⊥)
    (hcard : Nat.card (centralizerIn heP (bOf ws)) = 3 * Nat.card Q.originalSubgroup) :
    grpOf ws k = centralizerIn heP (bOf ws) ∧
      aschbacherSolvableCore 3 (centralizerIn heP (bOf ws)) = ⊥ :=
  thetaCore_eq_bot_of_restrict_three (grpOf_le hd) (b_mem_grpOf hk) (bOf_ne_one hd)
    (bOf_pow_three hd) (delta_injective hd) (grpOf_stab hd) (bOf_fix hd)
    (restrict_range hd Q hQ) hrad hcard

end Generic

end CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He

end
