module

public import Certificates.Data.Kernel.Co2Census.Spin
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.List.GetD
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.Co2Census

open Matrix

instance : NeZero spP := ⟨by decide⟩

@[expose] def decRP (A : List (List ℕ)) : Matrix (Fin 8) (Fin 8) (ZMod spP) :=
  fun i j => (((A.getD i.val []).getD j.val 0 : ℕ) : ZMod spP)

@[expose] def decV (v : List ℕ) : Fin 8 → ZMod spP := fun i => ((v.getD i.val 0 : ℕ) : ZMod spP)

@[expose] def WF8 (A : List (List ℕ)) : Prop := A.length = 8 ∧ ∀ r ∈ A, r.length = 8

theorem getD_map_range {α : Type*} (f : ℕ → α) {i : ℕ} (hi : i < 8) (d : α) :
    ((List.range 8).map f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]

theorem dotP_cast (r c : List ℕ) (hr : r.length = 8) (hc : c.length = 8) :
    ((dotP r c : ℕ) : ZMod spP) = ∑ t : Fin 8, ((r.getD t.val 0 : ℕ) : ZMod spP) *
      ((c.getD t.val 0 : ℕ) : ZMod spP) := by
  unfold dotP
  rw [ZMod.natCast_mod]
  match r, c, hr, hc with
  | [a0, a1, a2, a3, a4, a5, a6, a7], [b0, b1, b2, b3, b4, b5, b6, b7], _, _ =>
    simp [Fin.sum_univ_eight, List.zipWith, List.sum_cons]
    ring

theorem length_trP (B : List (List ℕ)) : (trP B).length = 8 := by simp [trP]

theorem getD_trP {B : List (List ℕ)} {j : ℕ} (hj : j < 8) :
    (trP B).getD j [] = B.map fun r => r.getD j 0 := by
  unfold trP
  exact getD_map_range (fun j => B.map fun r => r.getD j 0) hj []

theorem wf_mulRP {A B : List (List ℕ)} (hA : WF8 A) (_hB : WF8 B) : WF8 (mulRP A B) := by
  refine ⟨by simp [mulRP, hA.1], fun r hr => ?_⟩
  simp only [mulRP, List.mem_map] at hr
  obtain ⟨_, _, rfl⟩ := hr
  simp [length_trP]

theorem row_len {A : List (List ℕ)} (hA : WF8 A) (i : Fin 8) : (A.getD i.val []).length = 8 := by
  have hi : i.val < A.length := by rw [hA.1]; exact i.2
  rw [List.getD_eq_getElem _ _ hi]
  exact hA.2 _ (List.getElem_mem hi)

theorem decRP_mulRP {A B : List (List ℕ)} (hA : WF8 A) (hB : WF8 B) :
    decRP (mulRP A B) = decRP A * decRP B := by
  ext i j
  have hi : i.val < A.length := by rw [hA.1]; exact i.2
  have hcol : ((trP B).getD j.val []).length = 8 := by
    rw [getD_trP j.2]
    simp [hB.1]
  simp only [decRP, mul_apply]
  have e1 : ((mulRP A B).getD i.val []).getD j.val 0 =
      dotP (A.getD i.val []) ((trP B).getD j.val []) := by
    have h1 : (mulRP A B).getD i.val [] = (trP B).map (dotP (A.getD i.val [])) := by
      simp only [mulRP]
      rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_map,
        ← List.getD_eq_getElem _ _ hi]
    rw [h1, List.getD_eq_getElem _ _ (by simp [length_trP, j.2]), List.getElem_map,
      ← List.getD_eq_getElem _ _ (by rw [length_trP]; exact j.2)]
  rw [e1, dotP_cast _ _ (row_len hA i) hcol]
  refine Finset.sum_congr rfl fun t _ => ?_
  congr 2
  rw [getD_trP j.2, List.getD_eq_getElem _ _ (by simp [hB.1, t.2]), List.getElem_map,
    ← List.getD_eq_getElem _ _ (by rw [hB.1]; exact t.2)]

theorem decV_mvRP {A : List (List ℕ)} (hA : WF8 A) {v : List ℕ} (hv : v.length = 8) :
    decV (mvRP A v) = decRP A *ᵥ decV v := by
  ext i
  have hi : i.val < A.length := by rw [hA.1]; exact i.2
  simp only [decV, mulVec, dotProduct, decRP]
  have e1 : (mvRP A v).getD i.val 0 = dotP (A.getD i.val []) v := by
    simp only [mvRP]
    rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_map, ← List.getD_eq_getElem _ _ hi]
  rw [e1, dotP_cast _ _ (row_len hA i) hv]

theorem length_mvRP (A : List (List ℕ)) (v : List ℕ) : (mvRP A v).length = A.length := by
  simp [mvRP]

theorem wf_idRP : WF8 idRP := by
  refine ⟨by simp [idRP], fun r hr => ?_⟩
  simp only [idRP, List.mem_map, List.mem_range] at hr
  obtain ⟨_, _, rfl⟩ := hr
  simp

theorem decRP_idRP : decRP idRP = 1 := by
  ext i j
  simp only [decRP, idRP]
  rw [getD_map_range _ i.2, getD_map_range _ j.2, one_apply]
  by_cases h : i = j
  · subst h
    simp
  · have h' : (i : ℕ) ≠ j := fun e => h (Fin.ext e)
    simp [h, h']

theorem wf_rowsP (X : Array ℤ) : WF8 (rowsP X) := by
  refine ⟨by simp [rowsP], fun r hr => ?_⟩
  simp only [rowsP, List.mem_map, List.mem_range] at hr
  obtain ⟨_, _, rfl⟩ := hr
  simp

@[expose] noncomputable def castM (A : Matrix (Fin 8) (Fin 8) ℤ) : Matrix (Fin 8) (Fin 8) (ZMod spP) :=
  A.map (Int.castRingHom (ZMod spP))

theorem decRP_rowsP (X : Array ℤ) :
    decRP (rowsP X) = castM fun i j => X[8 * i.val + j.val]! := by
  ext i j
  rw [show castM (fun i j => X[8 * i.val + j.val]!) i j = ((X[8 * i.val + j.val]! : ℤ) : ZMod spP)
    from rfl]
  simp only [decRP, rowsP]
  rw [getD_map_range _ i.2, getD_map_range _ j.2]
  have h0 : (0 : ℤ) ≤ X[8 * i.val + j.val]! % (spP : ℤ) := Int.emod_nonneg _ (by decide)
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h0, ZMod.intCast_mod]

theorem wf_wordRP {L : ℕ → List (List ℕ)} :
    ∀ w : List ℕ, (∀ k ∈ w, WF8 (L k)) → WF8 (wordRP L w)
  | [], _ => wf_idRP
  | k :: w, hL => by
    change WF8 (mulRP (L k) (wordRP L w))
    exact wf_mulRP (hL k List.mem_cons_self)
      (wf_wordRP w fun j hj => hL j (List.mem_cons_of_mem _ hj))

theorem decRP_wordRP {L : ℕ → List (List ℕ)} :
    ∀ w : List ℕ, (∀ k ∈ w, WF8 (L k)) → decRP (wordRP L w) = (w.map fun k => decRP (L k)).prod
  | [], _ => decRP_idRP
  | k :: w, hL => by
    change decRP (mulRP (L k) (wordRP L w)) = _
    rw [decRP_mulRP (hL k List.mem_cons_self)
      (wf_wordRP w fun j hj => hL j (List.mem_cons_of_mem _ hj)),
      decRP_wordRP w (fun j hj => hL j (List.mem_cons_of_mem _ hj)), List.map_cons, List.prod_cons]

theorem two_mul_eq_zero {a : ZMod spP} (h : a + a = 0) : a = 0 := by
  have h2 : (1073741824 : ZMod spP) * 2 = 1 := by decide
  calc a = (1073741824 : ZMod spP) * 2 * a := by rw [h2, one_mul]
    _ = (1073741824 : ZMod spP) * (a + a) := by ring
    _ = 0 := by rw [h, mul_zero]

theorem decV_negVP (v : List ℕ) : decV (negVP v) = -decV v := by
  funext i
  simp only [decV, negVP, Pi.neg_apply]
  by_cases hi : i.val < v.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
      List.getD_eq_getElem _ _ hi]
    have hlt : v[i.val] % spP < spP := Nat.mod_lt _ (by decide)
    rw [ZMod.natCast_mod, Nat.cast_sub hlt.le, ZMod.natCast_self, zero_sub, ZMod.natCast_mod]
  · rw [List.getD_eq_default _ _ (by simpa using hi), List.getD_eq_default _ _ (by omega)]
    simp

theorem castM_neg (A : Matrix (Fin 8) (Fin 8) ℤ) : castM (-A) = -castM A := by
  ext i j
  simp [castM]

theorem castM_mul (A B : Matrix (Fin 8) (Fin 8) ℤ) : castM (A * B) = castM A * castM B :=
  Matrix.map_mul

theorem castM_one : castM 1 = 1 := by
  unfold castM
  exact Matrix.map_one _ (map_zero _) (map_one _)

end CFSG.KC.Co2Census

end
