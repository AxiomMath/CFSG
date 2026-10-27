module

public import CFSG.ClassicalInvolution.Phan.Phan3B3Coord
public import CFSG.ClassicalInvolution.Phan.Phan3B3TwistData
public import CFSG.ClassicalInvolution.Phan.Phan3B3Words

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

@[expose] def evalOrd {n : ℕ} {M : Type*} [Monoid M] (ord : Fin n → ℕ) (g : Fin n → M)
    (w : List (Fin n × Bool)) : M :=
  (w.map fun l => if l.2 then g l.1 else g l.1 ^ (ord l.1 - 1)).prod

theorem wordVal_eq_evalOrd {n : ℕ} {G : Type*} [Group G] (ord : Fin n → ℕ)
    (g : Fin n → G) (hpos : ∀ i, 0 < ord i) (hord : ∀ i, g i ^ ord i = 1)
    (w : List (Fin n × Bool)) : wordVal g w = evalOrd ord g w := by
  unfold wordVal evalOrd
  congr 1
  apply List.map_congr_left
  intro l _
  obtain ⟨i, b⟩ := l
  cases b
  · have h1 : g i * g i ^ (ord i - 1) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel (hpos i), hord i]
    simp only [letterVal, Bool.cond_false, Bool.false_eq_true, ↓reduceIte]
    exact inv_eq_of_mul_eq_one_right h1
  · simp [letterVal]

theorem map_evalOrd {n : ℕ} {M N : Type*} [Monoid M] [Monoid N] (ψ : M →* N)
    (ord : Fin n → ℕ) (g : Fin n → M) (w : List (Fin n × Bool)) :
    ψ (evalOrd ord g w) = evalOrd ord (fun i => ψ (g i)) w := by
  unfold evalOrd
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l _
  by_cases h : l.2 <;> simp [h, map_pow]

section Sp4

open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.Assembly.LowTwoRank (StatedSp)

@[expose] def spMats : Fin 4 → Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3) :=
  ![LAz, LBz, SAz, SBz]

@[expose] def spOrd : Fin 4 → ℕ := ![4, 3, 4, 3]

theorem spMats_ord : ∀ i, spMats i ^ spOrd i = 1 := by decide +kernel

theorem evalOrd_b3Sp4Rels : ∀ w ∈ b3Sp4Rels, evalOrd spOrd spMats w = 1 := by decide +kernel

@[expose] noncomputable def spGens : Fin 4 → StatedSp 2 F3F :=
  ![b2Coord3.ℓ A2, b2Coord3.ℓ B2, b2Coord3.s A2, b2Coord3.s B2]

theorem mat_spGens (i : Fin 4) : mat 2 F3F (spGens i) = (spMats i).map eF := by
  fin_cases i
  · exact mat_ell_A2
  · exact mat_ell_B2
  · exact mat_s_A2
  · exact mat_s_B2

@[expose] noncomputable def mapEF :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3) →*
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F3F :=
  (RingHom.mapMatrix (eF : ZMod 3 →+* F3F)).toMonoidHom

theorem mapEF_apply (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3)) :
    mapEF M = M.map eF := rfl

theorem spGens_pow (i : Fin 4) : spGens i ^ spOrd i = 1 := by
  apply mat_injective
  rw [map_pow, mat_spGens, map_one, ← mapEF_apply, ← map_pow, spMats_ord, map_one]

theorem spOrd_pos (i : Fin 4) : 0 < spOrd i := by
  fin_cases i <;> decide

theorem mat_wordVal_spGens (w : List (Fin 4 × Bool)) :
    mat 2 F3F (wordVal spGens w) = (evalOrd spOrd spMats w).map eF := by
  rw [wordVal_eq_evalOrd spOrd spGens spOrd_pos spGens_pow, map_evalOrd, ← mapEF_apply,
    map_evalOrd]
  congr 1
  funext i
  rw [mat_spGens, mapEF_apply]

theorem wordVal_spGens_eq_iff {w₁ w₂ : List (Fin 4 × Bool)} :
    wordVal spGens w₁ = wordVal spGens w₂ ↔ evalOrd spOrd spMats w₁ = evalOrd spOrd spMats w₂ := by
  rw [← mat_injective.eq_iff, mat_wordVal_spGens, mat_wordVal_spGens]
  exact (Matrix.map_injective eF.injective).eq_iff

theorem wordVal_spGens_b3Sp4Rels : ∀ w ∈ b3Sp4Rels, wordVal spGens w = 1 := by
  intro w hw
  have h : wordVal spGens w = wordVal spGens [] := by
    rw [wordVal_spGens_eq_iff]
    simpa [evalOrd] using evalOrd_b3Sp4Rels w hw
  simpa [wordVal] using h

@[expose] def wSp : List (Fin 4 × Bool) := [(3, false), (2, false), (3, true)]

@[expose] def conjSp (u : List (Fin 4 × Bool)) : List (Fin 4 × Bool) :=
  wSp ++ u ++ invWord wSp

theorem evalOrd_comm11 : ∀ p ∈ ([(0, 0), (0, 1), (1, 0), (1, 1)] : List (Fin 4 × Fin 4)),
    evalOrd spOrd spMats ([(p.1, true)] ++ conjSp [(p.2, true)] ++ invWord [(p.1, true)] ++
      invWord (conjSp [(p.2, true)])) = 1 := by
  decide +kernel

theorem spGens_comm11 : ∀ p ∈ ([(0, 0), (0, 1), (1, 0), (1, 1)] : List (Fin 4 × Fin 4)),
    spGens p.1 * wordVal spGens (conjSp [(p.2, true)]) =
      wordVal spGens (conjSp [(p.2, true)]) * spGens p.1 := by
  intro p hp
  have h : wordVal spGens ([(p.1, true)] ++ conjSp [(p.2, true)] ++ invWord [(p.1, true)] ++
      invWord (conjSp [(p.2, true)])) = wordVal spGens [] := by
    rw [wordVal_spGens_eq_iff]
    have := evalOrd_comm11 p hp
    rw [this]
    rfl
  have h1 := (wordVal_comm_iff spGens [(p.1, true)] (conjSp [(p.2, true)])).1 (by
    simpa [wordVal] using h)
  simpa [wordVal, letterVal] using h1

end Sp4

end CFSG.ClassicalInvolution.Phan.Q3G
