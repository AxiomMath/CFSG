module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverModelsSylow

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Twin3.M12W

open Equiv CFSG.Blueprint CFSG.ComponentClassification.M12Cover
open CFSG.ComponentClassification.M12Cover.InternalSylow

@[expose] def fp (σ : Perm (Fin 12)) : ℕ := (Finset.univ.filter fun p : Fin 12 => σ p = p).card

@[expose] def gC (j p : ℕ) : ℕ := SylowTable.nth 0 (SylowTable.code j) p

@[expose] def wxT : List (List ℕ) :=
  [[], [], [], [], [1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2,
    2, 1, 2], [], [1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2,
    2, 1, 2], [1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2,
    1, 2, 2, 1, 2, 1, 2, 1, 2, 1], [], [1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1,
    2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1], [], [], [], [], [], [], [], [], [], [],
    [], [], [], [2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1,
    2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2], [1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2,
    1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1], [], [1, 2, 1, 2, 1, 2, 1, 2, 1,
    2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2],
    [1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1,
    2, 1, 2, 1, 2, 2], [1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2,
    1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1], [], [], [1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2,
    2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2], [], [], [],
    [], [], [2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2,
    2, 1, 2, 1, 2, 1, 2, 1, 2, 2], [1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2,
    2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2], [1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2,
    2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2], [], [1, 2, 2, 1, 2, 1,
    2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2],
    [], [], [], [], [], [], [1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1,
    2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1], [], [], [], [], [], [], [1, 2, 1, 2, 2, 1, 2,
    1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2,
    1], [2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2,
    1, 2, 1, 2, 2], [2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2,
    1, 2, 1, 2, 1, 2, 1, 2, 2], [], [], [], [1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2,
    1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1], [1, 2, 1, 2, 2, 1, 2, 1, 2,
    1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1],
    []]

@[expose] def wuT : List (List ℕ) :=
  [[], [], [], [], [2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2], [],
    [2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2], [2, 2, 1, 2, 2, 1,
    2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2], [], [2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2,
    1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2], [], [], [], [], [], [], [], [], [], [], [], [], [], [2, 2,
    1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2], [2, 2, 1, 2, 1, 2, 2, 1, 2,
    1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2], [], [2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1,
    2, 2, 1, 2, 1, 2, 2, 1, 2], [2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2], [2, 2, 1, 2, 1, 2, 2, 1,
    2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2], [], [], [2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2,
    2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2], [], [], [], [], [], [2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2,
    2, 1, 2, 2, 1, 2, 1, 2, 1, 2], [2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2], [2, 1, 2, 1, 2, 1, 2,
    2, 1, 2, 2, 1, 2, 2], [], [2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2], [], [], [], [], [], [],
    [2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2], [], [], [], [], [], [], [2, 1, 2, 1, 2, 1, 2, 2, 1,
    2, 2, 1, 2, 2], [2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2], [2,
    1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2], [], [], [], [2, 1, 2,
    1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2], [2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2], []]

@[expose] def xC (j p : ℕ) : ℕ := wordCode (SylowTable.nth [] wxT j) p

@[expose] def uC (j p : ℕ) : ℕ := wordCode (SylowTable.nth [] wuT j) p

@[expose] def eqF (c d : ℕ → ℕ) : Bool := (List.range 12).all fun p => c p == d p

@[expose] def fixF (c : ℕ → ℕ) : ℕ := (List.range 12).countP fun p => c p == p

@[expose] def isJ (j : ℕ) : Bool :=
  !eqF (fun p => gC j (gC j p)) id && eqF (fun p => gC j (gC j (gC j (gC j p)))) id &&
    fixF (fun p => gC j (gC j p)) != 0

@[expose] def witOK (j : ℕ) : Bool :=
  eqF (fun p => xC j (xC j p)) id && eqF (fun p => xC j (gC j p)) (fun p => gC j (xC j p)) &&
    eqF (fun p => xC j (uC j p)) (fun p => uC j (xC j p)) && eqF (fun p => uC j (uC j p)) id &&
    eqF (fun p => uC j (gC j (uC j (gC j p)))) id &&
    ((fixF (xC j) == 0) == (fixF (fun p => xC j (gC j (gC j p))) == 0)) &&
    ((fixF (uC j) == 0) ^^ (fixF (fun p => xC j (uC j p)) == 0) ^^
      (fixF (fun p => uC j (gC j p)) == 0) ^^ (fixF (fun p => xC j (uC j (gC j p))) == 0))

theorem tab_ok : (List.range 64).all (fun j => !isJ j || witOK j) = true := by decide +kernel

theorem eqF_iff {c d : ℕ → ℕ} {σ τ : Perm (Fin 12)} (hc : IsFCode c σ) (hd : IsFCode d τ) :
    eqF c d = true ↔ σ = τ := by
  constructor
  · intro h
    refine Equiv.ext fun p => Fin.ext ?_
    rw [← hc p, ← hd p]
    exact eq_of_beq (all_range h p.2)
  · rintro rfl
    refine List.all_eq_true.2 fun p hp => ?_
    have hp' := List.mem_range.1 hp
    exact beq_iff_eq.2 ((hc ⟨p, hp'⟩).trans (hd ⟨p, hp'⟩).symm)

theorem fixF_eq {c : ℕ → ℕ} {σ : Perm (Fin 12)} (hc : IsFCode c σ) : fixF c = fp σ :=
  (card_fixed_eq hc).symm

theorem isFCode_gC {j : ℕ} (hj : j < 64) : IsFCode (gC j) (SylowTable.elt j : Perm (Fin 12)) :=
  isFCode_of_isCode (SylowTable.isCode_elt j hj)

theorem exists_witness {j : ℕ} (hj : j < 64) {σ : Perm (Fin 12)}
    (hσ : (SylowTable.elt j : Perm (Fin 12)) = σ) (h2 : σ * σ ≠ 1) (h4 : σ * σ * (σ * σ) = 1)
    (hf : fp (σ * σ) ≠ 0) :
    ∃ X U : Perm (Fin 12), X ∈ NativeSporadic.M12 ∧ U ∈ NativeSporadic.M12 ∧ X * X = 1 ∧
      X * σ = σ * X ∧ X * U = U * X ∧ U * U = 1 ∧ U * σ * (U * σ) = 1 ∧
      (fp X == 0) = (fp (X * (σ * σ)) == 0) ∧
      ((fp U == 0) ^^ (fp (X * U) == 0) ^^ (fp (U * σ) == 0) ^^
        (fp (X * (U * σ)) == 0)) = true := by
  have hG : IsFCode (gC j) σ := hσ ▸ isFCode_gC hj
  have hG2 : IsFCode (fun p => gC j (gC j p)) (σ * σ) := hG.mul hG
  have hI : IsFCode id (1 : Perm (Fin 12)) := IsFCode.one
  have hJ : isJ j = true := by
    have e1 : eqF (fun p => gC j (gC j p)) id = false :=
      Bool.eq_false_iff.2 fun h => h2 ((eqF_iff hG2 hI).1 h)
    have e2 : eqF (fun p => gC j (gC j (gC j (gC j p)))) id = true :=
      (eqF_iff (c := fun p => gC j (gC j (gC j (gC j p)))) (hG2.mul hG2) hI).2 h4
    simp only [isJ, e1, e2, fixF_eq hG2, Bool.not_false, Bool.true_and, bne_iff_ne, ne_eq, hf,
      not_false_eq_true]
  have hW : witOK j = true := by simpa [hJ] using all_range tab_ok hj
  have hX : IsFCode (xC j) (evalWord (SylowTable.nth [] wxT j)) := isFCode_evalWord _
  have hU : IsFCode (uC j) (evalWord (SylowTable.nth [] wuT j)) := isFCode_evalWord _
  set X := evalWord (SylowTable.nth [] wxT j)
  set U := evalWord (SylowTable.nth [] wuT j)
  simp only [witOK, Bool.and_eq_true] at hW
  obtain ⟨⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, he⟩, hf'⟩, hg⟩ := hW
  rw [fixF_eq hX, fixF_eq (c := fun p => xC j (gC j (gC j p))) (hX.mul hG2)] at hf'
  rw [fixF_eq hU, fixF_eq (c := fun p => xC j (uC j p)) (hX.mul hU),
    fixF_eq (c := fun p => uC j (gC j p)) (hU.mul hG),
    fixF_eq (c := fun p => xC j (uC j (gC j p))) (hX.mul (hU.mul hG))] at hg
  exact ⟨X, U, evalWord_mem _, evalWord_mem _, (eqF_iff (hX.mul hX) hI).1 ha,
    (eqF_iff (hX.mul hG) (hG.mul hX)).1 hb, (eqF_iff (hX.mul hU) (hU.mul hX)).1 hc,
    (eqF_iff (hU.mul hU) hI).1 hd,
    (eqF_iff (c := fun p => uC j (gC j (uC j (gC j p)))) ((hU.mul hG).mul (hU.mul hG)) hI).1 he,
    beq_iff_eq.1 hf', hg⟩

end CFSG.ClassicalInvolution.Q3.TA3.Twin3.M12W
