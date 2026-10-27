
module


public import CFSG.Sporadic.Schreier.J4SOdd276Base1
public import Certificates.Certificate12605
public import CFSG.Sporadic.Schreier.J4SFive

@[expose] public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2.Native
open scoped Matrix

theorem h11_cert :
    (h11B = h11Poly 1 ∧ comp11 h11B h11Binv = idRows 11 ∧ Bounded h11B ∧ Bounded h11Binv)
      ∧ (∀ w < 2048, Bounded (h11Poly w))
      ∧ (∀ w < 2048, powCols (h11X w) 1024 = h11X w)
      ∧ (∀ w < 2048, powCols (h11X w) 3 = idRows 11 →
        h11X w = idRows 11 ∨ fixCount (h11X w) < 4)
      ∧ (∀ k < 27, 0 < k → 4 ≤ fixCount q3Cols[k]!)
      ∧ (Bounded (idRows 11)) :=
  Certificates.certificate12605

theorem bounded_powCols_h11 :
    ∀ (m : ℕ) {C : Array ℕ}, Bounded C → Bounded (powCols C m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro C hC
    rw [powCols]
    split_ifs
    · exact h11_cert.2.2.2.2.2
    · exact bounded_comp11 hC (ih _ (by omega) (bounded_comp11 hC hC))
    · exact ih _ (by omega) (bounded_comp11 hC hC)

theorem bounded_h11X {w : ℕ} (hw : w < 2048) :
    Bounded (h11X w) :=
  bounded_comp11 (h11_cert.2.1 w hw)
    h11_cert.1.2.2.2

theorem exists_actsBy_h11X
    {k : J} (hk : k ∈ K) (hc : k * a276 = a276 * k) :
    ∃ w < 2048, ActsBy k (h11X w) := by
  obtain ⟨hC, hCb⟩ := colsOf_spec hk
  set C := colsOf k with hCdef
  have hQb : Bounded (wordCols a276Word) := a276_check.1
  have hcomm : comp11 C (wordCols a276Word) = comp11 (wordCols a276Word) C := by
    have h1 := actsBy_mul hC a276_acts
    have h2 := actsBy_mul a276_acts hC
    rw [hc] at h1
    exact eq_of_actsBy_bounded h1 h2 (bounded_comp11 hCb hQb) (bounded_comp11 hQb hCb)
  have hX : colsMatrix C * colsMatrix (wordCols a276Word) =
      colsMatrix (wordCols a276Word) * colsMatrix C := by
    rw [← colsMatrix_comp11, ← colsMatrix_comp11, hcomm]
  obtain ⟨hBeq, hBinv, hBb, hBib⟩ := h11_cert.1
  set w := app11 C 1 with hw
  have hwlt : w < 2048 := vecMulN_lt (bounded_getD hCb) 1
  have hXc : Commute (colsMatrix C) (colsMatrix (wordCols a276Word)) := hX
  have hXB : colsMatrix C * colsMatrix h11B = colsMatrix (h11Poly w) := by
    refine matrix_eq_of_cols fun i => ?_
    have hpoly : ∀ v, (h11Poly v)[i.val]?.getD 0 = app11 (powCols (wordCols a276Word) i) v := by
      intro v
      rw [h11Poly, Array.getElem?_ofFn, dite_eq_left i.isLt, Option.getD_some]
    rw [← Matrix.mulVec_mulVec, colsMatrix_mulVec_single, colsMatrix_mulVec_single, hBeq,
      hpoly, hpoly, ← colsMatrix_mulVec, ← colsMatrix_mulVec, colsMatrix_powCols,
      Matrix.mulVec_mulVec, (hXc.pow_right i).eq, ← Matrix.mulVec_mulVec, colsMatrix_mulVec]
  have hCeq : C = h11X w := by
    refine colsMatrix_inj hCb (bounded_h11X hwlt) ?_
    have hBB : colsMatrix h11B * colsMatrix h11Binv = 1 := by
      rw [← colsMatrix_comp11, hBinv, colsMatrix_idRows]
    rw [h11X, colsMatrix_comp11, ← hXB, Matrix.mul_assoc, hBB, Matrix.mul_one]
  exact ⟨w, hwlt, hCeq ▸ hC⟩

theorem card_centralizer_N_a276_le :
    Nat.card (Subgroup.centralizer {a276} ⊓ N : Subgroup J) ≤ 2 := by
  rw [card_centralizer_N_of_actsBy a276_acts (bounded_getD a276_check.1), fixCount]
  refine (Finset.card_le_card (t := {0, 14}) fun a ha => ?_).trans (by decide)
  rw [Finset.mem_filter, Finset.mem_range] at ha
  rw [Finset.mem_insert, Finset.mem_singleton]
  rcases a276_check.2.2.2 a ha.1 ha.2 with h | h
  · exact Or.inl h
  · exact Or.inr h

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
