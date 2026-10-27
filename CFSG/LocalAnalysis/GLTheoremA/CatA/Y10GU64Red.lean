module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Glue
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSimple

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Assembly CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem label_eq_of {lab : GLALabel} {t : LargeEvenLieTag} {r m : ℕ} (ht : lab.tag = t) (hr : lab.rank = r)
    (hm : lab.n = m) : lab = ⟨t, r, m⟩ := by
  obtain ⟨t', r', m'⟩ := lab
  simp only at ht hr hm
  subst ht hr hm
  rfl

theorem u64Concl_of_n_two {lab : GLALabel} (ht : lab.tag = .twA) (hn : lab.n = 2) (h5 : 5 ∣ lab.rank + 1) :
    lab = ⟨.twA, 4, 2⟩ ∨ lab = ⟨.twA, 4, 6⟩ ∨ ∃ r : ℕ, 1 < r ∧ lab = ⟨.twA, 5 * r - 1, 2⟩ := by
  obtain ⟨r, hr⟩ := h5
  rcases Nat.lt_or_ge r 2 with hr2 | hr2
  · have hr1 : r = 1 := by omega
    left
    exact label_eq_of ht (by omega) hn
  · right; right
    exact ⟨r, by omega, label_eq_of ht (by omega) hn⟩

theorem u64Concl_of_six {lab : GLALabel} (ht : lab.tag = .twA) (hn : lab.n = 6) (hd : lab.rank + 1 = 5) :
    lab = ⟨.twA, 4, 6⟩ :=
  label_eq_of ht (by omega) hn

theorem uFactor_uFieldAut_eq {K : Type} [Field K] {d n : ℕ} (hn : 1 ≤ n) (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hd1 : 1 ≤ d) (hd3 : 3 ≤ d) (hq : ¬(d = 3 ∧ 2 ^ n = 2)) (φ : K ≃+* K) :
    uFactor (unitaryFieldData_of_card hn hcard) hd3 hq
      (uFieldAut (unitaryFieldData_of_card hn hcard) hd1 φ) = φ := by
  have h1 := uFactor_apply (unitaryFieldData_of_card hn hcard) hd3 hq
    (1 : uU (unitaryFieldData_of_card hn hcard) d) φ
  rwa [map_one, one_mul] at h1

theorem U64FactS_of_pieces (hLin : U64LinearPiece) (hInn : U64InnerPiece) (hFld : U64FieldPiece) :
    U64FactS := by
  intro S _ _ lab hZ hl hfam β hβ J hJ hJl
  rcases hfam with ⟨ht, h4, h5⟩ | ⟨ht, hn4, h5⟩
  ·
    exfalso
    obtain ⟨K, hK, hKf, hcard, ⟨e⟩⟩ := model_A hZ hl ht
    have hd5 : 5 ≤ lab.rank + 1 := Nat.le_of_dvd (Nat.succ_pos _) h5
    have hβ' : (MulAut.congr e β) ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
    exact hLin (lab.rank + 1) lab.n K hcard h4 hd5 h5 (MulAut.congr e β) hβ' (J.map e.toMonoidHom)
      (glaPComponent_transport e β hJ) (hasLabel_transport e hJl)
  ·
    obtain ⟨K, hK, hKf, hcard, ⟨e⟩⟩ := model_twA hZ hl ht
    have hd5 : 5 ≤ lab.rank + 1 := Nat.le_of_dvd (Nat.succ_pos _) h5
    have hd1 : 1 ≤ lab.rank + 1 := by omega
    have hd3 : 3 ≤ lab.rank + 1 := by omega
    have hq : ¬(lab.rank + 1 = 3 ∧ 2 ^ lab.n = 2) := fun H => by have := H.1; omega
    have hn1 : 1 ≤ lab.n := by omega
    have hβ' : (MulAut.congr e β) ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
    have hJ' := glaPComponent_transport e β hJ
    have hJl' := hasLabel_transport e hJl
    obtain ⟨A, φ, hdec, hφ⟩ := unitary_decomp hn1 hcard hd5 (MulAut.congr e β) hβ'
    rcases hφ with hφ1 | hφ3
    ·
      have hu := uConjAut_mem_inner hn1 hcard hd1 A
      have hβu : MulAut.congr e β = uConjAut (unitaryFieldData_of_card hn1 hcard) hd1 A := by
        rw [hdec, hφ1, map_one, mul_one]
      have hn2 : lab.n = 2 :=
        hInn (lab.rank + 1) lab.n K hcard hd5 h5 hn4 (MulAut.congr e β) (by rw [hβu]; exact hu) hβ'
          (J.map e.toMonoidHom) hJ' hJl'
      exact u64Concl_of_n_two ht hn2 h5
    ·
      have hφ3' : φ ^ 3 = 1 := by rw [← hφ3]; exact pow_orderOf_eq_one φ
      have hf3 : (uFieldAut (unitaryFieldData_of_card hn1 hcard) hd1 φ) ^ 3 = 1 := by
        rw [← map_pow, hφ3', map_one]
      have hf1 : uFieldAut (unitaryFieldData_of_card hn1 hcard) hd1 φ ≠ 1 := by
        intro h1
        have h2 := uFactor_uFieldAut_eq hn1 hcard hd1 hd3 hq φ
        rw [h1, map_one] at h2
        rw [← h2, orderOf_one] at hφ3
        exact absurd hφ3 (by norm_num)
      have hfo : orderOf (uFieldAut (unitaryFieldData_of_card hn1 hcard) hd1 φ) = 3 :=
        orderOf_eq_prime hf3 hf1
      have huf : (uConjAut (unitaryFieldData_of_card hn1 hcard) hd1 A *
          uFieldAut (unitaryFieldData_of_card hn1 hcard) hd1 φ) ^ 3 = 1 := by
        rw [← hdec]
        exact hβ'
      obtain ⟨hn6, hd6⟩ :=
        hFld (lab.rank + 1) lab.n K hcard hd5 h5 hn4
          (uConjAut (unitaryFieldData_of_card hn1 hcard) hd1 A)
          (uFieldAut (unitaryFieldData_of_card hn1 hcard) hd1 φ)
          (uConjAut_mem_inner hn1 hcard hd1 A) (uFieldAut_mem_field hn1 hcard hd1 φ) hfo huf
          (J.map e.toMonoidHom) (by rw [← hdec]; exact hJ') hJl'
      right; left
      exact u64Concl_of_six ht hn6 hd6

end CFSG.LocalAnalysis.GLTheoremA.Y10F
