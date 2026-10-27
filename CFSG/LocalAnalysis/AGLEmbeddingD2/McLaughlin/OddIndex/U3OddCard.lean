module

public import CFSG.LieType.Universal.Unitary.Comparison
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups CFSG.LieType.BorelTits CFSG.LocalAnalysis.ComponentInitial

variable {F : Type} [Field F] {p f : ℕ}

theorem unitaryFieldData_of_card' [Fact p.Prime] [Finite F] (hF : Nat.card F = (p ^ f) ^ 2) :
    UnitaryFieldData p f F := by
  refine ⟨Fact.out, ?_, by rw [hF, ← pow_mul, mul_comm]⟩
  by_contra h
  have hf : f = 0 := by omega
  have := Finite.one_lt_card (α := F)
  rw [hF, hf] at this
  norm_num at this

theorem SU_eq_gramSU [Fact p.Prime] [CharP F p] [Finite F] (h : UnitaryFieldData p f F) :
    SU (unitaryInvolution F p f) 3 = gramSU h (antidiag 3) := by
  ext A
  rw [mem_SU, mem_gramSU, and_comm]
  have hσ : ∀ x : F, unitaryInvolution F p f x = h.bar x := fun x => by
    rw [unitaryInvolution_apply, h.bar_apply]
  have hfun : ⇑(unitaryInvolution F p f) = ⇑h.bar := funext hσ
  simp only [conjTr, hfun]

theorem antidiag_hermitian [Fact p.Prime] [CharP F p] [Finite F] (h : UnitaryFieldData p f F) (n : ℕ) :
    ((antidiag n : Matrix (Fin n) (Fin n) F).map h.bar)ᵀ = antidiag n := by
  ext i j
  simp only [transpose_apply, map_apply, antidiag, of_apply]
  by_cases hij : i = Fin.rev j
  · have hji : j = Fin.rev i := by rw [hij, Fin.rev_rev]
    simp only [eq_true hij, eq_true hji, ite_true, map_one]
  · have hji : ¬ j = Fin.rev i := fun h' => hij (by rw [h', Fin.rev_rev])
    simp only [eq_false hij, eq_false hji, ite_false, map_zero]

theorem card_SU3 [Fact p.Prime] [CharP F p] [Finite F] (hF : Nat.card F = (p ^ f) ^ 2) :
    Nat.card (SU (unitaryInvolution F p f) 3) =
      (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) := by
  have h := unitaryFieldData_of_card' hF
  have := Fintype.ofFinite F
  have hSU := (unitary_full_group_order h (gramForm_isSymm h (antidiag_hermitian h 3))
    (gramForm_separatingLeft h (det_antidiag_ne_zero 3)) (Module.finrank_fin_fun F)
    (by norm_num)).2.1
  rw [SU_eq_gramSU h, card_gramSU]
  have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ h.prime.pos
  have hprod : ∏ i ∈ Finset.Icc 2 3, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) =
      (((p ^ f : ℕ) : ℤ) ^ 2 - 1) * (((p ^ f : ℕ) : ℤ) ^ 3 + 1) := by
    rw [show Finset.Icc 2 3 = {2, 3} from rfl, Finset.prod_pair (by norm_num)]
    norm_num
  rw [hprod] at hSU
  norm_num at hSU
  have hq2 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ hq
  zify [hq2]
  rw [hSU]
  ring

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
