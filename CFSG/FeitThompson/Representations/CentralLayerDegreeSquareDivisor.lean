module

public import CFSG.FeitThompson.Representations.ClassFunctionInnerProductNorms
public import CFSG.FeitThompson.Definitions.CoreDetectingNormalInducedFamily
public import Mathlib.GroupTheory.Complement
import CFSG.FeitThompson.Representations.CentralSubgroupBoundsDegreeSquare
import CFSG.FeitThompson.Foundations.FittingContainsCentralizerSolvable
import CFSG.FeitThompson.Representations.PGroupIrreducibleDegreePower

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {L : Type*} [Group L] {p a : ℕ} {P E Z : Subgroup L}

theorem irrChar_eq_Irr (G : Type*) [Group G] : irrChar ℂ G = Irr G := by
  ext χ; rw [mem_irrChar, mem_Irr]

theorem relIndex_mul_card_of_le (h : Z ≤ P) : Z.relIndex P * Nat.card Z = Nat.card P := by
  rw [Subgroup.relIndex, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv,
    Subgroup.index_mul_card]

theorem relIndex_pos_of_le [Finite L] (h : Z ≤ P) : 0 < Z.relIndex P := by
  refine Nat.pos_of_ne_zero fun h0 => ?_
  have h1 := relIndex_mul_card_of_le h
  rw [h0, zero_mul] at h1
  exact (Nat.card_pos (α := P)).ne' h1.symm

theorem pow_two_mul_dvd_relIndex [Finite L] (hp : p.Prime) (hP : Nat.card P = p ^ a)
    (hZc : Z ≤ Subgroup.centralizer (P : Set L)) {θ : P → ℂ} (hθ : θ ∈ Irr P) {b : ℕ}
    (hb : θ 1 = (p : ℂ) ^ b) : p ^ (2 * b) ∣ Z.relIndex P := by
  obtain ⟨n, hn, hnle⟩ := exists_degree_eq_and_sq_le_index_of_le_center hθ
    (subgroupOf_le_center_of_le_centralizer le_rfl (Subgroup.le_centralizer_iff.1 hZc))
  have hnb : n = p ^ b := by
    have h : ((n : ℕ) : ℂ) = ((p ^ b : ℕ) : ℂ) := by push_cast; rw [← hn, hb]
    exact_mod_cast h
  obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow hp).1 (hP ▸ Subgroup.relIndex_dvd_card Z P)
  rw [hc]
  refine pow_dvd_pow p ((Nat.pow_le_pow_iff_right hp.one_lt).1 ?_)
  calc p ^ (2 * b) = n ^ 2 := by rw [hnb, ← pow_mul, mul_comm]
    _ ≤ p ^ c := by rw [← hc, Subgroup.relIndex]; exact hnle

theorem index_sq_mul_relIndex_pos [Finite L] (hZP : Z ≤ P) : 0 < P.index ^ 2 * Z.relIndex P :=
  Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero) 2)
    (relIndex_pos_of_le hZP)

variable [Fintype L]

theorem indClassFun_apply_one (P : Subgroup L) (θ : P → ℂ) :
    indClassFun P θ 1 = (P.index : ℂ) * θ 1 := by
  rw [indClassFun_one]
  congr 1
  have hcard : (Nat.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  field_simp
  rw [← Nat.cast_mul, Subgroup.card_mul_index]

theorem exists_degree_eq_index_mul_pow_and_sq_dvd (hp : p.Prime) (hP : Nat.card P = p ^ a)
    (hZ : Z ≤ P ⊓ Subgroup.centralizer (P : Set L)) {χ : L → ℂ}
    (hχ : χ ∈ indFamDetect P (Z.subgroupOf P)) :
    ∃ b : ℕ, χ 1 = ((P.index * p ^ b : ℕ) : ℂ) ∧
      (P.index * p ^ b) ^ 2 ∣ P.index ^ 2 * Z.relIndex P := by
  obtain ⟨θ, hθ, rfl⟩ := (mem_indFamDetect P).1 hχ
  have hθirr : θ ∈ Irr P := by rw [← irrChar_eq_Irr]; exact (mem_irrDetect.1 hθ).1
  obtain ⟨b, -, hb⟩ := Irr.exists_one_eq_pow_of_card_eq_prime_pow hp hP hθirr
  refine ⟨b, by rw [indClassFun_apply_one, hb]; push_cast; ring, ?_⟩
  have h := pow_two_mul_dvd_relIndex hp hP (hZ.trans inf_le_right) hθirr hb
  calc (P.index * p ^ b) ^ 2 = P.index ^ 2 * p ^ (2 * b) := by ring
    _ ∣ P.index ^ 2 * Z.relIndex P := mul_dvd_mul_left _ h

theorem exists_degree_eq_card_mul_pow_and_sq_dvd (_hpodd : Odd p) (hp : p.Prime) (_ha : 1 ≤ a)
    (_hLodd : Odd (Nat.card L)) [P.Normal] (hP : Nat.card P = p ^ a) (hPE : P.IsComplement' E)
    (_hE : E ≠ ⊥) [Z.Normal] (_hZ : Z ≠ ⊥) (hZP : Z ≤ P ⊓ Subgroup.centralizer (P : Set L))
    {χ : L → ℂ} (hχ : χ ∈ indFamDetect P (Z.subgroupOf P)) :
    ∃ b : ℕ, χ 1 = ((Nat.card E * p ^ b : ℕ) : ℂ) ∧
      0 < Nat.card E ^ 2 * Z.relIndex P ∧
      (Nat.card E * p ^ b) ^ 2 ∣ Nat.card E ^ 2 * Z.relIndex P := by
  have he : P.index = Nat.card E := hPE.symm.index_eq_card
  obtain ⟨b, h1, h2⟩ := exists_degree_eq_index_mul_pow_and_sq_dvd hp hP hZP hχ
  refine ⟨b, by rw [h1, he], ?_, by rw [← he]; exact h2⟩
  rw [← he]
  exact index_sq_mul_relIndex_pos (hZP.trans inf_le_left)

end CFSG.FeitThompson
