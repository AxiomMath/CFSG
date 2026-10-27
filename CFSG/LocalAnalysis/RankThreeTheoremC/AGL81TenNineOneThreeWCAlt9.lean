module

public import CFSG.GH74.Uniqueness.SU.SU13TA9PermE
import CFSG.Permutation.AlternatingAutomorphism.Conjugation
public import Mathlib.Data.Rat.Floor
import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TenNineOneThree

open Equiv Equiv.Perm Subgroup CFSG.GH74.Uniqueness.SU.SU13.TA.L9

theorem inner_of_odd_alt {X : Type*} [Group X] {n : ℕ} (hn : 7 ≤ n)
    (e : X ≃* alternatingGroup (Fin n)) (φ : MulAut X) {m : ℕ} (hm : φ ^ (2 * m + 1) = 1) :
    ∃ g : X, ∀ x : X, φ x = g * x * g⁻¹ := by
  set α := MulAut.congr e φ
  obtain ⟨σ, hσ⟩ := CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le
    (Or.inr hn) α
  have hpow : ∀ k : ℕ, ∀ y : alternatingGroup (Fin n),
      (((α ^ k) y : alternatingGroup (Fin n)) : Perm (Fin n)) = σ ^ k * y * (σ ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      rw [pow_succ', MulAut.mul_apply, hσ, ih, pow_succ']
      group
  have hα : α ^ (2 * m + 1) = 1 := by rw [← map_pow, hm, map_one]
  have h6 : α ^ (2 * m + 2) = α := by rw [pow_succ, hα, one_mul]
  have hsign : Perm.sign (σ ^ (2 * m + 2)) = 1 := by
    rw [map_pow, show 2 * m + 2 = 2 * (m + 1) by ring, pow_mul, Int.units_sq, one_pow]
  set l : alternatingGroup (Fin n) := ⟨σ ^ (2 * m + 2), Perm.mem_alternatingGroup.mpr hsign⟩
  refine ⟨e.symm l, fun x => e.injective ?_⟩
  have h1 : e (φ x) = α (e x) := by simp [α, MulAut.congr_apply]
  rw [h1, ← h6]
  apply Subtype.ext
  rw [hpow]
  simp [l]

theorem toP_comm_pw : ∀ i j k : Fin 3, toP i j k * pw = pw * toP i j k → j = i ∧ k = i := by
  decide

theorem pt_toP_comm : ∀ i : Fin 3,
    pt * toP i i i * pt⁻¹ * pa = pa * (pt * toP i i i * pt⁻¹) ∧
      pt * toP i i i * pt⁻¹ * pb = pb * (pt * toP i i i * pt⁻¹) ∧
      pt * toP i i i * pt⁻¹ * pc = pc * (pt * toP i i i * pt⁻¹) := by
  decide

theorem pt_toP_not_pow : ∀ i : Fin 3, i ≠ 0 → ∀ l : Fin 3,
    pt * toP i i i * pt⁻¹ ≠ toP i i i ^ (l : ℕ) := by
  decide

theorem toP_comm_pt : ∀ i : Fin 3, toP i i i * pt = pt * toP i i i → i = 0 := by
  decide

theorem toP_zero : toP 0 0 0 = 1 := by decide

theorem eq_toE_diag {x : alternatingGroup (Fin 9)} (hx : x ∈ Ebar)
    (hw : x * ew = ew * x) : ∃ i : Fin 3, x = toE i i i := by
  obtain ⟨i, j, k, rfl⟩ := mem_Ebar_iff_toE.mp hx
  obtain ⟨hj, hk⟩ := toP_comm_pw i j k (congrArg Subtype.val hw)
  exact ⟨i, by rw [hj, hk]⟩

theorem gens_mem_Pst : ea ∈ Pst ∧ eb ∈ Pst ∧ ec ∈ Pst :=
  ⟨Ebar_le_Pst ea_mem_Ebar, Ebar_le_Pst eb_mem_Ebar, Ebar_le_Pst ec_mem_Ebar⟩

theorem card_alt9 : Nat.card (alternatingGroup (Fin 9)) = 181440 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem not_three_dvd_index_Pst : ¬ 3 ∣ Pst.index := by
  have h := Pst.card_mul_index
  rw [card_Pst, card_alt9] at h
  have : Pst.index = 2240 := by omega
  rw [this]
  norm_num

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC
