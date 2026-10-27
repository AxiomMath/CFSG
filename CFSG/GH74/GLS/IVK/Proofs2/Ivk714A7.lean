module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Ord
public import CFSG.LieType.SteinbergBRSemidirectSL2

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG
open scoped MatrixGroups

theorem sl2_card_ne_alt7 (q : ℕ) (hq5 : 5 ≤ q) : q * (q ^ 2 - 1) ≠ 2520 ∧ q * (q ^ 2 - 1) ≠ 5040 :=
  ⟨sl2_card_ne_of_bound (B := 13) (by norm_num) (fun q h5 h13 => by interval_cases q <;> norm_num)
      q hq5,
    sl2_card_ne_of_bound (B := 17) (by norm_num) (fun q h5 h17 => by interval_cases q <;> norm_num)
      q hq5⟩

theorem not_surjective_sl2_alt7 {k : Type} [Field k] [Finite k] (hodd : Odd (Nat.card k))
    (h5 : 5 ≤ Nat.card k) (σ : SL(2, k) →* alternatingGroup (Fin 7)) (hσ : Function.Surjective σ) :
    False := by
  have hq : CFSG.IsQuasisimple SL(2, k) := CFSG.GH74.KGroups.L3Eps.isQuasisimple_sl2c (by omega)
  have hA : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hc2 : ringChar k ≠ 2 := by
    intro h
    have : (2 : ℕ) ∣ Nat.card k := by
      have hk : Fintype k := Fintype.ofFinite k
      obtain ⟨n, -, hn⟩ := FiniteField.card k (ringChar k)
      rw [Nat.card_eq_fintype_card, hn, h]
      exact dvd_pow_self 2 n.pos.ne'
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
  have hcard := CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two k
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup σ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective σ hσ).toEquiv, hA] at hmul
  rcases LocalCores.quasisimple_normal_subgroups hq σ.normal_ker with h1 | h1
  ·
    exfalso
    have : Subsingleton (alternatingGroup (Fin 7)) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨a', rfl⟩ := hσ a
      obtain ⟨b', rfl⟩ := hσ b
      have h2 : σ a' = 1 := MonoidHom.mem_ker.mp (by rw [h1]; trivial)
      have h3 : σ b' = 1 := MonoidHom.mem_ker.mp (by rw [h1]; trivial)
      rw [h2, h3]
    have := Nat.card_of_subsingleton (1 : alternatingGroup (Fin 7))
    omega
  · have hker : Nat.card σ.ker ∣ 2 := by
      have := Subgroup.card_dvd_of_le h1
      rwa [CFSG.LieType.SteinbergBR.card_center_SL2_eq_two hc2] at this
    have hpos : 0 < Nat.card σ.ker := Nat.card_pos
    have hle : Nat.card σ.ker ≤ 2 := Nat.le_of_dvd (by norm_num) hker
    have hk1 : Nat.card σ.ker = 1 ∨ Nat.card σ.ker = 2 := by omega
    obtain ⟨h2520, h5040⟩ := sl2_card_ne_alt7 (Nat.card k) h5
    rcases hk1 with h | h
    · rw [h] at hmul
      omega
    · rw [h] at hmul
      omega

end CFSG.GH74.GLS.IVK.Proofs2
