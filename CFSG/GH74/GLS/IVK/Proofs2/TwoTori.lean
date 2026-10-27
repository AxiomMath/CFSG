module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma118

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
open scoped commutatorElement Pointwise

section Arith

theorem eight_dvd_sq_sub_one {u : ℕ} (hu : Odd u) : 8 ∣ u ^ 2 - 1 := by
  obtain ⟨k, rfl⟩ := hu
  have h : (2 * k + 1) ^ 2 - 1 = 8 * (k * (k + 1) / 2) := by
    have h2 : 2 ∣ k * (k + 1) := (Nat.even_mul_succ_self k).two_dvd
    obtain ⟨j, hj⟩ := h2
    have : (2 * k + 1) ^ 2 = 8 * j + 1 := by nlinarith
    rw [hj, Nat.mul_div_cancel_left _ (by norm_num)]
    omega
  exact ⟨_, h⟩

end Arith

section PrimeCore

open CFSG.GH74.GLS.IVK.Proofs2.Lemma118 DihedralGroup

variable {C : Type*} [Group C] [Finite C] {k : ℕ}

theorem pPrimeCore_dihedral_odd [NeZero k] (hk : Odd k) (φ : C ≃* DihedralGroup k) :
    Nat.card (pPrimeCore 2 C) = k := by
  set R : Subgroup C := (Subgroup.zpowers (r (1 : ZMod k))).map φ.symm.toMonoidHom with hR
  have hRcard : Nat.card R = k := by
    rw [hR, Subgroup.card_map_of_injective φ.symm.injective, Nat.card_zpowers, orderOf_r_one]
  have hRn : R.Normal := by
    have hnormD : (Subgroup.zpowers (r (1 : ZMod k))).Normal := by
      refine ⟨fun n hn g => ?_⟩
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      have hconj : g * (r (1 : ZMod k)) ^ j * g⁻¹ = (g * r (1 : ZMod k) * g⁻¹) ^ j := (conj_zpow).symm
      rw [hconj]
      rcases conj_r g (1 : ZMod k) with h | h
      · rw [h]
        exact Subgroup.zpow_mem_zpowers _ _
      · rw [h, inv_zpow']
        exact Subgroup.zpow_mem_zpowers _ _
    exact hnormD.map _ φ.symm.surjective
  have hle : R ≤ pPrimeCore 2 C := le_pPrimeCore_of_normal R (hRcard ▸ hk)
  have hge : pPrimeCore 2 C ≤ R := by
    intro c hc
    have hodd : Odd (orderOf (φ c)) := by
      rw [MulEquiv.orderOf_eq]
      exact odd_orderOf_pPrimeCore (⟨c, hc⟩ : pPrimeCore 2 C)
    obtain ⟨i, hi⟩ := exists_r_of_odd_orderOf hodd
    rw [hR, Subgroup.mem_map_equiv]
    rw [MulEquiv.symm_symm, hi]
    exact r_mem_zpowers i
  rw [← hRcard, le_antisymm hle hge]

end PrimeCore

end CFSG.GH74.GLS.IVK.Proofs2
