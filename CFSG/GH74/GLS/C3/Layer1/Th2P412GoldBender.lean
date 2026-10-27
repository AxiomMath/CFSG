module

public import CFSG.GH74.Uniqueness.Bender.Models
public import CFSG.Goldschmidt.Basic

public section

namespace CFSG.GH74.GLS.Th2.P412

open Subgroup CFSG CFSG.Open CFSG.GH74.Uniqueness.Bender
open scoped MatrixGroups

theorem sylow_card_of_nonabelian_bender
    {K : Type} [Group K] [Finite K]
    (hK : (∃ n : ℕ, 1 ≤ n ∧ Nonempty (K ≃* Sz n)) ∨
      (∃ f : ℕ, 2 ≤ f ∧ Nonempty (K ≃* PSU3 2 f)))
    (T : Sylow 2 K) (h4 : Nat.card (CFSG.Goldschmidt.Omega1 (T : Subgroup K)) ≤ 4) :
    Nat.card (T : Subgroup K) = 64 := by
  have hcenter : ∀ {n i e : ℕ} (hBT : BenderType K n i e),
      2 ^ n ≤ 4 → Nat.card (T : Subgroup K) = (2 ^ n) ^ i := by
    intro n i e hBT hn
    obtain ⟨t, hc⟩ := hBT.exists_benderCore T
    exact hc.card_eq
  have hroot : ∀ {n i e : ℕ} (hBT : BenderType K n i e), 2 ^ n ≤ 4 := by
    intro n i e hBT
    obtain ⟨t, hc⟩ := hBT.exists_benderCore T
    have hle : rootCenter (T : Subgroup K) ≤ CFSG.Goldschmidt.Omega1 (T : Subgroup K) := by
      intro z hz
      exact Subgroup.subset_closure ⟨hz.1, by rw [sq]; exact hc.center_sq z hz⟩
    have h1 : Nat.card (rootCenter (T : Subgroup K)) ≤
        Nat.card (CFSG.Goldschmidt.Omega1 (T : Subgroup K)) :=
      Subgroup.card_le_of_le hle
    rw [hc.card_center] at h1
    exact h1.trans h4
  rcases hK with ⟨a, ha, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩
  ·
    exfalso
    have hmodel : CFSG.Theory.Comparator.SzModel a = Sz a := szModel_eq_open_sz a
    have hBT : BenderType K (2 * a + 1) 2 1 :=
      BenderType.suzuki a ha (e.trans (MulEquiv.subgroupCongr hmodel.symm))
    have h1 := hroot hBT
    have h2 : 2 ^ 3 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  ·
    have hmodel : CFSG.Theory.Comparator.PSU3Model f = PSU3 2 f := CFSG.Models.benderPSU3Model_eq_psu3 f
    have hBT : BenderType K f 3 ((2 ^ f + 1) / Nat.gcd 3 (2 ^ f + 1)) :=
      BenderType.unitary f hf (e.trans (MulEquiv.subgroupCongr hmodel.symm))
    have h1 := hroot hBT
    have hf2 : f = 2 := by
      by_contra hne
      have : 2 ^ 3 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    subst hf2
    rw [hcenter hBT h1]
    norm_num

end CFSG.GH74.GLS.Th2.P412
