module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private lemma eq_one_of_dvd_forty {m : ℕ} (hm : m ∣ 40) (hodd : Odd m) (h5 : ¬ 5 ∣ m) :
    m = 1 := by
  have hcop5 : Nat.Coprime m 5 := (Nat.prime_five.coprime_iff_not_dvd.mpr h5).symm
  have h8 : m ∣ 8 := by
    have h40 : m ∣ 8 * 5 := by rwa [show (8 * 5 : ℕ) = 40 by norm_num]
    exact hcop5.dvd_mul_right.mp h40
  have hcop8 : Nat.Coprime 8 m := by
    have h : Nat.Coprime m (2 ^ 3) :=
      Nat.prime_two.coprime_pow_of_not_dvd (m := 3) hodd.not_two_dvd_nat
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
    exact h.symm
  exact Nat.eq_one_of_dvd_coprimes hcop8 h8 (dvd_refl m)

theorem a6c_range_equiv_A6 {X Γ : Type} [Group X] [Group Γ] [Finite X] [Finite Γ] (φ : X →* Γ)
    (e : X ⧸ center X ≃* alternatingGroup (Fin 6)) (hodd : Odd (Nat.card (center X)))
    (hker : ∀ x : X, φ x = 1 → x ∈ center X) (hΓ : ¬ 25 ∣ Nat.card Γ)
    (hc : ∀ ξ : Γ, orderOf ξ = 5 → Nat.card (centralizer ({ξ} : Set Γ)) ∣ 40) :
    Nonempty (φ.range ≃* alternatingGroup (Fin 6)) := by
  have hKZ : φ.ker ≤ center X := fun x hx => hker x (MonoidHom.mem_ker.mp hx)
  have hquot : Nat.card (X ⧸ center X) = 360 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hmain : Nat.card φ.range = Nat.card ((center X).map φ) * Nat.card (X ⧸ center X) := by
    rw [← Subgroup.index_ker φ, ← Subgroup.relIndex_mul_index hKZ, Subgroup.relIndex_ker,
      Subgroup.index_eq_card]
  have hAeq : Nat.card φ.range = 360 * Nat.card ((center X).map φ) := by
    rw [hmain, hquot]
    ring
  have hZ'odd : Odd (Nat.card ((center X).map φ)) :=
    hodd.of_dvd_nat (Subgroup.card_map_dvd (H := center X) (f := φ))
  have h5Z' : ¬ 5 ∣ Nat.card ((center X).map φ) := by
    intro h5
    apply hΓ
    have h25 : 25 ∣ Nat.card φ.range := by
      rw [hAeq]
      obtain ⟨m, hm⟩ := h5
      exact ⟨72 * m, by rw [hm]; ring⟩
    exact h25.trans (Subgroup.card_subgroup_dvd_card φ.range)
  have h5A : 5 ∣ Nat.card φ.range := by
    rw [hAeq]
    exact ⟨72 * Nat.card ((center X).map φ), by ring⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨ξ, hξ⟩ := exists_prime_orderOf_dvd_card' (G := φ.range) 5 h5A
  have hξΓ : orderOf (ξ : Γ) = 5 := by rw [Subgroup.orderOf_coe, hξ]
  have hcenter_le : center X ≤ φ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hmemZ' : φ z ∈ (center X).map φ := ⟨z, hz, rfl⟩
    have hmemcen : φ z ∈ centralizer ({(ξ : Γ)} : Set Γ) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp ξ.2
      rw [← hx, ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]
    have h1 : orderOf (φ z) ∣ 40 :=
      (Subgroup.orderOf_dvd_natCard (centralizer ({(ξ : Γ)} : Set Γ)) hmemcen).trans
        (hc (ξ : Γ) hξΓ)
    have h2 : orderOf (φ z) ∣ Nat.card ((center X).map φ) :=
      Subgroup.orderOf_dvd_natCard ((center X).map φ) hmemZ'
    exact orderOf_eq_one_iff.mp
      (eq_one_of_dvd_forty h1 (hZ'odd.of_dvd_nat h2) fun h5 => h5Z' (h5.trans h2))
  have hker_eq : φ.ker = center X := le_antisymm hKZ hcenter_le
  exact ⟨(QuotientGroup.quotientKerEquivRange φ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker_eq).trans e)⟩

end CFSG.OddStandard.SmallF3.Omega
