module

public import CFSG.GroupTheory.ABGDGroups.LinearASeven
public import Certificates.Certificate7
public import CFSG.Adapters.QiuzhenLegacy.Compat.G7.ASeven

public section

namespace CFSG.ABGTheoremB.IV9DGroups

open CFSG.ABGDGroups
open CFSG.GorensteinWalter (a7t a7a a7v a7s a7S a7U a7V
  aSeven_structure_fact_1_8_ii_centralizer factorization_two_2520)

local notation "A₇" => alternatingGroup (Fin 7)

theorem a7S_center_certificate {y : A₇} (hy : y ∈ a7S) (hyv : y * a7v = a7v * y)
    (hys : y * a7s = a7s * y) : y = 1 ∨ y = a7t := by
  change y = 1 ∨ y = a7v ∨ y = a7v ^ 2 ∨ y = a7v ^ 3 ∨ y = a7s ∨ y = a7s * a7v ∨
    y = a7s * a7v ^ 2 ∨ y = a7s * a7v ^ 3 at hy
  revert hyv hys
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem a7t_centralizer_certificate : ∀ y : A₇, y * a7t = a7t * y →
    (y * a7a * y⁻¹ = a7a ∨ y * a7a * y⁻¹ = a7a ^ 2) ∧
      (y * a7a ^ 2 * y⁻¹ = a7a ∨ y * a7a ^ 2 * y⁻¹ = a7a ^ 2) := by
  decide +kernel

theorem a7t_mem_a7V : a7t ∈ a7V := Or.inr (Or.inl rfl)

theorem a7v_mem_a7S : a7v ∈ a7S := Or.inr (Or.inl rfl)

theorem a7s_mem_a7S : a7s ∈ a7S := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

theorem mem_normalizer_a7U_of_commute {y : A₇} (hy : y * a7t = a7t * y) :
    y ∈ Subgroup.normalizer (a7U : Set A₇) := by
  obtain ⟨h1, h2⟩ := a7t_centralizer_certificate y hy
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  change n = 1 ∨ n = a7a ∨ n = a7a ^ 2 at hn
  change y * n * y⁻¹ = 1 ∨ y * n * y⁻¹ = a7a ∨ y * n * y⁻¹ = a7a ^ 2
  rcases hn with rfl | rfl | rfl
  · left
    group
  · exact Or.inr h1
  · exact Or.inr h2

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem card_of_aSeven (e : Q ≃* A₇) : Nat.card Q = 2520 := by
  rw [Nat.card_congr e.toEquiv, card_alternatingGroup_fin_seven]

theorem exists_sylow_eq_of_aSeven (e : Q ≃* A₇) {D : Subgroup Q} (hD : IsPGroup 2 D)
    (h4 : 4 < Nat.card D) : ∃ P : Sylow 2 Q, (P : Subgroup Q) = D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hD.exists_card_eq
  have hdvd : 2 ^ k ∣ 2 ^ 3 * 315 := by
    rw [← hk, show (2 ^ 3 * 315 : ℕ) = 2520 by norm_num, ← card_of_aSeven e]
    exact Subgroup.card_subgroup_dvd_card D
  have hcop : Nat.Coprime (2 ^ k) 315 :=
    Nat.Coprime.pow_left k (by norm_num)
  have h8 : 2 ^ k ∣ 2 ^ 3 := hcop.dvd_of_dvd_mul_right hdvd
  have hk3 : k ≤ 3 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h8
  have hk3' : 3 ≤ k := by
    by_contra h
    have : k ≤ 2 := by omega
    have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
    omega
  have hcard : Nat.card D = 2 ^ (Nat.card Q).factorization 2 := by
    rw [hk, card_of_aSeven e, factorization_two_2520, show k = 3 by omega]
  exact ⟨Sylow.ofCard D hcard, Sylow.coe_ofCard _ _⟩

theorem inf_eq_bot_of_odd_of_isPGroup {X D : Subgroup Q} (hX : Odd (Nat.card X))
    (hD : IsPGroup 2 D) : X ⊓ D = ⊥ := by
  obtain ⟨k, hk⟩ := hD.exists_card_eq
  refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
  rw [hk]
  exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hX)

theorem exists_odd_le_centralizer_of_aSeven (e : Q ≃* A₇) {D : Subgroup Q}
    (hD : IsPGroup 2 D) (h4 : 4 < Nat.card D) {x : Q} (hxD : x ∈ D) (hx1 : x ≠ 1)
    (hxC : D ≤ Subgroup.centralizer ({x} : Set Q)) {Z : Subgroup Q} (hZ : Odd (Nat.card Z))
    (hZD : D ≤ Subgroup.normalizer (Z : Set Q)) :
    ∃ W : Subgroup Q, Odd (Nat.card W) ∧ Z ≤ W ∧
      W ≤ Subgroup.centralizer ({x} : Set Q) ∧
      Subgroup.centralizer ({x} : Set Q) ≤ Subgroup.normalizer (W : Set Q) := by
  obtain ⟨P, hP⟩ := exists_sylow_eq_of_aSeven e hD h4
  subst hP
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_aSeven_map_sylow_eq e P
  have hZU := map_le_a7U_of_sylow_signalizer φ hφ hZD (inf_eq_bot_of_odd_of_isPGroup hZ hD)
  have hmem : ∀ s ∈ a7S, φ x * s = s * φ x := by
    intro s hs
    rw [← hφ] at hs
    obtain ⟨d, hd, rfl⟩ := hs
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hxC hd)
    change φ x * φ d = φ d * φ x
    rw [← map_mul, ← map_mul, h1]
  have hφx : φ x = a7t := by
    have hxS : φ x ∈ a7S := hφ ▸ ⟨x, hxD, rfl⟩
    rcases a7S_center_certificate hxS (hmem _ a7v_mem_a7S) (hmem _ a7s_mem_a7S) with h | h
    · exact absurd (φ.injective (h.trans (map_one φ).symm)) hx1
    · exact h
  have hx : x = φ.symm a7t := by rw [← hφx, MulEquiv.symm_apply_apply]
  refine ⟨a7U.map φ.symm.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective φ.symm.injective,
      aSeven_structure_fact_1_8_ii_centralizer.1]
    decide
  · intro z hz
    exact ⟨φ z, hZU ⟨z, hz, rfl⟩, φ.symm_apply_apply z⟩
  · rintro _ ⟨u, hu, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hx]
    have hc := Subgroup.mem_centralizer_iff.mp (a7U_le_centralizer_a7V hu) a7t a7t_mem_a7V
    change φ.symm u * φ.symm a7t = φ.symm a7t * φ.symm u
    rw [← map_mul, ← map_mul, hc]
  · intro g hg
    have hg' : φ g * a7t = a7t * φ g := by
      rw [← hφx, ← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hg]
    have hN := mem_normalizer_a7U_of_commute hg'
    have h := Subgroup.le_normalizer_map φ.symm.toMonoidHom ⟨φ g, hN, rfl⟩
    rwa [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h

end CFSG.ABGTheoremB.IV9DGroups
