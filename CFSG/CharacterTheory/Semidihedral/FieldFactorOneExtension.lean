module

public import CFSG.CharacterTheory.Semidihedral.FieldFactorOneFamily
public import CFSG.CharacterTheory.Wreathed.BrauerWreathedOrderDegree

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.FieldFactorOne

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.TwoRankLowerBound.Helpers

theorem linear_character_eq_one_of_two_element {X : Type} [Group X] [Finite X]
    (hindex : ∀ V : Subgroup X, V.index ≠ 2) (lam : X →* ℂˣ) {a : X} {k : ℕ}
    (ha : orderOf a ∣ 2 ^ k) : lam a = 1 := by
  have hodd : Odd (Nat.card lam.range) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨H, -, hH⟩ := CFSG.Wreathed.BrauerWreathedOrder.exists_normal_index_two_of_even lam hev
    exact hindex H hH
  have h1 : orderOf (lam a) ∣ 2 ^ k := (orderOf_map_dvd lam a).trans ha
  have h2 : orderOf (lam a) ∣ Nat.card lam.range := by
    rw [← Subgroup.orderOf_mk (lam a) (MonoidHom.mem_range.mpr ⟨a, rfl⟩)]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (orderOf (lam a)) (Nat.card lam.range) :=
    Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd))
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop h2)

theorem mem_centralizer_zpowers_of_mem_C {G : Type} [Group G] {t y : G} (hy : y ∈ C t) :
    y ∈ Subgroup.centralizer (Subgroup.zpowers t : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hyt : Commute y t := Subgroup.mem_centralizer_singleton_iff.mp hy
  exact (hyt.zpow_right k).symm.eq

theorem extends_of_degree_one {G : Type} [Group G] [Fintype G] {n : ℕ} {S : Sylow 2 G}
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) {t : G} (hn : 4 ≤ n)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) (hindex : ∀ V : Subgroup G, V.index ≠ 2)
    (θ : C t →* ℂˣ) (hθS : ∀ c : C t, (c : G) ∈ (S : Subgroup G) → θ c = 1)
    (basis : FiniteIrreducibleCharacterBasis G) (χ₀ : basis.index)
    (hdeg : Module.finrank ℂ (basis.representation χ₀).vector = 1)
    (hval : ∀ y : Subgroup.centralizer (Subgroup.zpowers t : Set G), Odd (orderOf y) →
      (basis.representation χ₀).character (t * y) = thetaG t θ (y : G)) :
    ∃ lam : G →* ℂˣ, ∀ c : C t, lam c = θ c := by
  set lam := CFSG.Wreathed.BrauerWreathedOrder.linearCharacterHom (basis.representation χ₀) hdeg
    with hlam
  have hlamval : ∀ g, (lam g : ℂ) = (basis.representation χ₀).character g := fun g =>
    CFSG.Wreathed.BrauerWreathedOrder.linearCharacterHom_apply _ hdeg g
  refine ⟨lam, fun c => ?_⟩
  obtain ⟨a, y, k, ha, hy, hay, hayc, hak, hy2⟩ :=
    finite_prime_primary_factorization (c : G) 2 Nat.prime_two
  have hzc : Subgroup.zpowers (c : G) ≤ C t := (Subgroup.zpowers_le (H := C t)).mpr c.2
  have haC : a ∈ C t := hzc ha
  have hyC : y ∈ C t := hzc hy
  have hyodd : Odd (orderOf y) := Nat.coprime_two_left.mp hy2
  have ht2 : orderOf t ∣ 2 ^ 1 := by rw [orderOf_t fS hn ht, pow_one]
  have hy' : (lam y : ℂ) = ((θ ⟨y, hyC⟩ : ℂˣ) : ℂ) := by
    have h := hval ⟨y, mem_centralizer_zpowers_of_mem_C hyC⟩ (by
      rw [Subgroup.orderOf_mk]
      exact hyodd)
    rw [← hlamval, map_mul, Units.val_mul, linear_character_eq_one_of_two_element hindex lam ht2,
      Units.val_one, one_mul, hlamval, thetaG_of_mem θ hyC] at h
    rw [hlamval]
    exact h
  have ha2 : IsPGroup 2 (Subgroup.zpowers a) := by
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hak
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  have hθa : θ ⟨a, haC⟩ = 1 := by
    have h := thetaG_eq_one_of_isPGroup fS hn ht θ hθS haC ha2
    rwa [thetaG_of_mem θ haC] at h
  have hc : c = ⟨a, haC⟩ * ⟨y, hyC⟩ := Subtype.ext hayc.symm
  have hlamc : (lam (c : G) : ℂ) = (lam y : ℂ) := by
    rw [← hayc, map_mul, Units.val_mul, linear_character_eq_one_of_two_element hindex lam hak,
      Units.val_one, one_mul]
  have hθc : ((θ c : ℂˣ) : ℂ) = ((θ ⟨y, hyC⟩ : ℂˣ) : ℂ) := by
    rw [hc, map_mul, Units.val_mul, hθa, Units.val_one, one_mul]
  exact Units.ext (hlamc.trans (hy'.trans hθc.symm))

theorem cubic_moment_formula {q e a₀ a₁ a₂ a₃ : ℂ} (he : e = 1 ∨ e = -1) (hq1 : q ^ 2 ≠ 1)
    (hqe : q + e ≠ 0) (ha₀ : a₀ ≠ 0) (ha₁ : a₁ ≠ 0) (h01 : a₀ + a₁ ≠ 0)
    (hsum : a₀ + a₁ + a₂ + a₃ = 0) (hconic : a₁ * a₂ = q ^ 2 * a₀ * a₃) :
    1 / a₀ + e * q ^ 3 / a₁ - e * q ^ 3 / a₂ - 1 / a₃ - (1 - e * q) ^ 3 / (a₀ + a₂) -
        (1 + e * q) ^ 3 / (a₀ + a₁) =
      4 * q / (q + e) * ((a₁ - e * q * a₀) ^ 2 / (a₀ * a₁ * (a₀ + a₁))) := by
  have h3 : a₃ * (a₁ + q ^ 2 * a₀) = -(a₁ * (a₀ + a₁)) := by
    linear_combination (-1) * hconic + a₁ * hsum
  have h2 : a₂ * (a₁ + q ^ 2 * a₀) = -(q ^ 2 * a₀ * (a₀ + a₁)) := by
    linear_combination hconic + q ^ 2 * a₀ * hsum
  have hlc : a₁ + q ^ 2 * a₀ ≠ 0 := by
    intro h
    rw [h, mul_zero] at h3
    exact mul_ne_zero ha₁ h01 (neg_eq_zero.mp h3.symm)
  have h02' : (a₀ + a₂) * (a₁ + q ^ 2 * a₀) = a₀ * a₁ * (1 - q ^ 2) := by
    linear_combination h2
  have hq1' : (1 : ℂ) - q ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
  have r2 : e * q ^ 3 / a₂ = e * q ^ 3 * (a₁ + q ^ 2 * a₀) / (-(q ^ 2 * a₀ * (a₀ + a₁))) := by
    rw [← h2, mul_div_mul_right _ _ hlc]
  have r3 : 1 / a₃ = (a₁ + q ^ 2 * a₀) / (-(a₁ * (a₀ + a₁))) := by
    rw [← h3, div_mul_cancel_right₀ hlc, one_div]
  have r02 : (1 - e * q) ^ 3 / (a₀ + a₂) =
      (1 - e * q) ^ 3 * (a₁ + q ^ 2 * a₀) / (a₀ * a₁ * (1 - q ^ 2)) := by
    rw [← h02', mul_div_mul_right _ _ hlc]
  rw [r2, r3, r02]
  rcases he with rfl | rfl
  · field_simp
    ring
  · have hqe' : q - 1 ≠ 0 := by
      intro h
      apply hqe
      linear_combination h
    field_simp
    ring

end CFSG.Semidihedral.FieldFactorOne
