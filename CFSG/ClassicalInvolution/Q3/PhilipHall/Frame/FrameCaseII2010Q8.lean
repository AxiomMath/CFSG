module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscSixModCent
public import CFSG.ClassicalInvolution.Asc77.AscT3VBase
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf29Kbar
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open Out
open scoped commutatorElement

private theorem q8_invol : ∀ c : Q8, c * c = 1 → c = 1 ∨ c = QuaternionGroup.a 2 := by
  decide +kernel

private theorem q8_sq :
    ∀ c : Q8, c ≠ 1 → c ≠ QuaternionGroup.a 2 → c * c = QuaternionGroup.a 2 := by
  decide +kernel

private theorem q8_central : ∀ c y : Q8, (c = 1 ∨ c = QuaternionGroup.a 2) → c * y * c⁻¹ = y := by
  decide +kernel

private theorem q8_a2 : QuaternionGroup.a 2 ≠ (1 : Q8) ∧
    QuaternionGroup.a 2 * QuaternionGroup.a 2 = (1 : Q8) := by
  decide +kernel

variable {G : Type} [Group G] [Finite G]

theorem exists_order_four_fixed_q8 {K : Subgroup G} {z₀ : G} (hz : IsUniqueInvolution K z₀)
    (eK : Kbar K ≃* Q8) {e : G} (heK : e ∈ K) (he2 : e * e = z₀)
    {z' k : G} (hz'N : z' ∈ Subgroup.normalizer (K : Set G)) (hz'2 : z' * z' = 1) (hkK : k ∈ K)
    (hk : ∀ g ∈ K, (z' * g * z'⁻¹) * (k * g * k⁻¹)⁻¹ ∈ oddCoreOf K) :
    ∃ u ∈ K, orderOf u = 4 ∧ z' * u * z'⁻¹ = u := by
  set O : Subgroup ↥K := classicalInvolutionOddCore ↥K with hO
  let φ : ↥K →* Q8 := eK.toMonoidHom.comp (QuotientGroup.mk' O)
  have hφk : ∀ x : ↥K, φ x = 1 ↔ x ∈ O := by
    intro x
    constructor
    · intro h
      have h1 : (QuotientGroup.mk' O x : Kbar K) = 1 := by
        apply eK.injective
        rw [map_one]
        exact h
      exact (QuotientGroup.eq_one_iff _).mp h1
    · intro h
      show eK (QuotientGroup.mk' O x) = 1
      have h1 : (QuotientGroup.mk' O x : Kbar K) = 1 := (QuotientGroup.eq_one_iff _).mpr h
      rw [h1, map_one]
  have hconj : ∀ g : ↥K, z' * (g : G) * z'⁻¹ ∈ K := fun g =>
    (Subgroup.mem_normalizer_iff.mp hz'N g).mp g.2
  have hφσ : ∀ g : ↥K, φ ⟨z' * (g : G) * z'⁻¹, hconj g⟩ =
      φ ⟨k, hkK⟩ * φ g * (φ ⟨k, hkK⟩)⁻¹ := by
    intro g
    have h1 := hk g g.2
    obtain ⟨hmem, hker⟩ := mem_oddCoreOf_iff.mp h1
    have h2 := (hφk _).mpr hker
    have e1 : (⟨(z' * (g : G) * z'⁻¹) * (k * (g : G) * k⁻¹)⁻¹, hmem⟩ : ↥K) =
        ⟨z' * (g : G) * z'⁻¹, hconj g⟩ * (⟨k, hkK⟩ * g * ⟨k, hkK⟩⁻¹)⁻¹ := rfl
    rw [e1, map_mul, map_inv, map_mul, map_mul, map_inv] at h2
    exact mul_inv_eq_one.mp h2
  have hz₀O : (⟨z₀, hz.mem⟩ : ↥K) ∉ O := by
    intro h
    have h3 : z₀ ∈ oddCoreOf K := mem_oddCoreOf_iff.mpr ⟨hz.mem, h⟩
    have h4 : orderOf z₀ ∣ Nat.card (oddCoreOf K) := Subgroup.orderOf_dvd_natCard _ h3
    have h5 : orderOf z₀ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
    rw [h5] at h4
    exact (Nat.not_even_iff_odd.mpr ((oddCoreOf_odd_natCard K).of_dvd_nat h4)) even_two
  have hφz : φ ⟨z₀, hz.mem⟩ = QuaternionGroup.a 2 := by
    have h1 : φ ⟨z₀, hz.mem⟩ * φ ⟨z₀, hz.mem⟩ = 1 := by
      rw [← map_mul]
      have : (⟨z₀, hz.mem⟩ : ↥K) * ⟨z₀, hz.mem⟩ = 1 := Subtype.ext hz.sq
      rw [this, map_one]
    rcases q8_invol _ h1 with h | h
    · exact absurd ((hφk _).mp h) hz₀O
    · exact h
  obtain ⟨g₀, hg₀K, hg₀φ, hg₀c⟩ : ∃ g₀ : G, ∃ hg₀ : g₀ ∈ K,
      φ ⟨g₀, hg₀⟩ * φ ⟨g₀, hg₀⟩ = QuaternionGroup.a 2 ∧
        g₀⁻¹ * (z' * g₀ * z'⁻¹) ∈ oddCoreOf K := by
    by_cases hc : φ ⟨k, hkK⟩ = 1 ∨ φ ⟨k, hkK⟩ = QuaternionGroup.a 2
    · refine ⟨e, heK, ?_, ?_⟩
      · rw [← map_mul]
        have : (⟨e, heK⟩ : ↥K) * ⟨e, heK⟩ = ⟨z₀, hz.mem⟩ := Subtype.ext he2
        rw [this, hφz]
      · have hmem : e⁻¹ * (z' * e * z'⁻¹) ∈ K := K.mul_mem (K.inv_mem heK) (hconj ⟨e, heK⟩)
        refine mem_oddCoreOf_iff.mpr ⟨hmem, (hφk _).mp ?_⟩
        have e1 : (⟨e⁻¹ * (z' * e * z'⁻¹), hmem⟩ : ↥K) =
            (⟨e, heK⟩ : ↥K)⁻¹ * ⟨z' * e * z'⁻¹, hconj ⟨e, heK⟩⟩ := rfl
        rw [e1, map_mul, map_inv, hφσ ⟨e, heK⟩, q8_central _ _ hc, inv_mul_cancel]
    · push Not at hc
      refine ⟨k, hkK, q8_sq _ hc.1 hc.2, ?_⟩
      have h1 := hk k hkK
      have e1 : (z' * k * z'⁻¹) * (k * k * k⁻¹)⁻¹ = k * (k⁻¹ * (z' * k * z'⁻¹)) * k⁻¹ := by
        group
      rw [e1] at h1
      have := mem_normalizer_oddCoreOf_of_mem_normalizer
        (Subgroup.inv_mem _ (Subgroup.le_normalizer hkK)) h1
      simpa [mul_assoc] using this
  have hOK : ∀ o ∈ oddCoreOf K, z' * o * z'⁻¹ ∈ oddCoreOf K := fun o ho =>
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_oddCore_of_mem_normalizer hz'N) o).mp ho
  set Ψ : Set G := (fun o : G => g₀ * o) '' (oddCoreOf K : Set G) with hΨ
  have hΨcard : Odd (Nat.card Ψ) := by
    rw [hΨ, Nat.card_image_of_injective (mul_right_injective g₀)]
    exact oddCoreOf_odd_natCard K
  have hstab : ∀ y ∈ Ψ, z' * y * z'⁻¹ ∈ Ψ := by
    rintro _ ⟨o, ho, rfl⟩
    refine ⟨(g₀⁻¹ * (z' * g₀ * z'⁻¹)) * (z' * o * z'⁻¹),
      (oddCoreOf K).mul_mem hg₀c (hOK o ho), ?_⟩
    show g₀ * ((g₀⁻¹ * (z' * g₀ * z'⁻¹)) * (z' * o * z'⁻¹)) = z' * (g₀ * o) * z'⁻¹
    group
  obtain ⟨_, ⟨o, ho, rfl⟩, hfix⟩ := T3CII.T3V.exists_fixed_conj_of_odd hΨcard hz'2 hstab
  have hg₁K : g₀ * o ∈ K := K.mul_mem hg₀K (oddCoreOf_le_self K ho)
  have hφo : φ ⟨o, oddCoreOf_le_self K ho⟩ = 1 := (hφk _).mpr (mem_oddCoreOf_iff.mp ho).2
  have hφg₁ : φ ⟨g₀ * o, hg₁K⟩ = φ ⟨g₀, hg₀K⟩ := by
    have : (⟨g₀ * o, hg₁K⟩ : ↥K) = ⟨g₀, hg₀K⟩ * ⟨o, oddCoreOf_le_self K ho⟩ := rfl
    rw [this, map_mul, hφo, mul_one]
  have hord : orderOf (φ ⟨g₀ * o, hg₁K⟩) = 4 := by
    rw [hφg₁]
    have hx2 : φ ⟨g₀, hg₀K⟩ ^ 2 = QuaternionGroup.a 2 := by rw [pow_two]; exact hg₀φ
    have h2 : orderOf (φ ⟨g₀, hg₀K⟩) = 2 ^ (1 + 1) := by
      refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
      · rw [pow_one, hx2]
        exact q8_a2.1
      · rw [show (2 : ℕ) ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, hx2, pow_two]
        exact q8_a2.2
    simpa using h2
  have hdvd : 4 ∣ orderOf (g₀ * o) := by
    have h1 : orderOf (φ ⟨g₀ * o, hg₁K⟩) ∣ orderOf (⟨g₀ * o, hg₁K⟩ : ↥K) := orderOf_map_dvd φ _
    rw [hord, Subgroup.orderOf_mk] at h1
    exact h1
  obtain ⟨n, hn⟩ := hdvd
  have hpos : 0 < orderOf (g₀ * o) := orderOf_pos _
  have hn0 : n ≠ 0 := by
    rintro rfl
    omega
  refine ⟨(g₀ * o) ^ n, K.pow_mem hg₁K n, ?_, ?_⟩
  · have h3 : n ∣ orderOf (g₀ * o) := ⟨4, by rw [hn]; ring⟩
    rw [orderOf_pow_of_dvd hn0 h3, hn]
    have : 4 * n / n = 4 := by
      rw [Nat.mul_div_assoc _ (dvd_refl n), Nat.div_self (Nat.pos_of_ne_zero hn0), mul_one]
    exact this
  · calc z' * (g₀ * o) ^ n * z'⁻¹ = (z' * (g₀ * o) * z'⁻¹) ^ n := conj_pow.symm
      _ = (g₀ * o) ^ n := by rw [hfix]

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
