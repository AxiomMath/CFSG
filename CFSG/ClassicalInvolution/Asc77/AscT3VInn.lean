module

public import CFSG.ClassicalInvolution.Asc77.AscT3VBase
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscT3SInv

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII.T3V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]

theorem exists_order_four_fixed (hodd : Odd (Nat.card F)) {K : Subgroup G} {z₀ : G}
    (hz : IsUniqueInvolution K z₀) {φ : ↥K →* SL(2, F)} (hφs : Function.Surjective φ)
    (hφk : ∀ x : ↥K, φ x = 1 ↔ x ∈ classicalInvolutionOddCore ↥K) {e : G} (heK : e ∈ K)
    (he2 : e * e = z₀) {z' k : G} (hz'N : z' ∈ Subgroup.normalizer (K : Set G))
    (hz'2 : z' * z' = 1) (hkK : k ∈ K)
    (hk : ∀ g ∈ K, (k * g * k⁻¹)⁻¹ * (z' * g * z'⁻¹) ∈ oddCoreOf K) :
    ∃ u ∈ K, orderOf u = 4 ∧ z' * u * z'⁻¹ = u := by
  have hconj : ∀ g : ↥K, z' * (g : G) * z'⁻¹ ∈ K := fun g =>
    (Subgroup.mem_normalizer_iff.mp hz'N g).mp g.2
  have hφσ : ∀ g : ↥K, φ ⟨z' * (g : G) * z'⁻¹, hconj g⟩ =
      φ ⟨k, hkK⟩ * φ g * (φ ⟨k, hkK⟩)⁻¹ := by
    intro g
    have h1 := hk g g.2
    obtain ⟨hmem, hker⟩ := mem_oddCoreOf_iff.mp h1
    have h2 := (hφk _).mpr hker
    have e1 : (⟨(k * (g : G) * k⁻¹)⁻¹ * (z' * (g : G) * z'⁻¹), hmem⟩ : ↥K) =
        (⟨k, hkK⟩ * g * ⟨k, hkK⟩⁻¹)⁻¹ * ⟨z' * (g : G) * z'⁻¹, hconj g⟩ := rfl
    rw [e1, map_mul, map_inv, map_mul, map_mul, map_inv] at h2
    exact (inv_mul_eq_one.mp h2).symm
  set c : SL(2, F) := φ ⟨k, hkK⟩ with hc
  have hcen : c * c ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro s
    obtain ⟨g, rfl⟩ := hφs s
    have h1 := hφσ ⟨z' * (g : G) * z'⁻¹, hconj g⟩
    have h2 : (⟨z' * (z' * (g : G) * z'⁻¹) * z'⁻¹, hconj ⟨z' * (g : G) * z'⁻¹, hconj g⟩⟩ : ↥K) =
        g := by
      apply Subtype.ext
      show z' * (z' * (g : G) * z'⁻¹) * z'⁻¹ = g
      calc z' * (z' * (g : G) * z'⁻¹) * z'⁻¹ = (z' * z') * (g : G) * (z'⁻¹ * z'⁻¹) := by group
        _ = g := by
          have : z'⁻¹ * z'⁻¹ = 1 := by
            have h3 : z'⁻¹ = z' := inv_eq_of_mul_eq_one_right hz'2
            rw [h3, hz'2]
          rw [hz'2, this]; group
    rw [h2, hφσ g] at h1
    have h3 : φ g = (c * c) * φ g * (c * c)⁻¹ := by
      calc φ g = c * (c * φ g * c⁻¹) * c⁻¹ := h1
        _ = _ := by group
    calc φ g * (c * c) = ((c * c) * φ g * (c * c)⁻¹) * (c * c) := by rw [← h3]
      _ = (c * c) * φ g := by group
  have hsq : c * c = 1 ∨ c * c = -1 := (mem_center_sl2_iff _).mp hcen
  obtain ⟨g₀, hg₀K, hg₀φ, hg₀c⟩ : ∃ g₀ : G, ∃ hg₀ : g₀ ∈ K,
      φ ⟨g₀, hg₀⟩ * φ ⟨g₀, hg₀⟩ = -1 ∧ g₀⁻¹ * (z' * g₀ * z'⁻¹) ∈ oddCoreOf K := by
    rcases hsq with h1 | h1
    ·
      have hcc : c ∈ Subgroup.center SL(2, F) := by
        rw [mem_center_sl2_iff]
        exact T3S.sl2_sq_cases hodd h1
      have hcomm : ∀ x : SL(2, F), c * x * c⁻¹ = x := fun x => by
        have := Subgroup.mem_center_iff.mp hcc x
        calc c * x * c⁻¹ = x * c * c⁻¹ := by rw [this]
          _ = x := by group
      have hφz : φ ⟨z₀, hz.mem⟩ = -1 := T3S.chart_apply_z hodd hz hφk
      refine ⟨e, heK, ?_, ?_⟩
      · rw [← map_mul]
        have : (⟨e, heK⟩ : ↥K) * ⟨e, heK⟩ = ⟨z₀, hz.mem⟩ := Subtype.ext he2
        rw [this, hφz]
      · have hmem : e⁻¹ * (z' * e * z'⁻¹) ∈ K :=
          K.mul_mem (K.inv_mem heK) (hconj ⟨e, heK⟩)
        refine mem_oddCoreOf_iff.mpr ⟨hmem, (hφk _).mp ?_⟩
        have e1 : (⟨e⁻¹ * (z' * e * z'⁻¹), hmem⟩ : ↥K) =
            (⟨e, heK⟩ : ↥K)⁻¹ * ⟨z' * e * z'⁻¹, hconj ⟨e, heK⟩⟩ := rfl
        rw [e1, map_mul, map_inv, hφσ ⟨e, heK⟩, hcomm, inv_mul_cancel]
    · refine ⟨k, hkK, h1, ?_⟩
      have := hk k hkK
      have e1 : k * k * k⁻¹ = k := by group
      rwa [e1] at this
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
  obtain ⟨_, ⟨o, ho, rfl⟩, hfix⟩ := T3V.exists_fixed_conj_of_odd hΨcard hz'2 hstab
  have hg₁K : g₀ * o ∈ K := K.mul_mem hg₀K (oddCoreOf_le_self K ho)
  have hφo : φ ⟨o, oddCoreOf_le_self K ho⟩ = 1 := (hφk _).mpr (mem_oddCoreOf_iff.mp ho).2
  have hφg₁ : φ ⟨g₀ * o, hg₁K⟩ = φ ⟨g₀, hg₀K⟩ := by
    have : (⟨g₀ * o, hg₁K⟩ : ↥K) = ⟨g₀, hg₀K⟩ * ⟨o, oddCoreOf_le_self K ho⟩ := rfl
    rw [this, map_mul, hφo, mul_one]
  have hneg1 : (-1 : SL(2, F)) ≠ 1 := sl2_neg_one_ne_one hodd
  have hord : orderOf (φ ⟨g₀ * o, hg₁K⟩) = 4 := by
    rw [hφg₁]
    have hx2 : φ ⟨g₀, hg₀K⟩ ^ 2 = -1 := by rw [pow_two]; exact hg₀φ
    have h2 : orderOf (φ ⟨g₀, hg₀K⟩) = 2 ^ (1 + 1) := by
      refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
      · rw [pow_one, hx2]
        exact hneg1
      · rw [show (2 : ℕ) ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, hx2]
        simp [pow_two]
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

end CFSG.ClassicalInvolution.Asc77.T3CII.T3V
