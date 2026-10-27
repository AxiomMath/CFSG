module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WreathK
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WreathLift

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

theorem sq_eq_one_of_wreath {K : Type*} [Group K] [Finite K] {z : K} (hz : z * z = 1)
    {N₁ N₂ : Subgroup (K ⧸ fusionOddCore K)} (e₁ : ↥N₁ ≃* alternatingGroup (Fin 6))
    (e₂ : ↥N₂ ≃* alternatingGroup (Fin 6)) (hc : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a)
    (hd : Disjoint N₁ N₂)
    (hconj : N₁.map (MulAut.conj (QuotientGroup.mk z : K ⧸ fusionOddCore K)).toMonoidHom = N₂)
    {D : Subgroup K} (hD2 : IsPGroup 2 D) (hD8 : Nat.card D = 8) (hDz : ∀ d ∈ D, d * z = z * d)
    (hDN : ∀ d ∈ D, (QuotientGroup.mk d : K ⧸ fusionOddCore K) ∈ N₁ ⊔ N₂)
    {u : K} (hu : ∃ k : ℕ, orderOf u = 2 ^ k)
    (huN : (QuotientGroup.mk u : K ⧸ fusionOddCore K) ∈ N₁ ⊔ N₂)
    (huD : ∀ d ∈ D, u * d = d * u) : u * u = 1 := by
  classical
  set O := fusionOddCore K with hO
  let q : K →* K ⧸ O := QuotientGroup.mk' O
  set σ : K ⧸ O := QuotientGroup.mk z with hσdef
  have hσ2 : σ * σ = 1 := by
    rw [hσdef, ← QuotientGroup.mk_mul, hz, QuotientGroup.mk_one]
  obtain ⟨eDP⟩ := exists_equiv_map_quotient hD2
  set P : Subgroup (K ⧸ O) := D.map q with hP
  have hP8 : Nat.card P = 8 := by
    rw [← hD8]
    exact (Nat.card_congr eDP.toEquiv).symm
  have hPN : P ≤ N₁ ⊔ N₂ := by
    rintro _ ⟨d, hd', rfl⟩
    exact hDN d hd'
  have hPσ : ∀ x ∈ P, σ * x * σ⁻¹ = x := by
    rintro _ ⟨d, hd', rfl⟩
    have h1 : z * d * z⁻¹ = d := by
      rw [← hDz d hd']
      group
    calc σ * q d * σ⁻¹ = q z * q d * (q z)⁻¹ := rfl
      _ = q (z * d * z⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = q d := by rw [h1]
  have huP : ∀ x ∈ P, (QuotientGroup.mk u : K ⧸ O) * x = x * QuotientGroup.mk u := by
    rintro _ ⟨d, hd', rfl⟩
    show q u * q d = q d * q u
    rw [← map_mul, ← map_mul, huD d hd']
  have hsq := wreath_sq_eq_one (Y := K ⧸ O) (N₁ := N₁) (N₂ := N₂) (σ := σ)
    (fun b hb => mem_centralizer_iff.2 fun a ha => hc a ha b hb) hd hσ2 hconj
    (sq_eq_one_of_comm_order_eight_of_le e₁) (sq_eq_one_of_comm_order_eight_of_le e₂) P hP8 hPN
    hPσ huN huP
  have huu : u * u ∈ O := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]
    exact hsq
  apply eq_one_of_mem_fusionOddCore huu
  obtain ⟨k, hk⟩ := hu
  have h1 : orderOf (u * u) ∣ 2 ^ k := by
    rw [← pow_two]
    exact hk ▸ orderOf_pow_dvd 2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  exact ⟨j, hj⟩

end CFSG.EvenSporadicStandard.Fin76b
