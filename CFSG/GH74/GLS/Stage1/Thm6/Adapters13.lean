module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.ExtB
public import CFSG.GH74.GLS.Bg.Local.Transfer1515

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup

theorem exists_zpow_of_mem_sup {X : Type*} [Group X] {P Q : Subgroup X} {g : X}
    (hQn : ∀ t ∈ P, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q) (hg : g ∈ P) {t : X}
    (ht : t ∈ Q ⊔ zpowers g) : ∃ k : ℤ, (g ^ k)⁻¹ * t ∈ Q := by
  have hnorm : g ∈ normalizer (Q : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact fun hh => hQn g hg h hh
    · intro hh
      have := hQn g⁻¹ (P.inv_mem hg) _ hh
      simpa [mul_assoc] using this
  have hz : zpowers g ≤ normalizer (Q : Set X) := by
    rw [Subgroup.zpowers_le]; exact hnorm
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (zpowers g) Q hz
  rw [sup_comm] at ht
  have ht' : t ∈ (↑(zpowers g ⊔ Q) : Set X) := ht
  rw [hset] at ht'
  obtain ⟨a, ha, q, hq, rfl⟩ := Set.mem_mul.1 ht'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  exact ⟨k, by simpa using hq⟩

theorem ig_15_15_sec13 : IG_15_15 := by
  intro X _ _ P Q u hP hQP hQn hQne hcyc huP huQ hu2 hext
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨_, hP2, hPidx⟩ := hP
  have hPidx' : ¬ 2 ∣ P.index := by simpa [Subgroup.relIndex_top_right] using hPidx
  have hcyc' : ∃ b ∈ P, ∀ t ∈ P, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ Q := by
    obtain ⟨g, hg, hPg⟩ := hcyc
    refine ⟨g, hg, fun t ht => ?_⟩
    rw [hPg] at ht
    exact exists_zpow_of_mem_sup hQn hg ht
  have key := CFSG.GH74.GLS.Bg.Thompson.thompson_transfer_1515 (p := 2) hP2 hPidx' hQn hcyc'
    huP huQ
    (fun g k _ => by
      rw [pow_mul, pow_two, hu2, one_pow, mul_one, inv_mul_cancel]
      exact one_mem _)
    (fun g hgP hex => by
      have h1 := hext g⁻¹ (by rw [inv_inv]; exact ⟨hgP, hex⟩)
      simp only [inv_inv] at h1
      rcases h1 with h1 | ⟨q, hq, hqe⟩
      · exact Or.inl h1
      · refine Or.inr ?_
        rw [hqe]
        have := hQn u⁻¹ (P.inv_mem huP) q hq
        simpa [mul_assoc] using this)
  rcases key with h1 | ⟨g, hg1, hg2, hg3⟩
  · exact Or.inl h1
  · refine Or.inr ⟨g⁻¹, by simpa using hg1, by rw [inv_inv]; exact ⟨hQP hg1, hg2⟩, fun c hc => ?_⟩
    simpa using hg3 c hc

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
