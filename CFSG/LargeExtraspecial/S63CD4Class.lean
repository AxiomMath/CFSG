module

public import Certificates.Certificate21111

public section

namespace CFSG.LargeExtraspecial.S63

open Subgroup CFSG.Quasithin

theorem d4Gens_size : d4Gens.size = 8 := rfl

theorem d4ClassFacts :
    (∀ k < 8, d4GenG k * d4GenG k = 1) ∧ Nat.card d4U = 4096 ∧
      Nat.card (centralizer ({d4z} : Set trialityGroup8)) * 819 ≤ Nat.card trialityGroup8 ∧
      Nat.card (centralizer ({d4t} : Set trialityGroup8)) * 68796 ≤ Nat.card trialityGroup8 ∧
      ∀ u ∈ d4U, u * u = 1 → u ≠ 1 → ∃ c, u = c * d4z * c⁻¹ ∨ u = c * d4t * c⁻¹ :=
  Certificates.certificate21111

theorem d4Gens_hyp :
    ∀ k < d4Gens.size, RepE d4E d4Gens[k]! (d4GenG k) ∧ d4GenG k * d4GenG k = 1 :=
  fun _ hk => ⟨repE_d4Gens (d4Gens_size ▸ hk), d4ClassFacts.1 _ (d4Gens_size ▸ hk)⟩

theorem card_d4U : Nat.card d4U = 4096 := d4ClassFacts.2.1

theorem card_centralizer_d4z_le : Nat.card (centralizer ({d4z} : Set trialityGroup8)) ≤ 258048 := by
  have := d4ClassFacts.2.2.1
  rw [card_trialityGroup8] at this
  generalize Nat.card (centralizer ({d4z} : Set trialityGroup8)) = c at this ⊢
  omega

theorem card_centralizer_d4t_le : Nat.card (centralizer ({d4t} : Set trialityGroup8)) ≤ 3072 := by
  have := d4ClassFacts.2.2.2.1
  rw [card_trialityGroup8] at this
  generalize Nat.card (centralizer ({d4t} : Set trialityGroup8)) = c at this ⊢
  omega

theorem conj_of_mem_d4U {u : trialityGroup8} (hu : u ∈ d4U) (huu : u * u = 1) (hu1 : u ≠ 1) :
    ∃ c, u = c * d4z * c⁻¹ ∨ u = c * d4t * c⁻¹ :=
  d4ClassFacts.2.2.2.2 u hu huu hu1

theorem exists_conj_of_orderOf_eq_two {s : trialityGroup8} (hs : orderOf s = 2) :
    ∃ c, s = c * d4z * c⁻¹ ∨ s = c * d4t * c⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite trialityGroup8 := Nat.finite_of_card_ne_zero (by rw [card_trialityGroup8]; norm_num)
  have hU2 : IsPGroup 2 d4U := IsPGroup.of_card (n := 12) (by rw [card_d4U]; norm_num)
  have hindex : ¬ 2 ∣ d4U.index := by
    have h1 := d4U.card_mul_index
    rw [card_d4U, card_trialityGroup8] at h1
    have h2 : d4U.index = 51597 := by omega
    rw [h2]
    decide
  let S : Sylow 2 trialityGroup8 := hU2.toSylow hindex
  have hz2 : IsPGroup 2 (zpowers s) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs]; rfl)
  obtain ⟨P, hP⟩ := hz2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq trialityGroup8 S P
  have hsP : s ∈ (P : Subgroup trialityGroup8) := hP (mem_zpowers s)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hsP
  obtain ⟨u, huS, rfl⟩ := hsP
  have huU : u ∈ d4U := huS
  rw [MulAut.smul_def, MulAut.conj_apply] at hs ⊢
  have huu : u * u = 1 := by
    have h2 := pow_orderOf_eq_one (g * u * g⁻¹)
    rw [hs, pow_two, show g * u * g⁻¹ * (g * u * g⁻¹) = g * (u * u) * g⁻¹ by group] at h2
    simpa using h2
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [mul_one, mul_inv_cancel, orderOf_one] at hs
    exact absurd hs (by norm_num)
  obtain ⟨c, hc | hc⟩ := conj_of_mem_d4U huU huu hu1
  · exact ⟨g * c, Or.inl (by rw [hc]; group)⟩
  · exact ⟨g * c, Or.inr (by rw [hc]; group)⟩

end CFSG.LargeExtraspecial.S63
