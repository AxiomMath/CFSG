module

public import CFSG.Open.Defs

public section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

theorem exists_conj_le_of_not_dvd_index {G : Type*} [Group G] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] (H : Subgroup G) (hH : ¬ p ∣ H.index) {P : Subgroup G}
    (hP : IsPGroup p P) : ∃ g : G, ∀ x ∈ P, g⁻¹ * x * g ∈ H := by
  classical
  obtain ⟨S⟩ : Nonempty (Sylow p H) := inferInstance
  set T : Subgroup G := S.toSubgroup.map H.subtype with hTdef
  have hTH : T ≤ H := by
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  have hTp : IsPGroup p T := S.isPGroup'.map H.subtype
  have hTc : Nat.card T = Nat.card S := Subgroup.card_map_of_injective Subtype.val_injective
  have hGpos : 0 < Nat.card G := Nat.card_pos
  have hIne : H.index ≠ 0 := by
    intro h
    have h1 := Subgroup.card_mul_index H
    rw [h, mul_zero] at h1
    exact hGpos.ne' h1.symm
  have hHne : Nat.card H ≠ 0 := (Nat.card_pos).ne'
  have hfac : (Nat.card G).factorization p = (Nat.card H).factorization p := by
    rw [← Subgroup.card_mul_index H, Nat.factorization_mul hHne hIne, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hH, add_zero]
  obtain ⟨Q₀, hTQ₀⟩ := hTp.exists_le_sylow
  have hQ₀c : Nat.card Q₀ = Nat.card T := by
    rw [Sylow.card_eq_multiplicity, hTc, Sylow.card_eq_multiplicity, hfac]
  have hTQ : T = (Q₀ : Subgroup G) := Subgroup.eq_of_le_of_card_ge hTQ₀ hQ₀c.le
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q₀ Q
  refine ⟨g, fun x hx => ?_⟩
  have hxQ : x ∈ (Q : Subgroup G) := hPQ hx
  rw [← hg, Sylow.coe_subgroup_smul] at hxQ
  obtain ⟨t, ht, hte⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hxQ
  have htT : t ∈ T := by
    rw [hTQ]
    exact ht
  have hconj : g⁻¹ * x * g = t := by
    rw [← hte]
    simp [MulAut.smul_def, mul_assoc]
  rw [hconj]
  exact hTH htT

theorem ordE6_eq_ordF4_mul_of_mod_two {q : ℕ} (hq : q % 3 = 2) :
    CFSG.Open.ordE6 q = CFSG.Open.ordF4 q * (q ^ 12 * (q ^ 9 - 1) * (q ^ 5 - 1)) := by
  have hg : Nat.gcd 3 (q - 1) = 1 := by
    have h3 : ¬ 3 ∣ q - 1 := by omega
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
  unfold CFSG.Open.ordE6 CFSG.Open.ordF4
  rw [hg, Nat.div_one]
  ring

theorem not_dvd_three_mod_two {q : ℕ} (hq : q % 3 = 2) :
    ¬ 3 ∣ q ^ 12 * (q ^ 9 - 1) * (q ^ 5 - 1) := by
  have h9 : q ^ 9 % 3 = 2 := by
    rw [Nat.pow_mod, hq]
  have h5 : q ^ 5 % 3 = 2 := by
    rw [Nat.pow_mod, hq]
  have h12 : ¬ 3 ∣ q ^ 12 := fun h => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have h9' : ¬ 3 ∣ q ^ 9 - 1 := by omega
  have h5' : ¬ 3 ∣ q ^ 5 - 1 := by omega
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · exact h12 h
    · exact h9' h
  · exact h5' h

end CFSG.LieType.SeitzGeneration.ExcHighThree

end
