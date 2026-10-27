module

public import CFSG.CGT.Timmesfeld75.Sec3Iso

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem IsWC.conj_eq_conj_of_mem (hT : IsWC T) {a b u : G} (hu1 : u ≠ 1)
    (hua : u ∈ conjSubgroup a T) (hub : u ∈ conjSubgroup b T) :
    conjSubgroup a T = conjSubgroup b T := by
  have h1 : a⁻¹ * u * a ∈ T := mem_conjSubgroup.1 hua
  have h2 : a⁻¹ * u * a ∈ conjSubgroup (a⁻¹ * b) T := by
    rw [mem_conjSubgroup]
    have := mem_conjSubgroup.1 hub
    simpa [mul_assoc] using this
  have hne1 : a⁻¹ * u * a ≠ 1 := by
    intro h
    apply hu1
    have e : u = a * (a⁻¹ * u * a) * a⁻¹ := by group
    rw [e, h]
    group
  have hne : T ⊓ conjSubgroup (a⁻¹ * b) T ≠ ⊥ := fun h => hne1 (by
    have : a⁻¹ * u * a ∈ T ⊓ conjSubgroup (a⁻¹ * b) T := ⟨h1, h2⟩
    rw [h, Subgroup.mem_bot] at this
    exact this)
  have h3 := hT.conj_eq_of_inf_ne_bot hne
  calc conjSubgroup a T = conjSubgroup a (conjSubgroup (a⁻¹ * b) T) := by rw [h3]
    _ = conjSubgroup b T := by
      rw [conjSubgroup_conjSubgroup]
      congr 1
      group

theorem card_ge_two_mul_of_lt [Finite G] {H K : Subgroup G} (hHK : H ≤ K) {u : G} (huK : u ∈ K)
    (huH : u ∉ H) : 2 * Nat.card H ≤ Nat.card K := by
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hHK
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hHpos : 0 < Nat.card H := Nat.card_pos
  have hc0 : c ≠ 0 := by
    rintro rfl
    omega
  by_cases hc1 : c = 1
  · exfalso
    subst hc1
    have := Subgroup.eq_of_le_of_card_ge hHK (by omega)
    exact huH (this ▸ huK)
  · have : 2 ≤ c := by omega
    calc 2 * Nat.card H ≤ c * Nat.card H := Nat.mul_le_mul_right _ this
      _ = Nat.card K := by rw [hc]; ring

theorem Sec3.exists_fixed_conj_eight [Finite G] (hS : Sec3 T T₁) (hI : Sec3Iso T T₁) {y : G}
    (hyy : y * y = 1) (hy : conjSubgroup y T = T₁)
    (h16 : Nat.card T = 16) (h8 : Nat.card (normIn T T₁) = 8) :
    ∃ g ∈ T ⊔ T₁, conjSubgroup y (conjSubgroup g T) = conjSubgroup g T ∧
      ∃ u ∈ conjSubgroup g T, u ∉ cfgM T T₁ ∧ y * u = u * y := by
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hyT₁ : conjSubgroup y T₁ = T := by
    rw [← hy, conjSubgroup_conjSubgroup, hyy, conjSubgroup_one]
  have hyM : conjSubgroup y (cfgM T T₁) = cfgM T T₁ := by
    rw [← cfgM_conj, hy, hyT₁, cfgM_symm]
  have hM2 : IsPGroup 2 (cfgM T T₁) := isPGroup_two_of_isElemAbelian hS.cfg.isElemAbelian_cfgM
  obtain ⟨z, hzT, hzM⟩ : ∃ z ∈ T, z ∉ cfgM T T₁ := by
    by_contra hcon
    push Not at hcon
    have hle : T ≤ cfgM T T₁ := hcon
    have h1 : T ⊓ cfgM T T₁ = T := inf_eq_left.2 hle
    rw [hS.cfg.inf_cfgM] at h1
    have h2 : Nat.card ↥(normIn T T₁) = Nat.card ↥T := by rw [h1]
    omega
  have hzz : z * z = 1 := elemAbelian_mul_self hS.cfg.wc.1 hzT
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  obtain ⟨z', hz'def⟩ : ∃ z' : G, z' = y * z * y⁻¹ := ⟨_, rfl⟩
  have hz'T₁ : z' ∈ T₁ := by
    rw [hz'def, ← hy]
    exact conj_mem_conjSubgroup y hzT
  have hz'z' : z' * z' = 1 := by
    rw [hz'def]
    calc y * z * y⁻¹ * (y * z * y⁻¹) = y * (z * z) * y⁻¹ := by group
      _ = 1 := by rw [hzz]; group
  have hz'i : z'⁻¹ = z' := inv_eq_of_mul_eq_one_right hz'z'
  have hz'M : z' ∉ cfgM T T₁ := by
    intro h
    apply hzM
    have h1 := mem_conjSubgroup.1 (show z' ∈ conjSubgroup y (cfgM T T₁) by rw [hyM]; exact h)
    have e : y⁻¹ * z' * y = z := by rw [hz'def]; group
    rwa [e] at h1
  have hzL : z ∉ normIn T T₁ := fun h => hzM (Cfg.normIn_le_cfgM_left T T₁ h)
  have hz'L : z' ∉ normIn T₁ T := fun h => hz'M (Cfg.normIn_le_cfgM_right T T₁ h)
  have hodd : Odd (orderOf (z * z')) := hS.cfg.odd_orderOf_mul_gen hS.conj hzT hzL hz'T₁ hz'L
  obtain ⟨hN, f, hf, hiso⟩ := hI
  have := hN
  have hpair := hS.isL2Pair_quotient hf hiso
  have hcardT := hS.card_eq_mul hf hiso
  have h2f : 2 ^ f = 2 := by
    rw [h16, h8] at hcardT
    omega
  have hXQ : Nat.card (↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)) = 6 := by
    rw [hpair.card_eq_mul, h2f]
    norm_num
  have hwX : z * z' ∈ T ⊔ T₁ :=
    (T ⊔ T₁).mul_mem (Subgroup.mem_sup_left hzT) (Subgroup.mem_sup_right hz'T₁)
  have hord1 : Odd (orderOf (⟨z * z', hwX⟩ : ↥(T ⊔ T₁))) := by
    rw [← Subgroup.orderOf_coe]
    exact hodd
  have hord2 := Odd.of_dvd_nat hord1
    (orderOf_map_dvd (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))) ⟨z * z', hwX⟩)
  have hord3 : orderOf ((QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))
      (⟨z * z', hwX⟩ : ↥(T ⊔ T₁))) ∣ 3 := by
    have h6 : orderOf ((QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))
        (⟨z * z', hwX⟩ : ↥(T ⊔ T₁))) ∣ 2 * 3 := by
      have := orderOf_dvd_natCard ((QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))
        (⟨z * z', hwX⟩ : ↥(T ⊔ T₁)))
      rwa [hXQ] at this
    have hcop : Nat.Coprime (orderOf ((QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))
        (⟨z * z', hwX⟩ : ↥(T ⊔ T₁)))) 2 := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
      intro h2
      exact (Nat.not_even_iff_odd.2 hord2) (even_iff_two_dvd.2 h2)
    exact hcop.dvd_of_dvd_mul_left h6
  have hpow := orderOf_dvd_iff_pow_eq_one.1 hord3
  have hw3M : (z * z') ^ 3 ∈ cfgM T T₁ := by
    have h1 : (⟨z * z', hwX⟩ : ↥(T ⊔ T₁)) ^ 3 ∈ (cfgM T T₁).subgroupOf (T ⊔ T₁) := by
      rw [← QuotientGroup.eq_one_iff]
      have h2 : (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))
          ((⟨z * z', hwX⟩ : ↥(T ⊔ T₁)) ^ 3) = 1 := by
        rw [map_pow]
        exact hpow
      exact h2
    exact Subgroup.mem_subgroupOf.1 h1
  have hw3 : (z * z') ^ 3 = 1 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hM2 ⟨(z * z') ^ 3, hw3M⟩
    have hk' : orderOf ((z * z') ^ 3) = 2 ^ k := by
      rw [← Subgroup.orderOf_coe] at hk
      exact hk
    have hodd3 : Odd (orderOf ((z * z') ^ 3)) := Odd.of_dvd_nat hodd (orderOf_pow_dvd 3)
    rw [hk'] at hodd3
    have hk0 : k = 0 := by
      by_contra hk0
      exact (Nat.not_even_iff_odd.2 hodd3) (by rw [Nat.even_pow]; exact ⟨even_two, hk0⟩)
    rw [hk0, pow_zero] at hk'
    exact orderOf_eq_one_iff.1 hk'
  have hbraid : z * z' * z = z' * z * z' := by
    have h1 : (z * z' * z) * (z' * z * z') = 1 := by
      have : (z * z') ^ 3 = (z * z' * z) * (z' * z * z') := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      rw [← this]
      exact hw3
    have h2 := eq_inv_of_mul_eq_one_left h1
    rw [h2, mul_inv_rev, mul_inv_rev, hz'i, hzi]
    group
  have hz'X : z' ∈ T ⊔ T₁ := Subgroup.mem_sup_right hz'T₁
  have hu1 : z' * z * z'⁻¹ ≠ 1 := by
    intro h
    apply hzM
    have e : z = z'⁻¹ * (z' * z * z'⁻¹) * z' := by group
    rw [e, h]
    simp only [mul_one, inv_mul_cancel]
    exact (cfgM T T₁).one_mem
  have huU : z' * z * z'⁻¹ ∈ conjSubgroup z' T := conj_mem_conjSubgroup z' hzT
  have huT₁ : z' * z * z'⁻¹ ∈ conjSubgroup z T₁ := by
    have e : z' * z * z'⁻¹ = z * z' * z⁻¹ := by
      rw [hz'i, hzi]
      exact hbraid.symm
    rw [e]
    exact conj_mem_conjSubgroup z hz'T₁
  have huT : z' * z * z'⁻¹ ∈ conjSubgroup (z * y) T := by
    rw [← conjSubgroup_conjSubgroup, hy]
    exact huT₁
  have hUeq : conjSubgroup (z * y) T = conjSubgroup z' T :=
    hS.cfg.wc.conj_eq_conj_of_mem hu1 huT huU
  have hyz' : y * z' * y⁻¹ = z := by
    rw [hz'def]
    calc y * (y * z * y⁻¹) * y⁻¹ = (y * y) * z * (y⁻¹ * y⁻¹) := by group
      _ = z := by rw [hyi, hyy]; group
  refine ⟨z', hz'X, ?_, z' * z * z'⁻¹, huU, ?_, ?_⟩
  ·
    rw [conjSubgroup_conjSubgroup]
    have e : y * z' = z * y := by
      rw [hz'def, hyi]
      calc y * (y * z * y) = (y * y) * z * y := by group
        _ = z * y := by rw [hyy, one_mul]
    rw [e]
    exact hUeq
  ·
    intro hM
    apply hzM
    have h1 := hS.cfg.conj_mem_cfgM ((T ⊔ T₁).inv_mem hz'X) hM
    have e : z'⁻¹ * (z' * z * z'⁻¹) * z'⁻¹⁻¹ = z := by group
    rwa [e] at h1
  ·
    have e1 : y * (z' * z * z'⁻¹) * y⁻¹ = (y * z' * y⁻¹) * (y * z * y⁻¹) * (y * z'⁻¹ * y⁻¹) := by
      group
    have e2 : y * z'⁻¹ * y⁻¹ = z := by rw [hz'i]; exact hyz'
    have e3 : y * (z' * z * z'⁻¹) * y⁻¹ = z' * z * z'⁻¹ := by
      rw [e1, hyz', ← hz'def, e2, hz'i]
      exact hbraid
    calc y * (z' * z * z'⁻¹) = (y * (z' * z * z'⁻¹) * y⁻¹) * y := by group
      _ = (z' * z * z'⁻¹) * y := by rw [e3]

end CFSG.CGT.Timmesfeld75
