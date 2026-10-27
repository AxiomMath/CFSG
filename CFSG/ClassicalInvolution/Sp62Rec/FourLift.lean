module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open Subgroup
open scoped Pointwise

theorem natCard_comap_mk {H : Type*} [Group H] [Finite H] (Q : Subgroup H) [Q.Normal]
    (S : Subgroup (H ⧸ Q)) :
    Nat.card (S.comap (QuotientGroup.mk' Q)) = Nat.card S * Nat.card Q := by
  have hidx : (S.comap (QuotientGroup.mk' Q)).index = S.index :=
    S.index_comap_of_surjective (QuotientGroup.mk'_surjective Q)
  have hpos : 0 < S.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc Nat.card (S.comap (QuotientGroup.mk' Q)) * S.index
      = Nat.card H := by rw [← hidx]; exact Subgroup.card_mul_index _
    _ = Nat.card (H ⧸ Q) * Nat.card Q := Subgroup.card_eq_card_quotient_mul_card_subgroup Q
    _ = (Nat.card S * S.index) * Nat.card Q := by rw [Subgroup.card_mul_index S]
    _ = Nat.card S * Nat.card Q * S.index := by ring

theorem exists_four_isConj_of_quotient {H : Type*} [Group H] [Finite H] (Q : Subgroup H) [Q.Normal]
    (hQ : Odd (Nat.card Q)) {z : H} (hz : z * z = 1) (D : Subgroup (H ⧸ Q)) (hD4 : Nat.card D = 4)
    (hD2 : ∀ d ∈ D, d * d = 1) (hDz : ∀ d ∈ D, d ≠ 1 → IsConj d (z : H ⧸ Q)) :
    ∃ D₀ : Subgroup H, Nat.card D₀ = 4 ∧ (∀ d ∈ D₀, d * d = 1) ∧
      ∀ d ∈ D₀, d ≠ 1 → IsConj d z := by
  set π : H →* H ⧸ Q := QuotientGroup.mk' Q
  have hDt : 2 ^ 2 ∣ Nat.card (D.comap π) := by
    rw [natCard_comap_mk, hD4]
    exact dvd_mul_right _ _
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := D.comap π) 2 hDt
  obtain ⟨D₀, hD₀card, hD₀le⟩ : ∃ D₀ : Subgroup H, Nat.card D₀ = 4 ∧ D₀ ≤ D.comap π :=
    ⟨K.map (D.comap π).subtype, by
      rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hK]
      norm_num, Subgroup.map_subtype_le K⟩
  have hD₀inj : ∀ x ∈ D₀, π x = 1 → x = 1 := by
    intro x hx hπx
    have hxQ : x ∈ Q := (QuotientGroup.eq_one_iff x).1 hπx
    have h4 : x ^ 4 = 1 := by
      have h := pow_card_eq_one' (G := D₀) (x := (⟨x, hx⟩ : D₀))
      rw [hD₀card] at h
      exact congrArg Subtype.val h
    have hq : x ^ Nat.card Q = 1 := by
      have h := pow_card_eq_one' (G := Q) (x := (⟨x, hxQ⟩ : Q))
      exact congrArg Subtype.val h
    have hgcd : Nat.gcd 4 (Nat.card Q) = 1 := by
      have h := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hQ)
      simpa using h
    have h := pow_gcd_eq_one.2 ⟨h4, hq⟩
    rwa [hgcd, pow_one] at h
  have hsq : ∀ d ∈ D₀, d * d = 1 := by
    intro d hd
    refine hD₀inj (d * d) (D₀.mul_mem hd hd) ?_
    rw [map_mul]
    exact hD2 _ (hD₀le hd)
  refine ⟨D₀, hD₀card, hsq, ?_⟩
  intro d hd hd1
  have hπd : π d ∈ D := hD₀le hd
  have hπd1 : π d ≠ 1 := fun h => hd1 (hD₀inj d hd h)
  obtain ⟨cq, hcq⟩ := isConj_iff.1 (hDz (π d) hπd hπd1)
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective cq
  obtain ⟨z', hz'def⟩ : ∃ z' : H, z' = c⁻¹ * z * c := ⟨_, rfl⟩
  have hπz' : π z' = π d := by
    have h : π z = π c * π d * (π c)⁻¹ := hcq.symm
    calc π z' = (π c)⁻¹ * π z * π c := by rw [hz'def]; simp
      _ = (π c)⁻¹ * (π c * π d * (π c)⁻¹) * π c := by rw [h]
      _ = π d := by group
  have hz'sq : z' * z' = 1 := by
    calc z' * z' = c⁻¹ * (z * z) * c := by rw [hz'def]; group
      _ = 1 := by rw [hz]; group
  have hz'1 : z' ≠ 1 := fun h => hπd1 (by rw [← hπz', h, map_one])
  have hπd_sq : π d ^ 2 = 1 := by rw [pow_two, ← map_mul, hsq d hd, map_one]
  have hord : orderOf (π d) = 2 := orderOf_eq_prime hπd_sq hπd1
  set M : Subgroup H := (zpowers (π d)).comap π with hM
  have hMcard : Nat.card M = 2 * Nat.card Q := by
    rw [hM, natCard_comap_mk, Nat.card_zpowers, hord]
  have hdM : d ∈ M := by rw [hM, mem_comap]; exact mem_zpowers _
  have hz'M : z' ∈ M := by rw [hM, mem_comap, hπz']; exact mem_zpowers _
  have hfac : (Nat.card M).factorization 2 = 1 := by
    rw [hMcard, Nat.factorization_mul (by norm_num) (Nat.card_pos (α := Q)).ne', Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd hQ.not_two_dvd_nat]
  have hcardP : ∀ y ∈ M, y * y = 1 → y ≠ 1 → Nat.card ((zpowers y).subgroupOf M) = 2 ^
      (Nat.card M).factorization 2 := by
    intro y hy hy2 hy1
    have hle : zpowers y ≤ M := zpowers_le.2 hy
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, Nat.card_zpowers, hfac,
      pow_one]
    exact orderOf_eq_prime (by rwa [pow_two]) hy1
  let Sd : Sylow 2 M := Sylow.ofCard ((zpowers d).subgroupOf M) (hcardP d hdM (hsq d hd) hd1)
  let Sz : Sylow 2 M := Sylow.ofCard ((zpowers z').subgroupOf M) (hcardP z' hz'M hz'sq hz'1)
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M Sz Sd
  have hconj : (m : H) * z' * (m : H)⁻¹ ∈ zpowers d := by
    have h1 : (⟨z', hz'M⟩ : M) ∈ (Sz : Subgroup M) := by
      rw [Sylow.coe_ofCard]
      exact mem_subgroupOf.2 (mem_zpowers z')
    have h2 := Subgroup.smul_mem_pointwise_smul _ (MulAut.conj m) _ h1
    have h3 : MulAut.conj m • (Sz : Subgroup M) = (Sd : Subgroup M) := by
      rw [← hm]
      exact (Sylow.coe_subgroup_smul (g := m) (P := Sz)).symm
    rw [h3, Sylow.coe_ofCard] at h2
    exact mem_subgroupOf.1 h2
  have hdord : orderOf d = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq d hd) hd1
  have hzp : ∀ y ∈ zpowers d, y = 1 ∨ y = d := by
    intro y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    rw [← zpow_mod_orderOf, hdord]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [Nat.cast_ofNat, h, zpow_zero]
    · right
      rw [Nat.cast_ofNat, h, zpow_one]
  have hd_eq : (m : H) * z' * (m : H)⁻¹ = d := by
    rcases hzp _ hconj with h | h
    · exfalso
      apply hz'1
      calc z' = (m : H)⁻¹ * ((m : H) * z' * (m : H)⁻¹) * (m : H) := by group
        _ = 1 := by rw [h]; group
    · exact h
  refine isConj_iff.2 ⟨c * (m : H)⁻¹, ?_⟩
  rw [← hd_eq, hz'def]
  group

end CFSG.ClassicalInvolution.Sp62Rec
