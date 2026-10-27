module

public import CFSG.Holt.CaseTwoBW

public section

namespace CFSG.Holt.H78

open Subgroup MulAction CFSG.Holt
open scoped commutatorElement

section Lemma14

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

theorem odd_card_pPrimeCore_two [Finite G] : Odd (Nat.card (CFSG.pPrimeCore 2 G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Nat.coprime_two_left.1 CFSG.pPrimeCore_coprime_card

theorem odd_card_of_isPretransitive_pPrimeCore [Finite G] [Nonempty Ω]
    [IsPretransitive (CFSG.pPrimeCore 2 G) Ω] : Odd (Nat.card Ω) := by
  obtain ⟨α⟩ := ‹Nonempty Ω›
  rw [← index_stabilizer_of_transitive (CFSG.pPrimeCore 2 G) α]
  exact Odd.of_dvd_nat odd_card_pPrimeCore_two (index_dvd_card _)

variable (Ω) in
theorem exists_common_fixed_of_commute [Finite G] [Finite Ω] [Nonempty Ω]
    [IsPretransitive (CFSG.pPrimeCore 2 G) Ω] {t u : G} (ht : orderOf t = 2)
    (hu : orderOf u = 2) (htu : Commute t u) (hne : t ≠ u) :
    ∃ α : Ω, t • α = α ∧ u • α = α := by
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hu2 : u * u = 1 := by rw [← pow_two, ← hu, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht; omega
  have hu1 : u ≠ 1 := fun h => by rw [h, orderOf_one] at hu; omega
  set V := CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions t u ht2 hu2 htu
  have hVK : IsKleinFour V :=
    CFSG.GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions t u ht2 hu2 ht1 hu1 hne htu
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [IsKleinFour.card_four]; norm_num)
  obtain ⟨α, hα⟩ := fixSet_nonempty_of_odd
    (odd_card_of_isPretransitive_pPrimeCore (G := G) (Ω := Ω)) hV2
  exact ⟨α, hα t (Or.inr (Or.inl rfl)), hα u (Or.inr (Or.inr (Or.inl rfl)))⟩

theorem card_fixedBy_mul_card_fixedBy_mul_card_fixedBy [Finite G] [Finite Ω]
    [IsPretransitive (CFSG.pPrimeCore 2 G) Ω] {t u : G} (ht : orderOf t = 2)
    (hu : orderOf u = 2) (htu : Commute t u) (hne : t ≠ u) :
    (fixedBy Ω t).ncard * (fixedBy Ω u).ncard * (fixedBy Ω (t * u)).ncard =
      Nat.card Ω * (fixedBy Ω t ∩ fixedBy Ω u).ncard ^ 2 := by
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · simp [Set.eq_empty_of_isEmpty]
  obtain ⟨α, hαt, hαu⟩ := exists_common_fixed_of_commute Ω ht hu htu hne
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hu2 : u * u = 1 := by rw [← pow_two, ← hu, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht; omega
  have hu1 : u ≠ 1 := fun h => by rw [h, orderOf_one] at hu; omega
  have hN := normalizer_eq_top (CFSG.pPrimeCore 2 G)
  exact (ncard_mul_ncard_fixedBy_inter_sq odd_card_pPrimeCore_two ht2 hu2 htu ht1 hu1 hne
    (hN ▸ mem_top t) (hN ▸ mem_top u) hαt hαu).symm

theorem fixedBy_ne_fixedBy [Finite G] [Finite Ω] [FaithfulSMul G Ω]
    [IsPretransitive (CFSG.pPrimeCore 2 G) Ω] {t u : G} (ht : orderOf t = 2)
    (hu : orderOf u = 2) (htu : Commute t u) (hne : t ≠ u) : fixedBy Ω t ≠ fixedBy Ω u := by
  intro hFF
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · have : t = 1 := eq_of_smul_eq_smul (α := Ω) (fun a => isEmptyElim a)
    rw [this, orderOf_one] at ht
    omega
  obtain ⟨α, hαt, -⟩ := exists_common_fixed_of_commute Ω ht hu htu hne
  have h := card_fixedBy_mul_card_fixedBy_mul_card_fixedBy (Ω := Ω) ht hu htu hne
  rw [← hFF, Set.inter_self] at h
  have hpos : 0 < (fixedBy Ω t).ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨α, hαt⟩
  have hcard : (fixedBy Ω (t * u)).ncard = Nat.card Ω := by
    have h' : (fixedBy Ω t).ncard ^ 2 * (fixedBy Ω (t * u)).ncard =
        (fixedBy Ω t).ncard ^ 2 * Nat.card Ω := by rw [pow_two, h]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h'
  have huniv : fixedBy Ω (t * u) = Set.univ :=
    Set.eq_of_subset_of_ncard_le (Set.subset_univ _) (by rw [Set.ncard_univ, hcard])
  have h1 : t * u = 1 := eq_of_smul_eq_smul (fun a => by
    have : a ∈ fixedBy Ω (t * u) := huniv ▸ Set.mem_univ a
    rw [mem_fixedBy] at this
    rw [this, one_smul])
  have hu2 : u * u = 1 := by rw [← pow_two, ← hu, pow_orderOf_eq_one]
  exact hne (by rw [← mul_one t, ← hu2, ← mul_assoc, h1, one_mul])

theorem eq_of_commute_of_existsUnique_fixed [Finite G] [Finite Ω] [FaithfulSMul G Ω]
    [IsPretransitive (CFSG.pPrimeCore 2 G) Ω] {t u : G} (ht : orderOf t = 2)
    (hu : orderOf u = 2) (htu : Commute t u) (ht1 : ∃! ω : Ω, t • ω = ω)
    (hu1 : ∃! ω : Ω, u • ω = ω) : t = u := by
  by_contra hne
  obtain ⟨α, hα, hαu⟩ := ht1
  obtain ⟨β, hβ, hβu⟩ := hu1
  have huα : u • α = α := hαu _ (by
    show t • u • α = u • α
    rw [← mul_smul, htu.eq, mul_smul, hα])
  have hβα : β = α := (hβu α huα).symm
  have hF : ∀ (g : G) (γ : Ω), (∀ ω, g • ω = ω → ω = γ) → g • γ = γ → fixedBy Ω g = {γ} :=
    fun g γ h1 h2 => Set.ext fun ω => ⟨fun h => h1 ω h, fun h => h ▸ h2⟩
  exact fixedBy_ne_fixedBy ht hu htu hne
    ((hF t α hαu hα).trans (hF u α (fun ω h => (hβu ω h).trans hβα) huα).symm)

end Lemma14

section Lemma18

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem lemma_1_8_normalizer (H : Subgroup G) [H.Normal] (hH : ¬ p ∣ Nat.card H)
    {P : Subgroup G} (hP : IsPGroup p P) :
    (normalizer (P : Set G)).map (QuotientGroup.mk' H) =
      normalizer ((P.map (QuotientGroup.mk' H) : Subgroup (G ⧸ H)) : Set (G ⧸ H)) := by
  refine le_antisymm (le_normalizer_map _) (fun z hz => ?_)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H z
  have hPH : P ⊓ H = ⊥ := by rw [inf_comm]; exact inf_eq_bot_of_isPGroup_of_not_dvd hH hP
  have hHW : H ≤ P ⊔ H := le_sup_right
  have hcardW : Nat.card (P ⊔ H : Subgroup G) = Nat.card H * Nat.card P := by
    have h1 := relIndex_mul_card H (P ⊔ H)
    rw [inf_eq_left.2 hHW, relIndex_sup_right] at h1
    have h2 := relIndex_mul_card H P
    rw [inf_comm, hPH, card_bot, mul_one] at h2
    rw [← h1, h2, mul_comm]
  have hP'W : P.map (MulAut.conj x).toMonoidHom ≤ P ⊔ H := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 : QuotientGroup.mk' H (x * a * x⁻¹) ∈ P.map (QuotientGroup.mk' H) := by
      rw [map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.1 hz _).1 ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hbe⟩ := h1
    have h2 : b⁻¹ * (x * a * x⁻¹) ∈ H := QuotientGroup.eq.1 hbe
    have e : x * a * x⁻¹ = b * (b⁻¹ * (x * a * x⁻¹)) := by group
    change x * a * x⁻¹ ∈ P ⊔ H
    rw [e]
    exact mul_mem (mem_sup_left hb) (mem_sup_right h2)
  have hsyl : ∀ Q : Subgroup G, Q ≤ P ⊔ H → Nat.card Q = Nat.card P →
      ¬ p ∣ (Q.subgroupOf (P ⊔ H)).index := by
    intro Q hQW hQ
    have h1 := relIndex_mul_card Q (P ⊔ H)
    rw [inf_eq_left.2 hQW, hQ, hcardW] at h1
    have : Q.relIndex (P ⊔ H) = Nat.card H := Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
    change ¬ p ∣ Q.relIndex (P ⊔ H)
    rw [this]
    exact hH
  have hpg : ∀ Q : Subgroup G, IsPGroup p Q → IsPGroup p (Q.subgroupOf (P ⊔ H)) :=
    fun Q hQ => hQ.comap_of_injective _ (P ⊔ H).subtype_injective
  have hP' : IsPGroup p (P.map (MulAut.conj x).toMonoidHom) := hP.map _
  let S₁ : Sylow p (P ⊔ H : Subgroup G) := (hpg P hP).toSylow (hsyl P le_sup_left rfl)
  let S₂ : Sylow p (P ⊔ H : Subgroup G) := (hpg _ hP').toSylow
    (hsyl _ hP'W (card_map_of_injective (MulAut.conj x).injective))
  obtain ⟨w, hw⟩ := MulAction.exists_smul_eq (P ⊔ H : Subgroup G) S₂ S₁
  have hle : P.map (MulAut.conj ((w : G) * x)).toMonoidHom ≤ P := by
    rintro _ ⟨a, ha, rfl⟩
    have hxa' : x * a * x⁻¹ ∈ P.map (MulAut.conj x).toMonoidHom :=
      ⟨a, ha, by simp [MulAut.conj_apply]⟩
    have h1 : (⟨x * a * x⁻¹, hP'W hxa'⟩ : (P ⊔ H : Subgroup G)) ∈
        (S₂ : Subgroup (P ⊔ H : Subgroup G)) := mem_subgroupOf.2 hxa'
    have h2 : (MulAut.conj w) • (⟨x * a * x⁻¹, hP'W hxa'⟩ : (P ⊔ H : Subgroup G)) ∈
        (S₁ : Subgroup (P ⊔ H : Subgroup G)) := by
      rw [← hw, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ h1
    have h3 := mem_subgroupOf.1 h2
    simpa [MulAut.conj_apply, mul_assoc] using h3
  have heq : P.map (MulAut.conj ((w : G) * x)).toMonoidHom = P :=
    eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj _).injective])
  have hwx : (w : G) * x ∈ normalizer (P : Set G) := by
    generalize (w : G) * x = g at heq ⊢
    rw [mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      rw [← heq]
      exact ⟨a, ha, rfl⟩
    · intro ha
      rw [← heq] at ha
      obtain ⟨b, hb, hbe⟩ := ha
      have : b = a := (MulAut.conj g).injective hbe
      rwa [← this]
  obtain ⟨b, hb, h₀, hh₀, hbh⟩ := mem_sup_of_normal_right.1 w.2
  refine ⟨h₀ * x, ?_, ?_⟩
  · have : h₀ * x = b⁻¹ * ((w : G) * x) := by rw [← hbh]; group
    rw [this]
    exact mul_mem (inv_mem (le_normalizer hb)) hwx
  · rw [map_mul, (QuotientGroup.mk'_apply H h₀), (QuotientGroup.eq_one_iff h₀).2 hh₀, one_mul]

theorem lemma_1_8_centralizer (H : Subgroup G) [H.Normal] (hH : ¬ p ∣ Nat.card H)
    {P : Subgroup G} (hP : IsPGroup p P) :
    (centralizer (P : Set G)).map (QuotientGroup.mk' H) =
      centralizer ((P.map (QuotientGroup.mk' H) : Subgroup (G ⧸ H)) : Set (G ⧸ H)) := by
  apply le_antisymm
  · rintro _ ⟨c, hc, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.1 hc a ha]
  · intro z hz
    have hzN : z ∈ normalizer ((P.map (QuotientGroup.mk' H) : Subgroup (G ⧸ H)) :
        Set (G ⧸ H)) := by
      rw [mem_normalizer_iff]
      intro q
      constructor
      · intro hq
        rw [← mem_centralizer_iff.1 hz q hq, mul_inv_cancel_right]
        exact hq
      · intro hq
        have h := mem_centralizer_iff.1 (inv_mem hz) _ hq
        have e : q = z⁻¹ * (z * q * z⁻¹) * z := by group
        rw [e, ← h, inv_mul_cancel_right]
        exact hq
    rw [← lemma_1_8_normalizer H hH hP] at hzN
    obtain ⟨y, hy, rfl⟩ := hzN
    refine ⟨y, mem_centralizer_iff.2 (fun a ha => ?_), rfl⟩
    have h1 : y * a * y⁻¹ ∈ P := (mem_normalizer_iff.1 hy a).1 ha
    have h2 : QuotientGroup.mk' H (y * a * y⁻¹) = QuotientGroup.mk' H a := by
      rw [map_mul, map_mul, map_inv, ← mem_centralizer_iff.1 hz _ ⟨a, ha, rfl⟩,
        mul_inv_cancel_right]
    have h3 : (y * a * y⁻¹)⁻¹ * a ∈ P ⊓ H :=
      Subgroup.mem_inf.2 ⟨mul_mem (inv_mem h1) ha, QuotientGroup.eq.1 h2⟩
    rw [inf_comm, inf_eq_bot_of_isPGroup_of_not_dvd hH hP, mem_bot, inv_mul_eq_one] at h3
    have h4 := congrArg (· * y) h3
    simp only [inv_mul_cancel_right] at h4
    exact h4.symm

theorem map_normalizer_eq_of_odd (H : Subgroup G) [H.Normal] (hH : Odd (Nat.card H))
    {P : Subgroup G} (hP : IsPGroup 2 P) :
    (normalizer (P : Set G)).map (QuotientGroup.mk' H) =
      normalizer ((P.map (QuotientGroup.mk' H) : Subgroup (G ⧸ H)) : Set (G ⧸ H)) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  lemma_1_8_normalizer H hH.not_two_dvd_nat hP

theorem map_centralizer_eq_of_odd (H : Subgroup G) [H.Normal] (hH : Odd (Nat.card H))
    {P : Subgroup G} (hP : IsPGroup 2 P) :
    (centralizer (P : Set G)).map (QuotientGroup.mk' H) =
      centralizer ((P.map (QuotientGroup.mk' H) : Subgroup (G ⧸ H)) : Set (G ⧸ H)) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  lemma_1_8_centralizer H hH.not_two_dvd_nat hP

end Lemma18

end CFSG.Holt.H78
