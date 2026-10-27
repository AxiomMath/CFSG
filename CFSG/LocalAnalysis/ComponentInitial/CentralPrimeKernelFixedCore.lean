module

public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]

theorem central_prime_kernel_fixed_group_prime_complement_core (Z : Subgroup H) [Z.Normal]
    (hZ : Z ≤ Subgroup.center H) (hZp : IsPGroup p Z) (β : MulAut H)
    (hβZ : Z.map (β : H →* H) = Z)
    (hcore : pPrimeCore p (fixedSubgroup (QuotientGroup.congr Z Z β hβZ)) = ⊥) :
    pPrimeCore p (fixedSubgroup β) = ⊥ := by
  have hp : p.Prime := Fact.out
  have hmemV : ∀ x : H, x ∈ (fixedSubgroup (QuotientGroup.congr Z Z β hβZ)).comap
      (QuotientGroup.mk' Z) ↔ ((β x : H) : H ⧸ Z) = x := fun x => Iff.rfl
  have hVa : ∀ v ∈ (fixedSubgroup (QuotientGroup.congr Z Z β hβZ)).comap (QuotientGroup.mk' Z),
      ∃ a ∈ Subgroup.center H, β v = v * a := by
    intro v hv
    have h1 := (hmemV v).1 hv
    rw [eq_comm, QuotientGroup.eq] at h1
    exact ⟨v⁻¹ * β v, hZ h1, by group⟩
  have hCV : fixedSubgroup β ≤
      (fixedSubgroup (QuotientGroup.congr Z Z β hβZ)).comap (QuotientGroup.mk' Z) := by
    intro c hc
    rw [hmemV]
    have hc' : β c = c := hc
    rw [hc']
  have hZV : Z ≤ (fixedSubgroup (QuotientGroup.congr Z Z β hβZ)).comap (QuotientGroup.mk' Z) := by
    intro z hz
    rw [hmemV]
    have hβz : β z ∈ Z := hβZ ▸ Subgroup.mem_map_of_mem _ hz
    rw [(QuotientGroup.eq_one_iff (β z)).2 hβz, (QuotientGroup.eq_one_iff z).2 hz]
  have hCn : ((fixedSubgroup β).subgroupOf
      ((fixedSubgroup (QuotientGroup.congr Z Z β hβZ)).comap (QuotientGroup.mk' Z))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hCV]
    intro v hv
    obtain ⟨a, ha, hβv⟩ := hVa v hv
    rw [Subgroup.mem_normalizer_iff]
    intro c
    have hac : a * β c = β c * a := (Subgroup.mem_center_iff.1 ha (β c)).symm
    have key : β (v * c * v⁻¹) = v * β c * v⁻¹ := by
      rw [map_mul, map_mul, map_inv, hβv]
      calc v * a * β c * (v * a)⁻¹ = v * (a * β c) * a⁻¹ * v⁻¹ := by group
        _ = v * (β c * a) * a⁻¹ * v⁻¹ := by rw [hac]
        _ = v * β c * v⁻¹ := by group
    constructor
    · intro hc
      have hc' : β c = c := hc
      change β (v * c * v⁻¹) = v * c * v⁻¹
      rw [key, hc']
    · intro hc
      have hc' : β (v * c * v⁻¹) = v * c * v⁻¹ := hc
      rw [key] at hc'
      exact mul_left_cancel (mul_right_cancel hc')
  let V := (fixedSubgroup (QuotientGroup.congr Z Z β hβZ)).comap (QuotientGroup.mk' Z)
  let C' := (fixedSubgroup β).subgroupOf V
  have hRn : ((pPrimeCore p C').map C'.subtype).Normal := inferInstance
  have hRcop : Nat.Coprime p (Nat.card ((pPrimeCore p C').map C'.subtype)) := by
    rw [Subgroup.card_map_of_injective C'.subtype_injective]
    exact pPrimeCore_coprime_card
  let πV : V →* fixedSubgroup (QuotientGroup.congr Z Z β hβZ) :=
    ((QuotientGroup.mk' Z).comp V.subtype).codRestrict _ fun v => v.2
  have hπV : Function.Surjective πV := by
    rintro ⟨q, hq⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z q
    exact ⟨⟨x, hq⟩, rfl⟩
  have hRK : ((pPrimeCore p C').map C'.subtype).map πV ≤
      pPrimeCore p (fixedSubgroup (QuotientGroup.congr Z Z β hβZ)) :=
    le_sSup ⟨hRn.map πV hπV, Nat.Coprime.coprime_dvd_right
      (Subgroup.card_dvd_of_surjective (πV.subgroupMap_surjective _)) hRcop⟩
  rw [hcore] at hRK
  have hRZ : (pPrimeCore p C').map C'.subtype ≤ Z.subgroupOf V := by
    intro r hr
    have h1 : πV r = 1 := (Subgroup.mem_bot.1 (hRK (Subgroup.mem_map_of_mem πV hr)))
    have h2 : ((r : H) : H ⧸ Z) = 1 := congrArg Subtype.val h1
    exact (QuotientGroup.eq_one_iff (N := Z) (r : H)).1 h2
  have hRbot : (pPrimeCore p C').map C'.subtype = ⊥ := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hZp
    have hZcard : Nat.card (Z.subgroupOf V) = p ^ k := by
      rw [← hk]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv
    have hdvd : Nat.card ((pPrimeCore p C').map C'.subtype) ∣ p ^ k :=
      hZcard ▸ Subgroup.card_dvd_of_le hRZ
    exact Subgroup.card_eq_one.1
      (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k hRcop).symm dvd_rfl hdvd)
  have hC'bot : pPrimeCore p C' = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ C'.subtype_injective).1 hRbot
  rw [← pPrimeCore_map_iso p (Subgroup.subgroupOfEquivOfLe hCV), hC'bot, Subgroup.map_bot]

end CFSG.LocalAnalysis.ComponentInitial
