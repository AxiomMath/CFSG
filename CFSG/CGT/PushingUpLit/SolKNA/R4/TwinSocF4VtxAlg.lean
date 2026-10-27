module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp24LayerTq

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Balance
open CFSG.CGT.PushingUpLit.SolKNA.R4.Perp24
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y]

theorem inv_mul_mem_of_relIndex_two' {P Q : Subgroup Y} (h : Q.relIndex P = 2) {a b : Y}
    (ha : a ∈ P) (hb : b ∈ P) (haQ : a ∉ Q) (hbQ : b ∉ Q) : a⁻¹ * b ∈ Q := by
  have h2 : (Q.subgroupOf P).index = 2 := h
  have hiff := Subgroup.mul_mem_iff_of_index_two h2 (a := (⟨a, ha⟩ : ↥P)⁻¹) (b := ⟨b, hb⟩)
  have hmem : ((⟨a, ha⟩ : ↥P)⁻¹ * ⟨b, hb⟩) ∈ Q.subgroupOf P := by
    rw [hiff]
    constructor
    · intro h1
      exact absurd (Subgroup.mem_subgroupOf.mp (inv_mem_iff.mp h1)) haQ
    · intro h1
      exact absurd (Subgroup.mem_subgroupOf.mp h1) hbQ
  simpa [Subgroup.mem_subgroupOf] using hmem

theorem exists_oddCore_mul_of_centralizer {K P W : Subgroup Y} {c r t : Y}
    (hq : IsPGroup 2 (↥K ⧸ classicalInvolutionOddCore ↥K)) (hP : IsSylow2In P K)
    (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hcW : c ∈ W) (hrel : (P ⊓ W).relIndex P = 2)
    (hrP : r ∈ P) (hrW : r ∉ W) (hcr : c * r * c⁻¹ = t * r) (htK : t ∈ K) (ht2 : orderOf t = 2)
    {k : Y} (hk : k ∈ K) (hck : c * k = k * c) : ∃ o ∈ oddCoreIn K, ∃ p ∈ P ⊓ W, o * p = k := by
  obtain ⟨o, ho, p, hp, rfl⟩ := exists_oddCore_mul_of_sylow hq hP hk
  by_cases hpW : p ∈ W
  · exact ⟨o, ho, p, Subgroup.mem_inf.mpr ⟨hp, hpW⟩, rfl⟩
  · exfalso
    have hw : r⁻¹ * p ∈ P ⊓ W :=
      inv_mul_mem_of_relIndex_two' hrel hrP hp (fun hh => hrW hh.2) (fun hh => hpW hh.2)
    set w := r⁻¹ * p with hwdef
    have hpw : p = r * w := by rw [hwdef]; group
    have hcw : c * w * c⁻¹ = w := by
      rw [hWab c hcW w hw.2, mul_inv_cancel_right]
    have ht1 : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
    have hcp : c * p * c⁻¹ = t * p := by
      rw [hpw, show c * (r * w) * c⁻¹ = (c * r * c⁻¹) * (c * w * c⁻¹) by group, hcr, hcw]
      group
    have hkc : c * (o * p) * c⁻¹ = o * p := by
      rw [hck, mul_inv_cancel_right]
    have hco : c * o * c⁻¹ = o * t := by
      have h1 : (c * o * c⁻¹) * (c * p * c⁻¹) = o * p := by
        rw [← hkc]; group
      rw [hcp] at h1
      have h1' : (c * o * c⁻¹ * t) * p = o * p := by rw [mul_assoc]; exact h1
      have h2 : (c * o * c⁻¹) * t = o := mul_right_cancel h1'
      calc c * o * c⁻¹ = (c * o * c⁻¹) * (t * t) := by rw [ht1]; exact (mul_one _).symm
        _ = ((c * o * c⁻¹) * t) * t := by group
        _ = o * t := by rw [h2]
    have hodd : Odd (orderOf o) :=
      (odd_card_oddCoreIn K).of_dvd_nat (Subgroup.orderOf_dvd_natCard (oddCoreIn K) ho)
    obtain ⟨m, hm⟩ := hodd
    have hu : (o * t) ^ (2 * m + 1) = 1 := by
      rw [← hco, ← hm, conj_pow, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
    have htN : t * o * t⁻¹ ∈ oddCoreIn K := conj_mem_oddCoreIn htK ho
    have hu2 : (o * t) ^ 2 ∈ oddCoreIn K := by
      have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht1
      have : (o * t) ^ 2 = o * (t * o * t⁻¹) * (t * t) := by rw [pow_two]; group
      rw [this, ht1, mul_one]
      exact (oddCoreIn K).mul_mem ho htN
    have hut : o * t ∈ oddCoreIn K := by
      have : o * t = ((o * t) ^ 2) ^ (m + 1) := by
        rw [← pow_mul, show 2 * (m + 1) = (2 * m + 1) + 1 by ring, pow_succ, hu, one_mul]
      rw [this]
      exact (oddCoreIn K).pow_mem hu2 _
    have htO : t ∈ oddCoreIn K := by
      have := (oddCoreIn K).mul_mem ((oddCoreIn K).inv_mem ho) hut
      simpa using this
    exact not_mem_oddCoreIn_of_orderOf_two ht2 htO

theorem commutator_mem_oddCoreIn_of_centralizer {K P W : Subgroup Y} {c r t : Y}
    (hq : IsPGroup 2 (↥K ⧸ classicalInvolutionOddCore ↥K)) (hP : IsSylow2In P K)
    (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hcW : c ∈ W) (hrel : (P ⊓ W).relIndex P = 2)
    (hrP : r ∈ P) (hrW : r ∉ W) (hcr : c * r * c⁻¹ = t * r) (htK : t ∈ K) (ht2 : orderOf t = 2)
    {k₁ k₂ : Y} (hk₁ : k₁ ∈ K) (hk₂ : k₂ ∈ K) (hc₁ : c * k₁ = k₁ * c) (hc₂ : c * k₂ = k₂ * c) :
    ⁅k₁, k₂⁆ ∈ oddCoreIn K := by
  obtain ⟨o₁, ho₁, p₁, hp₁, rfl⟩ :=
    exists_oddCore_mul_of_centralizer hq hP hWab hcW hrel hrP hrW hcr htK ht2 hk₁ hc₁
  obtain ⟨o₂, ho₂, p₂, hp₂, rfl⟩ :=
    exists_oddCore_mul_of_centralizer hq hP hWab hcW hrel hrP hrW hcr htK ht2 hk₂ hc₂
  have hpK : ∀ p ∈ P ⊓ W, p ∈ K := fun p hp => hP.1 (Subgroup.mem_inf.mp hp).1
  obtain ⟨n₁, hn₁, rfl⟩ := ho₁
  obtain ⟨n₂, hn₂, rfl⟩ := ho₂
  set N := classicalInvolutionOddCore ↥K with hN
  let π₁ : ↥K := ⟨p₁, hpK p₁ hp₁⟩
  let π₂ : ↥K := ⟨p₂, hpK p₂ hp₂⟩
  have hπ : π₁ * π₂ = π₂ * π₁ := Subtype.ext (hWab _ (Subgroup.mem_inf.mp hp₁).2 _ (Subgroup.mem_inf.mp hp₂).2)
  have hn1 : (QuotientGroup.mk' N) n₁ = 1 := (QuotientGroup.eq_one_iff n₁).mpr hn₁
  have hn2 : (QuotientGroup.mk' N) n₂ = 1 := (QuotientGroup.eq_one_iff n₂).mpr hn₂
  have h1 : (QuotientGroup.mk' N) (n₁ * π₁) = (QuotientGroup.mk' N) π₁ := by
    rw [map_mul, hn1, one_mul]
  have h2 : (QuotientGroup.mk' N) (n₂ * π₂) = (QuotientGroup.mk' N) π₂ := by
    rw [map_mul, hn2, one_mul]
  have hcomm : ⁅n₁ * π₁, n₂ * π₂⁆ ∈ N := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement, h1, h2,
      ← map_commutatorElement]
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hπ, map_one]
  exact ⟨⁅n₁ * π₁, n₂ * π₂⁆, hcomm, by simp [commutatorElement_def, π₁, π₂]⟩

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4
