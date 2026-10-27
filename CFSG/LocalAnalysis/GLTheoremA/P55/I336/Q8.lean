module

public import CFSG.LocalAnalysis.GLTheoremA.P55.I336.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.P55.I336

open CFSG.Open
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

theorem centralizes_of_fixes_index_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Y F D : Subgroup G}
    (hY2 : IsPGroup 2 Y) (hD : IsPGroup p D) (hDY : D ≤ Subgroup.normalizer (Y : Set G))
    (hFY : F ≤ Y) (hidx : (F.subgroupOf Y).index = 2)
    (hF : F ≤ Subgroup.centralizer (D : Set G)) : Y ≤ Subgroup.centralizer (D : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfix : ∀ f ∈ F, ∀ a ∈ D, a * f * a⁻¹ = f := by
    intro f hf a ha
    have h := Subgroup.mem_centralizer_iff.mp (hF hf) a ha
    rw [h]
    group
  have hDF : D ≤ Subgroup.normalizer (F : Set G) :=
    le_normalizer_of_forall_mem fun d hd f hf => by rw [hfix f hf d hd]; exact hf
  have hFp : ¬ p ∣ Nat.card F := by
    obtain ⟨k, hk⟩ := (hY2.to_le hFY).exists_card_eq
    rw [hk]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  intro y hy
  have hhyp : ∀ a ∈ D, y⁻¹ * (a * y * a⁻¹) ∈ F := by
    intro a ha
    by_cases hyF : y ∈ F
    · rw [hfix y hyF a ha, inv_mul_cancel]
      exact F.one_mem
    · have hay : a * y * a⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hDY ha) y).mp hy
      have hayF : a * y * a⁻¹ ∉ F := by
        intro hf
        apply hyF
        have h := hfix _ hf a⁻¹ (D.inv_mem ha)
        have e : a⁻¹ * (a * y * a⁻¹) * a⁻¹⁻¹ = y := by group
        rw [e] at h
        rw [h]
        exact hf
      have h1 := (Subgroup.mul_mem_iff_of_index_two hidx
        (a := (⟨y, hy⟩ : ↥Y)⁻¹) (b := ⟨a * y * a⁻¹, hay⟩))
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at h1
      exact h1.mpr (iff_of_false (fun h => hyF (by simpa using F.inv_mem h)) hayF)
  obtain ⟨n, hnF, hn⟩ := exists_fixed_mem_coset hp hD hDF hFp hhyp
  have := Subgroup.mul_mem _ hn (Subgroup.inv_mem _ (hF hnF))
  rwa [mul_inv_cancel_right] at this

theorem inf_centralizer_eq_zpowers {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Y D : Subgroup G}
    (hY2 : IsPGroup 2 Y) (hY8 : Nat.card Y = 8) (hD : IsPGroup p D)
    (hDY : D ≤ Subgroup.normalizer (Y : Set G)) (hYD : ¬ Y ≤ Subgroup.centralizer (D : Set G))
    {z : G} (hzY : z ∈ Y) (hzD : z ∈ Subgroup.centralizer (D : Set G)) (hz : orderOf z = 2) :
    Y ⊓ Subgroup.centralizer (D : Set G) = Subgroup.zpowers z := by
  set F : Subgroup G := Y ⊓ Subgroup.centralizer (D : Set G) with hFdef
  have hzF : z ∈ F := ⟨hzY, hzD⟩
  have hFY : F ≤ Y := inf_le_left
  have hdvd : Nat.card F ∣ 8 := hY8 ▸ Subgroup.card_dvd_of_le hFY
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hF1 : Nat.card F ≠ 1 := by
    intro h
    have := Subgroup.card_eq_one.mp h
    rw [this, Subgroup.mem_bot] at hzF
    exact hz1 hzF
  have hF8 : Nat.card F ≠ 8 := by
    intro h
    apply hYD
    have : F = Y := Subgroup.eq_of_le_of_card_ge hFY (by rw [h, hY8])
    rw [← this]
    exact inf_le_right
  have hF4 : Nat.card F ≠ 4 := by
    intro h
    apply hYD
    refine centralizes_of_fixes_index_two hp hp2 hY2 hD hDY hFY ?_ inf_le_right
    have h1 := Subgroup.card_mul_index (F.subgroupOf Y)
    have h2 : Nat.card (F.subgroupOf Y) = Nat.card F :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFY).toEquiv
    rw [h2, h, hY8] at h1
    omega
  have hF2 : Nat.card F = 2 := by
    have hdiv : Nat.card F ∈ Nat.divisors 8 := by simp [hdvd]
    have : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    rw [this] at hdiv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
    omega
  have hcard : Nat.card (Subgroup.zpowers z) = 2 := by rw [Nat.card_zpowers, hz]
  exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzF) (by rw [hcard, hF2])).symm

section Q8

open QuaternionGroup

theorem exists_q8_data {Y : Subgroup G} (e : Y ≃* QuaternionGroup 2) :
    ∃ i j z : G, i ∈ Y ∧ j ∈ Y ∧ z ∈ Y ∧ orderOf z = 2 ∧ i ^ 2 = z ∧ j ^ 2 = z ∧
      i * j = z * (j * i) ∧ (∀ y ∈ Y, y ^ 2 = 1 → y = 1 ∨ y = z) := by
  refine ⟨(e.symm (a 1) : G), (e.symm (xa 0) : G), (e.symm (a 2) : G), (e.symm (a 1)).2,
    (e.symm (xa 0)).2, (e.symm (a 2)).2, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : (e.symm (a 2) : G) ≠ 1 := by
      intro h
      have h' : e.symm (a 2) = 1 := Subtype.ext h
      have := e.symm.injective (h'.trans (map_one e.symm).symm)
      exact absurd this (by decide)
    have h2 : (e.symm (a 2) : G) ^ 2 = 1 := by
      have : (a 2 : QuaternionGroup 2) ^ 2 = 1 := by decide
      have h3 : (e.symm (a 2)) ^ 2 = 1 := by rw [← map_pow, this, map_one]
      have h4 := congrArg Subtype.val h3
      rwa [Subgroup.coe_pow] at h4
    exact orderOf_eq_prime h2 h1
  · have : (a 1 : QuaternionGroup 2) ^ 2 = a 2 := by decide
    have h3 : (e.symm (a 1)) ^ 2 = e.symm (a 2) := by rw [← map_pow, this]
    have h4 := congrArg Subtype.val h3
    rwa [Subgroup.coe_pow] at h4
  · have : (xa 0 : QuaternionGroup 2) ^ 2 = a 2 := by decide
    have h3 : (e.symm (xa 0)) ^ 2 = e.symm (a 2) := by rw [← map_pow, this]
    have h4 := congrArg Subtype.val h3
    rwa [Subgroup.coe_pow] at h4
  · have : (a 1 : QuaternionGroup 2) * xa 0 = a 2 * (xa 0 * a 1) := by decide
    have h3 : e.symm (a 1) * e.symm (xa 0) = e.symm (a 2) * (e.symm (xa 0) * e.symm (a 1)) := by
      rw [← map_mul, ← map_mul, ← map_mul, this]
    have h4 := congrArg Subtype.val h3
    exact h4
  · intro y hy hy2
    have hq : (e ⟨y, hy⟩) ^ 2 = 1 := by
      rw [← map_pow, show (⟨y, hy⟩ : ↥Y) ^ 2 = 1 from Subtype.ext (by simpa using hy2), map_one]
    have hu : ∀ q : QuaternionGroup 2, q ^ 2 = 1 → q = 1 ∨ q = a 2 := by decide
    rcases hu _ hq with h | h
    · left
      have : (⟨y, hy⟩ : ↥Y) = 1 := e.injective (by rw [h, map_one])
      simpa using congrArg Subtype.val this
    · right
      have : (⟨y, hy⟩ : ↥Y) = e.symm (a 2) := e.injective (by rw [h, MulEquiv.apply_symm_apply])
      simpa using congrArg Subtype.val this

theorem card_eq_eight_of_q8 {Y : Subgroup G} (e : Y ≃* QuaternionGroup 2) : Nat.card Y = 8 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

end Q8

end CFSG.LocalAnalysis.GLTheoremA.P55.I336
