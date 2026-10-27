module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKEngel

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem fkCore_block {M : Type} [Group M] [Finite M] {N : Subgroup M} {X Y : Type} [Group X]
    [Group Y] (β : X × Y →* M) (hβ : Function.Injective β) {z : ↥N} {K : Subgroup ↥N}
    (hz : orderOf z = 2) (hP : Sl23PocketIn ⊤ z K) {a : X} (hza : β (a, 1) = (z : M))
    (hY : ∀ c : Y, Odd (orderOf c) → c ≠ 1 → ∃ E : Subgroup Y, (∀ e ∈ E, β (1, e) ∈ N) ∧
      (∀ e ∈ E, e * e = 1) ∧ (∃ e ∈ E, e ≠ 1) ∧ (∀ e ∈ E, c * e * c⁻¹ ∈ E) ∧
      (∀ e ∈ E, e ≠ 1 → c * e * c⁻¹ ≠ e))
    {k : ↥N} (hk : k ∈ K) (hkodd : Odd (orderOf k)) {p : X} {c : Y} (hpc : β (p, c) = (k : M)) :
    c = 1 := by
  by_contra hc1
  have hcodd : Odd (orderOf c) := by
    have h1 : orderOf (p, c) = orderOf k := by
      rw [← orderOf_injective β hβ (p, c), hpc, Subgroup.orderOf_coe]
    have hlcm : orderOf (p, c) = Nat.lcm (orderOf p) (orderOf c) := Prod.orderOf (p, c)
    exact (h1 ▸ hkodd).of_dvd_nat (hlcm ▸ Nat.dvd_lcm_right _ _)
  obtain ⟨E, hEN, hE2, ⟨e₀, he₀, he₀1⟩, hcE, hfree⟩ := hY c hcodd hc1
  set E' : Subgroup ↥N := (E.map (β.comp (MonoidHom.inr X Y))).subgroupOf N with hE'
  have hmem : ∀ x : ↥N, x ∈ E' ↔ ∃ e ∈ E, β (1, e) = (x : M) := by
    intro x
    rw [hE', Subgroup.mem_subgroupOf, Subgroup.mem_map]
    simp
  have hk' : ∀ x : ↥N, ∀ e : Y, β (1, e) = (x : M) →
      β (1, c * e * c⁻¹) = ((k * x * k⁻¹ : ↥N) : M) := by
    intro x e hex
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hex, ← hpc, ← map_inv, ← map_mul,
      ← map_mul]
    congr 1
    ext <;> simp
  refine fkPocket_no_free_involutions hz hP E' ?_ ?_ ?_ hk ?_ ?_
    (e := ⟨β (1, e₀), hEN e₀ he₀⟩) ((hmem _).mpr ⟨e₀, he₀, rfl⟩) ?_
  ·
    intro x hx
    obtain ⟨e, he, hex⟩ := (hmem x).mp hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hex, ← hza, ← map_mul, ← map_mul]
    congr 1
    ext <;> simp
  ·
    intro x hx
    obtain ⟨e, he, hex⟩ := (hmem x).mp hx
    apply Subtype.ext
    rw [Subgroup.coe_mul, ← hex, ← map_mul]
    have h1 : ((1 : X), e) * ((1 : X), e) = 1 := by
      ext
      · simp
      · exact hE2 e he
    rw [h1, map_one]
    rfl
  ·
    intro hzE
    obtain ⟨e, he, hez⟩ := (hmem z).mp hzE
    have h1 : ((1 : X), e) = (a, 1) := hβ (hez.trans hza.symm)
    have ha : a = 1 := (congrArg Prod.fst h1).symm
    have hz1 : z = 1 := by
      apply Subtype.ext
      rw [← hza, ha, Prod.mk_one_one, map_one]
      rfl
    rw [hz1, orderOf_one] at hz
    exact absurd hz (by decide)
  ·
    intro x hx
    obtain ⟨e, he, hex⟩ := (hmem x).mp hx
    exact (hmem _).mpr ⟨c * e * c⁻¹, hcE e he, hk' x e hex⟩
  ·
    intro x hx hx1 hkx
    obtain ⟨e, he, hex⟩ := (hmem x).mp hx
    have he1 : e ≠ 1 := by
      rintro rfl
      apply hx1
      apply Subtype.ext
      rw [← hex, Prod.mk_one_one, map_one]
      rfl
    apply hfree e he he1
    have h1 := hk' x e hex
    rw [hkx, ← hex] at h1
    exact (congrArg Prod.snd (hβ h1))
  ·
    intro h1
    apply he₀1
    have h2 : β (1, e₀) = 1 := congrArg Subtype.val h1
    exact (congrArg Prod.snd (hβ (h2.trans (map_one β).symm)))

end CFSG.OddStandard.SmallF3.Omega
