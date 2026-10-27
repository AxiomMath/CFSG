module

public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Goldschmidt

open CFSG.BenderSuzuki

variable {G : Type*} [Group G]

theorem mem_of_involution_conj_mem {M : Subgroup G} (hM : IsStronglyEmbeddedOrder M) {t g : G}
    (ht : orderOf t = 2) (htM : t ∈ M) (htg : g⁻¹ * t * g ∈ M) : g ∈ M := by
  by_contra hg
  have hmem : t ∈ M ⊓ M.map (MulAut.conj g).toMonoidHom :=
    ⟨htM, g⁻¹ * t * g, htg, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hdvd : 2 ∣ Nat.card (M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G) := by
    have := orderOf_dvd_natCard
      (⟨t, hmem⟩ : (M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G))
    rwa [Subgroup.orderOf_mk, ht] at this
  exact (Nat.not_even_iff_odd.mpr (hM.2.2 g hg)) (even_iff_two_dvd.mpr hdvd)

theorem centralizer_le_of_stronglyEmbedded {M : Subgroup G} (hM : IsStronglyEmbeddedOrder M)
    {t : G} (ht : orderOf t = 2) (htM : t ∈ M) : Subgroup.centralizer ({t} : Set G) ≤ M := by
  intro c hc
  refine mem_of_involution_conj_mem hM ht htM ?_
  have hct : c * t = t * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  have : c⁻¹ * t * c = t := by rw [mul_assoc, ← hct, inv_mul_cancel_left]
  rw [this]
  exact htM

theorem isConj_of_mem_of_not_mem [Finite G] {M : Subgroup G} (hM : IsStronglyEmbeddedOrder M)
    {t u : G} (ht : orderOf t = 2) (hu : orderOf u = 2) (htM : t ∈ M) (huM : u ∉ M) :
    IsConj t u := by
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hu2 : u * u = 1 := by rw [← sq, ← hu, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  set c := t * u with hc
  have hcinv : c⁻¹ = u * t := by rw [hc, mul_inv_rev, htinv, huinv]
  have htc : t * c * t⁻¹ = c⁻¹ := by
    rw [hcinv, hc, htinv, ← mul_assoc, ht2, one_mul]
  have huc : u * c * u⁻¹ = c⁻¹ := by
    rw [hcinv, hc, huinv, mul_assoc, mul_assoc, hu2, mul_one]
  rcases Nat.even_or_odd (orderOf c) with ⟨k, hk⟩ | ⟨k, hk⟩
  ·
    exfalso
    have hpos : 0 < orderOf c := orderOf_pos c
    have hk0 : 0 < k := by omega
    set w := c ^ k with hw
    have hw1 : w ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by omega)
    have hww : w * w = 1 := by rw [hw, ← pow_add, ← hk, pow_orderOf_eq_one]
    have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
    have hw2 : orderOf w = 2 :=
      orderOf_eq_prime (by rw [sq]; exact hww) hw1
    have htw : t * w * t⁻¹ = w := by rw [hw, ← conj_pow, htc, inv_pow, ← hw, hwinv]
    have huw : u * w * u⁻¹ = w := by rw [hw, ← conj_pow, huc, inv_pow, ← hw, hwinv]
    have hwM : w ∈ M := by
      apply centralizer_le_of_stronglyEmbedded hM ht htM
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc w * t = (t * w * t⁻¹) * t := by rw [htw]
        _ = t * w := by group
    apply huM
    apply centralizer_le_of_stronglyEmbedded hM hw2 hwM
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc u * w = (u * w * u⁻¹) * u := by group
      _ = w * u := by rw [huw]
  ·
    have h2k : c ^ (2 * k) = c⁻¹ := by
      have h1 : c ^ (2 * k) * c = 1 := by rw [← pow_succ, ← hk, pow_orderOf_eq_one]
      exact eq_inv_of_mul_eq_one_left h1
    have htc' : t * c⁻¹ * t⁻¹ = c := by
      calc t * c⁻¹ * t⁻¹ = (t * c * t⁻¹)⁻¹ := by group
        _ = c := by rw [htc, inv_inv]
    have htck : t * (c ^ k)⁻¹ * t⁻¹ = c ^ k := by
      rw [← inv_pow, ← conj_pow, htc']
    refine isConj_iff.mpr ⟨c ^ k, ?_⟩
    calc c ^ k * t * (c ^ k)⁻¹ = c ^ k * (t * (c ^ k)⁻¹ * t⁻¹) * t := by group
      _ = c ^ (2 * k) * t := by rw [htck, two_mul, pow_add]
      _ = u := by rw [h2k, hcinv, mul_assoc, ht2, mul_one]

theorem N9 :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (M : Subgroup G),
      CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M →
      (∀ t ∈ M, orderOf t = 2 → Subgroup.centralizer ({t} : Set G) ≤ M) ∧
      (∀ t ∈ M, ∀ g : G, orderOf t = 2 → g⁻¹ * t * g ∈ M →
        ∃ m ∈ M, m⁻¹ * t * m = g⁻¹ * t * g) ∧
      ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y := by
  intro G _ _ _ M hM
  refine ⟨fun t htM ht => centralizer_le_of_stronglyEmbedded hM ht htM,
    fun t htM g ht htg => ⟨g, mem_of_involution_conj_mem hM ht htM htg, rfl⟩, ?_⟩
  intro x y hx hy
  obtain ⟨t, htM, ht⟩ : ∃ t ∈ M, orderOf t = 2 := by
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := M) 2
      (even_iff_two_dvd.mp hM.2.1)
    exact ⟨t, t.2, by rwa [Subgroup.orderOf_coe]⟩
  obtain ⟨u, huM, hu⟩ : ∃ u, u ∉ M ∧ orderOf u = 2 := by
    by_contra hcon'
    have hcon : ∀ g : G, g ∉ M → orderOf g ≠ 2 := fun g hg h => hcon' ⟨g, hg, h⟩
    have hle : Subgroup.normalClosure {g : G | orderOf g = 2} ≤ M := by
      refine (Subgroup.closure_le M).mpr fun g hg => ?_
      obtain ⟨a, ha, hag⟩ := Group.mem_conjugatesOfSet_iff.mp hg
      obtain ⟨c, hc⟩ := isConj_iff.mp hag
      have hga : orderOf g = 2 := by
        rw [← hc, ← ha]
        exact (SemiconjBy.orderOf_eq c (by
          change c * a = c * a * c⁻¹ * c
          group)).symm
      by_contra hgM
      exact hcon g hgM hga
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (Subgroup.normalClosure {g : G | orderOf g = 2}) with hbot | htop
    · have : t ∈ Subgroup.normalClosure {g : G | orderOf g = 2} :=
        Subgroup.subset_normalClosure (show orderOf t = 2 from ht)
      rw [hbot, Subgroup.mem_bot] at this
      rw [this, orderOf_one] at ht
      exact absurd ht (by norm_num)
    · exact hM.1 (top_le_iff.mp (htop ▸ hle))
  have key : ∀ z : G, orderOf z = 2 → IsConj z u := by
    intro z hz
    by_cases hzM : z ∈ M
    · exact isConj_of_mem_of_not_mem hM hz hu hzM huM
    · exact (isConj_of_mem_of_not_mem hM ht hz htM hzM).symm.trans
        (isConj_of_mem_of_not_mem hM ht hu htM huM)
  exact (key x hx).trans (key y hy).symm

end CFSG.Goldschmidt
