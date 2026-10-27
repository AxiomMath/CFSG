module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5DescLayer
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFTransLayerAux

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem t5_isL29_layerCent_of_desc (hL : IsOm6Z2 L) {t : G} (ht : t ∈ centerIn L)
    (ht2 : orderOf t = 2) {s : G} (hs : s ∈ normalizer (L : Set G)) (htE : t ∉ layerCent L s)
    (h : IsL29 (layerCent (DescL L t) (descElt L t s hs))) : IsL29 (layerCent L s) := by
  let N : Subgroup G := normalizer (L : Set G)
  let f : ↥N →* DescG L t := descMk L t
  let En : Subgroup ↥N := CFSG.inSubgroup CFSG.layer (descCent L hs)
  have hN : En.map N.subtype = layerCent L s := (t5_layerCent_eq_map L hs).symm
  have hD : En.map f = layerCent (DescL L t) (descElt L t s hs) :=
    (t5_desc_layerCent hL ht ht2 hs).symm
  have ha2 : descT L ht * descT L ht = 1 := descT_mul_self ht ht2
  have hpow : ∀ k : ℤ, (descT L ht) ^ k = 1 ∨ (descT L ht) ^ k = descT L ht := by
    intro k
    rw [← zpow_mod_orderOf (descT L ht) k]
    have hdvd : orderOf (descT L ht) ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_two]
      exact ha2
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with ho | ho
    · left
      rw [ho]; simp
    · rw [ho]
      have h2 : k % (↑(2 : ℕ) : ℤ) = k % 2 := by norm_num
      rw [h2]
      rcases Int.emod_two_eq_zero_or_one k with hk0 | hk1
      · left; rw [hk0]; simp
      · right; rw [hk1]; simp
  have hg : Function.Injective (f.comp En.subtype) := by
    intro x y hxy
    change f (x : ↥N) = f (y : ↥N) at hxy
    have hker : (x : ↥N)⁻¹ * (y : ↥N) ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      calc f ((x : ↥N)⁻¹ * (y : ↥N))
          = (f (x : ↥N))⁻¹ * f (y : ↥N) := by rw [map_mul, map_inv]
        _ = (f (x : ↥N))⁻¹ * f (x : ↥N) := by rw [← hxy]
        _ = 1 := inv_mul_cancel _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (descMk_ker_le_zpowers hL ht ht2 hker)
    rcases hpow k with hk1 | hk2
    · have h1 : (x : ↥N)⁻¹ * (y : ↥N) = 1 := by rw [← hk, hk1]
      exact Subtype.ext (inv_mul_eq_one.mp h1)
    · exfalso
      have hmem : descT L ht ∈ En := by
        have hmem' : (x : ↥N)⁻¹ * (y : ↥N) ∈ En := mul_mem (inv_mem x.2) y.2
        rwa [← hk, hk2] at hmem'
      have htmem : t ∈ layerCent L s := by
        have hm : N.subtype (descT L ht) ∈ En.map N.subtype :=
          Subgroup.mem_map_of_mem N.subtype hmem
        rw [hN] at hm
        exact hm
      exact htE htmem
  have hrange : (f.comp En.subtype).range = En.map f := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(x : ↥N), x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  let e1 : ↥(En.map N.subtype) ≃* ↥En :=
    (Subgroup.equivMapOfInjective En N.subtype N.subtype_injective).symm
  let e2 : ↥En ≃* ↥(En.map f) :=
    (MonoidHom.ofInjective hg).trans (MulEquiv.subgroupCongr hrange)
  let e : ↥(layerCent L s) ≃* ↥(layerCent (DescL L t) (descElt L t s hs)) :=
    (MulEquiv.subgroupCongr hN).symm.trans (e1.trans (e2.trans (MulEquiv.subgroupCongr hD)))
  exact (ff_isL29_congr e).mpr h

end CFSG.OddStandard.SmallF3.Omega
