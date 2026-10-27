module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Thm11Transport
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotTools
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.GH74.GLS.Stage12.McLCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.OddStandard.Solomon75Inputs
public import CFSG.LocalAnalysis.OddStandard.Solomon75Thm11Defs

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.ComponentClassification CFSG.ComponentClassification.GSThmB

theorem exists_isPComponent_of_odd_quotient {G : Type*} [Group G] [Finite G] {O : Subgroup G}
    [O.Normal] (hO : Odd (Nat.card O)) {E H J : Subgroup G} (hEH : E ≤ H)
    (hJ : IsPComponent 2 J) (hcov : J ≤ E ⊔ O) :
    ∃ J' : Subgroup G, J' ≤ H ∧ IsPComponent 2 (J'.subgroupOf H) ∧ J' ≤ E ⊔ (O ⊓ H) ∧
      (∀ x ∈ J ⊓ H, (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ J') ∧
      Nonempty (↥J' ⧸ pPrimeCore 2 ↥J' ≃* ↥J ⧸ pPrimeCore 2 ↥J) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : G →* G ⧸ O := QuotientGroup.mk' O with hπdef
  have hker : ¬ 2 ∣ Nat.card π.ker := by
    rw [hπdef, QuotientGroup.ker_mk']
    intro h
    exact (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr h)
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective O
  obtain ⟨hbij, -, hiso⟩ :=
    CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection π hsurj hker
  have hKbar : IsPComponent 2 (J.map π) := hbij.mapsTo hJ
  have hOker : O ≤ π.ker := by rw [hπdef, QuotientGroup.ker_mk']
  have hOmap : O.map π = ⊥ := (Subgroup.map_eq_bot_iff O).2 hOker
  have hKE : J.map π ≤ E.map π := by
    have h1 : J.map π ≤ (E ⊔ O).map π := Subgroup.map_mono hcov
    rwa [Subgroup.map_sup, hOmap, sup_bot_eq] at h1
  have hKH : J.map π ≤ H.map π := hKE.trans (Subgroup.map_mono hEH)
  have hM : IsPComponent 2 ((J.map π).subgroupOf (H.map π)) :=
    isPComponent_subgroupOf_of_le hKH hKbar
  set ψ : ↥H →* ↥(H.map π) := π.subgroupMap H with hψdef
  have hψsurj : Function.Surjective ψ := π.subgroupMap_surjective H
  have hψker : ¬ 2 ∣ Nat.card ψ.ker := OddQuot.not_two_dvd_card_ker_subgroupMap π hker H
  obtain ⟨-, hlift, hiso'⟩ :=
    CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection ψ hψsurj hψker
  obtain ⟨hJ₀, hJ₀map⟩ := hlift _ hM
  set J₀ : Subgroup ↥H := Subgroup.closure {x : ↥H |
    x ∈ ((J.map π).subgroupOf (H.map π)).comap ψ ∧ ∃ k : ℕ, orderOf x = 2 ^ k} with hJ₀def
  have hmemJ₀ : ∀ x ∈ J₀, π (x : G) ∈ J.map π := by
    intro x hx
    have hx' : ψ x ∈ J₀.map ψ := Subgroup.mem_map_of_mem ψ hx
    rw [hJ₀map] at hx'
    exact hx'
  refine ⟨J₀.map H.subtype, Subgroup.map_subtype_le J₀, ?_, ?_, ?_, ?_⟩
  · change IsPComponent 2 ((J₀.map H.subtype).comap H.subtype)
    rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    exact hJ₀
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨e, heE, hex⟩ := Subgroup.mem_map.1 (hKE (hmemJ₀ x hx))
    have hmem : e⁻¹ * (x : G) ∈ O := by
      rw [← QuotientGroup.eq]
      exact hex
    have hmemH : e⁻¹ * (x : G) ∈ H := H.mul_mem (H.inv_mem (hEH heE)) x.2
    have := Subgroup.mul_mem_sup heE (Subgroup.mem_inf.2 ⟨hmem, hmemH⟩)
    simpa using this
  · intro x hx hx2
    obtain ⟨hxJ, hxH⟩ := hx
    obtain ⟨j, hj⟩ := hx2
    refine ⟨⟨x, hxH⟩, Subgroup.subset_closure ⟨?_, ?_⟩, rfl⟩
    · exact Subgroup.mem_map_of_mem π hxJ
    · obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hj)
      exact ⟨k, by rw [Subgroup.orderOf_mk]; exact hk⟩
  · obtain ⟨q₁⟩ := nonempty_quotPPrimeCore_equiv
      (J₀.equivMapOfInjective H.subtype H.subtype_injective).symm
    obtain ⟨q₂, -⟩ := hiso' J₀ hJ₀
    obtain ⟨q₃⟩ := nonempty_quotPPrimeCore_equiv (MulEquiv.subgroupCongr hJ₀map)
    obtain ⟨q₄⟩ := nonempty_quotPPrimeCore_equiv (Subgroup.subgroupOfEquivOfLe hKH)
    obtain ⟨q₅, -⟩ := hiso J hJ
    exact ⟨q₁.trans (q₂.trans (q₃.trans (q₄.trans q₅.symm)))⟩

theorem exists_isPComponent_inf_of_covered {X : Type*} [Group X] [Finite X]
    {C H O E J : Subgroup X} (hOC : O ≤ C) (hCn : C ≤ normalizer (O : Set X))
    (hOodd : Odd (Nat.card O)) (hEC : E ≤ C) (hEH : E ≤ H) (hJC : J ≤ C)
    (hJ : IsPComponent 2 (J.subgroupOf C)) (hcov : J ≤ E ⊔ O) :
    ∃ J' : Subgroup X, J' ≤ C ⊓ H ∧ IsPComponent 2 (J'.subgroupOf (C ⊓ H)) ∧
      J' ≤ E ⊔ (O ⊓ H) ∧ (∀ x ∈ J ⊓ H, (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ J') ∧
      Nonempty (↥J' ⧸ pPrimeCore 2 ↥J' ≃* ↥J ⧸ pPrimeCore 2 ↥J) := by
  have hOn : (O.subgroupOf C).Normal := (normal_subgroupOf_iff_le_normalizer hOC).2 hCn
  have hOoddC : Odd (Nat.card (O.subgroupOf C)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOC).toEquiv]
    exact hOodd
  have hcovC : J.subgroupOf C ≤ E.subgroupOf C ⊔ O.subgroupOf C := by
    rw [← Subgroup.subgroupOf_sup hEC hOC]
    exact Subgroup.subgroupOf_mono C hcov
  obtain ⟨J₁, h1, h2, h3, h4, h5⟩ := exists_isPComponent_of_odd_quotient hOoddC
    (Subgroup.subgroupOf_mono C hEH) hJ hcovC
  have hHC : (H.subgroupOf C).map C.subtype = C ⊓ H := by
    rw [Subgroup.subgroupOf_map_subtype, inf_comm]
  refine ⟨J₁.map C.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hHC]
    exact Subgroup.map_mono h1
  · have := (isPComponent_subgroupOf_map_iff 2 C.subtype C.subtype_injective h1).2 h2
    rwa [hHC] at this
  · have h6 := Subgroup.map_mono (f := C.subtype) h3
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hEC,
      Subgroup.map_inf_eq _ _ _ C.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hOC,
      Subgroup.subgroupOf_map_subtype] at h6
    refine h6.trans (sup_le_sup_left ?_ E)
    exact inf_le_inf_left O inf_le_left
  · intro x hx hx2
    obtain ⟨hxJ, hxH⟩ := hx
    obtain ⟨j, hj⟩ := hx2
    exact ⟨⟨x, hJC hxJ⟩, h4 ⟨x, hJC hxJ⟩ (Subgroup.mem_inf.2 ⟨hxJ, hxH⟩)
      ⟨j, Subtype.ext (by simpa using hj)⟩, rfl⟩
  · obtain ⟨q₁⟩ := nonempty_quotPPrimeCore_equiv
      (J₁.equivMapOfInjective C.subtype C.subtype_injective).symm
    obtain ⟨q₂⟩ := nonempty_quotPPrimeCore_equiv (Subgroup.subgroupOfEquivOfLe hJC)
    exact ⟨q₁.trans (h5.some.trans q₂)⟩

end CFSG.OddStandard.Solomon75
