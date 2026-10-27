module

public import CFSG.GH74.GLS.Basic
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreQuotient
import CFSG.LocalAnalysis.ComponentInitial.SolvableCoreComponents

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

theorem subsec_isPComponent_two {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (hL : IsComponent L) : IsPComponent 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 2 hL ?_
  have hodd : Odd (Nat.card ↥(pPrimeCore 2 X)) :=
    Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := X))
  exact CFSG.LocalAnalysis.ComponentInitial.not_le_of_isComponent_of_isSolvable hL
    (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)

theorem subsec_le_pPrimeCoreOf_of_odd {X : Type*} [Group X] {N L : Subgroup X} (hNL : N ≤ L)
    (hnorm : L ≤ normalizer (N : Set X)) (hodd : Odd (Nat.card ↥N)) :
    N ≤ pPrimeCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnormal : (N.subgroupOf L).Normal := (normal_subgroupOf_iff_le_normalizer hNL).2 hnorm
  have hcop : Nat.Coprime 2 (Nat.card ↥(N.subgroupOf L)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNL).toEquiv]
    exact Nat.coprime_two_left.2 hodd
  have hle : N.subgroupOf L ≤ pPrimeCore 2 ↥L := le_sSup ⟨hnormal, hcop⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hNL]
  exact Subgroup.map_mono hle

theorem subsec_normalizer_le_normalizer_pPrimeCoreOf {X : Type*} [Group X] (L : Subgroup X) :
    normalizer (L : Set X) ≤ normalizer ((pPrimeCoreOf 2 L : Subgroup X) : Set X) := by
  have key : ∀ g ∈ normalizer (L : Set X), ∀ x ∈ pPrimeCoreOf 2 L,
      g * x * g⁻¹ ∈ pPrimeCoreOf 2 L := by
    intro g hg x hx
    obtain ⟨y, hy, rfl⟩ := hx
    let φ : L ≃* L := L.normalizerMonoidHom ⟨g, hg⟩
    have hfix := Subgroup.characteristic_iff_map_eq.mp
      (pPrimeCore_characteristic (p := 2) (G := ↥L)) φ
    have hyK : φ y ∈ pPrimeCore 2 ↥L := by
      rw [← hfix]
      exact Subgroup.mem_map_of_mem _ hy
    refine Subgroup.mem_map.mpr ⟨φ y, hyK, ?_⟩
    exact L.normalizerMonoidHom_apply_apply_coe ⟨g, hg⟩ y
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key g hg x
  · intro hx
    have := key g⁻¹ (inv_mem hg) _ hx
    simpa [mul_assoc] using this

theorem subsec_pPrimeCoreOf_map {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Injective f) (K : Subgroup X) :
    pPrimeCoreOf 2 (K.map f) = (pPrimeCoreOf 2 K).map f := by
  unfold pPrimeCoreOf
  let ψ : K ≃* K.map f := K.equivMapOfInjective f hf
  rw [← pPrimeCore_map_iso 2 ψ, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem subsec_map_mem_centralizerSection {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Injective f) (K : Subgroup X) {x : X}
    (hx : x ∈ centralizerSection K (pPrimeCoreOf 2 K)) :
    f x ∈ centralizerSection (K.map f) (pPrimeCoreOf 2 (K.map f)) := by
  obtain ⟨h1, h2, h3⟩ := hx
  rw [subsec_pPrimeCoreOf_map f hf K]
  refine ⟨Subgroup.le_normalizer_map f (Subgroup.mem_map_of_mem f h1),
    Subgroup.le_normalizer_map f (Subgroup.mem_map_of_mem f h2), ?_⟩
  rintro _ ⟨k, hk, rfl⟩
  rw [← map_commutatorElement]
  exact Subgroup.mem_map_of_mem f (h3 k hk)

section Lift

variable {X B : Type} [Group X] [Finite X] [Group B] [Finite B]

theorem subsec_mem_normalizer_of_map (π : X →* B) (hπ : Function.Surjective π)
    (hker : ¬ 2 ∣ Nat.card π.ker) {L : Subgroup X} (hL : IsPComponent 2 L) {x : X}
    (hx : π x ∈ normalizer ((L.map π : Subgroup B) : Set B)) : x ∈ normalizer (L : Set X) := by
  have hbij :=
    (ComponentClassification.CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection
      (p := 2) π hπ hker).1
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change L.map (MulAut.conj x).toMonoidHom = L
  rw [ComponentClassification.UnbalancedLayer.map_conj_eq_conjugate]
  refine hbij.injOn
    (ComponentClassification.UnbalancedLayer.isPComponent_conjugate hL x⁻¹) hL ?_
  rw [ComponentClassification.UnbalancedLayer.map_conjugate, map_inv]
  exact ComponentClassification.UnbalancedLayer.conjugate_eq_of_mem_normalizer (inv_mem hx)

theorem subsec_lift_pcomp (π : X →* B) (hπ : Function.Surjective π)
    (hodd : Odd (Nat.card π.ker)) {J : Subgroup B} (hJ : IsComponent J) :
    ∃ L : Subgroup X, IsPComponent 2 L ∧ L.map π = J ∧
      Nonempty ((↥L ⧸ pPrimeCore 2 ↥L) ≃* (↥J ⧸ pPrimeCore 2 ↥J)) ∧
      ∀ x : X, π x ∈ centralizer (J : Set B) → x ∈ centralizerSection L (pPrimeCoreOf 2 L) := by
  have hker : ¬ 2 ∣ Nat.card π.ker := by
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact hodd
  obtain ⟨hbij, -, hquot⟩ :=
    ComponentClassification.CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection
      (p := 2) π hπ hker
  obtain ⟨L, hL, hLJ⟩ := hbij.surjOn (subsec_isPComponent_two hJ)
  refine ⟨L, hL, hLJ, ?_, ?_⟩
  · obtain ⟨e, -⟩ := hquot L hL
    subst hLJ
    exact ⟨e⟩
  · intro x hx
    have hxN : x ∈ normalizer (L : Set X) := by
      refine subsec_mem_normalizer_of_map π hπ hker hL ?_
      rw [show (L.map π : Subgroup B) = J from hLJ]
      exact Subgroup.centralizer_le_normalizer _ hx
    refine ⟨hxN, subsec_normalizer_le_normalizer_pPrimeCoreOf L hxN, fun k hk => ?_⟩
    have hkx : ⁅k, x⁆ ∈ L := by
      have h1 : ⁅k, x⁆ = k * (x * k⁻¹ * x⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [h1]
      exact L.mul_mem hk ((Subgroup.mem_normalizer_iff.mp hxN _).mp (L.inv_mem hk))
    have hπ1 : π ⁅k, x⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      have hkJ : π k ∈ J := hLJ ▸ Subgroup.mem_map_of_mem π hk
      exact Subgroup.mem_centralizer_iff.mp hx _ hkJ
    have hnormN : L ≤ normalizer ((π.ker ⊓ L : Subgroup X) : Set X) := by
      refine Subgroup.le_normalizer_iff.2 fun l hl n hn => ⟨?_, ?_⟩
      · exact π.normal_ker.conj_mem n hn.1 l
      · exact L.mul_mem (L.mul_mem hl hn.2) (L.inv_mem hl)
    have hoddN : Odd (Nat.card ↥(π.ker ⊓ L)) :=
      Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le inf_le_left)
    exact subsec_le_pPrimeCoreOf_of_odd inf_le_right hnormN hoddN ⟨hπ1, hkx⟩

end Lift

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
