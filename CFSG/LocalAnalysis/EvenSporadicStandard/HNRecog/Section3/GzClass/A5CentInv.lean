module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.A5CentBase
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.A5WrTwoInvolutions

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog
open Subgroup
open scoped Classical

private def sigmaC2 : Multiplicative (ZMod 2) := Multiplicative.ofAdd 1

private def swapW : A5WrTwo := ⟨1, sigmaC2⟩

private theorem coord_cases (q : Multiplicative (ZMod 2)) :
    q = 1 ∨ q = Multiplicative.ofAdd 1 := by
  rcases (show ∀ e : ZMod 2, e = 0 ∨ e = 1 by decide) (Multiplicative.toAdd q) with h | h
  · left
    rw [← ofAdd_toAdd q, h]
    rfl
  · right
    rw [← ofAdd_toAdd q, h]

private theorem sigmaC2_mul_self :
    (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := by decide

private theorem sigmaC2_ne_one : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide

private theorem swapW_mul_self : swapW * swapW = 1 := by
  apply RegularWreathProduct.ext
  · funext i
    simp [swapW, sigmaC2, RegularWreathProduct.mul_def]
  · simp [swapW, sigmaC2, RegularWreathProduct.mul_def, sigmaC2_mul_self]

private theorem swapW_sq : swapW ^ 2 = 1 := by
  rw [pow_two]
  exact swapW_mul_self

private theorem swapW_inv : swapW⁻¹ = swapW :=
  inv_eq_of_mul_eq_one_right swapW_mul_self

private theorem swapW_mul_baseEmb_mul_inv
    (p : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) :
    swapW * A5WrTwo.baseEmb p * swapW⁻¹ = A5WrTwo.baseEmb (p.2, p.1) := by
  have h := A5WrTwo.swap_mul_baseEmb_mul_inv p.1 p.2
  simpa [swapW, sigmaC2] using h

private def Kswap : Subgroup A5WrTwo := Subgroup.centralizer ({swapW} : Set A5WrTwo)

private def phiSwap : ↥Kswap →* Multiplicative (ZMod 2) :=
  (RegularWreathProduct.rightHom : A5WrTwo →* Multiplicative (ZMod 2)).comp Kswap.subtype

private theorem baseEmb_mem_Kswap_iff (p : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) :
    A5WrTwo.baseEmb p ∈ Kswap ↔ p.1 = p.2 := by
  constructor
  · intro hp
    have hcomm : A5WrTwo.baseEmb p * swapW = swapW * A5WrTwo.baseEmb p :=
      Subgroup.mem_centralizer_singleton_iff.mp hp
    have hconj : swapW * A5WrTwo.baseEmb p * swapW⁻¹ = A5WrTwo.baseEmb p := by
      rw [swapW_inv]
      calc swapW * A5WrTwo.baseEmb p * swapW
          = (A5WrTwo.baseEmb p * swapW) * swapW := by rw [hcomm]
        _ = A5WrTwo.baseEmb p * (swapW * swapW) := by group
        _ = A5WrTwo.baseEmb p := by rw [swapW_mul_self, mul_one]
    have h1 : A5WrTwo.baseEmb (p.2, p.1) = A5WrTwo.baseEmb p := by
      rw [← swapW_mul_baseEmb_mul_inv p]
      exact hconj
    have h2 : (p.2, p.1) = p := A5WrTwo.baseEmb_injective h1
    exact (Prod.ext_iff.mp h2).1.symm
  · intro hp
    show A5WrTwo.baseEmb p ∈ Subgroup.centralizer ({swapW} : Set A5WrTwo)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hconj : swapW * A5WrTwo.baseEmb p * swapW⁻¹ = A5WrTwo.baseEmb p := by
      rw [swapW_mul_baseEmb_mul_inv p]
      have hpair : (p.2, p.1) = p := by
        rw [Prod.ext_iff]
        exact ⟨hp.symm, hp⟩
      rw [hpair]
    calc A5WrTwo.baseEmb p * swapW
        = (swapW * A5WrTwo.baseEmb p * swapW⁻¹) * swapW := by rw [hconj]
      _ = swapW * A5WrTwo.baseEmb p := by group

private def diagSub : Subgroup (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) where
  carrier := {p | p.1 = p.2}
  mul_mem' := by
    intro a b ha hb
    show a.1 * b.1 = a.2 * b.2
    rw [ha, hb]
  one_mem' := rfl
  inv_mem' := by
    intro a ha
    show a.1⁻¹ = a.2⁻¹
    rw [ha]

private theorem natCard_A5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  norm_num

private noncomputable def diagSubEquivA5 : ↥diagSub ≃ alternatingGroup (Fin 5) where
  toFun p := p.val.1
  invFun g := ⟨(g, g), rfl⟩
  left_inv p := by
    apply Subtype.ext
    exact Prod.ext rfl p.property
  right_inv g := rfl

private theorem card_diagSub : Nat.card ↥diagSub = 60 := by
  rw [Nat.card_congr diagSubEquivA5, natCard_A5]

private theorem comap_baseEmb_Kswap : Kswap.comap A5WrTwo.baseEmb = diagSub := by
  ext p
  rw [Subgroup.mem_comap, baseEmb_mem_Kswap_iff]
  rfl

private theorem card_centralizer_swapW : Nat.card ↥Kswap = 120 := by
  have hker_eq : phiSwap.ker = (A5WrTwo.baseEmb.range).subgroupOf Kswap := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, A5WrTwo.range_baseEmb,
      A5WrTwo.commutator_eq_ker, MonoidHom.mem_ker]
    rfl
  have hker_inf : Nat.card ↥((A5WrTwo.baseEmb.range).subgroupOf Kswap) =
      Nat.card ↥(Kswap ⊓ A5WrTwo.baseEmb.range) := by
    have h := Subgroup.card_map_of_injective
      (K := (A5WrTwo.baseEmb.range).subgroupOf Kswap) Kswap.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype] at h
    rw [inf_comm] at h
    exact h.symm
  have hker_card : Nat.card ↥phiSwap.ker = 60 := by
    rw [hker_eq, hker_inf]
    have hmap : (Kswap.comap A5WrTwo.baseEmb).map A5WrTwo.baseEmb =
        Kswap ⊓ A5WrTwo.baseEmb.range := by
      rw [Subgroup.map_comap_eq, inf_comm]
    rw [← hmap, Subgroup.card_map_of_injective A5WrTwo.baseEmb_injective,
      comap_baseEmb_Kswap, card_diagSub]
  have hrange_top : phiSwap.range = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro q
    rcases coord_cases q with rfl | rfl
    · exact MonoidHom.mem_range.mpr ⟨1, map_one phiSwap⟩
    · have hmem : swapW ∈ Kswap := by
        show swapW ∈ Subgroup.centralizer ({swapW} : Set A5WrTwo)
        exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
      refine MonoidHom.mem_range.mpr ⟨⟨swapW, hmem⟩, ?_⟩
      show phiSwap ⟨swapW, hmem⟩ = sigmaC2
      simp [phiSwap, swapW, RegularWreathProduct.rightHom]
  have hrange : Nat.card ↥phiSwap.range = 2 := by
    rw [hrange_top, Subgroup.card_top]
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have h := Subgroup.card_ker_mul_card_range phiSwap
  rw [hker_card, hrange] at h
  rw [← h]

private noncomputable def conjCentralizerEquiv (b u : A5WrTwo) :
    ↥(Subgroup.centralizer ({b * u * b⁻¹} : Set A5WrTwo)) ≃
      ↥(Subgroup.centralizer ({u} : Set A5WrTwo)) where
  toFun k := ⟨b⁻¹ * k.val * b, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_centralizer_singleton_iff.mp k.2
    calc (b⁻¹ * k.val * b) * u
        = b⁻¹ * (k.val * (b * u * b⁻¹)) * b := by group
      _ = b⁻¹ * ((b * u * b⁻¹) * k.val) * b := by rw [h]
      _ = u * (b⁻¹ * k.val * b) := by group⟩
  invFun k := ⟨b * k.val * b⁻¹, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_centralizer_singleton_iff.mp k.2
    calc (b * k.val * b⁻¹) * (b * u * b⁻¹)
        = b * (k.val * u) * b⁻¹ := by group
      _ = b * (u * k.val) * b⁻¹ := by rw [h]
      _ = (b * u * b⁻¹) * (b * k.val * b⁻¹) := by group⟩
  left_inv k := by ext; group
  right_inv k := by ext; group

private theorem card_centralizer_conj (b u : A5WrTwo) :
    Nat.card ↥(Subgroup.centralizer ({b * u * b⁻¹} : Set A5WrTwo)) =
      Nat.card ↥(Subgroup.centralizer ({u} : Set A5WrTwo)) :=
  Nat.card_congr (conjCentralizerEquiv b u)

private def a5CentralizerCard (x : alternatingGroup (Fin 5)) : ℕ :=
  ((Finset.univ : Finset (alternatingGroup (Fin 5))).filter fun y => y * x = x * y).card

private theorem a5CentralizerCard_eq_four :
    ∀ x : alternatingGroup (Fin 5), x ≠ 1 → x ^ 2 = 1 → a5CentralizerCard x = 4 := by
  decide +kernel

private theorem card_centralizer_A5_involution {x : alternatingGroup (Fin 5)} (hx1 : x ≠ 1)
    (hx2 : x ^ 2 = 1) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))) = 4 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h := a5CentralizerCard_eq_four x hx1 hx2
  rw [a5CentralizerCard] at h
  rw [← h]
  congr 1
  ext y
  simp [Subgroup.mem_centralizer_singleton_iff]

private theorem card_centralizer_one_A5 :
    Nat.card ↥(Subgroup.centralizer ({(1 : alternatingGroup (Fin 5))} : Set _)) = 60 := by
  have htop : Subgroup.centralizer ({(1 : alternatingGroup (Fin 5))} : Set _) = ⊤ := by
    rw [Subgroup.centralizer_eq_top_iff_subset, Set.singleton_subset_iff]
    exact Subgroup.mem_center_iff.mpr (fun g => by simp)
  rw [htop, Subgroup.card_top, natCard_A5]

private theorem alternating_involution_conj :
    ∀ g g' : alternatingGroup (Fin 5), g ^ 2 = 1 → g ≠ 1 → g' ^ 2 = 1 → g' ≠ 1 →
      ∃ c : alternatingGroup (Fin 5), c * g * c⁻¹ = g' := by
  decide +kernel

theorem card_centralizer_outer_involution {u : A5WrTwo} (hu : u ∉ commutator A5WrTwo)
    (hu2 : u ^ 2 = 1) :
    Nat.card ↥(Subgroup.centralizer ({u} : Set A5WrTwo)) = 120 := by
  have hs_notMem : swapW ∉ commutator A5WrTwo := by
    rw [A5WrTwo.commutator_eq_ker]
    intro h
    exact sigmaC2_ne_one (by simpa [swapW, sigmaC2, RegularWreathProduct.rightHom] using h)
  obtain ⟨b, _hb, hbu⟩ := A5WrTwo.exists_conj_of_outer_involutions hu hs_notMem hu2 swapW_sq
  have hcard := card_centralizer_conj b u
  rw [hbu] at hcard
  rw [← hcard]
  exact card_centralizer_swapW

theorem baseInvolution_cases {u : A5WrTwo} (hu : u ∈ commutator A5WrTwo) (hu2 : u ^ 2 = 1)
    (hu1 : u ≠ 1) :
    (∃ x : alternatingGroup (Fin 5), x ^ 2 = 1 ∧ x ≠ 1 ∧
        (u = A5WrTwo.baseEmb (x, 1) ∨ u = A5WrTwo.baseEmb (1, x)) ∧
        Nat.card ↥(Subgroup.centralizer ({u} : Set A5WrTwo)) = 240) ∨
    (∃ x y : alternatingGroup (Fin 5), x ^ 2 = 1 ∧ y ^ 2 = 1 ∧ x ≠ 1 ∧ y ≠ 1 ∧
        u = A5WrTwo.baseEmb (x, y) ∧
        Nat.card ↥(Subgroup.centralizer ({u} : Set A5WrTwo)) = 32) := by
  have hu' : u ∈ A5WrTwo.baseEmb.range := by rwa [A5WrTwo.range_baseEmb]
  obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp hu'
  have hpe : A5WrTwo.baseEmb (p.1, p.2) = u := by simpa using hp
  have hp2 : p ^ 2 = 1 := by
    apply A5WrTwo.baseEmb_injective
    rw [map_pow, hp, hu2, map_one]
  have hp1sq : p.1 ^ 2 = 1 := (Prod.ext_iff.mp hp2).1
  have hp2sq : p.2 ^ 2 = 1 := (Prod.ext_iff.mp hp2).2
  have hp_ne : p ≠ 1 := by
    intro h
    exact hu1 (by rw [← hp, h, map_one])
  by_cases hy : p.2 = 1
  · have hx1 : p.1 ≠ 1 := by
      intro hx
      exact hp_ne (Prod.ext hx hy)
    have hnotconj : ¬ IsConj p.1 p.2 := by
      rw [hy]
      exact fun h => hx1 (isConj_one_left.mp h)
    have hcard := card_centralizer_baseEmb_of_not_isConj (x := p.1) (y := p.2) hnotconj
    have hcu : Nat.card ↥(Subgroup.centralizer ({u} : Set A5WrTwo)) =
        Nat.card ↥(Subgroup.centralizer ({p.1} : Set (alternatingGroup (Fin 5)))) *
          Nat.card ↥(Subgroup.centralizer ({p.2} : Set (alternatingGroup (Fin 5)))) := by
      rw [← hpe]
      exact hcard
    have hc1 : Nat.card ↥(Subgroup.centralizer ({p.1} : Set (alternatingGroup (Fin 5)))) = 4 :=
      card_centralizer_A5_involution hx1 hp1sq
    have hc2 : Nat.card ↥(Subgroup.centralizer ({p.2} : Set (alternatingGroup (Fin 5)))) = 60 := by
      rw [hy]
      exact card_centralizer_one_A5
    refine Or.inl ⟨p.1, hp1sq, hx1, Or.inl ?_, ?_⟩
    · rw [← hpe, hy]
    · rw [hcu, hc1, hc2]
  · by_cases hx : p.1 = 1
    · have hy1 : p.2 ≠ 1 := by
        intro h
        exact hp_ne (Prod.ext hx h)
      have hnotconj : ¬ IsConj p.1 p.2 := by
        rw [hx]
        exact fun h => hy1 (isConj_one_right.mp h)
      have hcard := card_centralizer_baseEmb_of_not_isConj (x := p.1) (y := p.2) hnotconj
      have hcu : Nat.card ↥(Subgroup.centralizer ({u} : Set A5WrTwo)) =
          Nat.card ↥(Subgroup.centralizer ({p.1} : Set (alternatingGroup (Fin 5)))) *
            Nat.card ↥(Subgroup.centralizer ({p.2} : Set (alternatingGroup (Fin 5)))) := by
        rw [← hpe]
        exact hcard
      have hc1 : Nat.card ↥(Subgroup.centralizer ({p.1} : Set (alternatingGroup (Fin 5)))) =
          60 := by
        rw [hx]
        exact card_centralizer_one_A5
      have hc2 : Nat.card ↥(Subgroup.centralizer ({p.2} : Set (alternatingGroup (Fin 5)))) = 4 :=
        card_centralizer_A5_involution hy1 hp2sq
      refine Or.inl ⟨p.2, hp2sq, hy1, Or.inr ?_, ?_⟩
      · rw [← hpe, hx]
      · rw [hcu, hc1, hc2]
    · have hconj : IsConj p.1 p.2 :=
        isConj_iff.mpr (alternating_involution_conj p.1 p.2 hp1sq hx hp2sq hy)
      have hcard := card_centralizer_baseEmb_of_isConj (x := p.1) (y := p.2) hconj
      have hcu : Nat.card ↥(Subgroup.centralizer ({u} : Set A5WrTwo)) =
          Nat.card ↥(Subgroup.centralizer ({p.1} : Set (alternatingGroup (Fin 5)))) *
            Nat.card ↥(Subgroup.centralizer ({p.2} : Set (alternatingGroup (Fin 5)))) * 2 := by
        rw [← hpe]
        exact hcard
      have hc1 : Nat.card ↥(Subgroup.centralizer ({p.1} : Set (alternatingGroup (Fin 5)))) = 4 :=
        card_centralizer_A5_involution hx hp1sq
      have hc2 : Nat.card ↥(Subgroup.centralizer ({p.2} : Set (alternatingGroup (Fin 5)))) = 4 :=
        card_centralizer_A5_involution hy hp2sq
      refine Or.inr ⟨p.1, p.2, hp1sq, hp2sq, hx, hy, hpe.symm, ?_⟩
      · rw [hcu, hc1, hc2]

end CFSG.EvenSporadicStandard.HNRecog.Section3
