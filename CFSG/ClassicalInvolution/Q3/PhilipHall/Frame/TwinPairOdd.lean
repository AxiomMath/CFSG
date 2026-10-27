module

public import CFSG.ClassicalInvolution.Q3.TL4OddKey

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Balance
open CFSG.Assembly.Dichotomy (involutionOddCore)

namespace TwinPairOdd

variable {G : Type} [Group G] [Finite G]

theorem oddCoreIn_inf_centralizer_eq_bot {u t : G} (htu : t ∈ Subgroup.centralizer ({u} : Set G))
    (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (h1 : oddCoreImg (Subgroup.centralizer ({u} : Set G)) = ⊥)
    (hL : ∀ L : Subgroup (OddQuot u), CFSG.IsComponent L →
      oddQuotMk u ⟨t, htu⟩ ∈ Subgroup.normalizer (L : Set (OddQuot u)) →
      (∃ y ∈ L, oddQuotMk u ⟨t, htu⟩ * y ≠ y * oddQuotMk u ⟨t, htu⟩) →
      Q3NM.AutOddFreeOn ↥L (TL4.IsInducedAut L (oddQuotMk u ⟨t, htu⟩))) :
    oddCoreIn (Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer ({t} : Set G)) = ⊥ := by
  set C := Subgroup.centralizer ({u} : Set G) with hC
  set X := C ⊓ Subgroup.centralizer ({t} : Set G) with hX
  set D := oddCoreIn X with hD
  have hDX : D ≤ X := oddCoreIn_le X
  have hDC : D ≤ C := hDX.trans inf_le_left
  have hCcore : componentClassificationOddCore ↥C = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).mp h1
  have hBt2 : (⟨t, htu⟩ : C) * ⟨t, htu⟩ = 1 := Subtype.ext ht2
  have hbt2 : oddQuotMk u ⟨t, htu⟩ * oddQuotMk u ⟨t, htu⟩ = 1 := by
    rw [← map_mul, hBt2, map_one]
  have hbt1 : oddQuotMk u ⟨t, htu⟩ ≠ 1 := by
    intro h
    have hmem : (⟨t, htu⟩ : C) ∈ componentClassificationOddCore C :=
      (QuotientGroup.eq_one_iff _).mp h
    have hord : orderOf (⟨t, htu⟩ : C) = 2 :=
      orderOf_eq_prime (by rw [sq]; exact hBt2) (fun h' => ht1 (congrArg Subtype.val h'))
    have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
    rw [hord] at hdvd
    exact (Nat.not_even_iff_odd.mpr (CFSG.ComponentClassification.OddCore.odd_card C))
      (even_iff_two_dvd.mpr hdvd)
  have hbot := TL4.oddCent_eq_bot_of_components (pPrimeCore_oddQuot_eq_bot u) hbt2 hbt1 hL
  set S : Subgroup (OddQuot u) := (D.subgroupOf C).map (oddQuotMk u) with hS
  have hSC : S ≤ Subgroup.centralizer ({oddQuotMk u ⟨t, htu⟩} : Set (OddQuot u)) := by
    rintro _ ⟨d, hd, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hdt : (d : G) * t = t * d :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (Subgroup.mem_inf.mp (hDX (Subgroup.mem_subgroupOf.mp hd))).2
    have e : d * ⟨t, htu⟩ = ⟨t, htu⟩ * d := Subtype.ext hdt
    rw [← map_mul, e, map_mul]
  have hnorm : ∀ c ∈ Subgroup.centralizer ({oddQuotMk u ⟨t, htu⟩} : Set (OddQuot u)),
      ∀ m ∈ S, c * m * c⁻¹ ∈ S := by
    intro c hc m hm
    obtain ⟨x, hxt, rfl⟩ :=
      TL4.exists_lift_of_commute htu ht2 (Subgroup.mem_centralizer_singleton_iff.mp hc)
    obtain ⟨d, hd, rfl⟩ := hm
    have hxX : (x : G) ∈ X :=
      Subgroup.mem_inf.mpr ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr hxt⟩
    exact ⟨x * d * x⁻¹,
      Subgroup.mem_subgroupOf.mpr (conj_mem_oddCoreIn hxX (Subgroup.mem_subgroupOf.mp hd)),
      by simp only [map_mul, map_inv]⟩
  have hodd : Odd (Nat.card S) := by
    have h1' : Nat.card S ∣ Nat.card (D.subgroupOf C) := Subgroup.card_map_dvd _ _
    have h2' : Nat.card (D.subgroupOf C) = Nat.card D :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv
    rw [h2'] at h1'
    exact (odd_card_oddCoreIn X).of_dvd_nat h1'
  have hSle : S ≤ involutionOddCore (oddQuotMk u ⟨t, htu⟩) :=
    CFSG.ClassicalInvolution.Q3.TC.le_oddCoreImg_of_normalizes hSC hnorm hodd
  rw [hbot] at hSle
  rw [eq_bot_iff]
  intro d hd
  have hdC : (d : G) ∈ C := (Subgroup.mem_inf.mp (hDX hd)).1
  have h3 : oddQuotMk u ⟨d, hdC⟩ ∈ S := ⟨⟨d, hdC⟩, Subgroup.mem_subgroupOf.mpr hd, rfl⟩
  have h3' : oddQuotMk u ⟨d, hdC⟩ ∈ (⊥ : Subgroup (OddQuot u)) := hSle h3
  rw [Subgroup.mem_bot] at h3'
  have h4 : (⟨d, hdC⟩ : C) ∈ componentClassificationOddCore C :=
    (QuotientGroup.eq_one_iff _).mp h3'
  rw [hCcore, Subgroup.mem_bot] at h4
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val h4

theorem oddCoreIn_inf_centralizer_of_normal_eq_bot {u t : G}
    (htu : t ∈ Subgroup.centralizer ({u} : Set G)) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (h1 : oddCoreImg (Subgroup.centralizer ({u} : Set G)) = ⊥)
    (hL : ∀ L : Subgroup (OddQuot u), CFSG.IsComponent L →
      oddQuotMk u ⟨t, htu⟩ ∈ Subgroup.normalizer (L : Set (OddQuot u)) →
      (∃ y ∈ L, oddQuotMk u ⟨t, htu⟩ * y ≠ y * oddQuotMk u ⟨t, htu⟩) →
      Q3NM.AutOddFreeOn ↥L (TL4.IsInducedAut L (oddQuotMk u ⟨t, htu⟩)))
    {X : Subgroup G} (hXt : X ≤ Subgroup.centralizer ({t} : Set G))
    (hXn : (X.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal) :
    oddCoreIn (X ⊓ Subgroup.centralizer ({u} : Set G)) = ⊥ := by
  set C := Subgroup.centralizer ({u} : Set G) with hC
  set Ct := Subgroup.centralizer ({t} : Set G) with hCt
  have hYX : X ⊓ C ≤ C ⊓ Ct := by
    intro y hy
    obtain ⟨hyX, hyC⟩ := Subgroup.mem_inf.mp hy
    exact Subgroup.mem_inf.mpr ⟨hyC, hXt hyX⟩
  have hnorm : ((X ⊓ C).subgroupOf (C ⊓ Ct)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : G) ∈ X ⊓ C := Subgroup.mem_subgroupOf.mp hn
    have hnX : (n : G) ∈ X := (Subgroup.mem_inf.mp hn').1
    have hnC : (n : G) ∈ C := (Subgroup.mem_inf.mp hn').2
    have hgC : (g : G) ∈ C := (Subgroup.mem_inf.mp g.2).1
    have hgCt : (g : G) ∈ Ct := (Subgroup.mem_inf.mp g.2).2
    have hconjX : (g : G) * (n : G) * (g : G)⁻¹ ∈ X := by
      have h := hXn.conj_mem ⟨(n : G), hXt hnX⟩ (Subgroup.mem_subgroupOf.mpr hnX) ⟨(g : G), hgCt⟩
      exact Subgroup.mem_subgroupOf.mp h
    exact Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_inf.mpr ⟨hconjX, C.mul_mem (C.mul_mem hgC hnC) (C.inv_mem hgC)⟩)
  have hsub : IsSubnormal (X ⊓ C) (C ⊓ Ct) := isSubnormal_of_normal_subgroupOf hYX hnorm
  have h0 : oddCoreIn (X ⊓ C) ≤ oddCoreIn (C ⊓ Ct) := oddCoreIn_le_of_isSubnormal hsub
  have h2 : oddCoreIn (C ⊓ Ct) = ⊥ := oddCoreIn_inf_centralizer_eq_bot htu ht2 ht1 h1 hL
  exact eq_bot_iff.mpr (h0.trans h2.le)

theorem oddCoreIn_eq_bot_of_isSubnormal {u t : G}
    (htu : t ∈ Subgroup.centralizer ({u} : Set G)) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (h1 : oddCoreImg (Subgroup.centralizer ({u} : Set G)) = ⊥)
    (hL : ∀ L : Subgroup (OddQuot u), CFSG.IsComponent L →
      oddQuotMk u ⟨t, htu⟩ ∈ Subgroup.normalizer (L : Set (OddQuot u)) →
      (∃ y ∈ L, oddQuotMk u ⟨t, htu⟩ * y ≠ y * oddQuotMk u ⟨t, htu⟩) →
      Q3NM.AutOddFreeOn ↥L (TL4.IsInducedAut L (oddQuotMk u ⟨t, htu⟩)))
    {X : Subgroup G} (hXt : X ≤ Subgroup.centralizer ({t} : Set G))
    (hXn : (X.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal)
    {L : Subgroup G} (_hLX : L ≤ X ⊓ Subgroup.centralizer ({u} : Set G))
    (hsub : IsSubnormal L (X ⊓ Subgroup.centralizer ({u} : Set G))) :
    oddCoreIn L = ⊥ ∧ classicalInvolutionOddCore ↥L = ⊥ := by
  have h0 : oddCoreIn L ≤ oddCoreIn (X ⊓ Subgroup.centralizer ({u} : Set G)) :=
    oddCoreIn_le_of_isSubnormal hsub
  have h2 : oddCoreIn (X ⊓ Subgroup.centralizer ({u} : Set G)) = ⊥ :=
    oddCoreIn_inf_centralizer_of_normal_eq_bot htu ht2 ht1 h1 hL hXt hXn
  have hL0 : oddCoreIn L = ⊥ := eq_bot_iff.mpr (h0.trans h2.le)
  refine ⟨hL0, ?_⟩
  have h3 : (componentClassificationOddCore ↥L).map L.subtype = ⊥ := hL0
  exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp h3

end TwinPairOdd

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
