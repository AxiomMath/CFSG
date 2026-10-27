module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CaseOne
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.InputWreath
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Provenance
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Wreath

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G}

theorem Setting.card_centralizer (hs : Setting G L z) :
    Nat.card (centralizer ({z} : Set G)) = 2 ^ (10 + 1) * 239085 := by
  have e := mulEquivProdSup hs.z_central hs.disjoint
  obtain ⟨e'⟩ := hs.sporadic
  have hLc : Nat.card L = 244823040 := by
    rw [Nat.card_congr e'.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M24
  rw [hs.centralizer_eq, ← Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zpowers,
    hs.order_z, hLc]
  norm_num

theorem Setting.false_of_wreathData (hs : Setting G L z)
    (hW : WreathData z) : False := by
  have := hs.simple
  obtain ⟨R, hR, hcomm, hinter⟩ := hW
  exact false_of_wreath (hom_units_eq_one_of_simple hs.nonabelian) hs.order_z (k := 10)
    (m := 239085) ⟨119542, by norm_num⟩ hs.card_centralizer hR hcomm hinter

theorem m24_not_standard_of_wreath
    (hA : Ega81HypAZ2A8K) (hW : Ega81Wreath) (h : StdHyp G L) : ¬ IsSporadic L .M24 := by
  intro hL
  have := h.simple
  have hS := fun S => card_sylow_eq_two_of_M24 h hL S
  have heven : Even (Nat.card G) :=
    even_iff_two_dvd.2 (dvd_trans (even_iff_two_dvd.1 h.standard.2.1)
      (Subgroup.card_subgroup_dvd_card _))
  have hcase : ∀ z : G, z ∈ centralizer (L : Set G) → orderOf z = 2 →
      centralizer ({z} : Set G) = L ⊔ zpowers z ∧ CaseTwo L z := by
    intro z hz hz2
    have hset := setting_of_stdHyp h hL hz hz2
    exact ⟨hset.centralizer_eq, fun B hBL hBc hBs hB64 =>
      hset.not_normalizer_le_centralizer hBL hBc hBs hB64⟩
  obtain ⟨z, hz, hz2, hWz⟩ := hW hA G L h.kLocalSections
    (fusionZStar_eq_bot_of_simple h.nonabelian heven) h.standard hL h.cyclicSylow hS hcase
  exact (setting_of_stdHyp h hL hz hz2).false_of_wreathData hWz

end CFSG.EvenSporadicStandard.M24Std
