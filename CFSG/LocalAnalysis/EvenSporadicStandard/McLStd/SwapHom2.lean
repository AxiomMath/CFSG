module

public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.ComponentSwap2
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Residual

public section

namespace CFSG.EvenSporadicStandard.McLStd

open Subgroup CFSG CFSG.ComponentClassification CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem exists_hom_of_swappedPair_corefree {L : Subgroup G} {t u : G} (ht2 : orderOf t = 2)
    (htu : t ∈ centralizer ({u} : Set G))
    (hcore : Open.componentClassificationOddCore ↥(centralizer ({u} : Set G)) = ⊥)
    (hD : ∀ x y : G, x ∈ centralizer ({t} : Set G) ⊓ centralizer ({u} : Set G) →
      y ∈ centralizer ({t} : Set G) ⊓ centralizer ({u} : Set G) →
      (∀ b ∈ centralizer ({u} : Set G) ⊓ L, x * b = b * x) →
      (∀ b ∈ centralizer ({u} : Set G) ⊓ L, y * b = b * y) → x * y = y * x)
    (hsw : SwappedPair L t u) :
    ∃ φ : centralizer ({u} : Set G) →* Multiplicative (ZMod 2), φ ⟨t, htu⟩ ≠ 1 := by
  obtain ⟨J, hJ, hJt, hKJ, -⟩ := hsw
  set H : Subgroup G := centralizer ({u} : Set G) with hH
  have hJH : J ≤ H := CFSG.Quasithin.le_of_mem_cComp hJ.1
  have hts : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  let t' : ↥H := ⟨t, htu⟩
  have ht't' : t' * t' = 1 := Subtype.ext (by simpa using hts)
  let A : Subgroup ↥H := J.subgroupOf H
  have hAmap : A.map H.subtype = J := Subgroup.map_subgroupOf_eq_of_le hJH
  have hA : TwoComponents.IsTwoComponent A := (I32.isTwoComponentIn_iff hJH).1 hJ
  have hĀ : IsComponent A :=
    (isComponent_iff_open _).2 (TwoComponents.ordinary_of_corefree hcore hA)
  have hAt : conjSub t' A = CFSG.conjugate A t' := (I32.conjugate_eq_map_conj ht't' A).symm
  have hA'map : (CFSG.conjugate A t').map H.subtype = CFSG.conjugate J t := by
    have h1 := I32.map_conjugate H.subtype A t'
    rw [hAmap] at h1
    exact h1
  have hne : conjSub t' A ≠ A := by
    intro h
    rw [hAt] at h
    apply hJt
    rw [← hA'map, h, hAmap]
  have hBH : centralizer ({u} : Set G) ⊓ L ≤ H := inf_le_left
  have hBle : (centralizer ({u} : Set G) ⊓ L).subgroupOf H ≤ A ⊔ conjSub t' A := by
    rw [hAt]
    intro b hb
    have hb' : (b : G) ∈ centralizer ({u} : Set G) ⊓ L := hb
    have hK : (b : G) ∈ (A ⊔ CFSG.conjugate A t').map H.subtype := by
      rw [Subgroup.map_sup, hAmap, hA'map, ← hKJ]
      exact le_layerClosure L u hb'
    obtain ⟨y, hy, hyb⟩ := hK
    have : y = b := Subtype.ext hyb
    rwa [← this]
  have hcomm : SwapCommuting t' A := by
    intro x y hx hy hxE hyE
    have hxy := hD (x : G) (y : G)
      ⟨mem_centralizer_singleton_iff.2 (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hx)),
        x.2⟩
      ⟨mem_centralizer_singleton_iff.2 (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hy)),
        y.2⟩
      (fun b hb => by
        have hbH : b ∈ H := hBH hb
        have := hxE ⟨b, hbH⟩ (hBle hb)
        exact congrArg Subtype.val this)
      (fun b hb => by
        have hbH : b ∈ H := hBH hb
        have := hyE ⟨b, hbH⟩ (hBle hb)
        exact congrArg Subtype.val this)
    exact Subtype.ext hxy
  exact exists_hom_of_swapped_component' ht't' hĀ hne hcomm

end CFSG.EvenSporadicStandard.McLStd
