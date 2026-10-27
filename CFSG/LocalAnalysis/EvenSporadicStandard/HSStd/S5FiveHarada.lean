module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveGood
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Props

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup

variable {G : Type} [Group G]

abbrev HSFiveBar (G : Type) [Group G] (r : G) : Type :=
  ↥(centralizer ({r} : Set G)) ⧸ CFSG.oddCore ↥(centralizer ({r} : Set G))

@[expose] def fiveBar {r x : G} (hx : x ∈ centralizer ({r} : Set G)) : HSFiveBar G r :=
  QuotientGroup.mk ⟨x, hx⟩

@[expose] def fiveRK (r : G) : ↥(centralizer ({r} : Set G)) :=
  ⟨r, mem_centralizer_singleton_iff.2 rfl⟩

theorem fiveRK_mem_center (r : G) : fiveRK r ∈ center ↥(centralizer ({r} : Set G)) := by
  rw [mem_center_iff]
  intro g
  exact Subtype.ext (mem_centralizer_singleton_iff.1 g.2)

theorem orderOf_fiveRK {r : G} (hr5 : orderOf r = 5) : orderOf (fiveRK r) = 5 :=
  (Subgroup.orderOf_mk r _).trans hr5

theorem good_bar [Finite G] {r x : G} (hr5 : orderOf r = 5) (hxr : x ∈ centralizer ({r} : Set G))
    (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (e : ↥(centralizer ({x} : Set G) ⊓ centralizer ({r} : Set G)) ≃*
      Multiplicative (ZMod 2) × Multiplicative (ZMod 5) × Equiv.Perm (Fin 5)) :
    Nonempty (↥(centralizer ({fiveBar hxr} : Set (HSFiveBar G r))) ≃*
      Multiplicative (ZMod 2) × Equiv.Perm (Fin 5)) :=
  good_quot (K := ↥(centralizer ({r} : Set G))) (r := fiveRK r)
    (x := (⟨x, hxr⟩ : ↥(centralizer ({r} : Set G)))) (fiveRK_mem_center r)
    (orderOf_fiveRK hr5) (Subtype.ext hx2) (fun h => hx1 (congrArg Subtype.val h))
    ((centralizerSubtypeEquiv (centralizer ({r} : Set G)) ⟨x, hxr⟩).trans e)

theorem orderOf_fiveBar [Finite G] {r x : G} (hxr : x ∈ centralizer ({r} : Set G))
    (hx2 : x * x = 1) (hx1 : x ≠ 1) : orderOf (fiveBar hxr) = 2 := by
  have hsq : fiveBar hxr * fiveBar hxr = 1 := by
    unfold fiveBar
    rw [← QuotientGroup.mk_mul]
    have : (⟨x, hxr⟩ * ⟨x, hxr⟩ : ↥(centralizer ({r} : Set G))) = 1 := Subtype.ext hx2
    rw [this, QuotientGroup.mk_one]
  refine orderOf_eq_prime (by rw [pow_two]; exact hsq) ?_
  intro h
  exact hx1 (congrArg Subtype.val (eq_one_of_sq_mem_oddCore
    ((QuotientGroup.eq_one_iff _).1 h) (Subtype.ext hx2)))

variable [Finite G] {r t v : G}

theorem fusionZStar_bar_eq_bot (hr5 : orderOf r = 5) (htr : t ∈ centralizer ({r} : Set G))
    (hvr : v ∈ centralizer ({r} : Set G)) (ht2 : t * t = 1) (hv2 : v * v = 1) (ht1 : t ≠ 1)
    (hv1 : v ≠ 1) (htv : t * v = v * t) (hne : t ≠ v)
    (Ct : ↥(centralizer ({t} : Set G) ⊓ centralizer ({r} : Set G)) ≃*
      Multiplicative (ZMod 2) × Multiplicative (ZMod 5) × Equiv.Perm (Fin 5))
    (Cv : ↥(centralizer ({v} : Set G) ⊓ centralizer ({r} : Set G)) ≃*
      Multiplicative (ZMod 2) × Multiplicative (ZMod 5) × Equiv.Perm (Fin 5)) :
    Open.fusionZStar (HSFiveBar G r) = ⊥ := by
  obtain ⟨et⟩ := good_bar hr5 htr ht2 ht1 Ct
  obtain ⟨ev⟩ := good_bar hr5 hvr hv2 hv1 Cv
  exact fusionZStar_quot_eq_bot (K := ↥(centralizer ({r} : Set G))) (t := ⟨t, htr⟩)
    (v := ⟨v, hvr⟩) (Subtype.ext ht2) (Subtype.ext hv2) (fun h => ht1 (congrArg Subtype.val h))
    (fun h => hv1 (congrArg Subtype.val h)) (Subtype.ext htv)
    (fun h => hne (congrArg Subtype.val h)) et ev

theorem harada_bar (hH : Harada39One)
    (hK : CFSG.SectionRank.IsKGroupCat ↥(centralizer ({r} : Set G))) (hr5 : orderOf r = 5)
    (htr : t ∈ centralizer ({r} : Set G))
    (hvr : v ∈ centralizer ({r} : Set G)) (ht2 : t * t = 1) (hv2 : v * v = 1) (ht1 : t ≠ 1)
    (hv1 : v ≠ 1) (htv : t * v = v * t) (hne : t ≠ v)
    (Ct : ↥(centralizer ({t} : Set G) ⊓ centralizer ({r} : Set G)) ≃*
      Multiplicative (ZMod 2) × Multiplicative (ZMod 5) × Equiv.Perm (Fin 5))
    (Cv : ↥(centralizer ({v} : Set G) ⊓ centralizer ({r} : Set G)) ≃*
      Multiplicative (ZMod 2) × Multiplicative (ZMod 5) × Equiv.Perm (Fin 5)) :
    HaradaOneList (HSFiveBar G r) :=
  hH (HSFiveBar G r) (hK.quotient _)
    (fusionZStar_bar_eq_bot hr5 htr hvr ht2 hv2 ht1 hv1 htv hne Ct Cv)
    (fiveBar htr) (orderOf_fiveBar htr ht2 ht1) (good_bar hr5 htr ht2 ht1 Ct)

end CFSG.EvenSporadicStandard.HSStd

