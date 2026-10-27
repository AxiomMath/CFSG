module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR8Kind
import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup

section Abstract

variable {Y : Type} [Group Y] [Finite Y]

theorem swapAlternative_of_neighbourRowOmega (hO : pPrimeCore 2 Y = ⊥) {s : Y}
    (hs : orderOf s = 2) {D : Subgroup Y}
    (hD : CFSG.Open.IsComponentOf D (centralizer ({s} : Set Y)))
    (hsyl : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ centralizer (D : Set Y) → Nat.card U ≤ 2)
    (hrow : NeighbourRowOmega s D .swap) (m f : ℕ) :
    ∃ Kc : Subgroup Y, IsComponent Kc ∧ OmegaNeighbourAlternative s D Kc m f ∧
      Kc.map (MulAut.conj s).toMonoidHom ≠ Kc := by
  have hs2 : s ^ 2 = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
  have hDs : D ≤ centralizer ({s} : Set Y) := hD.1
  have hDc : IsComponent (D.subgroupOf (centralizer ({s} : Set Y))) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hDs).1
      ((CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).2 hD)
  obtain ⟨-, Kc, hKc, -, hDKK, -, -, -, hswap⟩ :=
    CFSG.SeitzReduction.exists_isComponent_orbit_of_isComponent_centralizer hO hs2 hDs hDc
  have hDperf : ⁅D, D⁆ = D := SymplecticPilot.commutator_eq_self_of_isQuasisimple hD.2.2
  have hD1 : D ≠ ⊥ := CFSG.SeitzReduction.ne_bot_of_isQuasisimple hD.2.2
  have hne : Kc.map (MulAut.conj s).toMonoidHom ≠ Kc := by
    intro hKt
    have hfield : NeighbourRowOmega s D .field := ⟨Kc, hKc, hDKK, iff_of_true rfl hKt⟩
    exact absurd (NeighbourRowOmega.unique hs2 hDperf hD1 hfield hrow) (by decide)
  obtain ⟨hcomm, -, hdiag, -⟩ := hswap hne
  obtain ⟨hZ, hφ⟩ :=
    LinearPilot.center_eq_bot_and_nonempty_mulEquiv_of_swap hO hs hKc hne hcomm hdiag hDs hsyl
  exact ⟨Kc, hKc, ⟨hDKK, Or.inr ⟨hne, hcomm, hZ, hφ⟩⟩, hne⟩

end Abstract

section Ambient

variable {G : Type} [Group G] [Finite G]

theorem swapCase_of_omegaRowAt {t : G} (ht : orderOf t = 2) {X D : Subgroup G}
    (htX : t ∈ centralizer (X : Set G))
    (hcomp : CFSG.Open.IsComponentOf
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
      (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))))
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2)
    (hrow : OmegaRowAt t X D .swap) (m f : ℕ) :
    ∃ Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsComponent Kc ∧
      OmegaNeighbourAlternative (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) Kc m f ∧
      Kc.map (MulAut.conj
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom ≠ Kc := by
  obtain ⟨htX', hr⟩ := hrow
  have hs : orderOf (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩) = 2 := by
    have ht' : orderOf (⟨t, htX⟩ : centralizer (X : Set G)) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact ht
    exact orderOf_mk_oddCore ht'
  exact swapAlternative_of_neighbourRowOmega (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _)
    hs hcomp hsyl hr m f

end Ambient

end CFSG.SeitzReduction.OmegaPilot
