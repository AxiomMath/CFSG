module

import CFSG.ClassicalInvolution.Asc77.AscT8W6Eng
public import CFSG.ClassicalInvolution.Asc77.AscT8W2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

namespace T8W

section SixTwoGen

variable {H : Type} [Group H] [Finite H] {p f : ℕ} [Fact p.Prime]

theorem isConj_or_mem_omegaNbr_gen {Λ : Set (Subgroup H)} (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Λ) {K : Subgroup H} (hK : K ∈ Λ) (hAE : AEmpty Λ K)
    (hnt : ∀ K' ∈ twinSet Λ K, K' = K) {z : H} (hz : IsUniqueInvolution K z) {g : H}
    (hne : g⁻¹ * z * g ≠ z) (hcomm : z * (g⁻¹ * z * g) = g⁻¹ * z * g * z) :
    IsConj z (z * (g⁻¹ * z * g)) ∨ conjSub g⁻¹ K ∈ omegaNbr Λ K := by
  exact isConj_or_mem_omegaNbr_genE hΩ.conjInvariant
    (fun hM hR hRM => T3.isSylow2In_of_mem_RSet_of_le hp hΩ hM hR hRM)
    (fun hR => hΩ.eight_le_of_mem_RSet hp hR) hK hAE hnt hz
    (l6_2 p f hp hq H Λ hΩ K hK z hz) hne hcomm

end SixTwoGen

section Conj

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}


theorem exists_conj_mul_E4 [IsSimpleGroup G] (hs : Std8 p f Ω K J S R T W z t)
    (hdisc : ¬ DConnected Ω) (hE : MuIsoE4 Ω W) {g : G} (hgX : g ∈ omegaNbrGen Ω K)
    (hne : g⁻¹ * t * g ≠ t) (hcomm : t * (g⁻¹ * t * g) = g⁻¹ * t * g * t) :
    ∃ y ∈ omegaNbrGen Ω K, y * t * y⁻¹ = t * (g⁻¹ * t * g) := by
  classical
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hJΩ : J ∈ Ω := hs.hJ.1
  set X : Subgroup G := omegaNbrGen Ω K with hXdef
  have hJX : J ≤ X := le_iSup₂ (f := fun N (_ : N ∈ omegaNbr Ω K) => N) J hs.hJ
  have htX : t ∈ X := hJX hs.ht.mem
  have hΛ : HypOmegaMod p f (restrictFamily Ω X) := hΩ.restrict X
  have hKXΛ : J.subgroupOf X ∈ restrictFamily Ω X := subgroupOf_mem_restrictFamily hJΩ hJX
  have hA : AEmpty (restrictFamily Ω X) (J.subgroupOf X) :=
    AEmpty.restrict hp hΩ hJX (hs.stand.aEmpty J hJΩ)
  have hntJ : ∀ M' ∈ twinSet Ω J, M' = J :=
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hJΩ
  have hnt : ∀ K' ∈ twinSet (restrictFamily Ω X) (J.subgroupOf X), K' = J.subgroupOf X := by
    rintro _ ⟨⟨L, hL, hLX, rfl⟩, w, hwK, hwK'⟩
    have h1 := isUniqueInvolution_of_subgroupOf hwK hJX
    have h2 := isUniqueInvolution_of_subgroupOf hwK' hLX
    rw [hntJ L ⟨hL, (w : G), h1, h2⟩]
  have hz := isUniqueInvolution_subgroupOf hs.ht hJX
  set zt : ↥X := ⟨t, htX⟩ with hztdef
  set gX : ↥X := ⟨g, hgX⟩ with hgXdef
  have hne' : gX⁻¹ * zt * gX ≠ zt := fun h => hne (congrArg Subtype.val h)
  have hcomm' : zt * (gX⁻¹ * zt * gX) = gX⁻¹ * zt * gX * zt := Subtype.ext hcomm
  rcases isConj_or_mem_omegaNbr_gen hp hq hΛ hKXΛ hA hnt hz hne' hcomm' with hconj | hnbr
  · obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    exact ⟨c.1, c.2, congrArg Subtype.val hc⟩
  · exfalso
    have hNodd : Odd (Nat.card (classicalInvolutionOddCore ↥X)) :=
      CFSG.ComponentClassification.OddCore.odd_card ↥X
    set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥X) with hπ
    have hb : IsUniqueInvolution (conjSub gX⁻¹ (J.subgroupOf X)) (gX⁻¹ * zt * gX) := by
      have := hz.conj gX⁻¹
      rwa [inv_inv] at this
    have hconjΛ : conjSub gX⁻¹ (J.subgroupOf X) ∈ restrictFamily Ω X :=
      hΛ.conjInvariant gX⁻¹ _ hKXΛ
    have himg := T8S2.map_ne_of_noTwins hp hΛ hNodd hz hb hnbr (fun h => hnt _ h)
    have hnbr' := T8S2.omegaNbr_map_odd hp hΛ hNodd hnbr himg
    have hDE := s26XEdgeless_E4 hs hdisc hE
    exact hDE _ ⟨_, hKXΛ, rfl⟩ _ ⟨_, hconjΛ, rfl⟩ (Or.inl hnbr')

end Conj

end T8W

end CFSG.ClassicalInvolution.Asc77
