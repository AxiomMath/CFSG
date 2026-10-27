module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSecXg
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.LiftTransfer

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups

set_option linter.unusedSectionVars false

namespace TwinConnT

variable {G : Type} [Group G] [Finite G]

theorem oddCore_eq_bot_of_map {X : Subgroup G} {C : Subgroup X} {D : Subgroup G}
    (h : C.map X.subtype = D) (hD : classicalInvolutionOddCore ↥D = ⊥) :
    classicalInvolutionOddCore ↥C = ⊥ := by
  subst h
  let e : ↥C ≃* ↥(C.map X.subtype) := C.equivMapOfInjective X.subtype X.subtype_injective
  have hO : (classicalInvolutionOddCore ↥C).map e.toMonoidHom =
      classicalInvolutionOddCore ↥(C.map X.subtype) :=
    CFSG.ComponentClassification.OddCore.equiv_invariant e
  rw [hD] at hO
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hO

theorem classicalOddCore_eq_bot_of_oddCoreIn {H : Subgroup G} (h : Balance.oddCoreIn H = ⊥) :
    classicalInvolutionOddCore ↥H = ⊥ :=
  (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp h

theorem oddCoreIn_eq_bot_of_classicalOddCore {H : Subgroup G}
    (h : classicalInvolutionOddCore ↥H = ⊥) : Balance.oddCoreIn H = ⊥ := by
  show (classicalInvolutionOddCore ↥H).map _ = ⊥
  rw [h, Subgroup.map_bot]

theorem isSubnormal_of_on {X L : Subgroup G} {z : G} (hLX : L ≤ X)
    (h : TwinSecXg.IsClassicalMember3On X L z) :
    IsSubnormal L (X ⊓ Subgroup.centralizer ({z} : Set G)) := by
  obtain ⟨hz, hc⟩ := h
  have h1 := TwinSecXg.isSubnormal_map_hom X.subtype hc.subnormal
  rwa [Subgroup.map_subgroupOf_eq_of_le hLX, TwinSecXg.map_centralizer_subtype_singleton hz] at h1

theorem card_eq_24_of_exact {L : Subgroup G} (hOL : classicalInvolutionOddCore ↥L = ⊥)
    (hq : Nonempty (↥L ⧸ classicalInvolutionOddCore ↥L ≃* SL(2, ZMod 3))) : Nat.card L = 24 := by
  obtain ⟨e0⟩ := hq
  let e : ↥L ≃* SL(2, ZMod 3) :=
    ((QuotientGroup.quotientMulEquivOfEq hOL).trans QuotientGroup.quotientBot).symm.trans e0
  rw [Nat.card_congr e.toEquiv, natCard_sl2Three]

theorem liftUnique_on {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {X' J L₁ L₂ : Subgroup G} {t : G}
    (hJ : J ∈ Ω) (hz : IsUniqueInvolution J t) (hJ₁ : J ≤ L₁) (hJ₂ : J ≤ L₂) (hL₁ : L₁ ≤ X')
    (hL₂ : L₂ ≤ X') (h₁ : TwinSecXg.IsClassicalMember3On X' L₁ t)
    (h₂ : TwinSecXg.IsClassicalMember3On X' L₂ t)
    (hOC : classicalInvolutionOddCore ↥(X' ⊓ Subgroup.centralizer ({t} : Set G)) = ⊥) :
    L₁ = L₂ := by
  obtain ⟨hzX, hc₁⟩ := h₁
  obtain ⟨_hzX₂, hc₂⟩ := h₂
  have hJX : J ≤ X' := hJ₁.trans hL₁
  have hΩ' := hypOmegaGen_restrict hΩ X'
  have hmem : J.subgroupOf X' ∈ restrictFamily Ω X' := ⟨J, hJ, hJX, rfl⟩
  have hint : Balance.oddCoreIn
      (Subgroup.centralizer ({(⟨t, hzX⟩ : ↥X')} : Set ↥X')) = ⊥ := by
    apply oddCoreIn_eq_bot_of_classicalOddCore
    exact oddCore_eq_bot_of_map (TwinSecXg.map_centralizer_subtype_singleton hzX) hOC
  have hi : ∀ L : Subgroup X', Uniform.IsIntrinsicU (.sl2 3 1) L (⟨t, hzX⟩ : ↥X') := by
    intro L _
    rw [hint]
    exact bot_le
  have hle : ∀ {L : Subgroup G}, J ≤ L → J.subgroupOf X' ≤ L.subgroupOf X' := by
    intro L hJL x hx
    exact Subgroup.mem_subgroupOf.mpr (hJL (Subgroup.mem_subgroupOf.mp hx))
  have heq := eq_of_isLiftOf hΩ' hmem
    ⟨isUniqueInvolution_subgroupOf hz hJX, hle hJ₁, hc₁⟩
    ⟨isUniqueInvolution_subgroupOf hz hJX, hle hJ₂, hc₂⟩ (hi _) (hi _)
  rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hL₁, inf_eq_left.mpr hL₂] at heq
  exact heq

theorem liftUnique_in {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {J L₁ L₂ : Subgroup G} {t : G}
    (hJ : J ∈ Ω) (hz : IsUniqueInvolution J t) (hJ₁ : J ≤ L₁) (hJ₂ : J ≤ L₂)
    (h₁ : IsClassicalMember3 L₁ t) (h₂ : IsClassicalMember3 L₂ t)
    (hO : classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set G)) = ⊥) : L₁ = L₂ := by
  have hint : Balance.oddCoreIn (Subgroup.centralizer ({t} : Set G)) = ⊥ :=
    oddCoreIn_eq_bot_of_classicalOddCore hO
  have hi : ∀ L : Subgroup G, Uniform.IsIntrinsicU (.sl2 3 1) L t := by
    intro L _
    rw [hint]
    exact bot_le
  exact eq_of_isLiftOf hΩ hJ ⟨hz, hJ₁, h₁⟩ ⟨hz, hJ₂, h₂⟩ (hi _) (hi _)

theorem isClassicalMember3On_conj {X L : Subgroup G} {z c : G}
    (hc : c ∈ Subgroup.normalizer (X : Set G)) (hcz : c * z * c⁻¹ = z)
    (h : TwinSecXg.IsClassicalMember3On X L z) :
    TwinSecXg.IsClassicalMember3On X (conjSub c L) z := by
  obtain ⟨hz, h'⟩ := h
  have hX : conjSub c X = X := conjSub_eq_of_mem_normalizer hc
  let φ : ↥X ≃* ↥X :=
    (X.equivMapOfInjective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective).trans
      (MulEquiv.subgroupCongr hX)
  have hφ : ∀ x : X, ((φ x : X) : G) = c * (x : G) * c⁻¹ := fun x => rfl
  refine ⟨hz, ?_⟩
  have h1 := TwinSecXg.isClassicalMember3_map_equiv φ h'
  have e1 : φ ⟨z, hz⟩ = ⟨z, hz⟩ := Subtype.ext (by rw [hφ]; exact hcz)
  have e2 : (L.subgroupOf X).map φ.toMonoidHom = (conjSub c L).subgroupOf X := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (conj_mem_conjSub (Subgroup.mem_subgroupOf.mp hy))
    · intro hx
      have hx' : c⁻¹ * (x : G) * c ∈ X := (mem_conj_iff_of_mem_normalizer hc x).mpr x.2
      refine ⟨⟨c⁻¹ * (x : G) * c, hx'⟩, Subgroup.mem_subgroupOf.mpr ?_, Subtype.ext ?_⟩
      · have := Subgroup.mem_subgroupOf.mp hx
        rwa [mem_conjSub_iff] at this
      · show c * (c⁻¹ * (x : G) * c) * c⁻¹ = x
        group
  rw [e1, e2] at h1
  exact h1

end TwinConnT

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
