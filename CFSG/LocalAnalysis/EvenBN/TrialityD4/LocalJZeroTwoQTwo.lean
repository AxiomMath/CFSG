module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalJZeroTwoNeighbourCat
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalJZeroTwoQTwoLocal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2HR8
import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents
public import CFSG.GH74.SectionalRank

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def D4QTwoSmallKindInput : Prop :=
  ∀ (S : Type) [Group S] [Finite S], CFSG.IsQuasisimple S → center S = ⊥ →
    SeitzReduction.LinearPilot.SLmSmall (S ⧸ center S) 3 1 → GH74.Gen4 S →
    ∀ τ : MulAut S, orderOf τ = 2 →
    ∀ D : Subgroup (fixedSubgroup τ), CFSG.IsComponent D →
      LieModel (D ⧸ center D) .PSL 3 2 1 → center D = ⊥ →
      (SeitzReduction.F4Pilot.FixedCentralizerTwoFree τ D ∨
        (τ ∈ (MulAut.conj : S →* MulAut S).range ∧
          SeitzReduction.LinearPilot.FixedCentralizerTwoSmall τ D)) →
      168 < Nat.card (fixedSubgroup τ) ∧
        (τ ∈ (MulAut.conj : S →* MulAut S).range → 336 < Nat.card (fixedSubgroup τ))

section Generic

variable {G : Type} [Group G] [Finite G]

theorem card_fixedSubgroup_le_of_mem_or_mul_mem {Y : Type} [Group Y] [Finite Y]
    {Kc D : Subgroup Y} {s : Y} (hsN : s ∈ normalizer (Kc : Set Y)) (hs : s * s = 1)
    (hDK : D ≤ Kc) (hO1 : ∀ k : Y, k * s = s * k → k ∈ D ∨ k * s ∈ D) :
    (s ∉ Kc → Nat.card (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩)) ≤ Nat.card D) ∧
      (s ∈ Kc →
        Nat.card (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩)) ≤ 2 * Nat.card D) := by
  have hmem : ∀ k : Kc, k ∈ fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩) →
      (k : Y) * s = s * k := by
    intro k hk
    rw [SeitzReduction.F4Pilot.fixedSubgroup_normalizerMonoidHom Kc hsN, mem_subgroupOf,
      mem_centralizer_singleton_iff] at hk
    exact hk
  have hDc : Nat.card (D.subgroupOf Kc) = Nat.card D :=
    Nat.card_congr (subgroupOfEquivOfLe hDK).toEquiv
  refine ⟨fun hsK => ?_, fun hsK => ?_⟩
  · have hsub : fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩) ≤ D.subgroupOf Kc := by
      intro k hk
      rcases hO1 k (hmem k hk) with h1 | h1
      · exact mem_subgroupOf.2 h1
      · exfalso
        apply hsK
        have h2 : s = (k : Y)⁻¹ * ((k : Y) * s) := by group
        rw [h2]
        exact mul_mem (inv_mem k.2) (hDK h1)
    exact (Subgroup.card_le_of_le hsub).trans hDc.le
  · set s' : Kc := ⟨s, hsK⟩ with hs'
    have hss : s' * s' = 1 := Subtype.ext hs
    have hsub : (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩) : Set Kc) ⊆
        (D.subgroupOf Kc : Set Kc) ∪ (fun a => a * s') '' (D.subgroupOf Kc : Set Kc) := by
      intro k hk
      rcases hO1 k (hmem k hk) with h1 | h1
      · exact .inl (mem_subgroupOf.2 h1)
      · right
        refine ⟨k * s', mem_subgroupOf.2 h1, ?_⟩
        change k * s' * s' = k
        rw [mul_assoc, hss, mul_one]
    have hle := Set.ncard_le_ncard hsub
    have hu := Set.ncard_union_le (D.subgroupOf Kc : Set Kc)
      ((fun a => a * s') '' (D.subgroupOf Kc : Set Kc))
    have hi := Set.ncard_image_of_injective (D.subgroupOf Kc : Set Kc) (mul_left_injective s')
    have e1 : Nat.card (D.subgroupOf Kc) = (D.subgroupOf Kc : Set Kc).ncard :=
      Nat.card_coe_set_eq _
    have e2 : Nat.card (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩)) =
        (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩) : Set Kc).ncard :=
      Nat.card_coe_set_eq _
    omega

theorem false_of_smallKind_of_input {Y : Type} [Group Y] [Finite Y]
    (hsk : D4QTwoSmallKindInput) (hgen : GH74.Gen4 Y) {s : Y} (hs : orderOf s = 2)
    {D : Subgroup Y}
    (hD : CFSG.Open.IsComponentOf D (centralizer ({s} : Set Y)))
    (hsyl : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ centralizer (D : Set Y) → Nat.card U ≤ 2)
    (hDm : LieModel (D ⧸ center D) .PSL 3 2 1) (hD168 : Nat.card D ≤ 168)
    (hO1 : ∀ k : Y, k * s = s * k → k ∈ D ∨ k * s ∈ D)
    (hsm : SeitzReduction.LinearPilot.NeighbourOvergroupSLmSmall s D 3 1) : False := by
  obtain ⟨Kc, hKc, hDK, hKt', hsC, hZ, hsmall⟩ := hsm
  have hs2 : s ^ 2 = 1 := by rw [← hs, pow_orderOf_eq_one]
  have hss : s * s = 1 := by rw [← sq, hs2]
  have hsN : s ∈ normalizer (Kc : Set Y) := mem_normalizer_iff_map_conj_eq.2 hKt'
  have hKs : ¬ Kc ≤ centralizer ({s} : Set Y) := fun hle =>
    hsC (mem_centralizer_iff.2 fun k hk => mem_centralizer_singleton_iff.1 (hle hk))
  have hτ2 := SeitzReduction.F4Pilot.orderOf_normalizerMonoidHom_eq_two Kc hsN hs2 hKs
  have hDs : D ≤ centralizer ({s} : Set Y) := hD.1
  have hDc : CFSG.IsComponent (D.subgroupOf (centralizer ({s} : Set Y))) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hDs).1
      ((ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).2 hD)
  have hDcomp := SeitzReduction.CentralizerComponents.isComponent_subgroupOf_inf_centralizer hDs
    hDc hDK.le
  obtain ⟨hD'c, hD'm, hD'map⟩ :=
    SeitzReduction.LinearPilot.isComponent_fixedSubgroup_of_le_of_quotient hsN hDK.le hDs hDcomp
      hDm
  have h2cond : SeitzReduction.F4Pilot.FixedCentralizerTwoFree
        (Kc.normalizerMonoidHom ⟨s, hsN⟩)
        ((D.subgroupOf Kc).subgroupOf (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩))) ∨
      (Kc.normalizerMonoidHom ⟨s, hsN⟩ ∈ (MulAut.conj : Kc →* MulAut Kc).range ∧
        SeitzReduction.LinearPilot.FixedCentralizerTwoSmall (Kc.normalizerMonoidHom ⟨s, hsN⟩)
          ((D.subgroupOf Kc).subgroupOf
            (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩)))) := by
    by_cases hsK : s ∈ Kc
    · exact .inr ⟨SeitzReduction.F4Pilot.normalizerMonoidHom_mem_range_conj Kc hsN hsK,
        SeitzReduction.E6Pilot.fixedCentralizerTwoSmall_of_card_le_two _ hDK.le hsyl _ hD'map⟩
    · exact .inl (SeitzReduction.F4Pilot.fixedCentralizerTwoFree_of_card_le_two hsN hs hsK hDs
        hDK.le hsyl _ hD'map)
  have hcardD' : Nat.card ((D.subgroupOf Kc).subgroupOf
      (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩))) = Nat.card D := by
    rw [← card_map_of_injective (fixedSubgroup _).subtype_injective, hD'map]
    exact Nat.card_congr (subgroupOfEquivOfLe hDK.le).toEquiv
  obtain ⟨hD'168, hZD'⟩ := card_eq_and_center_eq_bot_of_lieModel hD'm (hcardD' ▸ hD168)
  obtain ⟨hlo, hli⟩ := hsk Kc hKc.1 hZ hsmall (hgen.subgroup Kc) _ hτ2 _ hD'c hD'm hZD' h2cond
  obtain ⟨hout, hinn⟩ := card_fixedSubgroup_le_of_mem_or_mul_mem hsN hss hDK.le hO1
  rw [hcardD'] at hD'168
  by_cases hsK : s ∈ Kc
  · have := hinn hsK
    have := hli (SeitzReduction.F4Pilot.normalizerMonoidHom_mem_range_conj Kc hsN hsK)
    omega
  · have := hout hsK
    omega

end Generic

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem false_of_smallKind (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hf : f = 1)
    (hsk : D4QTwoSmallKindInput)
    (hgen : GH74.Gen4 (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ⧸
      CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))))
    (hsm : SeitzReduction.LinearPilot.NeighbourOvergroupSLmSmall
      (QuotientGroup.mk' (CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
        ⟨t, h.t_mem_centralizer_J₀ d⟩)
      (((d.leviJ₀.map L.subtype).subgroupOf
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))).map
          (QuotientGroup.mk' (CFSG.oddCore
            (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))))) 3 1) : False := by
  obtain ⟨hcomp, hsyl, -⟩ := h.yamada_5_4_hr7 d
  have hDm := lieModel_leviJ₀_map d (f := f) (by omega)
  subst hf
  exact false_of_smallKind_of_input hsk hgen
    (SeitzReduction.orderOf_mk_oddCore (by rw [orderOf_mk]; exact h.ht)) hcomp hsyl
    (SeitzReduction.LinearPilot.lieModel_quotient_center_map_oddCore
      (leviJ₀_map_le_centralizer_J₀ d) (isQuasisimple_leviJ₀_map d) hDm
      (SeitzReduction.ne_bot_of_isQuasisimple hcomp.2.2))
    (card_leviJ₀_bar_le d rfl) (h.mem_or_mul_mem_leviJ₀_bar d rfl) hsm

end Setup


section Main


namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem yamada_5_4_two_of_input (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hf : f = 1)
    (hsk : D4QTwoSmallKindInput) :
    ∃ Kc : Subgroup (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) ⧸
        CFSG.oddCore (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))),
      CFSG.IsComponent Kc ∧
      ((d.leviJ₀.map L.subtype).subgroupOf
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))).map
          (QuotientGroup.mk' (CFSG.oddCore
            (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))) ≤
        Kc ⊔ Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
            ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom ∧
      ((Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
          (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
            ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom = Kc ∧
          ((d.leviJ₀.map L.subtype).subgroupOf
            (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))).map
            (QuotientGroup.mk' (CFSG.oddCore
              (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))) < Kc ∧
          QuotientGroup.mk' (CFSG.oddCore
            (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
              ⟨t, h.t_mem_centralizer_J₀ d⟩ ∉ Kc ∧
          (∃ hsN : QuotientGroup.mk' (CFSG.oddCore
              (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
                ⟨t, h.t_mem_centralizer_J₀ d⟩ ∈ normalizer (Kc : Set _),
            Kc.normalizerMonoidHom ⟨_, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range) ∧
          center Kc = ⊥ ∧ LieModel Kc .PSL 3 2 (2 * f)) ∨
        (Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
            (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
              ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom ≠ Kc ∧
          ⁅Kc, Kc.map (MulAut.conj (QuotientGroup.mk' (CFSG.oddCore
            (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))
              ⟨t, h.t_mem_centralizer_J₀ d⟩)).toMonoidHom⁆ = ⊥ ∧
          center Kc = ⊥ ∧
          Nonempty (Kc ≃* (((d.leviJ₀.map L.subtype).subgroupOf
            (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G))).map
            (QuotientGroup.mk' (CFSG.oddCore
              (centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G)))) : Subgroup _)))) := by
  obtain ⟨hcomp, hsyl, hstd⟩ := h.yamada_5_4_hr7 d
  have hDm := lieModel_leviJ₀_map d (f := f) (by omega)
  subst hf
  rcases SeitzReduction.LinearPilot.neighbour_overgroup_slm_center_or_inner le_rfl
      slmCatalogueClausesAt_three_D4 h.kproper (h.centralizer_J₀_ne_top d)
      (h.t_mem_centralizer_J₀ d) h.ht (leviJ₀_map_le_centralizer_J₀ d)
      (isQuasisimple_leviJ₀_map d) hDm hcomp hsyl hstd (h.not_normal_leviJ₀_bar d) with
    hov | hin
  · rcases hov.field_or_small_oddCore (h.t_mem_centralizer_J₀ d) h.ht
        (leviJ₀_map_le_centralizer_J₀ d) (isQuasisimple_leviJ₀_map d) le_rfl
        (SeitzReduction.LinearPilot.slmEvenTypeDetAt le_rfl) hDm hcomp with
      ⟨hfld, -⟩ | hsm
    · obtain ⟨Kc, hKc, hDKK, ⟨hKt, hDK, hsK, hsN, hout, hZ, hmodel, -⟩ | hswap⟩ := hfld
      · exact ⟨Kc, hKc, hDKK, .inl ⟨hKt, hDK, hsK, ⟨hsN, hout⟩, hZ, hmodel⟩⟩
      · exact ⟨Kc, hKc, hDKK, .inr hswap⟩
    · exact (h.false_of_smallKind d rfl hsk (h.gen4_bar d rfl) hsm).elim
  · exact (h.false_of_smallKind d rfl hsk (h.gen4_bar d rfl) hin.small).elim

end Setup

end Main

end CFSG.LocalAnalysis.EvenBN.TrialityD4
