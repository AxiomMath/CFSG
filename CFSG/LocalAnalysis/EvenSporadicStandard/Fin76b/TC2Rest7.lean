module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Rest6
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Beta
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Rest4
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Roots
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2WFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.ThmCFinal

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise
open CFSG.Sporadic.Schreier (j3P j3PermEquiv)

@[expose] def Fin76bOuterRest₇ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G) (T E : Subgroup G) (Q : Sylow 2 G)
    (x : G) (B : Subgroup G) (β : G), StdHyp G L → (IsSporadic L .J2 ∨ IsSporadic L .J3) →
    (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) →
    (L ⊔ centralizer (L : Set G)).relIndex (normalizer (L : Set G)) = 2 →
    OuterE G L z t T E → Nat.card (MulAut ↥E) = 1920 → Nat.card ↥T = 512 → WFacts L t E →
    (∀ m ∈ normalizer (E : Set G), ∃ c ∈ centralizer (E : Set G),
      ∃ n ∈ normalizer (E : Set G), n ∈ centralizer ({z} : Set G) ∧ m = c * n) →
    (∀ v ∈ centralizer (E : Set G), v * z = z * v → v = 1 ∨ v = z ∨ v = t ∨ v = t * z) →
    OuterB L t B β → Nat.card ↥(E ⊓ centralizer ({β} : Set G)) = 8 →
    (∀ S : Subgroup G, IsPGroup 2 S → S ≤ centralizer (E : Set G) →
      (∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S) →
      z ∈ S → OuterSylowFacts z E S ∧ ∀ b ∈ B, ∀ s ∈ S, b * s = s * b) →
    T ≤ (Q : Subgroup G) → x ∈ (Q : Subgroup G) → x ∉ T →
    x ∈ normalizer (T : Set G) → x * z * x⁻¹ = z * t → x * t * x⁻¹ = t →
    (∀ q ∈ (Q : Subgroup G), q * t = t * q) → (Q : Subgroup G) ⊓ centralizer ({z} : Set G) = T →
    z ∈ (commutator ↥(centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype →
    False

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem betaDataSqB_of_sporadic
    (hBJ2 : BetaDataSqB ↥ComponentClassification.J2Cover.Models.P) (hBJ3 : BetaDataSqB ↥j3P)
    (hJ : IsSporadic L .J2 ∨ IsSporadic L .J3) : BetaDataSqB ↥L := by
  rcases hJ with hL | hL
  · obtain ⟨e⟩ := hL
    exact BetaDataSqB.of_mulEquiv
      ((MulEquiv.subgroupCongr ComponentClassification.J2Cover.Models.P_eq_autP).trans
        (ComponentClassification.J2Cover.nativeEquivP.symm.trans e.symm)) hBJ2
  · obtain ⟨e⟩ := hL
    exact BetaDataSqB.of_mulEquiv (e.trans j3PermEquiv).symm hBJ3

theorem fin76bOuterRest_of_rest₇
    (hR : Fin76bOuterRest₇) (hOJ2 : OuterEData ↥ComponentClassification.J2Cover.Models.P)
    (hOJ3 : OuterEData ↥j3P) (hRJ2 : RootFactsClass ↥ComponentClassification.J2Cover.Models.P)
    (hRJ3 : RootFactsClass ↥j3P) (hBJ2 : BetaDataSqB ↥ComponentClassification.J2Cover.Models.P)
    (hBJ3 : BetaDataSqB ↥j3P) : Fin76bOuterRest := by
  intro G _ _ L z t T Q x h hJ hS hidx cfg hTQ hxQ hxT hxN hxz hxt htQ hQz hcomm
  obtain ⟨hZ, hcZ, hOE, hout⟩ := outer_inputs_of_sporadic hOJ2 hOJ3 hJ
  obtain ⟨E, hE, haut, hT, hgen, hge⟩ := exists_outerE_roots h hS hZ hcZ hOE hout hidx cfg
  have hW : WFacts L t E := hE.wFacts (rootFactsClass_of_sporadic hRJ2 hRJ3 hJ) hgen hge
  have hzt : ∃ y : G, y * z * y⁻¹ = z * t := ⟨x, hxz⟩
  have hBL : BetaDataSqB ↥L := betaDataSqB_of_sporadic hBJ2 hBJ3 hJ
  have htL : t ∈ L := cfg.t_mem_A
  have ht2 : orderOf t = 2 := hE.t_order
  have hsq : ∃ g ∈ L, g * g = t := by
    obtain ⟨g, hg, hg4⟩ := cfg.t_fourth
    exact ⟨g * g, mul_mem hg hg, hg4⟩
  obtain ⟨B, β, hB⟩ := OuterB.exists_of_betaDataSqB hBL htL ht2 hsq
  refine hR G L z t T E Q x B β h hJ hS hidx hE haut hT hW
    (fun m hm => hE.normalizer_eq_mul hzt hW haut hT hm)
    (fun v hv hvz => hE.cent_cent_z hzt hW hv hvz) hB
    (card_inf_centralizer_eq_eight hW (hB.B_le hB.beta_mem)
      (mem_centralizer_singleton_iff.1 (hB.B_cent hB.beta_mem)) hB.beta_order) ?_
    hTQ hxQ hxT hxN hxz hxt htQ hQz hcomm
  intro S hS2 hSC hSmax hzS
  exact ⟨⟨hE.sylow_centralizer_shape' hzt haut hT Q.isPGroup' hTQ hxQ hxT hxN hS2 hSC hSmax hzS,
    fun k hk hSd => hE.centralizer_oddCore_dihedral hS2 hSC hSmax hk hSd,
    fun g hg => hE.fusion_in_sylow hzt hW haut hT Q.isPGroup' hTQ hxQ hxT hxN hS2 hSC hSmax hzS
      hg⟩,
    hE.B_centralizes_S hzt hW haut hT Q.isPGroup' hTQ hxQ hxT hxN hB hS2 hSC hSmax hzS⟩

end CFSG.EvenSporadicStandard.Fin76b
