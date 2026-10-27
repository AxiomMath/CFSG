module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Rest7
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3GlueG
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3Theta
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3Sylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3Sq

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.Finkelstein77 (innAut)
open CFSG.Sporadic.Schreier (j3P j3PermEquiv)

@[expose] def Fin76bOuterRest₈ : Prop :=
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
    (∃ hz : z ∈ centralizer ({β} : Set G), Lemma96Conclusion ↥(centralizer ({β} : Set G))
      (QuotientGroup.mk (⟨z, hz⟩ : ↥(centralizer ({β} : Set G))))) →
    (∀ y ∈ centralizer ({z} : Set G), y * y ∈ L) →
    False

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem betaDataSqBO_of_sporadic
    (hBJ2 : BetaDataSqBO ↥ComponentClassification.J2Cover.Models.P) (hBJ3 : BetaDataSqBO ↥j3P)
    (hJ : IsSporadic L .J2 ∨ IsSporadic L .J3) : BetaDataSqBO ↥L := by
  rcases hJ with hL | hL
  · obtain ⟨e⟩ := hL
    exact BetaDataSqBO.of_mulEquiv
      ((MulEquiv.subgroupCongr ComponentClassification.J2Cover.Models.P_eq_autP).trans
        (ComponentClassification.J2Cover.nativeEquivP.symm.trans e.symm)) hBJ2
  · obtain ⟨e⟩ := hL
    exact BetaDataSqBO.of_mulEquiv (e.trans j3PermEquiv).symm hBJ3

theorem OuterB.exists_of_betaDataSqBO (hB : BetaDataSqBO ↥L) {t : G} (htL : t ∈ L)
    (ht2 : orderOf t = 2) (hsq : ∃ g ∈ L, g * g = t) :
    ∃ (B : Subgroup G) (β : G) (hβL : β ∈ L),
      OuterB L t B β ∧ OuterBetaFor ↥L (⟨β, hβL⟩ : ↥L) := by
  classical
  let t' : ↥L := ⟨t, htL⟩
  have ht'2 : orderOf t' = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact ht2
  obtain ⟨g, hgL, hg⟩ := hsq
  have hsq' : ∃ g' : ↥L, g' * g' = t' := ⟨⟨g, hgL⟩, Subtype.ext hg⟩
  obtain ⟨B, β, hBt, ⟨eB⟩, hβB, hβ, hO⟩ := hB t' ht'2 hsq'
  obtain ⟨hβ3, hD, hOd⟩ := hβ.transport (MulEquiv.refl ↥L)
  refine ⟨B.map L.subtype, ((β : ↥L) : G), β.2, ?_, by simpa using hO⟩
  refine
  { B_le := ?_
    B_cent := ?_
    B_iso := ⟨((B.equivMapOfInjective L.subtype L.subtype_injective)).symm.trans eB⟩
    beta_mem := ⟨β, hβB, rfl⟩
    beta_order := hβ3
    D_quot := hD
    D_odd := hOd }
  · rintro _ ⟨b, hb, rfl⟩
    exact b.2
  · rintro _ ⟨b, hb, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have := congrArg Subtype.val (mem_centralizer_singleton_iff.1 (hBt hb))
    exact this

omit [Finite G] in
theorem outerBetaFor_quotient {β : ↥L} (hZ : center ↥L = ⊥) (h : OuterBetaFor ↥L β) :
    OuterBetaFor (↥L ⧸ center ↥L) (QuotientGroup.mk β) := by
  let e : ↥L ≃* ↥L ⧸ center ↥L :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  exact h.map e

theorem fin76bOuterRest₇_of_rest₈
    (hSol : SolomonM10) (hR : Fin76bOuterRest₈)
    (hOJ2 : OuterEData ↥ComponentClassification.J2Cover.Models.P) (hOJ3 : OuterEData ↥j3P)
    (hBJ2 : BetaDataSqBO ↥ComponentClassification.J2Cover.Models.P)
    (hBJ3 : BetaDataSqBO ↥j3P) : Fin76bOuterRest₇ := by
  intro G _ _ L z t T E Q x B β h hJ hS hidx hE haut hT hW hN hcent hB hβ8 hSyl hTQ hxQ hxT hxN
    hxz hxt htQ hQz hcomm
  have hzt : ∃ y : G, y * z * y⁻¹ = z * t := ⟨x, hxz⟩
  obtain ⟨hZ, hcZ, hOE, hout⟩ := outer_inputs_of_sporadic hOJ2 hOJ3 hJ
  obtain ⟨EY, hP⟩ := exists_pullHyp h hS hZ hcZ hOE hout hidx hE.cfg
  have hsurj := thetaH_surjective h hS hE.cfg.z_cent hE.cfg.z_order hE.cfg.cent_le hout hidx
  have hBL : BetaDataSqBO ↥L := betaDataSqBO_of_sporadic hBJ2 hBJ3 hJ
  have htL : t ∈ L := hE.cfg.t_mem_A
  have hsq : ∃ g ∈ L, g * g = t := by
    obtain ⟨g, hg, hg4⟩ := hE.cfg.t_fourth
    exact ⟨g * g, mul_mem hg hg, hg4⟩
  obtain ⟨B', β', hβ'L, hB', hOβ'⟩ := OuterB.exists_of_betaDataSqBO hBL htL hE.t_order hsq
  have hO' := outerBetaFor_quotient hZ hOβ'
  have hM1 := hP.exists_outer_fix hsurj hβ'L hO'
  have hM2 : ∀ c ∈ centralizer ({z} : Set G), c * β' = β' * c → c * c ∈ zpowers z ⊔ zpowers β' →
      c ∈ L ⊔ zpowers z := fun c hc hcβ hcc =>
    hP.mem_of_sq_mem hβ'L hB'.beta_order hO' hc hcβ hcc
  have hSyl' : ∀ S : Subgroup G, IsPGroup 2 S → S ≤ centralizer (E : Set G) →
      (∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S) →
      z ∈ S → OuterSylowFacts z E S ∧ ∀ b ∈ B', ∀ s ∈ S, b * s = s * b := by
    intro S hS2 hSC hSmax hzS
    exact ⟨(hSyl S hS2 hSC hSmax hzS).1,
      hE.B_centralizes_S hzt hW haut hT Q.isPGroup' hTQ hxQ hxT hxN hB' hS2 hSC hSmax hzS⟩
  obtain ⟨S, hS2, hSC, hSmax, hzS⟩ := exists_maximal_two_subgroup (centralizer (E : Set G))
    (hE.zpowers_le_cent_E (mem_zpowers z)) hE.cfg.z_order
  obtain ⟨hshape, hBS⟩ := hSyl' S hS2 hSC hSmax hzS
  obtain ⟨s, hsS, hs1, n, hsn⟩ := exists_noncomm_of_shape hS2 hSC hzS hshape.1 hcent
  have hsβ : s * β' = β' * s := (hBS β' hB'.beta_mem s hsS).symm
  obtain ⟨hz, hconc, c, hc, -, hcL, hcc⟩ := lemma96_of_outerConfig hSol hE.cfg
    (h.isKGroupCat_centralizer_of_orderOf (by norm_num) hB'.beta_order) hβ'L hB'.D_quot
    hB'.D_odd hM1 hM2 ⟨s, hsβ, hs1, n, hsn⟩
  exact hR G L z t T E Q x B' β' h hJ hS hidx hE haut hT hW hN hcent hB'
    (card_inf_centralizer_eq_eight hW (hB'.B_le hB'.beta_mem)
      (mem_centralizer_singleton_iff.1 (hB'.B_cent hB'.beta_mem)) hB'.beta_order)
    hSyl' hTQ hxQ hxT hxN hxz hxt htQ hQz hcomm ⟨hz, hconc⟩
    (fun y hy => hE.cfg.sq_mem_L hc hcL hcc hy)

end CFSG.EvenSporadicStandard.Fin76b
