module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3Rest8
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3Sigma

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Schreier (j3P j3PermEquiv)

@[expose] def Fin76bOuterRest₉ : Prop :=
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
    (∃ σ ∈ T, σ * σ = 1 ∧ σ ∉ L ⊔ zpowers z) → (∀ g : G, g * z * g⁻¹ ∉ L) →
    False

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem outerInvData_of_sporadic
    (hZ : center ↥L = ⊥)
    (hIJ2 : OuterInvData ↥ComponentClassification.J2Cover.Models.P) (hIJ3 : OuterInvData ↥j3P)
    (hJ : IsSporadic L .J2 ∨ IsSporadic L .J3) : OuterInvData (↥L ⧸ center ↥L) := by
  rcases hJ with hL | hL
  · obtain ⟨e⟩ := hL
    obtain ⟨eq⟩ := isSporadic_quotient_of_center_eq_bot hZ ⟨e⟩
    exact hIJ2.of_mulEquiv ((MulEquiv.subgroupCongr
      ComponentClassification.J2Cover.Models.P_eq_autP).trans
        (ComponentClassification.J2Cover.nativeEquivP.symm.trans eq.symm))
  · obtain ⟨e⟩ := hL
    obtain ⟨eq⟩ := isSporadic_quotient_of_center_eq_bot hZ ⟨e⟩
    exact hIJ3.of_mulEquiv (j3PermEquiv.symm.trans eq.symm)

theorem fin76bOuterRest₈_of_rest₉
    (hR : Fin76bOuterRest₉) (hOJ2 : OuterEData ↥ComponentClassification.J2Cover.Models.P)
    (hOJ3 : OuterEData ↥j3P) (hIJ2 : OuterInvData ↥ComponentClassification.J2Cover.Models.P)
    (hIJ3 : OuterInvData ↥j3P) : Fin76bOuterRest₈ := by
  intro G _ _ L z t T E Q x B β h hJ hS hidx hE haut hT hW hN hcent hB hβ8 hSyl hTQ hxQ hxT hxN
    hxz hxt htQ hQz hcomm hconc hsq
  obtain ⟨hZ, hcZ, hOE, hout⟩ := outer_inputs_of_sporadic hOJ2 hOJ3 hJ
  obtain ⟨EY, hP⟩ := exists_pullHyp h hS hZ hcZ hOE hout hidx hE.cfg
  have hsurj := thetaH_surjective h hS hE.cfg.z_cent hE.cfg.z_order hE.cfg.cent_le hout hidx
  obtain ⟨hF1, hF2⟩ := outerInvData_of_sporadic hZ hIJ2 hIJ3 hJ
  exact hR G L z t T E Q x B β h hJ hS hidx hE haut hT hW hN hcent hB hβ8 hSyl hTQ hxQ hxT hxN
    hxz hxt htQ hQz hcomm hconc hsq (hP.exists_outer_involution hsurj hsq hF1)
    (hP.not_mem_L_of_conj hsurj hsq hF2)

end CFSG.EvenSporadicStandard.Fin76b
