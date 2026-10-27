module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3Rest9
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3Nine10

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def Fin76bOuterRest₁₀ : Prop :=
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
    (∀ S : Subgroup G, IsPGroup 2 S → S ≤ centralizer (E : Set G) →
      (∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S) →
      z ∈ S → Nat.card ↥S ≤ 16) →
    False

theorem fin76bOuterRest₉_of_rest₁₀ (hFin : FinK16) (hR : Fin76bOuterRest₁₀) : Fin76bOuterRest₉ := by
  intro G _ _ L z t T E Q x B β h hJ hS hidx hE haut hT hW hN hcent hB hβ8 hSyl hTQ hxQ hxT hxN
    hxz hxt htQ hQz hcomm hconc hsq hσ h98
  refine hR G L z t T E Q x B β h hJ hS hidx hE haut hT hW hN hcent hB hβ8 hSyl hTQ hxQ hxT hxN
    hxz hxt htQ hQz hcomm hconc hsq hσ h98 ?_
  intro S hS2 hSC hSmax hzS
  obtain ⟨hsh, hBS⟩ := hSyl S hS2 hSC hSmax hzS
  obtain ⟨hz, hc⟩ := hconc
  exact card_le_sixteen_of_finK16 hFin (hE.cfg.T_pgroup.to_le hE.E_le_T) hE.E_le_L hB.D_quot hβ8
    hSC (fun s hs => (hBS β hB.beta_mem s hs).symm) hsh.1 hc.2

end CFSG.EvenSporadicStandard.Fin76b
