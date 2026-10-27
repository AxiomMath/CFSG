module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8Lemma112
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3Rest11

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

@[expose] def Fin76bOuterUCent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G) (T E : Subgroup G),
    StdHyp G L → (IsSporadic L .J2 ∨ IsSporadic L .J3) → OuterE G L z t T E → WFacts L t E →
    ∀ S : Subgroup G, IsPGroup 2 S → S ≤ centralizer (E : Set G) →
    (∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S) →
    z ∈ S → Nonempty (S ≃* DihedralGroup 4) →
    ∀ u ∈ S ⊔ E, u * u = 1 → u ∉ zpowers t →
      ∃ X : Subgroup G, X ≤ S ⊔ E ∧ Nonempty (E ≃* X) ∧ u ∉ X ∧ ∀ x ∈ X, u * x = x * u

@[expose] def Fin76bOuterS8₃ : Prop :=
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
    (∃ S : Subgroup G, IsPGroup 2 S ∧ S ≤ centralizer (E : Set G) ∧
      (∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S) ∧
      z ∈ S ∧ Nonempty (S ≃* DihedralGroup 4) ∧
      (∀ g : G, g * z * g⁻¹ ∈ S → g * z * g⁻¹ = z ∨ g * z * g⁻¹ = z * t) ∧
      (∃ N : Subgroup (centralizer (E : Set G)), N.Normal ∧ (∀ x, x ∈ N ↔ Odd (orderOf x)) ∧
        N ⊓ S.subgroupOf (centralizer (E : Set G)) = ⊥ ∧
        (N : Set (centralizer (E : Set G))) *
          (S.subgroupOf (centralizer (E : Set G)) : Set (centralizer (E : Set G))) =
            Set.univ) ∧
      (∀ b ∈ B, ∀ s ∈ S, b * s = s * b) ∧
      (∀ g : G, g * z * g⁻¹ ∈ S ⊔ E →
        ∃ m ∈ normalizer ((S ⊔ E : Subgroup G) : Set G), m * z * m⁻¹ = g * z * g⁻¹)) →
    False

theorem fin76bOuterS8_of_s8₃ (hX : Fin76bOuterUCent) (h3 : Fin76bOuterS8₃) : Fin76bOuterS8 := by
  intro G _ _ L z t T E Q x B β h hJ hS hidx hE haut hT hW hN hcent hB hβ8 hSyl hTQ hxQ hxT hxN
    hxz hxt htQ hQz hcomm hconc hsq hσ h98 hS8
  obtain ⟨S, hS2, hSC, hSmax, hzS, hc8⟩ := hS8
  obtain ⟨hsh, hBS⟩ := hSyl S hS2 hSC hSmax hzS
  have hD8 : Nonempty (S ≃* DihedralGroup 4) := card_eq_eight_dihedral hsh.1 hc8
  have hcfg := hE.cfg
  have htE : t ∈ E := hE.econfig.t_mem
  have htc : ∀ e ∈ E, e * t = t * e := fun e he => hcfg.t_central e (hE.E_le_T he)
  have htS : t ∈ S := mem_of_maximal hS2 hSC hSmax hcfg.t_sq htE htc
  have hSt : ∀ s ∈ S, s * t = t * s := fun s hs => (mem_centralizer_iff.1 (hSC hs) t htE).symm
  have h67 : ∀ g : G, g * z * g⁻¹ ∈ S → g * z * g⁻¹ = z ∨ g * z * g⁻¹ = z * t := by
    intro g hg
    obtain ⟨s, hs, hgs⟩ := hsh.2.2 g hg
    rw [hgs]
    exact conj_z_cases hD8 htS hSt hcfg.t_sq hcfg.t_ne hcfg.t_comm_z hzS hs
  have hodd := hsh.2.1 2 le_rfl hD8
  have h112 := outerLemma112 hE hW hS2 hSC hSmax hzS hD8 hcent h67
    (hX G L z t T E h hJ hE hW S hS2 hSC hSmax hzS hD8)
  exact h3 G L z t T E Q x B β h hJ hS hidx hE haut hT hW hN hcent hB hβ8 hSyl hTQ hxQ hxT hxN
    hxz hxt htQ hQz hcomm hconc hsq hσ h98 ⟨S, hS2, hSC, hSmax, hzS, hD8, h67, hodd, hBS, h112⟩

end CFSG.EvenSporadicStandard.Fin76b
