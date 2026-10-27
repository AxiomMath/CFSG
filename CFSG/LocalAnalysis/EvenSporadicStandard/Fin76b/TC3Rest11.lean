module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3Rest10

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def Fin76bOuterS16 : Prop :=
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
      z ∈ S ∧ Nat.card ↥S = 16) →
    False

@[expose] def Fin76bOuterS8 : Prop :=
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
      z ∈ S ∧ Nat.card ↥S = 8) →
    False

theorem fin76bOuterRest₁₀_of_S (h16 : Fin76bOuterS16) (h8 : Fin76bOuterS8) :
    Fin76bOuterRest₁₀ := by
  intro G _ _ L z t T E Q x B β h hJ hS hidx hE haut hT hW hN hcent hB hβ8 hSyl hTQ hxQ hxT hxN
    hxz hxt htQ hQz hcomm hconc hsq hσ h98 hS16
  obtain ⟨S, hS2, hSC, hSmax, hzS⟩ := exists_maximal_two_subgroup (centralizer (E : Set G))
    (hE.zpowers_le_cent_E (mem_zpowers z)) hE.cfg.z_order
  obtain ⟨hsh, -⟩ := hSyl S hS2 hSC hSmax hzS
  have hge : 8 ≤ Nat.card ↥S := eight_le_card_of_shape hsh.1
  have hle : Nat.card ↥S ≤ 16 := hS16 S hS2 hSC hSmax hzS
  obtain ⟨n, hn⟩ := hS2.exists_card_eq
  have hcases : Nat.card ↥S = 8 ∨ Nat.card ↥S = 16 := by
    rw [hn] at hge hle ⊢
    have h3 : 3 ≤ n := by
      by_contra hlt
      have : 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h4 : n ≤ 4 := by
      by_contra hlt
      have : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases n <;> simp
  rcases hcases with hc | hc
  · exact h8 G L z t T E Q x B β h hJ hS hidx hE haut hT hW hN hcent hB hβ8 hSyl hTQ hxQ hxT hxN
      hxz hxt htQ hQz hcomm hconc hsq hσ h98 ⟨S, hS2, hSC, hSmax, hzS, hc⟩
  · exact h16 G L z t T E Q x B β h hJ hS hidx hE haut hT hW hN hcent hB hβ8 hSyl hTQ hxQ hxT hxN
      hxz hxt htQ hQz hcomm hconc hsq hσ h98 ⟨S, hS2, hSC, hSmax, hzS, hc⟩

end CFSG.EvenSporadicStandard.Fin76b
