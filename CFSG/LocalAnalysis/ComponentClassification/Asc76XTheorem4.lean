module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76XLemma316
public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XGoldschmidt

public section

namespace CFSG.ComponentClassification.Asc76X

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76
open scoped Pointwise commutatorElement

@[expose] def Asc76FinalStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K J R T S : Subgroup G),
    MinCounter Ω → K ∈ Ω → Ω = Set.range (rightConjugate K) →
    (∀ M ∈ Ω, ∀ N ∈ Ω, reach Ω M N) →
    (∀ L ∈ Ω, L ≤ sSup (nbr Ω K) ↔ L ∈ nbr Ω K) → IsSzOrU3 (BarGroup (sSup (nbr Ω K))) →
    (∀ M ∈ Ω, (∀ L ∈ nbr Ω K, adj Ω L M) → M = K) →
    adj Ω K J → IsSylowOf 2 R K → IsSylowOf 2 T J → IsSylowOf 2 S ⊤ → R ≤ S → T ≤ S →
    (∀ L ∈ Ω, ∀ P : Subgroup G, IsSylowOf 2 P L → P ≤ S → P = R ∨ P = T) →
    (∀ z ∈ omega1 R ⊔ omega1 T, ∀ g : G, g⁻¹ * z * g ∈ S →
      g⁻¹ * z * g ∈ omega1 R ⊔ omega1 T) →
    (sSup (nbr Ω K)).Normal

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem MinCounter.false (hM : MinCounter Ω) (hI : Sec3Inputs) (hesc : GoldschmidtEscape)
    (hfin : Asc76FinalStep) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.setting
  obtain ⟨K, hK⟩ : Ω.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact hM.not_conc fun K hK => absurd (h ▸ hK) (Set.notMem_empty K)
  have hΩK := hM.lemma312 hI.h22 hI.hB hK
  obtain ⟨R, hR⟩ := Sec3Setting.exists_sylow K
  obtain ⟨S, hS, hRS, hgood⟩ := hM.exists_sylow_good hK hR
  obtain ⟨hπ, -, -⟩ := hM.nbr_facts hI hK
  obtain ⟨J₀, hJ₀, -⟩ := hπ.nontrivial
  have hJ₀' : adj Ω K J₀ := hJ₀
  have hXN : sSup (perp Ω K) ≤ normalizer (K : Set G) := hΩ.sSup_perp_le_normalizer hI.h22 hK
  obtain ⟨T₀, hT₀⟩ := Sec3Setting.exists_sylow J₀
  have hT₀' := isSylowOf_iff_card.mp hT₀
  have hJ₀X : J₀ ≤ sSup (perp Ω K) := le_sSup (hΩ.mem_perp_of_le_normalizer hJ₀'.1 hJ₀'.2.2)
  obtain ⟨P, hP, hT₀P⟩ := exists_isSylowOf_le (hT₀'.1.trans hJ₀X) (IsPGroup.of_card hT₀'.2)
  obtain ⟨x, hx, hPx⟩ := exists_conj_of_isSylowOf hgood hP
  have hTS : rightConjugate T₀ x⁻¹ ≤ S := by
    intro y hy
    rw [mem_rightConjugate_iff, inv_inv] at hy
    have h1 := hT₀P hy
    rw [hPx, mem_rightConjugate_iff] at h1
    have e : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
    rw [e] at h1
    exact h1.1
  have hc : Config Ω K (rightConjugate J₀ x⁻¹) R (rightConjugate T₀ x⁻¹) S :=
    ⟨hK, adj_rightConjugate_of_mem_normalizer hΩ.conj_mem hJ₀' (inv_mem (hXN hx)), hR,
      isSylowOf_rightConjugate hT₀ x⁻¹, hS, hRS, hTS, hgood⟩
  have h314 := hM.lemma314 hI.h22 hI.hB hI.h26 hI.h28 hK
  have hAn := hfin G Ω K _ R _ S hM hK hΩK (hM.lemma313 hI.h22 hI.hB hI.h26) h314.1 h314.2.1
    h314.2.2 hc.adjKJ hR hc.sylowT hS hRS hTS (fun L hL P hP hPS => hc.sylow_eq hM hI hL hP hPS)
    (hc.lemma316 hM hI hesc)
  have hJ : rightConjugate J₀ x⁻¹ ∈ Set.range (rightConjugate K) := by
    rw [← hΩK]
    exact hc.J_mem
  obtain ⟨g, hg⟩ := hJ
  have hKA : K ≤ sSup (nbr Ω K) := by
    intro k hk
    have h1 : g⁻¹ * k * g ∈ rightConjugate J₀ x⁻¹ := by
      rw [← hg, mem_rightConjugate_iff]
      simpa [mul_assoc] using hk
    have hJn : rightConjugate J₀ x⁻¹ ∈ nbr Ω K := hc.adjKJ
    have h2 := hAn.conj_mem _ (le_sSup hJn h1) g
    simpa [mul_assoc] using h2
  exact ((h314.1 K hK).mp hKA).2.1 rfl

theorem asc76Theorem4_of_finalStep (h22 : Lemma22Four) (h26 : L26.Asc76Lemma26) (h28 : Asc76Lemma28)
    (hfin : Asc76FinalStep) : Asc76Theorem4 :=
  asc76Theorem4_of_forall_not_minCounter fun _ _ _ _ hM =>
    hM.false ⟨h22, benderFacts, h26, h28⟩ goldschmidtEscape hfin

theorem asc76Theorem1_of_finalStep (h22 : Lemma22Four) (h26 : L26.Asc76Lemma26) (h28 : Asc76Lemma28)
    (hfin : Asc76FinalStep) : Asc76Theorem1 :=
  asc76Theorem1_of_theorem4 benderFacts (asc76Theorem4_of_finalStep h22 h26 h28 hfin)

end CFSG.ComponentClassification.Asc76X
