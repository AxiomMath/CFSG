module

public import CFSG.GH74.GLS.C3.Layer1.Back114Main
public import CFSG.GH74.GLS.C3.Layer1.BkL27K
public import CFSG.GH74.GLS.C3.Layer1.Back114Aut
public import CFSG.GH74.GLS.C3.Layer1.BackLeaves

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS

@[expose] def B_L114_fusion57 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ n ∈ ({5, 7} : Finset ℕ),
    ∀ (x : G) (K T Q S : Subgroup G) (a : G), IsAConfigW n x K T Q S a →
      a * x * a⁻¹ ∈ T ⊓ K ∧ S = T ⊔ zpowers a ∧
      (n = 7 → ∀ u ∈ centralizer ((Ysub x K T a : Subgroup G) : Set G),
        Odd (orderOf u) → u ∈ CxK x K)

@[expose] def B_L114_final57 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ n ∈ ({5, 7} : Finset ℕ),
    ∀ (x : G) (K T Q S : Subgroup G) (a : G), IsAConfigW n x K T Q S a → S = T ⊔ zpowers a →
      a ∈ normalizer (pPrimeCoreOf 2 (centralizer ({x} : Set G)) : Set G) →
        pPrimeCore 2 ↥(centralizer ({x} : Set G)) = ⊥

theorem b_lemma114_nonEven_of_leaves57 (hA : B_L114_fusion57) (hF : B_L114_final57) :
    B_lemma114_nonEven := by
  intro G _ _ hG hne x K L M T Q h p91 l113
  obtain ⟨n, hn, S, a, hcfg⟩ := C3.Layer1.Back.aconfigW_of_concl h.a p91 l113
  have hn6 : n ≠ 6 := by
    intro hn6
    subst hn6
    obtain ⟨e⟩ := hcfg.kbar
    have h360 : Nat.card (kBar K) = 360 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    have hnoV2 : ¬ ∃ (x' y' : G) (K' : Subgroup G), IsV2Triple x' y' K' := by
      intro hex
      rcases p91.2.2.2 hex with h5 | h7
      · have := card_eq_of_hasL2Model_five h5
        omega
      · obtain ⟨e7⟩ := h7
        have h2520 : Nat.card (kBar K) = 2520 := by
          rw [Nat.card_congr e7.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
          simp [Nat.factorial]
        omega
    rcases h.b with hB1 | hB2
    · obtain ⟨y, hy⟩ := hB1.v2star
      exact hnoV2 ⟨x, y, K, hy.1.1.1.1⟩
    · exact hne hB2.evenType
  have hn57 : n ∈ ({5, 7} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn ⊢
    omega
  obtain ⟨hz, hS, hA7⟩ := hA G hG n hn57 x K T Q S a hcfg
  have hA2 : ∀ u ∈ centralizer ((Ysub x K T a : Subgroup G) : Set G),
      Odd (orderOf u) → u ∈ CxK x K := by
    by_cases h7 : n = 7
    · exact hA7 h7
    · have h56 : n = 5 ∨ n = 6 := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hn
        omega
      exact hcfg.U_le_CxK_of_five_six h56 hz
  exact hF G hG n hn57 x K T Q S a hcfg hS (hcfg.a_mem_normalizer_W hA2)

end CFSG.GH74.GLS.C3.Layer1.Bk
