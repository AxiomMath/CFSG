module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrRankGap

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open CFSG CFSG.LocalCores Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type*} [Group G]

@[expose] noncomputable def gsMeasure (c : G) (K : Subgroup G) : ℕ ×ₗ (ℕ ×ₗ ℕ) :=
  toLex ((pPrimeCore 2 K).index,
    toLex (pRank 2 ↥(centralizer ({c} : Set G) ⊓ normalizer (K : Set G) ⊓ coreActionKernel K),
      2 ^ (Nat.card ↥(centralizer ({c} : Set G) ⊓ normalizer (K : Set G))).factorization 2))

variable [Finite G]

theorem reachable_unbalancing_triple_central_sylow_maximality {a₀ x₀ : G} {J₀ : Subgroup G}
    (h₀ : GSUnbalancingTriple a₀ x₀ J₀) :
    ∃ (a x : G) (J : Subgroup G), GSUnbalancingTriple a x J ∧ GSReach J₀ J ∧
      (∀ (b y : G) (L : Subgroup G), GSUnbalancingTriple b y L → GSReach J₀ L →
        gsMeasure b L ≤ gsMeasure a J) ∧
      (2 ≤ pRank 2 ↥J → ∀ S : Subgroup G,
        S ≤ centralizer ({a} : Set G) ⊓ normalizer (J : Set G) →
        (∃ P₀ : Sylow 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G)),
          (P₀ : Subgroup _) = S.subgroupOf (centralizer ({a} : Set G) ⊓ normalizer (J : Set G))) →
        ∀ b : G, orderOf b = 2 → b ∈ S → (∀ s ∈ S, s * b = b * s) →
        ∀ L : Subgroup G, UnbalancedGS.GSCorr a J b L →
          UnbalancedGS.GSIsoCorr a J b L ∧
          S ≤ centralizer ({b} : Set G) ⊓ normalizer (L : Set G) ∧
          ∃ P₁ : Sylow 2 ↥(centralizer ({b} : Set G) ⊓ normalizer (L : Set G)),
            (P₁ : Subgroup _) =
              S.subgroupOf (centralizer ({b} : Set G) ⊓ normalizer (L : Set G))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  let X := {p : G × G × Subgroup G // GSUnbalancingTriple p.1 p.2.1 p.2.2 ∧ GSReach J₀ p.2.2}
  have : Nonempty X := ⟨⟨(a₀, x₀, J₀), h₀, GSReach.refl_of_gsUnbalancingTriple h₀⟩⟩
  obtain ⟨⟨⟨a, x, J⟩, hU, hR⟩, hmax⟩ := Finite.exists_max (fun p : X => gsMeasure p.1.1 p.1.2.2)
  dsimp only at hU hR hmax
  have hmax' : ∀ (b y : G) (L : Subgroup G), GSUnbalancingTriple b y L → GSReach J₀ L →
      gsMeasure b L ≤ gsMeasure a J := fun b y L hU' hR' => hmax ⟨(b, y, L), hU', hR'⟩
  refine ⟨a, x, J, hU, hR, hmax', fun hJ2 S hSH hSsyl b hb hbS hbZ L hC => ?_⟩
  obtain ⟨ha, hxo, hax, hJa, -, hJx, -⟩ := gsUnbalancingTriple_iff.mp hU
  have hxN : x ∈ normalizer (J : Set G) := by
    have h := le_normalizer_commutator (zpowers x) J
    rw [commutator_comm, hJx] at h
    exact h (mem_zpowers x)
  have hxH : x ∈ centralizer ({a} : Set G) ⊓ normalizer (J : Set G) :=
    mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hax.symm, hxN⟩
  have hx2 : IsPGroup 2 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo, pow_one])
  obtain ⟨h, hh, hxS⟩ := exists_conjugate_le_of_sylow hSsyl (zpowers_le.mpr hxH) hx2
  have hxhS : h⁻¹ * x * h ∈ S := hxS (conj_mem_conjugate (mem_zpowers x) h)
  have hU' := gsUnbalancingTriple_conj hU (mem_inf.mp hh).1 (mem_inf.mp hh).2
  have hUL := unbalancing_triple_correspondence_transfer hU' hC (hbZ _ hxhS).symm
  have hle := hmax' b _ L hUL (hR.tail hC)
  unfold gsMeasure at hle
  obtain ⟨hdle, hle2⟩ := Prod.Lex.toLex_le_toLex'.mp hle
  dsimp only at hdle hle2
  have hcmp := UnbalancingLocal.correspondence_quotient_order_comparison hC
  have hdge : (pPrimeCore 2 J).index ≤ (pPrimeCore 2 L).index := by
    rw [index_eq_card, index_eq_card]
    exact hcmp.1
  have hdeq : (pPrimeCore 2 L).index = (pPrimeCore 2 J).index := le_antisymm hdle hdge
  obtain ⟨hrank, hord⟩ := Prod.Lex.toLex_le_toLex'.mp (hle2 hdeq)
  dsimp only at hrank hord
  have hLa : conjugate L a = L := by
    by_contra hne
    have hS2 : IsPGroup 2 S := by
      obtain ⟨P₀, hP₀⟩ := hSsyl
      have h1 : IsPGroup 2 ((P₀ : Subgroup _).map
          (centralizer ({a} : Set G) ⊓ normalizer (J : Set G)).subtype) := P₀.isPGroup'.map _
      rwa [hP₀, map_subgroupOf_eq_of_le hSH] at h1
    have hP2 : IsPGroup 2 ↥(S ⊓ (centralizer ({a} : Set G) ⊓ normalizer (J : Set G) ⊓
        coreActionKernel J)) := hS2.to_le inf_le_left
    have hPle : S ⊓ (centralizer ({a} : Set G) ⊓ normalizer (J : Set G) ⊓ coreActionKernel J) ≤
        centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G) ⊓ normalizer (J : Set G) :=
      fun u hu => by
        obtain ⟨huS, huQ⟩ := mem_inf.mp hu
        have hHJ' := (mem_inf.mp huQ).1
        exact mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp hHJ').1,
          mem_centralizer_singleton_iff.mpr (hbZ u huS)⟩, (mem_inf.mp hHJ').2⟩
    have hJP : ∀ u ∈ S ⊓ (centralizer ({a} : Set G) ⊓ normalizer (J : Set G) ⊓
        coreActionKernel J), ∀ j ∈ J, j⁻¹ * u⁻¹ * j * u ∈ (pPrimeCore 2 J).map J.subtype :=
      fun u hu => (mem_coreActionKernel.mp (mem_inf.mp (mem_inf.mp hu).2).2).2
    obtain ⟨-, -, -, -, -, -, -, hrk, hLJ⟩ := swapped_correspondence_centralizer_rank_bound hC
      hne hdeq.symm hP2 hPle (mem_inf_coreActionKernel_of_sylow ha hJa hSsyl) hJP
    rw [hLJ, (sylow_inf_coreActionKernel hSH hSsyl).2] at hrk
    omega
  have hiso : UnbalancedGS.GSIsoCorr a J b L :=
    (hcmp.2.1 hLa).mp (by rw [← index_eq_card, ← index_eq_card]; exact hdeq.symm)
  obtain ⟨-, -, -, -, -, -, -, -, hSyl⟩ :=
    isomorphic_correspondence_sylow_growth hiso rfl rfl rfl rfl
  obtain ⟨hSHL, hrank', -, hstrict, -⟩ := hSyl S hSH hSsyl fun s hs =>
    mem_centralizer_singleton_iff.mpr (hbZ s hs)
  refine ⟨hiso, hSHL, ?_⟩
  by_contra hnot
  have h1 := hstrict hnot
  exact absurd (hord (le_antisymm hrank hrank')) (not_le.mpr h1)

end CFSG.ComponentClassification.UnbalancedCorr
