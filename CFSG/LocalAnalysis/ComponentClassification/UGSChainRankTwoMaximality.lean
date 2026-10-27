module

public import CFSG.LocalAnalysis.ComponentClassification.UGSChainEqualOrderComposition
public import CFSG.LocalAnalysis.ComponentClassification.UGSChainRankDominant
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrReplacementInvolution
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrMaximalTriple

public section

namespace CFSG.ComponentClassification.UGSChain

open CFSG CFSG.LocalCores Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedGS CFSG.ComponentClassification.UnbalancedCorr
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem globally_first_maximal_rank_two_unbalancing_maximality_of_schreier {G : Type} [Group G]
    [Finite G] (hS : SchreierFor Blueprint.Catalog) (hK : Assembly.KProper Blueprint.Catalog G)
    (hZ : ∀ z : G, orderOf z = 2 → z ∉ center G) {a x : G} {J : Subgroup G}
    (hU : GSUnbalancingTriple a x J) (hJ2 : 2 ≤ pRank 2 ↥J)
    (hfirst : ∀ (c v : G) (K : Subgroup G), GSUnbalancingTriple c v K →
      (pPrimeCore 2 K).index ≤ (pPrimeCore 2 J).index)
    (hrank : ∀ (c v : G) (K : Subgroup G), GSUnbalancingTriple c v K → GSReach J K →
      (pPrimeCore 2 K).index = (pPrimeCore 2 J).index →
      pRank 2 ↥(centralizer ({c} : Set G) ⊓ normalizer (K : Set G) ⊓ coreActionKernel K) ≤
        pRank 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G) ⊓ coreActionKernel J))
    (hsyl : ∀ (c v : G) (K : Subgroup G), GSUnbalancingTriple c v K → GSReach J K →
      (pPrimeCore 2 K).index = (pPrimeCore 2 J).index →
      pRank 2 ↥(centralizer ({c} : Set G) ⊓ normalizer (K : Set G) ⊓ coreActionKernel K) =
        pRank 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G) ⊓ coreActionKernel J) →
      2 ^ (Nat.card ↥(centralizer ({c} : Set G) ⊓ normalizer (K : Set G))).factorization 2 ≤
        2 ^ (Nat.card ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G))).factorization 2) :
    GSMaximalUnbalancingTriple a x J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  obtain ⟨ha, hxo, hax, hJa, hJ, hJx, -⟩ := gsUnbalancingTriple_iff.mp hU
  have hmaxJ : ∀ (c v : G) (K : Subgroup G), GSUnbalancingTriple c v K → GSReach J K →
      (pPrimeCore 2 K).index ≤ (pPrimeCore 2 J).index ∧
        ((pPrimeCore 2 K).index = (pPrimeCore 2 J).index →
          pRank 2 ↥(centralizer ({c} : Set G) ⊓ normalizer (K : Set G) ⊓ coreActionKernel K) ≤
            pRank 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G) ⊓
              coreActionKernel J)) :=
    fun c v K hUK hRK => ⟨hfirst c v K hUK, hrank c v K hUK hRK⟩
  have hcl1 : ∀ (b₀ : G) (L₀ : Subgroup G), GSCorr a J b₀ L₀ →
      ∀ y ∈ centralizer ({a} : Set G) ⊓ normalizer (J : Set G), GSUnbalancingTriple b₀ y L₀ →
        GSIsoCorr a J b₀ L₀ := by
    intro b₀ L₀ hC₀ y hyH hU₀
    by_contra hnot₀
    have hb₀b₀ : b₀ * b₀ = 1 := by rw [← pow_two, ← hC₀.2.1, pow_orderOf_eq_one]
    have hyy : y * y = 1 := by rw [← pow_two, ← hU₀.2.1, pow_orderOf_eq_one]
    have hb₀H : b₀ ∈ centralizer ({a} : Set G) ⊓ normalizer (J : Set G) :=
      mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hC₀.2.2.1.symm, hC₀.2.2.2.2.2.2.2.1⟩
    have hEH : closure ({b₀, y} : Set G) ≤ centralizer ({a} : Set G) ⊓ normalizer (J : Set G) := by
      rw [closure_le]
      rintro _ (rfl | rfl)
      · exact hb₀H
      · exact hyH
    obtain ⟨S, hSH, hSsyl, hES⟩ :=
      exists_sylow_two_le hEH (isPGroup_closure_pair hb₀b₀ hyy hU₀.2.2.1)
    have hb₀S : b₀ ∈ S := hES (mem_closure_of_mem (Set.mem_insert b₀ {y}))
    have hyS : y ∈ S := hES (mem_closure_of_mem (Set.mem_insert_of_mem b₀ (Set.mem_singleton y)))
    let X := {p : G × Subgroup G // p.1 ∈ S ∧ GSCorr a J p.1 p.2 ∧
      GSUnbalancingTriple p.1 y p.2 ∧ ¬ GSIsoCorr a J p.1 p.2}
    have : Nonempty X := ⟨⟨(b₀, L₀), hb₀S, hC₀, hU₀, hnot₀⟩⟩
    obtain ⟨⟨⟨b, L⟩, hbS, hC, hUL, hnot⟩, hbest⟩ :=
      Finite.exists_max (fun p : X => Nat.card ↥(S ⊓ centralizer ({p.1.1} : Set G)))
    dsimp only at hbS hC hUL hnot hbest
    obtain ⟨hLne, -⟩ := nonisomorphic_unbalancing_correspondence_rank_gap ha hJa hJ hmaxJ hC hUL
      hnot hSH hSsyl hbS rfl rfl rfl
    obtain ⟨-, -, -, -, -, -, -, R, -, -, -, -, -, -, w, -, -, -, -, e, he, -, -, hQlt, heP, heN,
      heJ, heK, hea, heb, hey⟩ :=
      noncentral_unbalancing_replacement_involution ha hJa hJ hmaxJ hC hUL hnot hSH hSsyl hbS
        rfl rfl rfl hJ2 hyS
    have heZ := hZ e he
    obtain ⟨-, hbo, hab, -, -, hLb, hL, -, -, -⟩ := id hC
    obtain ⟨heL, -, hLe, -⟩ := kProper_core_trivial_orbit_fixed_layer_containment_of_schreier
      hS hK hbo he hab heb.symm heZ hLb hL heK
    obtain ⟨M, -, -, hUM, -, -, hle, hcorr, -⟩ :=
      kProper_unbalancing_orbit_target_production_of_schreier hS hK hUL he heZ heb.symm hey.symm
        heL hLe
    have hdge : (pPrimeCore 2 J).index ≤ (pPrimeCore 2 L).index := by
      rw [index_eq_card, index_eq_card]
      exact (UnbalancingLocal.correspondence_quotient_order_comparison hC).1
    have hdLM : (pPrimeCore 2 L).index = (pPrimeCore 2 M).index :=
      le_antisymm hle ((hfirst e y M hUM).trans hdge)
    have hdJM : (pPrimeCore 2 J).index = (pPrimeCore 2 M).index :=
      le_antisymm (hdge.trans hle) (hfirst e y M hUM)
    have hC2 : GSCorr b L e M := hcorr (Or.inr hdLM)
    obtain ⟨hC3, hmoved⟩ := equal_order_core_trivial_correspondence_composition_of_schreier hS hK
      hC hC2 hea.symm heZ heN heJ hdJM
    have hbest' := hbest ⟨(e, M), (mem_inf.mp heP).1, hC3, hUM, (hmoved (Ne.symm hLne)).2⟩
    exact absurd hbest' (not_le.mpr (card_lt_of_lt hQlt))
  refine ⟨hU, fun b L _ _ hC => ⟨fun y hy hUL => hcl1 b L hC y hy hUL, ?_⟩⟩
  intro S hSH hSsyl hbS hbZ
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
  have hiso := hcl1 b L hC _ (hSH hxhS) hUL
  obtain ⟨-, -, -, -, -, -, hdeq, -, hSyl⟩ :=
    isomorphic_correspondence_sylow_growth hiso rfl rfl rfl rfl
  obtain ⟨hSHL, hrank', -, hstrict, -⟩ := hSyl S hSH hSsyl fun s hs =>
    mem_centralizer_singleton_iff.mpr (hbZ s hs)
  refine ⟨hSHL, ?_⟩
  have hR := GSReach.of_gsCorr hC
  have hrk := le_antisymm (hrank b _ L hUL hR hdeq.symm) hrank'
  by_contra hnot
  exact absurd (hsyl b _ L hUL hR hdeq.symm hrk) (not_le.mpr (hstrict hnot))

end CFSG.ComponentClassification.UGSChain
