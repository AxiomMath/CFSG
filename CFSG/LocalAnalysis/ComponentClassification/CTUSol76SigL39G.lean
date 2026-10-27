module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigWG
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigL39

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {N K K' : Subgroup G}

theorem oddCoreIn_le_normalizer_wGroup_of_mem (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hBQ : B ≤ coreActionKernel K') (hBV : B ≤ centralizer (V : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B) (hB8 : Nat.card B = 8) (hE : IsKleinFour E)
    (hEB : E ≤ B) (hEK : E ≤ K) (hBN : B ≤ N) :
    oddCoreIn N ≤ normalizer (wGroup B V : Set G) :=
  le_normalizer_wGroup_of_odd_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hE hEB hEK hB8
    (coprime_card_oddCoreIn N) (hBN.trans (le_normalizer_oddCoreIn N))
    ((hVK'.trans hK'.1.1).trans (le_normalizer_oddCoreIn N))

theorem le_normalizer_wGroup_of_ne_of_mem (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hBQ : B ≤ coreActionKernel K') (hBV : B ≤ centralizer (V : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B) (hB8 : Nat.card B = 8) (hE : IsKleinFour E)
    (hEB : E ≤ B) (hEK : E ≤ K) (hBN : B ≤ N) {K'' : Subgroup G}
    (hK'' : K'' ∈ kStarComponents N) (hK''K : K'' ≠ K) (hK''K' : K'' ≠ K') :
    K'' ≤ normalizer (wGroup B V : Set G) := by
  have hE2 : IsPGroup 2 E := isPGroup_of_isKleinFour hE
  have hV2 := isPGroup_of_isKleinFour hV
  have hEV : E ≤ centralizer (V : Set G) := hEB.trans hBV
  have hS2 := isPGroup_sup_of_le_centralizer hE2 hV2 hEV
  have hSQ : E ⊔ V ≤ coreActionKernel K'' :=
    sup_le (hEK.trans (le_coreActionKernel_of_ne hK'' hK hK''K))
      (hVK'.trans (le_coreActionKernel_of_ne hK'' hK' hK''K'))
  have hcov := inf_centralizer_sup_oddCoreIn_eq hS2 hSQ
  obtain ⟨v, hv, hv1⟩ := exists_mem_ne_one_of_isKleinFour hV
  rw [← hcov]
  refine sup_le ?_ ?_
  ·
    intro x hx
    have hxS : x ∈ centralizer ((E ⊔ V : Subgroup G) : Set G) := hx.2
    have hxE : x ∈ centralizer (E : Set G) := centralizer_le (by exact_mod_cast le_sup_left) hxS
    have hxV : x ∈ centralizer (V : Set G) := centralizer_le (by exact_mod_cast le_sup_right) hxS
    exact le_normalizer_wGroup_of_mem_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hE hEB
      hEK hE hEB hv hv1 (Subgroup.centralizer_le_normalizer (E : Set G) hxE)
      (centralizer_le (Set.singleton_subset_iff.mpr hv) hxV)
  · exact (oddCoreIn_le_of_isTwoComponentIn hK''.1).trans
      (oddCoreIn_le_normalizer_wGroup_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8 hE hEB
        hEK hBN)

theorem le_normalizer_wGroup_of_preconnected_of_mem (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hBQ : B ≤ coreActionKernel K') (hBV : B ≤ centralizer (V : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B) (hB8 : Nat.card B = 8) (hE : IsKleinFour E)
    (hEB : E ≤ B) (hEK : E ≤ K)
    (hconn : (CFSG.Assembly.involutionGraph ↥(K' ⊓ centralizer (E : Set G))).Preconnected) :
    K' ≤ normalizer (wGroup B V : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h32 := lemma32FullFor_simple_of_twoPart hq hR1
  set Y := K' ⊓ centralizer (E : Set G) with hY
  have hE2 := isPGroup_of_isKleinFour hE
  have hEQ : E ≤ coreActionKernel K' := hEK.trans (le_coreActionKernel_of_ne hK' hK hne.symm)
  have hK'q : IsQuasisimple (↥K' ⧸ pPrimeCore 2 ↥K') :=
    isQuasisimple_quotient_of_isPComponent hK'.1.1 hK'.1.2
  obtain ⟨-, -, hsup, -⟩ := cover_facts hK'q inf_le_left (inf_centralizer_sup_oddCoreIn_eq hE2 hEQ)
  have hWE : wGroup E V = wGroup B V :=
    wGroup_eq_of_le_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hE hEB hEK hE hEB
  obtain ⟨v, hv, hv1⟩ := exists_mem_ne_one_of_isKleinFour hV
  have hv2 : orderOf v = 2 := orderOf_eq_two_of_isKleinFour hV hv hv1
  have hvY : v ∈ Y := ⟨hVK' hv, fun e he =>
    ((mem_centralizer_iff.mp (hBV (hEB he))) v hv).symm⟩
  have hWv : wGroup E (zpowers v) = wGroup B V := by
    rw [← hWE, wGroup_eq_wGroup_zpowers h32 hG hN hK hK' hne hV hVK' hE hEK
      (hEB.trans hBV) hv hv1]
  set v₀ : {t : ↥Y // orderOf t = 2} := ⟨⟨v, hvY⟩, by rw [Subgroup.orderOf_mk]; exact hv2⟩
  have hWt : ∀ t ∈ Y, orderOf t = 2 → wGroup E (zpowers t) = wGroup B V := by
    intro t htY ht2
    set t₀ : {t : ↥Y // orderOf t = 2} := ⟨⟨t, htY⟩, by rw [Subgroup.orderOf_mk]; exact ht2⟩
    rw [← hWv]
    exact (wGroup_zpowers_eq_of_reachable h32 hG hN hK hK' hne hE hEK (hconn v₀ t₀)).symm
  rw [← hsup]
  refine sup_le ?_ ?_
  · rw [oddResidualIn, closure_le]
    rintro x ⟨hxY, k, hk⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [pow_zero, orderOf_eq_one_iff] at hk
      rw [hk]
      exact one_mem _
    · set t := x ^ (2 ^ (k - 1)) with ht
      have ht2 : orderOf t = 2 := by
        refine orderOf_eq_prime ?_ ?_
        · rw [ht, ← pow_mul, ← pow_succ, Nat.sub_add_cancel hk0, ← hk, pow_orderOf_eq_one]
        · rw [ht]
          exact pow_ne_one_of_lt_orderOf (by positivity)
            (by rw [hk]; exact Nat.pow_lt_pow_right (by norm_num) (by omega))
      have htY : t ∈ Y := pow_mem hxY _
      have hxE : x ∈ normalizer (E : Set G) :=
        Subgroup.centralizer_le_normalizer (E : Set G) hxY.2
      have hxt : x ∈ normalizer ((zpowers t : Subgroup G) : Set G) := by
        refine Subgroup.centralizer_le_normalizer _ ?_
        rw [centralizer_zpowers_eq, mem_centralizer_singleton_iff, ht]
        exact (Commute.self_pow x _).eq
      have h := le_normalizer_wGroup hxE hxt
      rwa [hWt t htY ht2] at h
  · refine le_normalizer_wGroup_of_odd_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hE hEB
      hEK hB8 (coprime_card_oddCoreIn K') ?_ ?_
    · exact fun b hb => mem_normalizer_iff_map_conj_eq.mpr (map_conj_oddCoreIn (hBQ hb).1)
    · exact fun w hw => le_normalizer_oddCoreIn K' (hVK' hw)

theorem le_normalizer_wGroup_of_twoConnected_of_mem (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hBQ : B ≤ coreActionKernel K') (hBV : B ≤ centralizer (V : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B) (hB8 : Nat.card B = 8) (hE : IsKleinFour E)
    (hEB : E ≤ B) (hEK : E ≤ K) (hBN : B ≤ N)
    (hconn : ∀ F : Subgroup G, IsKleinFour F → F ≤ K ⊓ centralizer (V : Set G) →
      Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (V : Set G))) E F) :
    K ≤ normalizer (wGroup B V : Set G) := by
  have h32 := lemma32FullFor_simple_of_twoPart hq hR1
  have hWE : wGroup E V = wGroup B V :=
    wGroup_eq_of_le_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hE hEB hEK hE hEB
  have hV2 := isPGroup_of_isKleinFour hV
  have hVQ : V ≤ coreActionKernel K := hVK'.trans (le_coreActionKernel_of_ne hK hK' hne)
  rw [← inf_centralizer_sup_oddCoreIn_eq hV2 hVQ]
  refine sup_le ?_ ?_
  · intro g hg
    have hVg : V.map (MulAut.conj g).toMonoidHom = V := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        show g * y * g⁻¹ ∈ V
        have hgy : g * y = y * g := ((mem_centralizer_iff.mp hg.2) y hy).symm
        rw [hgy, mul_inv_cancel_right]
        exact hy
      · intro hx
        refine ⟨x, hx, ?_⟩
        show g * x * g⁻¹ = x
        have hgx : g * x = x * g := ((mem_centralizer_iff.mp hg.2) x hx).symm
        rw [hgx, mul_inv_cancel_right]
    set Eg := E.map (MulAut.conj g).toMonoidHom with hEg
    have hEg4 : IsKleinFour Eg := by
      refine isKleinFour_of_card_eq_four ?_ fun x hx => ?_
      · rw [hEg, Subgroup.card_map_of_injective (MulAut.conj g).injective, hE.card_four]
      · obtain ⟨v, hv, rfl⟩ := hx
        rw [← map_pow, sq_eq_one_of_isKleinFour hE hv, map_one]
    have hEX : E ≤ K ⊓ centralizer (V : Set G) := le_inf hEK (hEB.trans hBV)
    have hEgX : Eg ≤ K ⊓ centralizer (V : Set G) := by
      rintro _ ⟨e, he, rfl⟩
      exact (mul_mem (mul_mem hg (hEX he)) (inv_mem hg))
    have key : (wGroup B V).map (MulAut.conj g).toMonoidHom = wGroup B V := by
      rw [← hWE, map_wGroup, hVg]
      exact wGroup_eq_of_reflTransGen h32 hG hN hK hK' hne hV hVK' (hconn Eg hEg4 hEgX)
    exact mem_normalizer_iff_map_conj_eq.mpr key
  · exact (oddCoreIn_le_of_isTwoComponentIn hK.1).trans
      (oddCoreIn_le_normalizer_wGroup_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8 hE hEB
        hEK hBN)

end CFSG.ComponentClassification.Sol76.Sig
