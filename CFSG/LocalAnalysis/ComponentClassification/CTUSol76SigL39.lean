module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigComp

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {𝒜 : Thm13Ambient} {N K K' : Subgroup G}

theorem wGroup_zpowers_eq_of_commute (h32 : Lemma32FullFor 𝒜) (hG : 𝒜 G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {E : Subgroup G} (hE : IsKleinFour E) (hEK : E ≤ K) {t t' : G}
    (ht : t ∈ K' ⊓ centralizer (E : Set G)) (ht' : t' ∈ K' ⊓ centralizer (E : Set G))
    (ht2 : orderOf t = 2) (ht'2 : orderOf t' = 2) (htt' : t ≠ t') (hcomm : t * t' = t' * t) :
    wGroup E (zpowers t) = wGroup E (zpowers t') := by
  set V' := closure ({t, t'} : Set G) with hV'
  have hV'4 : IsKleinFour V' :=
    UnbalancedGS.ReciprocalFusion.isKleinFour_closure_pair ht2 ht'2 hcomm htt'
  have hV'K' : V' ≤ K' := by
    rw [hV', closure_le]
    rintro x (rfl | rfl)
    · exact ht.1
    · exact ht'.1
  have hEV' : E ≤ centralizer (V' : Set G) := by
    intro e he
    rw [hV', mem_centralizer_iff]
    intro x hx
    have hxC : x ∈ centralizer (E : Set G) := by
      have hle : V' ≤ centralizer (E : Set G) := by
        rw [hV', closure_le]
        rintro y (rfl | rfl)
        · exact ht.2
        · exact ht'.2
      exact hle hx
    exact ((mem_centralizer_iff.mp hxC) e he).symm
  have htV' : t ∈ V' := subset_closure (Set.mem_insert t _)
  have ht'V' : t' ∈ V' := subset_closure (Set.mem_insert_of_mem t rfl)
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht2; norm_num at ht2
  have ht'1 : t' ≠ 1 := fun h => by rw [h, orderOf_one] at ht'2; norm_num at ht'2
  rw [← wGroup_eq_wGroup_zpowers h32 hG hN hK hK' hne hV'4 hV'K' hE hEK hEV' htV' ht1,
    wGroup_eq_wGroup_zpowers h32 hG hN hK hK' hne hV'4 hV'K' hE hEK hEV' ht'V' ht'1]

theorem wGroup_zpowers_eq_of_reachable (h32 : Lemma32FullFor 𝒜) (hG : 𝒜 G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {E : Subgroup G} (hE : IsKleinFour E) (hEK : E ≤ K)
    {a b : {t : ↥(K' ⊓ centralizer (E : Set G)) // orderOf t = 2}}
    (h : (CFSG.Assembly.involutionGraph ↥(K' ⊓ centralizer (E : Set G))).Reachable a b) :
    wGroup E (zpowers (((a : ↥(K' ⊓ centralizer (E : Set G))) : G))) =
      wGroup E (zpowers (((b : ↥(K' ⊓ centralizer (E : Set G))) : G))) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | @tail c d _ hadj ih =>
    rw [ih]
    rw [CFSG.Assembly.involutionGraph, SimpleGraph.fromRel_adj] at hadj
    obtain ⟨hcd, hcomm⟩ := hadj
    have hc2 : orderOf (((c : ↥(K' ⊓ centralizer (E : Set G))) : G)) = 2 := by
      rw [Subgroup.orderOf_coe]; exact c.2
    have hd2 : orderOf (((d : ↥(K' ⊓ centralizer (E : Set G))) : G)) = 2 := by
      rw [Subgroup.orderOf_coe]; exact d.2
    have hne' : (((c : ↥(K' ⊓ centralizer (E : Set G))) : G)) ≠
        (((d : ↥(K' ⊓ centralizer (E : Set G))) : G)) :=
      fun h => hcd (Subtype.ext (Subtype.ext h))
    have hcomm' : (((c : ↥(K' ⊓ centralizer (E : Set G))) : G)) *
        (((d : ↥(K' ⊓ centralizer (E : Set G))) : G)) =
          (((d : ↥(K' ⊓ centralizer (E : Set G))) : G)) *
            (((c : ↥(K' ⊓ centralizer (E : Set G))) : G)) := by
      rcases hcomm with h | h
      · exact congrArg Subtype.val h
      · exact (congrArg Subtype.val h).symm
    exact wGroup_zpowers_eq_of_commute h32 hG hN hK hK' hne hE hEK c.1.2 d.1.2 hc2 hd2
      hne' hcomm'

theorem le_normalizer_wGroup_of_preconnected (h32 : Lemma32FullFor 𝒜) (hG : 𝒜 G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K') (hBK : B ≤ K)
    (hBV : B ≤ centralizer (V : Set G)) (hB : CFSG.Open.IsElemAbelian 2 B)
    (hB8 : Nat.card B = 8) (hE : IsKleinFour E) (hEB : E ≤ B)
    (hconn : (CFSG.Assembly.involutionGraph ↥(K' ⊓ centralizer (E : Set G))).Preconnected) :
    K' ≤ normalizer (wGroup B V : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := K' ⊓ centralizer (E : Set G) with hY
  have hEK : E ≤ K := hEB.trans hBK
  have hE2 := isPGroup_of_isKleinFour hE
  have hEQ : E ≤ coreActionKernel K' := hEK.trans (le_coreActionKernel_of_ne hK' hK hne.symm)
  have hK'q : IsQuasisimple (↥K' ⧸ pPrimeCore 2 ↥K') :=
    isQuasisimple_quotient_of_isPComponent hK'.1.1 hK'.1.2
  obtain ⟨-, -, hsup, -⟩ := cover_facts hK'q inf_le_left (inf_centralizer_sup_oddCoreIn_eq hE2 hEQ)
  have hWE : wGroup E V = wGroup B V :=
    wGroup_eq_of_le h32 hG hN hK hK' hne hV hVK' hBK hBV hB hE hEB
  obtain ⟨v, hv, hv1⟩ : ∃ v ∈ V, v ≠ 1 := by
    by_contra h
    push Not at h
    have h4 := hV.card_four
    rw [show V = ⊥ from eq_bot_iff.mpr fun x hx => (mem_bot).mpr (h x hx), card_bot] at h4
    norm_num at h4
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
  ·
    rw [oddResidualIn, closure_le]
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
  ·
    refine le_normalizer_wGroup_of_odd h32 hG hN hK hK' hne hV hVK' hBK hBV hB hB8
      (coprime_card_oddCoreIn K') ?_ ?_
    · exact fun b hb => mem_normalizer_iff_map_conj_eq.mpr
        (map_conj_oddCoreIn (le_normalizer_of_mem_kStarComponents hK hK' (hBK hb)))
    · exact fun w hw => le_normalizer_oddCoreIn K' (hVK' hw)

@[expose] def CommFourIn (X F F' : Subgroup G) : Prop :=
  IsKleinFour F ∧ IsKleinFour F' ∧ F ≤ X ∧ F' ≤ X ∧ F ≤ centralizer (F' : Set G)

theorem wGroup_eq_of_reflTransGen (h32 : Lemma32FullFor 𝒜) (hG : 𝒜 G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V E F : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (h : Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (V : Set G))) E F) :
    wGroup F V = wGroup E V := by
  induction h with
  | refl => rfl
  | @tail C D _ hCD ih =>
    rw [← ih]
    obtain ⟨hC, hD, hCX, hDX, hCDc⟩ := hCD
    have hDCc : D ≤ centralizer (C : Set G) := fun d hd => mem_centralizer_iff.mpr fun c hc =>
      ((mem_centralizer_iff.mp (hCDc hc)) d hd).symm
    exact le_antisymm
      (wGroup_le_wGroup h32 hG hN hK hK' hne hV hVK' hD (hDX.trans inf_le_left)
        (hDX.trans inf_le_right) hC (hCX.trans inf_le_left) (hCX.trans inf_le_right) hDCc)
      (wGroup_le_wGroup h32 hG hN hK hK' hne hV hVK' hC (hCX.trans inf_le_left)
        (hCX.trans inf_le_right) hD (hDX.trans inf_le_left) (hDX.trans inf_le_right) hCDc)

theorem le_normalizer_wGroup_of_twoConnected (h32 : Lemma32FullFor 𝒜) (hG : 𝒜 G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K') (hBK : B ≤ K)
    (hBV : B ≤ centralizer (V : Set G)) (hB : CFSG.Open.IsElemAbelian 2 B)
    (hB8 : Nat.card B = 8) (hE : IsKleinFour E) (hEB : E ≤ B)
    (hconn : ∀ F : Subgroup G, IsKleinFour F → F ≤ K ⊓ centralizer (V : Set G) →
      Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (V : Set G))) E F) :
    K ≤ normalizer (wGroup B V : Set G) := by
  have hWE : wGroup E V = wGroup B V :=
    wGroup_eq_of_le h32 hG hN hK hK' hne hV hVK' hBK hBV hB hE hEB
  have hV2 := isPGroup_of_isKleinFour hV
  have hVQ : V ≤ coreActionKernel K := hVK'.trans (le_coreActionKernel_of_ne hK hK' hne)
  rw [← inf_centralizer_sup_oddCoreIn_eq hV2 hVQ]
  refine sup_le ?_ ?_
  ·
    intro g hg
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
    have hEX : E ≤ K ⊓ centralizer (V : Set G) := le_inf (hEB.trans hBK) (hEB.trans hBV)
    have hEgX : Eg ≤ K ⊓ centralizer (V : Set G) := by
      rintro _ ⟨e, he, rfl⟩
      exact (mul_mem (mul_mem hg (hEX he)) (inv_mem hg))
    have key : (wGroup B V).map (MulAut.conj g).toMonoidHom = wGroup B V := by
      rw [← hWE, map_wGroup, hVg]
      exact wGroup_eq_of_reflTransGen h32 hG hN hK hK' hne hV hVK' (hconn Eg hEg4 hEgX)
    exact mem_normalizer_iff_map_conj_eq.mpr key
  ·
    refine le_normalizer_wGroup_of_odd h32 hG hN hK hK' hne hV hVK' hBK hBV hB hB8
      (coprime_card_oddCoreIn K) ?_ ?_
    · exact fun b hb => le_normalizer_oddCoreIn K (hBK hb)
    · exact fun w hw => mem_normalizer_iff_map_conj_eq.mpr
        (map_conj_oddCoreIn (le_normalizer_of_mem_kStarComponents hK' hK (hVK' hw)))

end CFSG.ComponentClassification.Sol76.Sig
