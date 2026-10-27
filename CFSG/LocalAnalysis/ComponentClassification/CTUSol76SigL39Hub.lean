module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76SigLift
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13

variable {G : Type} [Group G] [Finite G] {N K K' : Subgroup G}

theorem isKleinFour_zpowers_sup_zpowers {x y : G} (hx2 : orderOf x = 2) (hy2 : orderOf y = 2)
    (hxy : x ≠ y) (hc : x * y = y * x) : IsKleinFour (zpowers x ⊔ zpowers y : Subgroup G) := by
  have hxsq : x ^ 2 = 1 := Sig.sq_eq_one_of_orderOf_eq_two hx2
  have hysq : y ^ 2 = 1 := Sig.sq_eq_one_of_orderOf_eq_two hy2
  have hyx : y ∉ zpowers x := by
    intro h
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
    have hy1 : y ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hy2; norm_num at hy2
    have hkm : x ^ (k % 2) = x ^ k := by
      have := zpow_mod_orderOf x k
      rwa [hx2, Nat.cast_ofNat] at this
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · apply hy1
      rw [← hk, ← hkm, h0, zpow_zero]
    · apply hxy
      rw [← hk, ← hkm, h1, zpow_one]
  have hcard := FooteLit.card_sup_zpowers_eq hyx hysq fun w hw => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    exact (Commute.zpow_left hc k).eq
  refine FooteLit.isKleinFour_of_card_eq_four ?_ ?_
  · rw [hcard, Nat.card_zpowers, hx2]
  · exact FooteLit.sq_eq_one_of_mem_sup (fun g hg => FooteLit.sq_eq_one_of_mem_zpowers hxsq hg)
      (fun g hg => FooteLit.sq_eq_one_of_mem_zpowers hysq hg) fun g hg h hh => by
        obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hg
        obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hh
        exact (Commute.zpow_zpow hc i j).eq

theorem le_normalizer_wGroup_of_hub (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hBQ : B ≤ coreActionKernel K') (hBV : B ≤ centralizer (V : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B) (hB8 : Nat.card B = 8) (hE : IsKleinFour E)
    (hEB : E ≤ B) (hEK : E ≤ K) (hBN : B ≤ N) {b : G} (hb2 : orderOf b = 2) (hbK : b ∉ K)
    (hbQ' : b ∈ coreActionKernel K') (hbQ : b ∈ coreActionKernel K)
    (hbV : b ∈ centralizer (V : Set G)) (hbE : b ∈ centralizer (E : Set G))
    (hconn : (CFSG.Assembly.involutionGraph (coreQuot K)).Preconnected) :
    K ≤ normalizer (wGroup B V : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbsq : b ^ 2 = 1 := Sig.sq_eq_one_of_orderOf_eq_two hb2
  have hKQ' : K ≤ coreActionKernel K' := le_coreActionKernel_of_ne hK' hK hne.symm
  have hWE : wGroup E V = wGroup B V :=
    wGroup_eq_of_le_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hE hEB hEK hE hEB
  set S := V ⊔ zpowers b with hSdef
  have hSsq : ∀ s ∈ S, s ^ 2 = 1 :=
    FooteLit.sq_eq_one_of_mem_sup (fun v hv => Sig.sq_eq_one_of_isKleinFour hV hv)
      (fun g hg => FooteLit.sq_eq_one_of_mem_zpowers hbsq hg) fun v hv g hg => by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
        exact (Commute.zpow_right (mem_centralizer_iff.mp hbV v hv) k).eq
  have hS2 : IsPGroup 2 S := isPGroup_of_sq_eq_one hSsq
  have hSQ : S ≤ coreActionKernel K :=
    sup_le (hVK'.trans (le_coreActionKernel_of_ne hK hK' hne)) (zpowers_le.mpr hbQ)
  set Y := K ⊓ centralizer (S : Set G) with hYdef
  have hYconn := involutionGraph_preconnected_of_quot hK hS2 hSQ hconn
  have hYV : ∀ y ∈ Y, y ∈ centralizer (V : Set G) := fun y hy =>
    centralizer_le (le_sup_left : V ≤ S) hy.2
  have hYb : ∀ y ∈ Y, y * b = b * y := fun y hy =>
    ((mem_centralizer_iff.mp hy.2) b (mem_sup_right (mem_zpowers b))).symm
  have hyb : ∀ y ∈ Y, orderOf y = 2 → IsKleinFour (zpowers y ⊔ zpowers b : Subgroup G) :=
    fun y hy hy2 =>
    isKleinFour_zpowers_sup_zpowers hy2 hb2 (fun h => hbK (h ▸ hy.1)) (hYb y hy)
  have hhub : ∀ F : Subgroup G, IsKleinFour F → F ≤ Y → ∀ f ∈ F, orderOf f = 2 →
      wGroup F V = wGroup (zpowers f ⊔ zpowers b) V := by
    intro F hF hFY f hf hf2
    have hbF : b ∉ F := fun h => hbK (hFY h).1
    obtain ⟨hB'2, hB'8⟩ := FooteLit.sup_zpowers_spec hF hbF hbsq fun w hw => hYb w (hFY hw)
    have hB'e : CFSG.Open.IsElemAbelian 2 (F ⊔ zpowers b) :=
      ⟨FooteLit.isMulCommutative_of_sq_eq_one hB'2, hB'2⟩
    have hB'Q : F ⊔ zpowers b ≤ coreActionKernel K' :=
      sup_le ((show F ≤ K from fun x hx => (hFY hx).1).trans hKQ') (zpowers_le.mpr hbQ')
    have hB'V : F ⊔ zpowers b ≤ centralizer (V : Set G) :=
      sup_le (fun x hx => hYV x (hFY hx)) (zpowers_le.mpr hbV)
    have hFK : F ≤ K := fun x hx => (hFY hx).1
    rw [wGroup_eq_of_le_of_mem hq hR1 hG hN hK hK' hne hV hVK' hB'Q hB'V hB'e hF le_sup_left hFK
        hF le_sup_left,
      wGroup_eq_of_le_of_mem hq hR1 hG hN hK hK' hne hV hVK' hB'Q hB'V hB'e hF le_sup_left hFK
        (hyb f (hFY hf) hf2) (sup_le_sup_right (zpowers_le.mpr hf) _)]
  set T : {y : ↥Y // orderOf y = 2} → Subgroup G :=
    fun t => zpowers ((t.1 : ↥Y) : G) ⊔ zpowers b with hTdef
  have hadj : ∀ t t' : {y : ↥Y // orderOf y = 2},
      (CFSG.Assembly.involutionGraph ↥Y).Adj t t' → wGroup (T t) V = wGroup (T t') V := by
    intro t t' h
    rw [CFSG.Assembly.involutionGraph, SimpleGraph.fromRel_adj] at h
    obtain ⟨hne', hc⟩ := h
    set y : G := ((t.1 : ↥Y) : G) with hy
    set y' : G := ((t'.1 : ↥Y) : G) with hy'
    have hy2 : orderOf y = 2 := by rw [hy, Subgroup.orderOf_coe]; exact t.2
    have hy'2 : orderOf y' = 2 := by rw [hy', Subgroup.orderOf_coe]; exact t'.2
    have hyy' : y * y' = y' * y := by
      rcases hc with hc | hc
      · exact congrArg Subtype.val hc
      · exact (congrArg Subtype.val hc).symm
    have hne'' : y ≠ y' := fun h => hne' (Subtype.ext (Subtype.ext h))
    have hF := isKleinFour_zpowers_sup_zpowers hy2 hy'2 hne'' hyy'
    have hFY : zpowers y ⊔ zpowers y' ≤ Y := sup_le (zpowers_le.mpr t.1.2) (zpowers_le.mpr t'.1.2)
    rw [← hhub _ hF hFY y (mem_sup_left (mem_zpowers y)) hy2,
      hhub _ hF hFY y' (mem_sup_right (mem_zpowers y')) hy'2]
  have hwalk : ∀ (u v : {y : ↥Y // orderOf y = 2})
      (p : (CFSG.Assembly.involutionGraph ↥Y).Walk u v), wGroup (T u) V = wGroup (T v) V := by
    intro u v p
    induction p with
    | nil => rfl
    | cons h _ ih => exact (hadj _ _ h).trans ih
  have hEY : E ≤ Y := le_inf hEK (le_centralizer_iff.mp (sup_le
    (le_centralizer_iff.mp (hEB.trans hBV)) (zpowers_le.mpr hbE)))
  obtain ⟨e, heE, he1⟩ := exists_mem_ne_one_of_isKleinFour hE
  have he2 : orderOf e = 2 := orderOf_eq_two_of_isKleinFour hE heE he1
  set te : {y : ↥Y // orderOf y = 2} := ⟨⟨e, hEY heE⟩, by rw [Subgroup.orderOf_mk]; exact he2⟩
  have hTe : wGroup (T te) V = wGroup B V := by
    rw [← hWE]
    exact (hhub E hE hEY e heE he2).symm
  have hT : ∀ t : {y : ↥Y // orderOf y = 2}, wGroup (T t) V = wGroup B V := fun t => by
    obtain ⟨p⟩ := hYconn t te
    exact (hwalk t te p).trans hTe
  rw [← inf_centralizer_sup_oddCoreIn_eq hS2 hSQ]
  refine sup_le ?_ ?_
  · intro g hg
    have hVg : V.map (MulAut.conj g).toMonoidHom = V := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        show g * y * g⁻¹ ∈ V
        have hgy : g * y = y * g := ((mem_centralizer_iff.mp (hYV g hg)) y hy).symm
        rw [hgy, mul_inv_cancel_right]
        exact hy
      · intro hx
        refine ⟨x, hx, ?_⟩
        show g * x * g⁻¹ = x
        have hgx : g * x = x * g := ((mem_centralizer_iff.mp (hYV g hg)) x hx).symm
        rw [hgx, mul_inv_cancel_right]
    set Eg := E.map (MulAut.conj g).toMonoidHom with hEg
    have hEg4 : IsKleinFour Eg := by
      refine isKleinFour_of_card_eq_four ?_ fun x hx => ?_
      · rw [hEg, Subgroup.card_map_of_injective (MulAut.conj g).injective, hE.card_four]
      · obtain ⟨v, hv, rfl⟩ := hx
        rw [← map_pow, sq_eq_one_of_isKleinFour hE hv, map_one]
    have hEgY : Eg ≤ Y := by
      rintro _ ⟨x, hx, rfl⟩
      exact mul_mem (mul_mem hg (hEY hx)) (inv_mem hg)
    obtain ⟨e', he'E, he'1⟩ := exists_mem_ne_one_of_isKleinFour hEg4
    have he'2 : orderOf e' = 2 := orderOf_eq_two_of_isKleinFour hEg4 he'E he'1
    have h1 : (wGroup B V).map (MulAut.conj g).toMonoidHom = wGroup Eg V := by
      rw [← hWE, map_wGroup, hVg]
    have key : (wGroup B V).map (MulAut.conj g).toMonoidHom = wGroup B V := by
      rw [h1, hhub Eg hEg4 hEgY e' he'E he'2]
      exact hT ⟨⟨e', hEgY he'E⟩, by rw [Subgroup.orderOf_mk]; exact he'2⟩
    exact mem_normalizer_iff_map_conj_eq.mpr key
  · exact (oddCoreIn_le_of_isTwoComponentIn hK.1).trans
      (oddCoreIn_le_normalizer_wGroup_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8 hE hEB
        hEK hBN)

end CFSG.ComponentClassification.Sol76.Sig
