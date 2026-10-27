module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingle
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigCross

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13

variable {G : Type} [Group G] [Finite G] {N : Subgroup G}

theorem wGroup_eq_of_le_centralizer_right (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) {K K' V B : Subgroup G} (hP : SigPair N K K' V B)
    (hK'W : K' ≤ normalizer (wGroup B V : Set G)) {E : Subgroup G} (hE : IsKleinFour E)
    (hEB : E ≤ B) (hEK : E ≤ K) {U : Subgroup G} (hU : IsKleinFour U)
    (hUY : U ≤ K' ⊓ centralizer (B : Set G)) : wGroup E U = wGroup B V := by
  classical
  have h32 := lemma32FullFor_simple_of_twoPart hq hR1
  obtain ⟨hK, hK', hne, hV, hVK', hBQ, hBV, hB, hB8, hBN, -⟩ := hP
  set Y := K' ⊓ centralizer (B : Set G) with hYdef
  have hBX : ∀ {X : Subgroup G}, X ≤ Y → E ≤ centralizer (X : Set G) := fun {X} hX e he =>
    mem_centralizer_iff.mpr fun x hx => ((mem_centralizer_iff.mp (hX hx).2) e (hEB he)).symm
  have hVY : V ≤ Y := le_inf hVK' fun v hv => mem_centralizer_iff.mpr fun b hb =>
    ((mem_centralizer_iff.mp (hBV hb)) v hv).symm
  have hYE : Y ≤ centralizer (E : Set G) := inf_le_right.trans (centralizer_le hEB)
  have hgoodV : wGroup E V = wGroup B V :=
    wGroup_eq_of_le_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hE hEB hEK hE hEB
  have hstep : ∀ {P X X' : Subgroup G}, IsPGroup 2 P → P ≤ Y → IsKleinFour X → X ≤ P →
      IsKleinFour X' → X' ≤ P → ∀ {y : G}, y ∈ X → y ∈ X' → y ≠ 1 →
      wGroup E X = wGroup E X' := by
    intro P X X' _ hPY hX hXP hX' hX'P y hyX hyX' hy1
    exact (wGroup_eq_wGroup_zpowers h32 hG hN hK hK' hne hX ((hXP.trans hPY).trans inf_le_left)
      hE hEK (hBX (hXP.trans hPY)) hyX hy1).trans
      (wGroup_eq_wGroup_zpowers h32 hG hN hK hK' hne hX' ((hX'P.trans hPY).trans inf_le_left)
        hE hEK (hBX (hX'P.trans hPY)) hyX' hy1).symm
  have hpgroup : ∀ {P X X' : Subgroup G}, IsPGroup 2 P → P ≤ Y → IsKleinFour X → X ≤ P →
      IsKleinFour X' → X' ≤ P → wGroup E X = wGroup E X' := by
    intro P X X' hP2 hPY hX hXP hX' hX'P
    have hPne : P ≠ ⊥ := fun h => by
      have h4 := hX.card_four
      rw [show X = ⊥ from eq_bot_iff.mpr (h ▸ hXP), card_bot] at h4
      norm_num at h4
    obtain ⟨z, hzP, hz2, hzc⟩ := exists_central_involution_of_isPGroup hP2 hPne
    have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; norm_num at hz2
    obtain ⟨Z, hZ, hZP, hzZ, x, hxX, hxZ, hx1⟩ := exists_isKleinFour_mem_center hX hXP hzP hz2 hzc
    obtain ⟨Z', hZ', hZ'P, hzZ', x', hxX', hxZ', hx'1⟩ :=
      exists_isKleinFour_mem_center hX' hX'P hzP hz2 hzc
    rw [hstep hP2 hPY hX hXP hZ hZP hxX hxZ hx1, hstep hP2 hPY hZ hZP hZ' hZ'P hzZ hzZ' hz1,
      hstep hP2 hPY hZ' hZ'P hX' hX'P hxZ' hxX' hx'1]
  obtain ⟨P, hPY, hP2, hVP, k, hkY, hUk⟩ :=
    exists_pGroup_conj_le hVY (isPGroup_of_isKleinFour hV) hUY (isPGroup_of_isKleinFour hU)
  have hgoodUk : wGroup E (U.map (MulAut.conj k).toMonoidHom) = wGroup B V := by
    rw [← hpgroup hP2 hPY hV hVP (isKleinFour_map_conj hU k) hUk]
    exact hgoodV
  have hEk : E.map (MulAut.conj k⁻¹).toMonoidHom = E :=
    map_conj_eq_of_mem_centralizer (inv_mem (hYE hkY))
  have hWk : (wGroup B V).map (MulAut.conj k⁻¹).toMonoidHom = wGroup B V :=
    mem_normalizer_iff_map_conj_eq.mp (inv_mem (hK'W hkY.1))
  have h3 : (U.map (MulAut.conj k).toMonoidHom).map (MulAut.conj k⁻¹).toMonoidHom = U := by
    have := map_conj_map_conj_inv U k⁻¹
    rwa [inv_inv] at this
  have h4 : (wGroup E (U.map (MulAut.conj k).toMonoidHom)).map (MulAut.conj k⁻¹).toMonoidHom =
      (wGroup B V).map (MulAut.conj k⁻¹).toMonoidHom := by rw [hgoodUk]
  rwa [map_wGroup, hEk, h3, hWk] at h4

theorem exists_isGoodFor_of_mem_right_all (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) {K K' V B : Subgroup G} (hP : SigPair N K K' V B)
    (hK'W : K' ≤ normalizer (wGroup B V : Set G)) {x : G} (hx : x ∈ K') (hx2 : orderOf x = 2) :
    ∃ g ∈ K', IsGoodFor N (wGroup B V) (g⁻¹ * x * g) := by
  classical
  have hP' := hP
  obtain ⟨hK, hK', hne, hV, hVK', hBQ, hBV, hB, hB8, hBN, E, hE, hEB, hEK⟩ := hP'
  have hB2 : IsPGroup 2 B := CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup 2 B hB
  have hcov := inf_centralizer_sup_oddCoreIn_eq hB2 hBQ
  obtain ⟨m, hm, hmY⟩ := exists_conj_mem_of_sup_oddCoreIn inf_le_left hcov hx hx2
  have hm2 : orderOf (m⁻¹ * x * m) = 2 := by rw [orderOf_inv_mul_mul, hx2]
  have hm1 : m⁻¹ * x * m ≠ 1 := fun h => by rw [h, orderOf_one] at hm2; norm_num at hm2
  obtain ⟨U, hUY, hU, hxU⟩ :=
    exists_isKleinFour_mem (two_le_pRank_inf_centralizer hK' hB2 hBQ) hmY hm2
  have hUK' : U ≤ K' := hUY.trans inf_le_left
  have hBU : B ≤ centralizer (U : Set G) := fun b hb => mem_centralizer_iff.mpr fun u hu =>
    ((mem_centralizer_iff.mp (hUY hu).2) b hb).symm
  have hW := wGroup_eq_of_le_centralizer_right hq hR1 hG hN hP hK'W hE hEB hEK hU hUY
  have hWBU : wGroup E U = wGroup B U :=
    wGroup_eq_of_le_of_mem hq hR1 hG hN hK hK' hne hU hUK' hBQ hBU hB hE hEB hEK hE hEB
  exact ⟨m, hm, hm1, K, K', U, B, ⟨hK, hK', hne, hU, hUK', hBQ, hBU, hB, hB8, hBN, E, hE, hEB,
    hEK⟩, hWBU.symm.trans hW, Or.inr hxU⟩

@[expose] def GoodInvolutionsLeftTwoFor : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SimpleAmbient G → ∀ N : Subgroup G, IsSolomonChoice N →
    (kStarComponents N).ncard = 2 →
    ∀ K K' V B : Subgroup G, SigPair N K K' V B → wGroup B V ≠ ⊥ →
      (∀ K'' ∈ kStarComponents N, K'' ≤ normalizer (wGroup B V : Set G)) →
      ∀ x ∈ K, orderOf x = 2 →
        ∃ g ∈ normalizer (wGroup B V : Set G), IsGoodFor N (wGroup B V) (g⁻¹ * x * g)

theorem goodInvolutionsTwoFor_of_left (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (h : GoodInvolutionsLeftTwoFor) :
    GoodInvolutionsTwoFor := by
  classical
  intro G _ _ hG N hN h2 K K' V B hP hW hKH K'' hK'' x hx hx2
  by_cases hK''K : K'' = K
  · rw [hK''K] at hx
    exact h G hG N hN h2 K K' V B hP hW hKH x hx hx2
  by_cases hK''K' : K'' = K'
  · rw [hK''K'] at hx
    obtain ⟨g, hg, hgood⟩ :=
      exists_isGoodFor_of_mem_right_all hq hR1 hG hN hP (hKH K' hP.2.1) hx hx2
    exact ⟨g, hKH K' hP.2.1 hg, hgood⟩
  exfalso
  have hsub : ({K'', K, K'} : Set (Subgroup G)) ⊆ kStarComponents N := by
    rintro J (rfl | rfl | rfl)
    · exact hK''
    · exact hP.1
    · exact hP.2.1
  have h3 : ({K'', K, K'} : Set (Subgroup G)).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_pair hP.2.2.1]
    simp [hK''K, hK''K']
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

theorem lemma315bInputFor_simple_of_left_residues (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hF : False316CoverFor simpleAmbient)
    (h39 : Lemma39TwoRestFor) (hgood : GoodInvolutionsLeftTwoFor)
    (hC : SingleComponentCatalogFor) (hpair : SigPairExistsTwoFor) :
    Lemma315bInputFor simpleAmbient :=
  lemma315bInputFor_simple_of_two_residues hq hR1 hF h39
    (goodInvolutionsTwoFor_of_left hq hR1 hgood) (singleComponentExcludedFor_of_catalog hq hR1 hC)
    hpair

end CFSG.ComponentClassification.Sol76.Sig
