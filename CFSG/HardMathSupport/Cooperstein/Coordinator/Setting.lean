module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockStructure
public import CFSG.LocalAnalysis.AGLEmbedding.AscTenThreeModule
public import CFSG.LocalAnalysis.AGLEmbedding.AscEightSix
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3
public import CFSG.Quasithin.Background.B2Factorization

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {X S L : Subgroup G}

omit [Finite G] in
theorem cgsIn_eq_of_le (hA : Asc81bHyp X S) {Y : Subgroup G} (hYX : Y ≤ X) :
    cgsIn Y S = Y ⊓ Subgroup.normalizer (S : Set G) := by
  refine le_antisymm ?_ (inf_normalizer_le_cgsIn hA.twoRadical.2.1)
  refine iSup_le fun C => iSup_le fun hCS => iSup_le fun hC1 => iSup_le fun hchar => ?_
  have h1 : X ⊓ Subgroup.normalizer (C : Set G) ≤ cgsIn X S :=
    le_iSup_of_le C (le_iSup_of_le hCS (le_iSup_of_le hC1 (le_iSup_of_le hchar le_rfl)))
  rw [hA.cgs] at h1
  intro x hx
  exact ⟨hx.1, (h1 ⟨hYX hx.1, hx.2⟩).2⟩

theorem le_of_le_twoPrimeComponent (hA : Asc81bHyp X S) (hL : IsTwoPrimeComponent X L)
    {U : Subgroup G} (hUL : U ≤ L) (hU : IsPGroup 2 U)
    (hN : X ⊓ Subgroup.normalizer (S : Set G) ⊓ Subgroup.normalizer (L : Set G) ≤
      Subgroup.normalizer (U : Set G)) : U ≤ S := by
  let K := X ⊓ Subgroup.normalizer (S : Set G)
  let C : Set (Subgroup G) := {V | ∃ k ∈ K, V = U.map (MulAut.conj k).toMonoidHom}
  have hQX : X ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) := localGroup_le_normalizer_pCoreOf 2 X
  have hCX : ∀ V ∈ C, V ≤ X := by
    rintro _ ⟨k, hk, rfl⟩
    exact (Subgroup.map_mono (hUL.trans hL.le)).trans
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hk.1)).le
  have hCp : IsPGroup 2 ((sSup C : Subgroup G) ⊔ pCoreOf 2 X : Subgroup G) := by
    rw [sSup_eq_iSup']
    refine isPGroup_iSup_sup_of_pairwise_commutator_le _ (pCoreOf_isPGroup 2 X) ?_
      (fun V => (hCX V.1 V.2).trans hQX) ?_
    · rintro ⟨V, k, hk, rfl⟩
      exact hU.map _
    · rintro ⟨V, k, hk, rfl⟩ ⟨V', k', hk', rfl⟩ hne
      have hLne : L.map (MulAut.conj k).toMonoidHom ≠ L.map (MulAut.conj k').toMonoidHom :=
        fun he => hne (Subtype.ext (CFSG.AGLEmbedding.map_conj_eq_of_map_conj_eq hN hk hk' he))
      exact (Subgroup.commutator_mono (Subgroup.map_mono hUL) (Subgroup.map_mono hUL)).trans
        ((hL.map_conj hk.1).commutator_le (hL.map_conj hk'.1) hLne)
  have hCN : K ≤ Subgroup.normalizer (((sSup C : Subgroup G) ⊔ pCoreOf 2 X : Subgroup G) :
      Set G) := by
    refine (le_inf ?_ (inf_le_left.trans hQX)).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
    refine CFSG.AGLEmbedding.le_normalizer_of_forall_map_conj_le fun g hg => ?_
    refine Subgroup.map_le_iff_le_comap.mpr (sSup_le ?_)
    rintro _ ⟨k, hk, rfl⟩
    refine Subgroup.map_le_iff_le_comap.mp (le_sSup ⟨g * k, K.mul_mem hg hk, ?_⟩)
    rw [CFSG.AGLEmbedding.map_conj_mul_eq]
  have hUC : U ≤ (sSup C : Subgroup G) := le_sSup ⟨1, K.one_mem, by ext x; simp⟩
  exact (hUC.trans le_sup_left).trans (le_of_two_radical hA.twoRadical.1 hA.twoRadical.2.2
    (sup_le (sSup_le hCX) (pCoreOf_le 2 X)) hCp hCN)

theorem eq_pCoreOf_normalizer_sup (hA : Asc81bHyp X S) (hL : IsTwoPrimeComponent X L)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) :
    S = pCoreOf 2 ((L ⊔ S) ⊓ Subgroup.normalizer (S : Set G)) := by
  set Y := (L ⊔ S) ⊓ Subgroup.normalizer (S : Set G)
  have hSY : S ≤ Y := le_inf le_sup_right Subgroup.le_normalizer
  have hST : S ≤ pCoreOf 2 Y := normal_pGroup_le_pCoreOf 2 S Y hSY
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hSY).mpr inf_le_right)
    hA.twoRadical.isPGroup
  have hU : pCoreOf 2 Y ⊓ L ≤ S := by
    refine le_of_le_twoPrimeComponent hA hL inf_le_right
      ((pCoreOf_isPGroup 2 Y).to_le inf_le_left) fun g hg => ?_
    have hgY : g ∈ Subgroup.normalizer (Y : Set G) := Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hg.2, hg.1.2⟩,
        Subgroup.le_normalizer hg.1.2⟩
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨normalizer_localGroup_le_normalizer_pCoreOf 2 Y hgY, hg.2⟩
  refine le_antisymm hST fun t ht => ?_
  have htLS : t ∈ ((S ⊔ L : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact ((pCoreOf_le 2 Y).trans inf_le_left) ht
  rw [Subgroup.coe_mul_of_left_le_normalizer_right S L hSL] at htLS
  obtain ⟨s, hs, l, hl, rfl⟩ := htLS
  have hlT : l ∈ pCoreOf 2 Y := by
    have := (pCoreOf 2 Y).mul_mem ((pCoreOf 2 Y).inv_mem (hST hs)) ht
    rwa [inv_mul_cancel_left] at this
  exact S.mul_mem hs (hU ⟨hlT, hl⟩)

theorem asc81bHyp_sup (hA : Asc81bHyp X S) (hL : IsTwoPrimeComponent X L)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) : Asc81bHyp (L ⊔ S) S :=
  ⟨⟨le_sup_right, hA.twoRadical.2.1, eq_pCoreOf_normalizer_sup hA hL hSL⟩,
    charTwo_of_twoCore_le hA.charTwo (hA.twoCore_le.trans le_sup_right)
      (sup_le hL.le hA.twoRadical.1),
    cgsIn_eq_of_le hA (sup_le hL.le hA.twoRadical.1)⟩

omit [Finite G] in
theorem isKGroup_sup (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S)
    (hL : IsTwoPrimeComponent X L) : CFSG.Open.IsKGroup ↥(L ⊔ S) :=
  AscEightFour.isKGroup_mono hX (sup_le hL.le hA.twoRadical.1)

section EightSix


theorem le_normalizer_of_isWeakSBlock (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S)
    (hL : IsWeakSBlock X S L) : S ≤ Subgroup.normalizer (L : Set G) :=
  hL.toIsTwoPrimeComponent.le_normalizer
    (asc81bEightSix_of_bhs CFSG.LocalAnalysis.RankThreeTheoremC.bhsLocalCStar_proved G X S hX hA
      _ hL.component) hA.twoRadical.1

end EightSix

section EightSeven

variable (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L) (hSL : S ≤ Subgroup.normalizer (L : Set G))

include hA hL hSL

theorem twoCore_sup_le : pCoreOf 2 (L ⊔ S) ≤ S :=
  (asc81bHyp_sup hA hL.toIsTwoPrimeComponent hSL).twoCore_le

theorem omegaOneCenterOf_le_blockV : omegaOneCenterOf S ≤ blockV S L :=
  AscTenThree.omegaOneCenterOf_le_V (asc81bHyp_sup hA hL.toIsTwoPrimeComponent hSL)

theorem inf_centralizer_blockV_le_normalizer :
    (L ⊔ S) ⊓ Subgroup.centralizer (blockV S L : Set G) ≤ Subgroup.normalizer (S : Set G) :=
  AscTenThree.inf_centralizer_V_le_normalizer (asc81bHyp_sup hA hL.toIsTwoPrimeComponent hSL)

theorem inf_centralizer_blockV_le_twoCore :
    S ⊓ Subgroup.centralizer (blockV S L : Set G) ≤ pCoreOf 2 (L ⊔ S) :=
  AscTenThree.inf_centralizer_V_le_twoCore (asc81bHyp_sup hA hL.toIsTwoPrimeComponent hSL)

theorem not_le_centralizer_blockV : ¬ L ≤ Subgroup.centralizer (blockV S L : Set G) := fun h =>
  hL.not_le_normalizer fun _ hl =>
    inf_centralizer_blockV_le_normalizer hA hL hSL ⟨Subgroup.mem_sup_left hl, h hl⟩

theorem thompsonJ_ne : thompsonJ S ≠ thompsonJ (pCoreOf 2 (L ⊔ S)) := by
  intro hJ
  have hA' := asc81bHyp_sup hA hL.toIsTwoPrimeComponent hSL
  have hS2 : IsPGroup 2 S := hA.twoRadical.isPGroup
  have hJne : thompsonJ S ≠ ⊥ := by
    obtain ⟨B, hB⟩ := exists_isMaxElemAbelian S
    intro hbot
    have hBb : B = ⊥ := le_bot_iff.mp (hbot ▸ B6.le_thompsonJ hB)
    have h1 := hB.2.2 (omegaOneCenterOf S) (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le S)
      (CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf S)
    rw [hBb, Subgroup.card_bot] at h1
    exact CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hS2 hA.twoRadical.2.1
      (Subgroup.eq_bot_of_card_le _ h1)
  have hJchar : ((thompsonJ S).subgroupOf S).Characteristic :=
    CFSG.QuasithinUnique.Setup.characteristic_thompsonJ S
  have hle : (L ⊔ S) ⊓ Subgroup.normalizer (thompsonJ S : Set G) ≤ cgsIn (L ⊔ S) S :=
    le_iSup_of_le (thompsonJ S) (le_iSup_of_le (B6.thompsonJ_le S)
      (le_iSup_of_le hJne (le_iSup_of_le hJchar le_rfl)))
  rw [hA'.cgs] at hle
  apply hL.not_le_normalizer
  intro l hl
  have hlQ : l ∈ Subgroup.normalizer (pCoreOf 2 (L ⊔ S) : Set G) :=
    localGroup_le_normalizer_pCoreOf 2 (L ⊔ S) (Subgroup.mem_sup_left hl)
  have hlJ : l ∈ Subgroup.normalizer (thompsonJ (pCoreOf 2 (L ⊔ S)) : Set G) :=
    CFSG.Quasithin.normalizer_le_normalizer_thompsonJ _ hlQ
  rw [← hJ] at hlJ
  exact (hle ⟨Subgroup.mem_sup_left hl, hlJ⟩).2

theorem exists_isMaxElemAbelian_not_le :
    ∃ A : Subgroup G, IsMaxElemAbelian S A ∧ ¬ A ≤ pCoreOf 2 (L ⊔ S) := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hJQ : thompsonJ S ≤ pCoreOf 2 (L ⊔ S) := by
    unfold thompsonJ
    exact iSup₂_le fun A hA' => h A hA'
  exact thompsonJ_ne hA hL hSL (thompsonJ_eq_of_le hJQ (twoCore_sup_le hA hL hSL))

theorem not_le_centralizer_blockV_of_not_le {A : Subgroup G} (hAS : A ≤ S)
    (hAQ : ¬ A ≤ pCoreOf 2 (L ⊔ S)) : ¬ A ≤ Subgroup.centralizer (blockV S L : Set G) :=
  fun h => hAQ fun _ ha => inf_centralizer_blockV_le_twoCore hA hL hSL ⟨hAS ha, h ha⟩

theorem blockV_le : blockV S L ≤ S :=
  (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le _).trans (twoCore_sup_le hA hL hSL)

theorem isFFModule_autOn_blockV :
    @IsFFModule ↥(blockV S L)
      (commGroupOfElemAbelian (CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf _))
      (autOn (L ⊔ S) (blockV S L)) := by
  obtain ⟨A, hAmax, hAQ⟩ := exists_isMaxElemAbelian_not_le hA hL hSL
  exact isFFModule_autOn (CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf _)
    (blockV_le hA hL hSL) (AscTenThree.le_normalizer_omegaOneCenterOf_twoCore (L ⊔ S))
    (hAmax.1.trans le_sup_right) hAmax
    (not_le_centralizer_blockV_of_not_le hA hL hSL hAmax.1 hAQ)

end EightSeven

end CFSG.HardMathSupport.Cooperstein.Coordinator
