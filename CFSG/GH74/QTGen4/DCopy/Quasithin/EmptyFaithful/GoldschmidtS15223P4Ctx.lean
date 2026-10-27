module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4Ctx
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Background.C2Seven
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152Stmts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S15223P4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

section Front

variable {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I : Subgroup G}

theorem p4Ctx_exists_F4 (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G)
    (h5 : StageLemma15205_F4) (h159 : StageLemma1519)
    (h8 : StageLemma15208_F4) (h11 : StageLemma15211_F4) (h13 : StageLemma15213_F4)
    (h14 : StageLemma15214_F4)
    (hN : StageNotation15209_F4) (h16 : StageLemma15216_F4) (h17 : StageLemma15217_F4)
    (h18 : StageLemma15218_F4)
    (hs : Setting152 T Mc M) (hH : IsHStar T M H) (hB₀ : IsB0 T Mc M B₀)
    (hI : Hyp15215.Min T Mc M B₀ I) (hchar : CharTwo I)
    (hno : ∀ X : Subgroup G, ¬ IsChiBlock2 I X) (hii : Concl15218ii T Mc M H B₀ I) :
    ∃ X : Subgroup G, P4Ctx T Mc M H B₀ I X := by
  have hD : Inputs152 T Mc M H B₀ I :=
    ⟨h5 G T Mc M hs, h159 G T Mc M hs.qtfe hs.mf hs.ce, h13 G T Mc M hs H hH,
      h14 G T Mc M hs B₀ hB₀, h11 G T Mc M hs H hH, hN G T Mc M hs H hH,
      h16 G T Mc M hs H hH B₀ hB₀ I hI.1, h17 G T Mc M hs B₀ hB₀ I hI.1⟩
  have hOm : Om4FactsStatement := fun _ _ _ _ hX => S152O4.om4_facts hX
  have hyp : HypC23 I (P4R M I) (M ⊓ I) := lemma_15_2_19_two hs hB₀ hI.1 hD hOm hii
  set R := P4R M I with hRdef
  set N := M ⊓ I with hNdef
  have hsyl : IsSylowTwoOf (sOf152 T Mc M B₀) I := (h18 G T Mc M hs H hH B₀ hB₀ I hI.1).sylow
  have hTM : T ≤ M := T_le_M152 hs
  have hSN : sOf152 T Mc M B₀ ≤ N := le_inf (S_le_T152.trans hTM) (S_le_I152 hD)
  have hPN : pCoreOf 2 I ≤ N := hsyl.pCoreOf_le.trans hSN
  have hKI : oTwoUpper H ≤ I := (K_le_inf152 hD).trans inf_le_right
  have hKM : ¬ oTwoUpper H ≤ M := fun h => hH.2.1 (by
    rw [H_eq152 hs hH]; exact sup_le h hTM)
  have hKN : ¬ oTwoUpper H ≤ N := fun h => hKM (h.trans inf_le_left)

  have hFN : oTwoFIn I ≤ N := by
    by_contra hnot
    have hF : CharTwo (oTwoFIn I) :=
      CT.CharTwo.of_normal hchar C2Six.oTwoFIn_le C2Six.normal_oTwoFIn_subgroupOf
    obtain ⟨r, Lb, hLb, hprod⟩ := c2_6_two (hC129 G) hyp hF hnot
    have hr : 0 < r := by
      by_contra hr0
      have hr0' : r = 0 := Nat.eq_zero_of_not_pos hr0
      subst hr0'
      apply hnot
      intro x hx
      obtain ⟨m, hm, y, -, hxy⟩ := hprod x hx
      have hxm : x = m := by simpa using hxy
      rw [hxm]
      exact hm.1
    obtain ⟨hblock, hA3, -⟩ := hLb ⟨0, hr⟩
    exact hno (Lb ⟨0, hr⟩) ⟨isBlock2_of_oTwoFIn hblock, Or.inr ⟨3, by decide, hA3⟩⟩

  have hex : ∃ X : Subgroup G, X ∈ cComp I ∧ CFSG.IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X) ∧
      ¬ X ≤ N := by
    by_contra hcon
    push Not at hcon
    have hFs : oTwoFstarIn I ≤ N := oTwoFstarIn_le_of_components1516 hPN hFN hcon
    have h441 := a4_4_1 (pCoreOf_le_oTwoFstarIn I)
      (le_inf (oTwoFstarIn_le I) hFs) (a44Hyp_oTwoFstarIn I)
    rw [inf_eq_right.mpr (inf_le_right : M ⊓ I ≤ I)] at h441
    have hRne : R ≠ ⊥ := hyp.radical.2.1
    have hIR : I ≤ Subgroup.normalizer (R : Set G) := by
      rw [hRdef]
      show I ≤ Subgroup.normalizer ((pCoreOf 2 (M ⊓ I) : Subgroup G) : Set G)
      rw [h441]
      exact le_normalizer_pCoreOf 2 I
    have hIN : I ≤ N :=
      (le_inf le_rfl hIR).trans ((inf_normalizer_le_cgsIn hRne).trans hyp.cgs)
    exact hKN (hKI.trans hIN)
  obtain ⟨X, hX, hXq, hXN⟩ := hex
  have hXI : X ≤ I := le_of_mem_cComp hX
  have hXchar : CharTwo X := charTwo_of_isSubnormal_of_charTwo hchar (subnormal_of_mem_cComp hX)

  have hKX : oTwoUpper H ≤ Subgroup.normalizer (X : Set G) := by
    have hc : (X.subgroupOf I).Normal ∨ (conjSubgroupsBy I X).ncard = 2 :=
      (lemma_1_2_1_three hs.qtfe.qtke hs.qtfe.simple hs.qtfe.nonabelian h37 h38 hI.1.inH.2
        hX).imp id And.left
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    exact odd_mem_normalizer_conjSubgroupsBy1516 hXI hc
      (hKI (mem_oTwoUpper_of_odd hx.1 hx.2)) hx.2 ⟨1, I.one_mem, (conjByElt_one1516 X).symm⟩

  have hRX : R ≤ Subgroup.normalizer (X : Set G) := by
    by_contra hRX
    have hSR : sOf152 T Mc M B₀ ≤ Subgroup.normalizer (R : Set G) :=
      hSN.trans (le_normalizer_pCoreOf 2 N)
    have hS : IsSylowTwoOf (R ⊓ X) X :=
      C2Push.isSylowTwoOf_inf_of_not_le_normalizer hyp.radical hsyl hSR hX hXq hRX
    obtain ⟨hshort, htype, -⟩ := S146zV.exists_block_data_of_asc129 (hC129 G) hchar hyp.sqtk
      hyp.radical hyp.cgs hX hXq hS hXN
    exact hno X ⟨⟨hshort, hXI, (isSubnormal_iff_subgroupOf hXI).mp (subnormal_of_mem_cComp hX)⟩,
      htype.imp id fun h5 => ⟨5, by decide, h5⟩⟩

  exact ⟨X, ⟨hs, hH, hB₀, hI, hchar, hD, h8 G T Mc M hs H hH, hno, hii, hyp, hX, hXq, hXchar, hXN,
    hKX, hRX, hsyl,
    hC27 G I R N X (omegaOneCenterOf (pCoreOf 2 (X ⊔ R))) hyp hX hXq hXchar hXN hRX rfl⟩⟩

end Front

end S15223P4

end CFSG.Quasithin
