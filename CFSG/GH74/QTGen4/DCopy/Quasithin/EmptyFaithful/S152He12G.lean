module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152He12E
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152He12F
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152L15
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152Stmts2
public import CFSG.Quasithin.EmptyFaithful.S152L26
public import CFSG.Quasithin.EmptyFaithful.S152L26One
public import CFSG.Quasithin.EmptyFaithful.S152L28

public section

namespace CFSG.Quasithin

namespace He12

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S152N CFSG.Quasithin.S152N2

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem stageTheorem15215W_of_F4 (h11 : StageLemma15211_F4) (h12 : StageLemma15212W_F4)
    (h13 : StageLemma15213_F4) (h14 : StageLemma15214_F4) (hN : StageNotation15209_F4)
    (h20 : StageLemma15220_F4) (h23 : StageLemma15223_F4) (h24 : StageLemma15224_F4)
    (htail : Stage15215TailW_F4) : StageTheorem15215_F4 := by
  classical
  intro G _ _ T Mc M hs B₀ hB₀
  have h16 := stageLemma15216_of_F4 h14 h13 h11 hN
  refine ⟨⟨hs.qtfe.mc_max, inf_le_left⟩, fun M₁ hM₁ => ?_⟩
  by_contra hne
  have hnotle : ¬ M₁ ≤ Mc := fun hle => hne (hM₁.1.2 Mc hs.qtfe.mc_max.1 hle).symm
  obtain ⟨H, hH⟩ := exists_isHStar hs.qtfe.inM_mc hs.mf.1.1 hs.mf.2.1.symm
  obtain ⟨B, hB⟩ := (hN G T Mc M hs H hH).sigmaPrime_nonempty

  have hI0 : Hyp15215 T Mc M B₀ M₁ := ⟨inH_of_inM hM₁, hnotle⟩
  have hC0 := h16 G T Mc M hs H hH B₀ hB₀ M₁ hI0

  set S : Set (Subgroup G) := {I | InH (Subgroup.centralizer (zSOf T Mc M B₀ : Set G)) I ∧
    ¬ I ≤ Mc ∧ I ≤ M₁} with hS
  have hM₁S : M₁ ∈ S := by
    refine ⟨⟨?_, hI0.inH.2⟩, hnotle, le_rfl⟩
    rw [hC0.centralizer_eq]
    exact hI0.inH.1
  obtain ⟨I, ⟨hIH, hIM, hIM₁⟩, hmin⟩ := Set.exists_min_image S (fun K => Nat.card K)
    (Set.toFinite _) ⟨M₁, hM₁S⟩
  have hI : Hyp15215 T Mc M B₀ I :=
    ⟨by
      refine ⟨?_, hIH.2⟩
      rw [← (h16 G T Mc M hs H hH B₀ hB₀ M₁ hI0).centralizer_eq]
      exact hIH.1, hIM⟩
  have hImin : Hyp15215.Min T Mc M B₀ I := by
    refine ⟨hI, fun I' hI'H hI'M hI'I => ?_⟩
    exact Subgroup.eq_of_le_of_card_ge hI'I (hmin I' ⟨hI'H, hI'M, hI'I.trans hIM₁⟩)
  exact htail G T Mc M hs H hH B hB B₀ hB₀ (h12 G T Mc M hs H hH B hB) (h14 G T Mc M hs B₀ hB₀)
    I hImin (h20 G T Mc M hs H hH B₀ hB₀ I hI) (h23 G T Mc M hs H hH B₀ hB₀ I hImin)
    (fun L hL hLM => h24 G T Mc M hs H hH B₀ hB₀ I hImin L hL hLM)

theorem stageLemma15226OneW_of_F4 (h15209 : StageNotation15209_F4) (h15211 : StageLemma15211_F4)
    (h15212 : StageLemma15212W_F4) (h15213 : StageLemma15213_F4) (h15214 : StageLemma15214_F4)
    (h15215 : StageTheorem15215_F4) : StageLemma15226One_F4 := by
  intro G _ _ T Mc M hs
  obtain ⟨H, hH⟩ := exists_isHStar hs.qtfe.inM_mc hs.mf.1.1 hs.mf.2.1.symm
  obtain ⟨B, hB⟩ := (h15209 G T Mc M hs H hH).sigmaPrime_nonempty
  obtain ⟨B₀, hB₀, -, hBdata⟩ := (h15213 G T Mc M hs H hH).exists_B0
  obtain ⟨-, -, hZSeq, -⟩ := hBdata B hB
  have h11 := h15211 G T Mc M hs H hH B hB
  have hcard : Nat.card (zSOf T Mc M B₀) = 4 := by
    unfold zSOf
    rw [← hZSeq]
    exact h11.card
  have h14 := h15214 G T Mc M hs B₀ hB₀
  have hU := h15215 G T Mc M hs B₀ hB₀
  have hVZ : V154 T Mc M = conjClosure (quasithinOmegaOneCenter T) M :=
    (h15212 G T Mc M hs H hH B hB).eq_VZ
  have hV : IsElemAbelian 2 (V154 T Mc M) :=
    isElemAbelian_mono151 (V154_le_VZ T Mc M) (isElemAbelian_VZ hs.qtfe hs.mf.1.1)
  have hMV : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hr : (2 : ℕ∞) ≤ E3.rParam (V154 T Mc M) := by
    refine two_le_rParam hV fun U hUV hidx => ?_
    exact (centralizer_hyperplane_le hMV hV (zSOf_le_V154 T Mc M B₀) hcard h14.mc_eq hU hVZ
      hidx).trans (Subgroup.centralizer_le_normalizer _)
  refine ⟨hV, lt_of_lt_of_le (by norm_num) hr, ?_⟩
  obtain ⟨hV', hm2, -⟩ := h14.params
  refine one_lt_sParam hV hr ?_
  rw [autI_top_eq hV (normalizer_V154_eq hs.qtfe hs.mf).le, hm2]

theorem stageLemma15228W_of_F4 (h15111 : StageLemma15111) (h12 : StageLemma15212W_F4)
    (h13 : StageLemma15213_F4) (hN : StageNotation15209_F4) (h25 : StageLemma15225_F4) :
    StageLemma15228_F4 := by
  intro G _ _ T Mc M hs H hH B₀ hB₀
  obtain ⟨B, hB⟩ := (hN G T Mc M hs H hH).sigmaPrime_nonempty
  have hZ := commutator_eq_zSOf (h13 G T Mc M hs H hH) hB₀ hB
  have hnorm : H ≤ Subgroup.normalizer (zSOf T Mc M B₀ : Set G) := by
    have := (h12 G T Mc M hs H hH B hB).normal
    rwa [hZ] at this
  exact lemma_15_2_28 hs.qtfe hH hB₀ (h25 G T Mc M hs)
    (h15111 G T Mc M hs.qtfe hs.mf hs.ce H hH).1 hnorm

end He12

end CFSG.Quasithin
