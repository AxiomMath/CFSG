module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtS15223P2Ctx
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtS15223P2Pieces
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223A57Alt7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S15223

theorem core57_of_F4 (h5 : StageLemma15205_F4) (h159 : StageLemma1519)
    (h11 : StageLemma15211_F4) (h12 : He12.StageLemma15212W_F4) (h13 : StageLemma15213_F4)
    (h14 : StageLemma15214_F4) (hN : StageNotation15209_F4) (h16 : StageLemma15216_F4)
    (h17 : StageLemma15217_F4) (h18 : StageLemma15218_F4) {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]
    {T Mc M H : Subgroup G} (hs : Setting152 T Mc M) (hH : IsHStar T M H)
    {B₀ : Subgroup (MulAut (V154 T Mc M))} (hB₀ : IsB0 T Mc M B₀) {I : Subgroup G}
    (hI : Hyp15215.Min T Mc M B₀ I) (hchar : CharTwo I) (hP1 : Reduction15223P1_F4) :
    Core57 I (sOf152 T Mc M B₀) (oTwoUpper H) H Mc := by
  have hctx := ctx15223_of_F4 h5 h159 h11 h12 h13 h14 hN h16 h17 h18 hs hH hB₀ hI
  have hKS := hctx.inputs.h16.KS_le
  obtain ⟨B, hB⟩ := hctx.inputs.hN.sigmaPrime_nonempty
  have hSle : sOf152 T Mc M B₀ ≤ T := S_le_T152
  have hTH : T ≤ H := hH.1.1
  have hTK : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) := hTH.trans (le_normalizer_oTwoUpper H)
  have hST2 : (sOf152 T Mc M B₀).relIndex T = 2 := (h17 G T Mc M hs B₀ hB₀ I hI.1).2.2
  have hTS : T ≤ Subgroup.normalizer (sOf152 T Mc M B₀ : Set G) :=
    le_normalizer_of_relIndex_two hSle hST2
  obtain ⟨P, hPK, hP3, hP9, -⟩ := hctx.sylow_three
  exact ⟨hchar, hctx.rank, hctx.sylow, hctx.K_le, oTwoUpper_idem H, hSle.trans hTK,
    (le_sup_left.trans hKS).trans inf_le_left, (le_sup_right.trans hKS).trans inf_le_left,
    (h12 G T Mc M hs H hH B hB).unique,
    le_normalizer_pCoreOf_sup (H_eq152 hs hH) hTK hTS, ⟨P, hPK, hP3, hP9⟩, hctx.K_solvable,
    fun Y h1 h2 h3 h4 h5' => hP1 G T Mc M hs H hH B₀ hB₀ I hI.1 Y h1 h2 h3 h4 h5'⟩

theorem reduction15223P2A5A7_of_F4 (h5 : StageLemma15205_F4)
    (h159 : StageLemma1519) (h11 : StageLemma15211_F4) (h12 : He12.StageLemma15212W_F4)
    (h13 : StageLemma15213_F4) (h14 : StageLemma15214_F4) (hN : StageNotation15209_F4)
    (h16 : StageLemma15216_F4) (h17 : StageLemma15217_F4) (h18 : StageLemma15218_F4) :
    Reduction15223P2A5A7_F4 := by
  intro hP1 G _ _ T Mc M hs H hH B₀ hB₀ I hI hchar X hX htype
  have c := core57_of_F4 h5 h159 h11 h12 h13 h14 hN h16 h17 h18 hs hH hB₀ hI hchar hP1
  rcases htype with h | h
  · exact c.false_of_alt5 hX h
  · exact c.false_of_alt7 hX h

end S15223

end CFSG.Quasithin
