module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15221Final
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtS15221Hstar
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152He12E
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152U21

public section

namespace CFSG.Quasithin.S15221

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem input15221Three_of_F4 (h5 : StageLemma15205_F4) (h159 : StageLemma1519)
    (h11 : StageLemma15211_F4) (h12 : He12.StageLemma15212W_F4) (h13 : StageLemma15213_F4)
    (h14 : StageLemma15214_F4) (hN : StageNotation15209_F4) (h16 : StageLemma15216_F4)
    (h17 : StageLemma15217_F4) (h18 : StageLemma15218_F4) (h1515 : StageLemma1515CE)
    (h1521 : StageLemma15201_F4) (h03 : StageLemma15203_F4) (h08 : StageLemma15208_F4)
    (hIrr : Input15209Irr_F4) (hJ : Input15112J_F4) (hKc : Input1210Kc_F4) : Input15221Three_F4 := by
  intro G _ _ T Mc M hs H hH H₁ H₂ hP B₀ hB₀ I hI hL hii hY
  by_contra hnot
  obtain ⟨Y₁, hY₁eq, hY₁N, hSY₁, hq, hnY₁⟩ := hY
  have hD : Inputs152 T Mc M H B₀ I :=
    ⟨h5 G T Mc M hs, h159 G T Mc M hs.qtfe hs.mf hs.ce, h13 G T Mc M hs H hH,
      h14 G T Mc M hs B₀ hB₀, h11 G T Mc M hs H hH, hN G T Mc M hs H hH,
      h16 G T Mc M hs H hH B₀ hB₀ I hI, h17 G T Mc M hs B₀ hB₀ I hI⟩
  obtain ⟨B, hB⟩ := (hN G T Mc M hs H hH).sigmaPrime_nonempty
  have h12' := h12 G T Mc M hs H hH B hB
  have hData : S152Y.Data T Mc M :=
    ⟨hs.qtfe, hs.mf, h1515 G T Mc M hs.qtfe hs.mf hs.ce, h1521 G T Mc M hs⟩
  have c18 := h18 G T Mc M hs H hH B₀ hB₀ I hI
  have c03 := h03 G T Mc M hs

  have hone := lemma_15_2_21_one_W hs hH hP hB₀ hD h12' (hIrr G T Mc M hs H hH)
    (hJ G T Mc M hs H hH H₁ H₂ hP) (hKc G T Mc M hs B₀ hB₀ H hH) hnot
  have hKcI : conjClosure (oTwoUpper H) Mc ≤ Mc ⊓ I :=
    hone.2.2.1.trans (centralizer_zS_le_inf152 hD)

  have hTM : T ≤ M := T_le_M152 hs
  have hTMc : T ≤ Mc := hs.qtfe.t_le_mc
  have hT2 : IsPGroup 2 T := hs.qtfe.sylow.1
  have hS2 : IsPGroup 2 (sOf152 T Mc M B₀) := hT2.to_le S_le_T152
  have hTS : T ≤ Subgroup.normalizer (sOf152 T Mc M B₀ : Set G) := T_le_normalizer_S152 hD
  have hTKc : T ≤ Subgroup.normalizer (conjClosure (oTwoUpper H) Mc : Set G) :=
    hTMc.trans (le_normalizer_conjClosure _ _)

  have hSylI : IsSylowTwoOf (sOf152 T Mc M B₀) I := c18.sylow
  have hSylP : IsSylowTwoOf (sOf152 T Mc M B₀)
      (conjClosure (oTwoUpper H) Mc ⊔ sOf152 T Mc M B₀) := by
    have hle : conjClosure (oTwoUpper H) Mc ⊔ sOf152 T Mc M B₀ ≤ I :=
      sup_le (hKcI.trans inf_le_right) (S_le_I152 hD)
    refine ⟨le_sup_right, hSylI.2.1, fun hdvd => hSylI.2.2 ?_⟩
    have := Subgroup.relIndex_mul_relIndex (sOf152 T Mc M B₀)
      (conjClosure (oTwoUpper H) Mc ⊔ sOf152 T Mc M B₀) I le_sup_right hle
    have h2 : 2 ∣ (sOf152 T Mc M B₀).relIndex I := by
      rw [← this]
      exact (hdvd : 2 ∣ (sOf152 T Mc M B₀).relIndex
        (conjClosure (oTwoUpper H) Mc ⊔ sOf152 T Mc M B₀)).mul_right _
    exact h2
  have hSylD : IsSylowTwoOf (sOf152 T Mc M B₀ ⊓ conjClosure (oTwoUpper H) Mc)
      (conjClosure (oTwoUpper H) Mc) := by
    refine isSylowTwoOf_inf_of_le_normalizer hSylP le_sup_left (sup_le Subgroup.le_normalizer ?_)
    exact (S_le_T152.trans hTMc).trans (le_normalizer_conjClosure _ _)
  have hTD : T ≤ Subgroup.normalizer
      ((sOf152 T Mc M B₀ ⊓ conjClosure (oTwoUpper H) Mc : Subgroup G) : Set G) :=
    fun g hg => mem_normalizer_inf_of (hTS hg) (hTKc hg)

  obtain ⟨Y₀, hY₀K, hY₀eq, hY₀n, hY₀3, hY₀ne, d, hdD, hd⟩ :=
    exists_Y0_eq (K := conjClosure (oTwoUpper H) Mc)
      (D := sOf152 T Mc M B₀ ⊓ conjClosure (oTwoUpper H) Mc) inf_le_right hS2.to_inf_left
      hSylD.2.2 hL
  have hTY₀ : T ≤ Subgroup.normalizer (Y₀ : Set G) := fun g hg => hY₀n g (hTKc hg) (hTD hg)
  have hSY₀ : sOf152 T Mc M B₀ ≤ Subgroup.normalizer (Y₀ : Set G) := S_le_T152.trans hTY₀
  have hY₀Mc : Y₀ ≤ Mc := (hY₀K.trans hKcI).trans inf_le_left
  have hY₀C : Y₀ ≤ M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) :=
    Y0_le_cv_F4 h08 hs hD hTY₀ hY₀eq hY₀3 hY₀ne hY₀Mc
  have h3dvd : 3 ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) :=
    (three_dvd_card_of_relIndex hY₀3).trans (Subgroup.card_dvd_of_le hY₀C)
  have hYn : M ≤ Subgroup.normalizer (yOf152 T Mc M : Set G) := c03.normal
  have hY₁3 : (pCoreOf 2 Y₁).relIndex Y₁ = 3 :=
    relIndex_pCoreOf_of_quot_perm hS2 hY₁eq hSY₁ hq
  have hdS : d ∈ sOf152 T Mc M B₀ := hdD.1
  rcases c03.cases with hi | hii' | hiii
  · obtain ⟨-, -, h3'⟩ := hi
    exact h3' hii.2.1.1 h3dvd
  · obtain ⟨-, -, -, hMb0, -, -, hθ⟩ := hii'
    exact false_of_caseII hData hs hB₀ hD hii hYn hMb0 hθ hY₀eq hY₀3 hY₀C hSY₀ hdS hd
  · exact isThreePrimeGroup_of_caseIII hData hs hB₀ hD hii hYn hiii hY₁N hY₁eq hY₁3 hnY₁ h3dvd

end CFSG.Quasithin.S15221
