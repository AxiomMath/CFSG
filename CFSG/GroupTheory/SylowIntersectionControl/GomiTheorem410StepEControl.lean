module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepEFact36
public import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepERegular

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.RankThree.PartOne

variable {Ω : Type} [Group Ω] [Finite Ω] {f : PSubgroupSelection 2 Ω}
  {hyp : Subgroup Ω → Prop} {G : Subgroup Ω}

private theorem twoResidual_inf_centralizer_eq_bot_ectl {Y : Type} [Group Y] [Finite Y]
    {M : Subgroup Y}
    (h : M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set Y) ≤ pCoreOf 2 M) :
    twoResidual (M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set Y)) = ⊥ := by
  refine le_bot_iff.mp (twoResidual_le_of_isTwoQuotient
    (H := M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set Y)) (N := (⊥ : Subgroup Y))
    bot_le ?_ ?_)
  · rw [Subgroup.normalizer_eq_top_iff.mpr Subgroup.normal_bot]; exact le_top
  · intro y hy
    obtain ⟨k, hk⟩ := IsPGroup.exists_pow_pow_eq_one
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M) ⟨y, h hy⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem isNormalSetIn_gomiRegFamily (f : PSubgroupSelection 2 Ω) (G : Subgroup Ω) :
    IsNormalSetIn (gomiRegFamily f G) ⊤ := by
  constructor
  · intro M _
    exact le_top
  · rintro M ⟨hMne, hModd, hMreg⟩ g -
    obtain ⟨g', rfl⟩ := gomiBar_surjective G g
    refine ⟨?_, ?_, ?_⟩
    · refine ne_of_lt ?_
      rw [← Subgroup.map_top_of_surjective (MulAut.conj (gomiBar G g')).toMonoidHom
        (MulAut.conj (gomiBar G g')).surjective]
      exact (Subgroup.map_lt_map_iff_of_injective
        (f := (MulAut.conj (gomiBar G g')).toMonoidHom)
        (MulAut.conj (gomiBar G g')).injective).mpr hMne.lt_top
    · rw [Subgroup.index_map_of_bijective (MulAut.conj (gomiBar G g')).bijective M]
      exact hModd
    · rw [gomiBarPre_map_conj G M g']
      exact hMreg.map_conj (g' : Ω)

theorem Gomi410Cex.controls_gomiRegFamily_chev (h : Gomi410Cex f hyp G)
    (hfZ : ∀ P : Subgroup Ω, IsPGroup 2 P → omegaOneCenterOf P ∈ f.sets P)
    (hchar : CharTwo G) (hmono : ∀ H : Subgroup Ω, H ≤ G → pCoreOf 2 G ≤ H → hyp H)
    (h22 : GomiFact22) (h36 : GomiFact36)
    (h45 : ∀ S : Subgroup Ω, IsSylowTwoOf S G → ∃ X : Subgroup Ω, IsGomiSingularSubgroup G S X)
    {B : Subgroup Ω} (hB : IsGomiTwoComponent G B) (hBt : IsGomi410Type G B)
    (hGB : ∀ S : Subgroup Ω, IsSylowTwoOf S G → G = conjClosure B G ⊔ S)
    (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G)
    (hchev : IsGomiChevTwo (↥B ⧸ CFSG.pCore 2 ↥B) ∧
      ¬ IsGomiL2 ((↥B ⧸ CFSG.pCore 2 ↥B) ⧸ Subgroup.center (↥B ⧸ CFSG.pCore 2 ↥B)) ∧
      ¬ IsGomiU3 ((↥B ⧸ CFSG.pCore 2 ↥B) ⧸ Subgroup.center (↥B ⧸ CFSG.pCore 2 ↥B)) ∧
      ¬ IsGomiSz ((↥B ⧸ CFSG.pCore 2 ↥B) ⧸ Subgroup.center (↥B ⧸ CFSG.pCore 2 ↥B))) :
    ControlsSylowIntersections 2 (gomiRegFamily f G) ⊤ := by
  refine controlsSylowIntersections_of_isPIsolatedOver (G := ↥(autOn G (gomiV G))) (p := 2)
    (𝓕 := gomiRegFamily f G) ?_
  intro H hHne hH2 hHiso
  obtain ⟨e₀⟩ := nonempty_mulEquiv_gomiBarOf hB hCQ
  have e₁ := QuotientGroup.congr (Subgroup.center _) (Subgroup.center _) e₀
    (Subgroup.map_center_eq e₀)
  have hchev2 : IsGomiChevTwo ↥(gomiBarOf G B) := hchev.1.of_mulEquiv e₀
  have hnot : ¬ (IsGomiL2 (↥(gomiBarOf G B) ⧸ Subgroup.center ↥(gomiBarOf G B)) ∨
      IsGomiU3 (↥(gomiBarOf G B) ⧸ Subgroup.center ↥(gomiBarOf G B)) ∨
      IsGomiSz (↥(gomiBarOf G B) ⧸ Subgroup.center ↥(gomiBarOf G B))) := by
    rintro (hL2 | hU3 | hSz)
    · exact hchev.2.1 (hL2.of_mulEquiv e₁.symm)
    · exact hchev.2.2.1 (hU3.of_mulEquiv e₁.symm)
    · exact hchev.2.2.2 (hSz.of_mulEquiv e₁.symm)
  have hex2 : (IsGomiL3 (↥(gomiBarOf G B) ⧸ Subgroup.center ↥(gomiBarOf G B)) ∨
      IsGomiSp4 (↥(gomiBarOf G B) ⧸ Subgroup.center ↥(gomiBarOf G B))) →
      ∃ S : Sylow 2 ↥(autOn G (gomiV G)),
        ¬ IsGomiParabolicSwap (S : Subgroup ↥(autOn G (gomiV G))) (gomiBarOf G B) :=
    fun hL => h.exists_not_isGomiParabolicSwap hfZ hchar hmono h36 h45 hB hBt hGB hCQ
      hchev.1 hL
  obtain ⟨M, hMne, hModd, ⟨K, hHK, hKN, hKsub, hKdvd, hKM⟩, hle⟩ :=
    h22 ↥(autOn G (gomiV G)) (gomiBarOf G B) (gomiHyp21_gomiBarOf hB hBt hGB hCQ)
      hchev2 hnot hex2 H hHne hH2 hHiso
  exact ⟨K, hHK, hKN, hKsub, hKdvd, M,
    ⟨hMne, hModd, isRegular_gomiBarPre_of_le_center h hchar hmono hB hGB hCQ hMne hModd hle⟩,
    hKM⟩

theorem Gomi410Cex.controls_gomiRegFamily_alt (h : Gomi410Cex f hyp G) (hchar : CharTwo G)
    (hmono : ∀ H : Subgroup Ω, H ≤ G → pCoreOf 2 G ≤ H → hyp H) (h23 : GomiFact23)
    {B : Subgroup Ω} (hB : IsGomiTwoComponent G B) (hBt : IsGomi410Type G B)
    (hGB : ∀ S : Subgroup Ω, IsSylowTwoOf S G → G = conjClosure B G ⊔ S)
    (hCQ : G ⊓ Subgroup.centralizer (gomiV G : Set Ω) = pCoreOf 2 G) {m : ℕ} (hm : 4 ≤ m)
    (e : (↥B ⧸ CFSG.pCore 2 ↥B) ≃* alternatingGroup (Fin (2 * m))) :
    ControlsSylowIntersections 2 (gomiRegFamily f G) ⊤ := by
  refine controlsSylowIntersections_of_isPIsolatedOver (G := ↥(autOn G (gomiV G))) (p := 2)
    (𝓕 := gomiRegFamily f G) ?_
  intro H hHne hH2 hHiso
  obtain ⟨e₀⟩ := nonempty_mulEquiv_gomiBarOf hB hCQ
  obtain ⟨M, hMne, hModd, ⟨K, hHK, hKN, hKsub, hKdvd, hKM⟩, hcharM⟩ :=
    (h23 ↥(autOn G (gomiV G)) (gomiBarOf G B) (2 * m)
      (gomiHyp21_gomiBarOf hB hBt hGB hCQ) (by omega) ⟨e₀.symm.trans e⟩
      H hHne hH2 hHiso).2.1 (even_two_mul m)
  have hle : twoResidual (M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set ↥(autOn G (gomiV G)))) ≤
      Subgroup.normalClosure (gomiBarOf G B : Set ↥(autOn G (gomiV G))) ⊓
        Subgroup.centralizer (Subgroup.normalClosure (gomiBarOf G B :
          Set ↥(autOn G (gomiV G))) : Set ↥(autOn G (gomiV G))) :=
    (le_of_eq (twoResidual_inf_centralizer_eq_bot_ectl hcharM)).trans bot_le
  exact ⟨K, hHK, hKN, hKsub, hKdvd, M,
    ⟨hMne, hModd, isRegular_gomiBarPre_of_le_center h hchar hmono hB hGB hCQ hMne hModd hle⟩,
    hKM⟩

end CFSG.GroupTheory
