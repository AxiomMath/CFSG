module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LIComponent
public import CFSG.ClassicalGroups.SpecialLinear.OddCentralizerSylow

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.QuasithinUnique

theorem odd_centralizer_sylow_le_center_of_isSylowTwoOf
    {m : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (hm : 2 ≤ m)
    {V : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) F)}
    (hV : IsSylowTwoOf V ⊤)
    {y : Matrix.SpecialLinearGroup (Fin (m + 1)) F} (hyodd : Odd (orderOf y))
    (hyc : y ∈ Subgroup.centralizer (V : Set _)) :
    y ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F) := by
  have hVindex : ¬ 2 ∣ V.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hV.2.2
  let W : Sylow 2 (Matrix.SpecialLinearGroup (Fin (m + 1)) F) :=
    hV.2.1.toSylow hVindex
  have hWy : y ∈ Subgroup.centralizer
      ((W : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) : Set _) := by
    simpa only [W, IsPGroup.toSylow_coe] using hyc
  exact CFSG.ClassicalGroups.SpecialLinear.odd_centralizer_sylow_le_center
    (m := m) (by omega) W hyodd hWy

theorem odd_centralizer_centralizes_of_component_A_uncond
    {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsQuasisimple L)
    (m : ℕ) (hm : 3 ≤ m) (Q : TauCeti.PrimePower) (hQ : Q.p = 2)
    (hv : (TauCeti.LieTypeIndex.A m Q).Valid)
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.A m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    {U : Subgroup L} (hU2 : IsPGroup 2 U) (hUmax : IsSylowTwoOf U ⊤)
    {x : L} (hxodd : Odd (orderOf x)) (hxc : x ∈ Subgroup.centralizer (U : Set L)) :
    ∀ l : L, x * l = l * x := by
  refine odd_centralizer_centralizes_of_component_A hL m hm Q hQ hv e hU2 hUmax hxodd hxc ?_
  intro F hFfield hFfinite hFchar hFcard V hV y hyodd hyc
  letI : Field F := hFfield
  letI : Finite F := hFfinite
  letI : CharP F 2 := hFchar
  exact odd_centralizer_sylow_le_center_of_isSylowTwoOf (m := m) (by omega) hV hyodd hyc

end CFSG.LocalAnalysis.RankThreeUC.S15

end
