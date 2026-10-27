module

public import CFSG.GroupTheory.SylowIntersectionControl.SingularSubgroup.Regular
import CFSG.GroupTheory.NatL2SectionIrreducible
import CFSG.GroupTheory.PCore.InfPCoreOf
import CFSG.GroupTheory.SylowIntersectionControl.GomiOverCore
import CFSG.Quasithin.Background.B6Basic
import CFSG.Quasithin.Background.C1GNNotation
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCShort

public section

namespace CFSG.GroupTheory.GomiThm45Counterexample

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {Ω : Type} [Group Ω] [Finite Ω] {c : GNPairChoice Ω} {G S : Subgroup Ω}

private theorem commutator_pCoreOf_le_gomiV_g45ib1 {G M T X : Subgroup Ω}
    (hMG : M ≤ G) (hGM : G ≤ Subgroup.normalizer (M : Set Ω))
    (hX : IsGomiSingularSubgroup M T X) :
    ⁅pCoreOf 2 G, X⁆ ≤ gomiV M := by
  have hXQ : X ≤ Subgroup.normalizer (pCoreOf 2 G : Set Ω) :=
    hX.le.trans (hMG.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G))
  have hQX : ⁅pCoreOf 2 G, X⁆ ≤ pCoreOf 2 G :=
    (Subgroup.le_normalizer_iff_commutator_le_left (H := X) (K := pCoreOf 2 G)).mp hXQ
  have hQM : ⁅pCoreOf 2 G, M⁆ ≤ M :=
    (Subgroup.le_normalizer_iff_commutator_le_right (H := pCoreOf 2 G) (K := M)).mp
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 G).trans hGM)
  have hQXM : ⁅pCoreOf 2 G, X⁆ ≤ pCoreOf 2 G ⊓ M :=
    le_inf hQX ((Subgroup.commutator_mono le_rfl hX.le).trans hQM)
  have hQXR : ⁅pCoreOf 2 G, X⁆ ≤ pCoreOf 2 M :=
    hQXM.trans ((inf_comm (pCoreOf 2 G) M).le.trans (inf_pCoreOf_le_pCoreOf 2 hMG))
  have hJ := eq_top_of_isPGroup_quotient_of_twoResidual_eq hX.twoResidual_eq
  have hsims := CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.commutator_commutator_eq_of_twoResidual
    hJ (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G) hXQ
  calc ⁅pCoreOf 2 G, X⁆ = ⁅⁅pCoreOf 2 G, X⁆, X⁆ := hsims.symm
    _ ≤ ⁅pCoreOf 2 M, X⁆ := Subgroup.commutator_mono hQXR le_rfl
    _ ≤ gomiV M := hX.commutator_pCoreOf_le

private theorem commutator_gomiV_eq_g45ib1 {G M T X : Subgroup Ω}
    (hMG : M ≤ G) (hGM : G ≤ Subgroup.normalizer (M : Set Ω))
    (hX : IsGomiSingularSubgroup M T X)
    (hWX : ⁅gomiV M, X⁆ ≤ gomiV G) :
    ⁅gomiV G, X⁆ = ⁅gomiV M, X⁆ := by
  have hXG : X ≤ G := hX.le.trans hMG
  have hV2 : IsPGroup 2 (gomiV G) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G).to_le
      (CFSG.Quasithin.C1GN.omegaOneCenterOf_le_self _)
  have hW2 : IsPGroup 2 (gomiV M) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le
      (CFSG.Quasithin.C1GN.omegaOneCenterOf_le_self _)
  have hXV : X ≤ Subgroup.normalizer (gomiV G : Set Ω) :=
    hXG.trans (gomiV_moduleSetting G).2
  have hXW : X ≤ Subgroup.normalizer (gomiV M : Set Ω) :=
    hX.le.trans (gomiV_moduleSetting M).2
  have hJ := eq_top_of_isPGroup_quotient_of_twoResidual_eq hX.twoResidual_eq
  have hsimsV := CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.commutator_commutator_eq_of_twoResidual
    hJ hV2 hXV
  have hsimsW := CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.commutator_commutator_eq_of_twoResidual
    hJ hW2 hXW
  have hVXW : ⁅gomiV G, X⁆ ≤ gomiV M :=
    (Subgroup.commutator_mono (CFSG.Quasithin.C1GN.omegaOneCenterOf_le_self _) le_rfl).trans
      (commutator_pCoreOf_le_gomiV_g45ib1 hMG hGM hX)
  apply le_antisymm
  · calc ⁅gomiV G, X⁆ = ⁅⁅gomiV G, X⁆, X⁆ := hsimsV.symm
      _ ≤ ⁅gomiV M, X⁆ := Subgroup.commutator_mono hVXW le_rfl
  · calc ⁅gomiV M, X⁆ = ⁅⁅gomiV M, X⁆, X⁆ := hsimsW.symm
      _ ≤ ⁅gomiV G, X⁆ := Subgroup.commutator_mono hWX le_rfl

private theorem isGomiSingularSubgroup_of_commutator_le_g45ib1 {G S M T X : Subgroup Ω}
    (hMG : M ≤ G) (hGM : G ≤ Subgroup.normalizer (M : Set Ω))
    (hJST : thompsonJ T = thompsonJ S) (hX : IsGomiSingularSubgroup M T X)
    (hWX : ⁅gomiV M, X⁆ ≤ gomiV G) : IsGomiSingularSubgroup G S X := by
  have hcomm : ⁅gomiV G, X⁆ = ⁅gomiV M, X⁆ :=
    commutator_gomiV_eq_g45ib1 hMG hGM hX hWX
  have hQXW : ⁅pCoreOf 2 G, X⁆ ≤ gomiV M :=
    commutator_pCoreOf_le_gomiV_g45ib1 hMG hGM hX
  have hXQ : X ≤ Subgroup.normalizer (pCoreOf 2 G : Set Ω) :=
    hX.le.trans (hMG.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G))
  have hJ := eq_top_of_isPGroup_quotient_of_twoResidual_eq hX.twoResidual_eq
  have hsimsQ := CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.commutator_commutator_eq_of_twoResidual
    hJ (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G) hXQ
  refine ⟨hX.le.trans hMG, ?_, hX.twoResidual_eq, ?_, ?_⟩
  · simpa only [hJST] using hX.eq_commutator_thompsonJ
  · calc ⁅pCoreOf 2 G, X⁆ = ⁅⁅pCoreOf 2 G, X⁆, X⁆ := hsimsQ.symm
      _ ≤ ⁅gomiV M, X⁆ := Subgroup.commutator_mono hQXW le_rfl
      _ ≤ gomiV G := hWX
  · obtain ⟨C, n, hn, hnat⟩ := hX.natural
    exact ⟨C, n, hn, by simpa only [hcomm] using hnat⟩

private theorem le_centralizer_gomiV_of_not_commutator_le_g45ib1 {G M T X : Subgroup Ω}
    (hMG : M ≤ G) (hGM : G ≤ Subgroup.normalizer (M : Set Ω))
    (hX : IsGomiSingularSubgroup M T X)
    (hWX : ¬ ⁅gomiV M, X⁆ ≤ gomiV G) :
    X ≤ Subgroup.centralizer (gomiV G : Set Ω) := by
  have hXG : X ≤ G := hX.le.trans hMG
  have hV2 : IsPGroup 2 (gomiV G) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G).to_le
      (CFSG.Quasithin.C1GN.omegaOneCenterOf_le_self _)
  have hW2 : IsPGroup 2 (gomiV M) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le
      (CFSG.Quasithin.C1GN.omegaOneCenterOf_le_self _)
  have hXV : X ≤ Subgroup.normalizer (gomiV G : Set Ω) :=
    hXG.trans (gomiV_moduleSetting G).2
  have hXW : X ≤ Subgroup.normalizer (gomiV M : Set Ω) :=
    hX.le.trans (gomiV_moduleSetting M).2
  have hVXW : ⁅gomiV G, X⁆ ≤ gomiV M :=
    (Subgroup.commutator_mono (CFSG.Quasithin.C1GN.omegaOneCenterOf_le_self _) le_rfl).trans
      (commutator_pCoreOf_le_gomiV_g45ib1 hMG hGM hX)
  obtain ⟨C, n, -, hnat⟩ := hX.natural
  have hXVW : X ≤ Subgroup.normalizer (gomiV G ⊓ gomiV M : Set Ω) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hXV hx, hXW hx⟩
  have hcent : X ≤ Subgroup.centralizer (gomiV G ⊓ gomiV M : Set Ω) := by
    by_contra hc
    have hle : ⁅gomiV M, X⁆ ≤ gomiV G ⊓ gomiV M :=
      CFSG.Quasithin.commutator_le_of_isNatL2Section (V := gomiV M)
        (W := gomiV G ⊓ gomiV M) (X := X) (C := C) (n := n)
        hW2 hX.twoResidual_eq hXW inf_le_right hXVW hnat hc
    exact hWX (hle.trans inf_le_left)
  have hVXleV : ⁅gomiV G, X⁆ ≤ gomiV G :=
    (Subgroup.le_normalizer_iff_commutator_le_left (H := X) (K := gomiV G)).mp hXV
  have hcent' : gomiV G ⊓ gomiV M ≤ Subgroup.centralizer (X : Set Ω) :=
    Subgroup.le_centralizer_iff.mp hcent
  have hbot : ⁅⁅gomiV G, X⁆, X⁆ = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := ⁅gomiV G, X⁆) (H₂ := X)).mpr
      ((le_inf hVXleV hVXW).trans hcent')
  have hJ := eq_top_of_isPGroup_quotient_of_twoResidual_eq hX.twoResidual_eq
  have hsimsV := CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.commutator_commutator_eq_of_twoResidual
    hJ hV2 hXV
  have hVXbot : ⁅gomiV G, X⁆ = ⊥ := by
    rw [← hsimsV]
    exact hbot
  exact Subgroup.le_centralizer_iff.mp
    ((Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := gomiV G) (H₂ := X)).mp hVXbot)

theorem le_centralizer_gomiV_of_isGomiSingularSubgroup (h : GomiThm45Counterexample c G S)
    {M X : Subgroup Ω} (hMG : M ≤ G) (hGM : G ≤ Subgroup.normalizer (M : Set Ω))
    (hJM : thompsonJ S ≤ M) (hX : IsGomiSingularSubgroup M (S ⊓ M) X) :
    X ≤ Subgroup.centralizer (gomiV G : Set Ω) := by
  have hJT : thompsonJ (S ⊓ M) = thompsonJ S :=
    thompsonJ_eq_of_thompsonJ_le h.isSylowTwoOf (inf_le_right.trans hMG)
      (h.isSylowTwoOf.2.1.to_le inf_le_left) (le_inf (B6.thompsonJ_le S) hJM)
  by_cases hWX : ⁅gomiV M, X⁆ ≤ gomiV G
  · exact absurd
      (isGomiSingularSubgroup_of_commutator_le_g45ib1 hMG hGM hJT hX hWX)
      (h.not_isGomiSingularSubgroup X)
  · exact le_centralizer_gomiV_of_not_commutator_le_g45ib1 hMG hGM hX hWX

end CFSG.GroupTheory.GomiThm45Counterexample
