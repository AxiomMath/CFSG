module

public import CFSG.GroupTheory.SylowIntersectionControl.SingularSubgroup.UniqueMax
import CFSG.GroupTheory.SylowIntersectionControl.SingularSubgroup.GenerationOffender
import CFSG.Quasithin.Background.B6Basic
import CFSG.Quasithin.Background.C1GNNotation
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic
import CFSG.GroupTheory.PCore.NormalPCoreOf
import CFSG.GroupTheory.SylowIntersectionControl.IsolatedCore
import CFSG.GroupTheory.SylowIntersectionControl.RegularGeneration
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.GroupTheory

open CFSG.Open

theorem GomiHyp43.pCoreOf_ne_bot {X : Type} [Group X] [Finite X] {M : Subgroup X}
    (hM : GomiHyp43 M) : pCoreOf 2 M ≠ ⊥ := by
  intro hbot
  have hcent : Subgroup.centralizer ((⊥ : Subgroup X) : Set X) = ⊤ :=
    Subgroup.centralizer_eq_top_iff_subset.mpr (SetLike.coe_subset_coe.mpr bot_le)
  have hle : M ≤ ⊥ := by
    have hc : M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set X) ≤ pCoreOf 2 M := hM.charTwo
    rw [hbot, hcent, inf_top_eq] at hc
    exact hc
  have hMbot : M = ⊥ := le_bot_iff.mp hle
  have hcard : Nat.card M = 1 := by rw [hMbot, Subgroup.card_bot]
  have heven : Even (Nat.card M) := hM.even
  rw [hcard] at heven
  exact Nat.not_even_one heven

end CFSG.GroupTheory

namespace CFSG.GroupTheory.GomiThm45Counterexample

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ABGLocalTools
open scoped IsMulCommutative

variable {Ω : Type} [Group Ω] [Finite Ω] {c : GNPairChoice Ω} {G S : Subgroup Ω}

theorem sup_eq_of_thompsonJ_le (h : GomiThm45Counterexample c G S) {M : Subgroup Ω}
    (hMG : M ≤ G) (hGM : G ≤ Subgroup.normalizer (M : Set Ω)) (hJM : thompsonJ S ≤ M) :
    M ⊔ S = G := by
  by_contra hMS
  have hMsyl : IsSylowTwoOf (pCoreOf 2 M) M :=
    h.isSylowTwoOf_pCoreOf_of_sup_ne hMG hGM hMS
  have hT : IsSylowTwoOf (S ⊓ M) M :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr
      ((CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mp
        h.isSylowTwoOf).inf_of_le_normalizer hMG hGM)
  have hEq : S ⊓ M = pCoreOf 2 M :=
    IsSylowTwoOf.eq_of_le hMsyl (CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hT)
      inf_le_right hT.isPGroup
  have hJQ : thompsonJ S ≤ pCoreOf 2 M :=
    (le_inf (CFSG.Quasithin.B6.thompsonJ_le S) hJM).trans (le_of_eq hEq)
  have hQ : pCoreOf 2 M ≤ pCoreOf 2 G :=
    pCoreOf_le_pCoreOf_of_le_normalizer 2 hMG hGM
  have hQcent : pCoreOf 2 G ≤ Subgroup.centralizer (gomiV G : Set Ω) := by
    refine Subgroup.le_centralizer_iff.mpr ?_
    exact (CFSG.Quasithin.C1GN.omegaOneCenterOf_le_centerOf (pCoreOf 2 G)).trans
      (show CFSG.Quasithin.centerOf (pCoreOf 2 G) ≤
        Subgroup.centralizer (pCoreOf 2 G : Set Ω) from inf_le_right)
  exact h.not_thompsonJ_le_centralizer (hJQ.trans (hQ.trans hQcent))

theorem gomiHyp43_of_thompsonJ_le (h : GomiThm45Counterexample c G S) {M : Subgroup Ω}
    (hMG : M ≤ G) (hGM : G ≤ Subgroup.normalizer (M : Set Ω)) (hJM : thompsonJ S ≤ M) :
    GomiHyp43 M := by
  have hJne : thompsonJ S ≠ ⊥ := fun hbot =>
    h.not_thompsonJ_le_centralizer (hbot ▸ bot_le)
  have hJ2 : IsPGroup 2 (thompsonJ S) :=
    h.isSylowTwoOf.2.1.to_le (CFSG.Quasithin.B6.thompsonJ_le S)
  have hdvd : 2 ∣ Nat.card (thompsonJ S) :=
    hJ2.card_eq_or_dvd.resolve_left (fun h1 => hJne (Subgroup.card_eq_one.mp h1))
  have heven : Even (Nat.card M) :=
    even_iff_two_dvd.mpr (hdvd.trans (Subgroup.card_dvd_of_le hJM))
  refine GomiHyp43.mono h.hyp43 hMG heven ?_
  exact CFSG.QuasithinUnique.CharTwo.of_normal h.hyp43.charTwo hMG
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hMG).mpr hGM)

theorem le_iSup_sylowMembers_of_isRegular (h : GomiThm45Counterexample c G S)
    {Y : Subgroup Ω} (hYG : Y ≤ G) (hreg : c.selection.IsRegular Y) (hbaum : baum S ≤ Y)
    (hIso : ¬ IsPIsolatedOver 2 Y ⊥) (hSyl : IsSylowOf 2 (S ⊓ Y) Y) :
    Y ≤ ⨆ X ∈ sylowMembers 2 (c.selection.family G) S, X := by
  have hgen : Y = ⨆ F ∈ c.selection.sets (S ⊓ Y),
      Y ⊓ Subgroup.normalizer (F : Set Ω) :=
    c.eq_iSup_inf_normalizer_of_isRegular hreg hIso hSyl
  have hle : Y ≤ ⨆ F ∈ c.selection.sets S, G ⊓ Subgroup.normalizer (F : Set Ω) := by
    rw [hgen]
    exact c.iSup_inf_normalizer_le_of_baum_le hYG hSyl inf_le_left h.isSylowTwoOf.2.1
      (le_inf (C1GN.baum_le S) hbaum)
  have hEq : (⨆ X' ∈ sylowMembers 2 (c.selection.family G) S, X') =
      ⨆ F ∈ c.selection.sets S, G ⊓ Subgroup.normalizer (F : Set Ω) := by
    rw [c.selection.sylowMembers_family (isSylowOf_iff.mpr h.isSylowTwoOf), iSup_image]
  rwa [hEq]

theorem not_isRegular_of_baum_le (h : GomiThm45Counterexample c G S)
    {Lb : Subgroup (MulAut ↥(gomiV G))}
    (hL : IsGomiStepE (autOn G (gomiV G)) (autOn S (gomiV G)) Lb) (hg : IsGomiStepG Lb)
    {M : Subgroup Ω} (hMG : M ≤ G) (hGM : G ≤ Subgroup.normalizer (M : Set Ω))
    (hbM : baum S ≤ M) : ¬ c.selection.IsRegular M := by
  intro hreg
  have hJM : thompsonJ S ≤ M := (CFSG.Quasithin.B6.thompsonJ_le_baum S).trans hbM
  have hMS : M ⊔ S = G := h.sup_eq_of_thompsonJ_le hMG hGM hJM
  have hSyl : IsSylowOf 2 (S ⊓ M) M :=
    (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mp
      h.isSylowTwoOf).inf_of_le_normalizer hMG hGM
  have h43 : GomiHyp43 M := h.gomiHyp43_of_thompsonJ_le hMG hGM hJM
  have hpCore : pCoreOf 2 M ≠ ⊥ := GomiHyp43.pCoreOf_ne_bot h43
  have hIso : ¬ IsPIsolatedOver 2 M ⊥ := by
    intro hiso
    have hle : pCoreOf 2 M ≤ ⊥ :=
      IsPIsolatedOver.le_of_normal hiso (p := 2) IsPGroup.of_bot bot_le
        (by rw [Subgroup.normalizer_eq_top]; exact le_top)
        (CFSG.LieType.BorelTits.pCoreOf_le 2 M)
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
    exact hpCore (le_bot_iff.mp hle)
  have hMle : M ≤ ⨆ X ∈ sylowMembers 2 (c.selection.family G) S, X :=
    h.le_iSup_sylowMembers_of_isRegular hMG hreg hbM hIso hSyl
  have hSN : S ≤ Subgroup.normalizer (omegaOneCenterOf S : Set Ω) :=
    (Subgroup.le_centralizer_iff.mpr
      ((CFSG.Quasithin.C1GN.omegaOneCenterOf_le_centerOf S).trans
        (show CFSG.Quasithin.centerOf S ≤ Subgroup.centralizer (S : Set Ω) from
          inf_le_right))).trans (Subgroup.centralizer_le_normalizer _)
  let X : Subgroup Ω := G ⊓ Subgroup.normalizer (omegaOneCenterOf S : Set Ω)
  have hSX : S ≤ X := le_inf h.isSylowTwoOf.1 hSN
  have hXmem : X ∈ sylowMembers 2 (c.selection.family G) S := by
    refine ⟨⟨S, isSylowOf_iff.mpr h.isSylowTwoOf, omegaOneCenterOf S, ?_, rfl⟩, ?_⟩
    · simp [GNPairChoice.selection]
    · rw [inf_eq_left.mpr hSX]
      exact (isSylowOf_iff.mpr h.isSylowTwoOf).of_le hSX inf_le_left
  have hSle : S ≤ ⨆ X' ∈ sylowMembers 2 (c.selection.family G) S, X' :=
    le_iSup₂_of_le X hXmem hSX
  have hGle : G ≤ ⨆ X' ∈ sylowMembers 2 (c.selection.family G) S, X' := by
    have h := sup_le hMle hSle
    rwa [hMS] at h
  have hJoin_le : (⨆ X' ∈ sylowMembers 2 (c.selection.family G) S, X') ≤ G := by
    refine iSup_le fun X' => iSup_le fun hX' => ?_
    obtain ⟨P, hP, F, hF, rfl⟩ := hX'.1
    exact inf_le_left
  exact h.iSup_sylowMembers_ne hL hg (le_antisymm hJoin_le hGle)

theorem le_conjClosure_baum (h : GomiThm45Counterexample c G S) (h31 : GomiFact31)
    (h33 : GomiFact33) {Lb : Subgroup (MulAut ↥(gomiV G))}
    (hL : IsGomiStepE (autOn G (gomiV G)) (autOn S (gomiV G)) Lb) (hg : IsGomiStepG Lb) :
    G ≤ conjClosure (baum S) G := by
  have hbG : baum S ≤ G := (C1GN.baum_le S).trans h.isSylowTwoOf.1
  have hMG : conjClosure (baum S) G ≤ G :=
    conjClosure_le fun g hg z hz => G.mul_mem (G.mul_mem hg (hbG hz)) (G.inv_mem hg)
  have hGM : G ≤ Subgroup.normalizer (conjClosure (baum S) G : Set Ω) :=
    le_normalizer_conjClosure (baum S) G
  have hbM : baum S ≤ conjClosure (baum S) G := le_conjClosure (baum S) G
  have hJM : thompsonJ S ≤ conjClosure (baum S) G := (B6.thompsonJ_le_baum S).trans hbM
  by_contra hle
  have hlt : conjClosure (baum S) G < G := lt_of_le_of_ne hMG fun e => hle e.ge
  have hT : IsSylowTwoOf (S ⊓ conjClosure (baum S) G) (conjClosure (baum S) G) :=
    Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr
      ((Setup.X6.isSylowTwoOf_iff_isSylowOf.mp h.isSylowTwoOf).inf_of_le_normalizer hMG hGM)
  obtain ⟨X, hX⟩ := h.minimal _ hlt (h.gomiHyp43_of_thompsonJ_le hMG hGM hJM)
    (h.not_isRegular_of_baum_le hL hg hMG hGM hbM) _ hT
  exact h.false_of_isGomiSingularSubgroup h31 h33 hMG hGM hJM hX

end CFSG.GroupTheory.GomiThm45Counterexample
