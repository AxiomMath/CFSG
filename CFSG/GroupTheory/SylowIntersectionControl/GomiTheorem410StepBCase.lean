module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsGF2
import CFSG.GroupTheory.SylowIntersectionControl.GomiGstar
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S2L6Gen
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellShort
import CFSG.LocalAnalysis.RankThreeEvenClassification.SubgroupWeakClosure

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin (commV ffJ BinaryNaturalSL)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 (Pset PstarSet O2Trivial)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsSLn)

private theorem isSubnormal_subgroupOf_of_normal_bcase {Q : Type*} [Group Q]
    {F N L : Subgroup Q} (hNF : N ≤ F) (hn : (N.subgroupOf F).Normal) (hLN : L ≤ N)
    (hsub : (L.subgroupOf N).IsSubnormal) : (L.subgroupOf F).IsSubnormal := by
  have hHK : L.subgroupOf F ≤ N.subgroupOf F := fun _ hx => hLN hx
  refine Subgroup.IsSubnormal.trans hHK ?_ hn.isSubnormal
  let f : ↥N →* ↥(N.subgroupOf F) := (Subgroup.subgroupOfEquivOfLe hNF).symm.toMonoidHom
  have hf : Function.Surjective f := (Subgroup.subgroupOfEquivOfLe hNF).symm.surjective
  have hmap := hsub.map hf
  convert hmap using 1
  ext y
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · intro hy
    exact ⟨⟨((y : ↥F) : Q), y.2⟩, hy, Subtype.ext (Subtype.ext rfl)⟩
  · rintro ⟨z, hz, rfl⟩
    exact hz

private theorem isComponent_subgroupOf_of_normal_bcase {Q : Type*} [Group Q]
    {F N L₀ : Subgroup Q} (hNF : N ≤ F) (hn : (N.subgroupOf F).Normal) (hL₀N : L₀ ≤ N)
    (hcomp : CFSG.IsComponent (L₀.subgroupOf N)) : CFSG.IsComponent (L₀.subgroupOf F) := by
  have hL₀F : L₀ ≤ F := hL₀N.trans hNF
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((Subgroup.subgroupOfEquivOfLe hL₀N).trans
      (Subgroup.subgroupOfEquivOfLe hL₀F).symm) hcomp.1, ?_⟩
  exact isSubnormal_subgroupOf_of_normal_bcase hNF hn hL₀N hcomp.2

private theorem gomiStepB_pCore_eq_bot_bcase {W : Type} [CommGroup W] [Finite W]
    {G M : Subgroup (MulAut W)} (hO2 : O2Trivial G) (hMG : M ≤ G)
    (hsub : (M.subgroupOf G).IsSubnormal) : CFSG.pCore 2 ↥M = ⊥ := by
  have hO2G : CFSG.Open.pCoreOf 2 G = ⊥ := by
    have hle : CFSG.Open.pCoreOf 2 G ≤ G := CFSG.LieType.BorelTits.pCoreOf_le 2 _
    refine hO2 _ hle ?_ (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) (H := G)
  have hle := CFSG.QuasithinUnique.Setup.Campbell.pCoreOf_le_of_isSubnormal 2 hMG hsub
  have hbot : CFSG.Open.pCoreOf 2 M = ⊥ := le_bot_iff.mp (hO2G ▸ hle)
  rw [CFSG.Open.pCoreOf] at hbot
  exact (Subgroup.map_eq_bot_iff_of_injective (H := CFSG.pCore 2 ↥M) (f := M.subtype)
    M.subtype_injective).mp hbot

private theorem gomiStepB_comm_ne_bot_bcase {W : Type} [CommGroup W]
    {Y M : Subgroup (MulAut W)} (hcomp : CFSG.IsQuasisimple ↥M)
    (hMlePstar : M ≤ (sSup (PstarSet Y) : Subgroup (MulAut W))) :
    ⁅M, ffJ Y⁆ ≠ ⊥ ∧ ⁅M, (sSup (PstarSet Y) : Subgroup (MulAut W))⁆ ≠ ⊥ := by
  have hss : ⁅M, (sSup (PstarSet Y) : Subgroup (MulAut W))⁆ ≠ ⊥ := by
    intro hbot
    have hcent : M ≤
        Subgroup.centralizer ((sSup (PstarSet Y) : Subgroup (MulAut W)) : Set (MulAut W)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    have hcentM : M ≤ Subgroup.centralizer (M : Set (MulAut W)) :=
      hcent.trans (Subgroup.centralizer_le fun _ hx => hMlePstar hx)
    have hcomm : IsMulCommutative ↥M :=
      Subgroup.le_centralizer_iff_isMulCommutative.mp hcentM
    have hcenter : Subgroup.center ↥M = ⊤ := Subgroup.center_eq_top_iff.mpr hcomm
    have hsubsing : Subsingleton (↥M ⧸ Subgroup.center ↥M) := by
      rw [hcenter]
      exact QuotientGroup.subsingleton_quotient_top
    obtain ⟨a, b, hab⟩ := hcomp.2.2
    exact hab (@Subsingleton.elim _ hsubsing (a * b) (b * a))
  refine ⟨?_, hss⟩
  intro hbot
  apply hss
  have hle : (sSup (PstarSet Y) : Subgroup (MulAut W)) ≤ ffJ Y :=
    sSup_le fun A hA => le_iSup_of_le A (le_iSup_of_le hA.1 le_rfl)
  have hmono := Subgroup.commutator_mono (le_refl M) hle
  rw [hbot] at hmono
  exact le_bot_iff.mp hmono

private theorem gomiStepB_case0_bcase {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)} (hY : O2Trivial Y)
    (h31 : GomiFact31) (hP0 : (gomiPstar0Set Y).Nonempty) :
    ∃ N : Subgroup (MulAut W), N ≤ Y ∧ (N.subgroupOf Y).IsSubnormal ∧ IsSLn ↥N 2 1 ∧
      BinaryNaturalSL N (commV N) ⊥ 2 1 := by
  obtain ⟨A, hA0⟩ := hP0
  let N : Subgroup (MulAut W) := gomiOrbitSpan Y A
  have hO2 : O2Trivial (gomiGstar0 Y) :=
    o2Trivial_of_normal hY (gomiGstar0_le Y) (gomiGstar0_subgroupOf_normal Y)
  obtain ⟨⟨hSL, -, -, hsup⟩, ⟨hBN, -, -⟩, -⟩ := h31 W hW Y ⟨A, hA0⟩ hO2
  have hNmem : N ∈ gomiNSet Y := ⟨A, hA0, rfl⟩
  have hNle : N ≤ gomiGstar0 Y := hsup ▸ le_sSup hNmem
  have hNnorm : (N.subgroupOf (gomiGstar0 Y)).Normal := by
    have hN_eq : N = CFSG.RankThreeEvenClassification.Helpers.subgroupConjugateOrbit
        (gomiGstar0 Y) A := by
      show gomiOrbitSpan Y A = CFSG.RankThreeEvenClassification.Helpers.subgroupConjugateOrbit
        (gomiGstar0 Y) A
      rw [gomiOrbitSpan, CFSG.RankThreeEvenClassification.Helpers.subgroupConjugateOrbit]
      refine le_antisymm ?_ ?_
      · refine iSup_le fun g => iSup_le fun hg => ?_
        exact le_iSup (fun member : ↥(gomiGstar0 Y) =>
          A.map (MulAut.conj (member : MulAut W)).toMonoidHom) ⟨g, hg⟩
      · refine iSup_le fun member => ?_
        exact le_iSup_of_le (member : MulAut W)
          (le_iSup (fun _ : (member : MulAut W) ∈ gomiGstar0 Y =>
            A.map (MulAut.conj (member : MulAut W)).toMonoidHom) member.2)
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNle, hN_eq]
    exact CFSG.RankThreeEvenClassification.Helpers.subgroupConjugateOrbit_normalized
      (gomiGstar0 Y) A
  exact ⟨N, hNle.trans (gomiGstar0_le Y),
    isSubnormal_subgroupOf_of_normal_bcase (gomiGstar0_le Y)
      (gomiGstar0_subgroupOf_normal Y) hNle hNnorm.isSubnormal,
    hSL N hNmem, hBN N hNmem⟩

private theorem gomiStepB_case1_bcase {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)} (hY : O2Trivial Y)
    (h33 : GomiFact33) (hP1 : (gomiPstar1Set Y).Nonempty) :
    ∃ M : Subgroup (MulAut W), M ≤ Y ∧ CFSG.IsComponent (M.subgroupOf Y) ∧
      CFSG.pCore 2 ↥M = ⊥ ∧ ⁅M, ffJ Y⁆ ≠ ⊥ ∧ ⁅M, sSup (PstarSet Y)⁆ ≠ ⊥ := by
  have hO2 : O2Trivial (gomiGstar1 Y) :=
    o2Trivial_of_normal hY (gomiGstar1_le Y) (gomiGstar1_subgroupOf_normal Y)
  have hlayer : CFSG.layer ↥(gomiGstar1 Y) ≠ ⊥ := (h33 W hW Y hP1 hO2).1
  obtain ⟨K, hKcomp⟩ :=
    CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2.exists_isComponent_of_layer_ne_bot hlayer
  let M : Subgroup (MulAut W) := K.map (gomiGstar1 Y).subtype
  have hMleGstar : M ≤ gomiGstar1 Y := Subgroup.map_subtype_le K
  have hMY : M ≤ Y := hMleGstar.trans (gomiGstar1_le Y)
  have hMsub_eq : M.subgroupOf (gomiGstar1 Y) = K := by
    ext y
    simp only [M, Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨z, hz, hzy⟩
      simpa [Subtype.ext_iff.mpr hzy] using hz
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hcompM : CFSG.IsComponent (M.subgroupOf (gomiGstar1 Y)) := by
    rw [hMsub_eq]; exact hKcomp
  have hcompMY : CFSG.IsComponent (M.subgroupOf Y) :=
    isComponent_subgroupOf_of_normal_bcase (gomiGstar1_le Y)
      (gomiGstar1_subgroupOf_normal Y) hMleGstar hcompM
  have hQM : CFSG.IsQuasisimple ↥M :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hMY) hcompMY.1
  have hMlePstar : M ≤ (sSup (PstarSet Y) : Subgroup (MulAut W)) :=
    hMleGstar.trans (sSup_le_sSup fun _ hx => hx.1)
  obtain ⟨hff, hss⟩ := gomiStepB_comm_ne_bot_bcase hQM hMlePstar
  exact ⟨M, hMY, hcompMY, gomiStepB_pCore_eq_bot_bcase hO2 hMleGstar hcompM.2, hff, hss⟩

theorem exists_binaryNaturalSL_or_isComponent (h31 : GomiFact31) (h33 : GomiFact33)
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)}
    (hY : O2Trivial Y) (hP : (Pset Y).Nonempty) :
    (∃ N : Subgroup (MulAut W), N ≤ Y ∧ (N.subgroupOf Y).IsSubnormal ∧ IsSLn ↥N 2 1 ∧
        BinaryNaturalSL N (commV N) ⊥ 2 1) ∨
      ∃ M : Subgroup (MulAut W), M ≤ Y ∧ CFSG.IsComponent (M.subgroupOf Y) ∧
        CFSG.pCore 2 ↥M = ⊥ ∧ ⁅M, ffJ Y⁆ ≠ ⊥ ∧ ⁅M, sSup (PstarSet Y)⁆ ≠ ⊥ := by
  obtain ⟨A, hA⟩ := pstarSet_nonempty hP
  by_cases h0 : A ∈ gomiPstar0Set Y
  · exact Or.inl (gomiStepB_case0_bcase hW hY h31 ⟨A, h0⟩)
  · exact Or.inr (gomiStepB_case1_bcase hW hY h33 ⟨A, ⟨hA, h0⟩⟩)

end CFSG.GroupTheory

end
