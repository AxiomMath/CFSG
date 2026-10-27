module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenTwelve
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.S11CharNormal
import CFSG.Quasithin.Recognition.F112Crit.Theorem723

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup

theorem fiveTwentyFiveS11Use_holds :
    FiveTwentyFiveS11Use := by
  intro G _ _ X L T R φ i j hcharX hT hLn hcomp _ hφ hker hQR hRT hij hNR hnoX
  classical
  have hLX : L ≤ X := hcomp.1
  have hTX : T ≤ X := hT.le
  have hRX : R ≤ X := hRT.trans hTX
  have hC : CFSG.QuasithinUnique.CharTwo (⊤ : Subgroup ↥X) :=
    CFSG.AGLEmbeddingD2.McLaughlin.charTwo_top_of_le hcharX
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 X) le_rfl
  have hcore : CFSG.Open.pCoreOf 2 (⊤ : Subgroup ↥X) =
      (CFSG.Open.pCoreOf 2 X).subgroupOf X := by
    rw [← Subgroup.subgroupOf_self (H := X)]
    exact (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_subgroupOf 2 X X le_rfl).symm
  have hker' : φ.ker = CFSG.Open.pCoreOf 2 (⊤ : Subgroup ↥X) := hker.trans hcore.symm
  have hQR' : CFSG.Open.pCoreOf 2 (⊤ : Subgroup ↥X) ≤ R.subgroupOf X := by
    rw [hcore]
    exact Subgroup.subgroupOf_mono X hQR
  have hR2 : IsPGroup 2 R := hT.isPGroup.to_le hRT
  have hR2' : IsPGroup 2 (R.subgroupOf X) := hR2.comap_subtype
  have hLodd' : L.subgroupOf X =
      Subgroup.closure {x : ↥X | x ∈ L.subgroupOf X ∧ Odd (orderOf x)} := by
    refine le_antisymm ?_ ?_
    · exact CFSG.Quasithin.F112Crit.T723.subgroupOf_odd_gen hLX (le_of_eq hcomp.2.2.2)
    · exact (Subgroup.closure_le (L.subgroupOf X)).mpr fun x hx => hx.1
  have hLker' : ¬ L.subgroupOf X ≤ φ.ker := by
    intro hle
    have hLleP : L ≤ CFSG.Open.pCoreOf 2 X := by
      intro l hl
      have hl' : (⟨l, hLX hl⟩ : ↥X) ∈ L.subgroupOf X := Subgroup.mem_subgroupOf.mpr hl
      have hmem : (⟨l, hLX hl⟩ : ↥X) ∈ φ.ker := hle hl'
      rw [hker', hcore] at hmem
      simpa using Subgroup.mem_subgroupOf.mp hmem
    have hL2 : IsPGroup 2 L :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le hLleP
    have htop2 : IsPGroup 2 ↥(⊤ : Subgroup ↥L) := hL2.of_equiv Subgroup.topEquiv.symm
    have hpCoreL : CFSG.pCore 2 ↥L = ⊤ := by
      rw [CFSG.RankThreeCoreUniqueness.Helpers.pCore_eq_sSup]
      exact top_le_iff.mp (le_sSup (s := {K : Subgroup ↥L | K.Normal ∧ IsPGroup 2 ↥K})
        ⟨inferInstance, htop2⟩)
    have hnt : Nontrivial (↥L ⧸ CFSG.pCore 2 ↥L) :=
      CFSG.LocalCores.isQuasisimple_nontrivial hcomp.2.2.1
    have hsub : Subsingleton (↥L ⧸ CFSG.pCore 2 ↥L) := by
      rw [hpCoreL]
      exact QuotientGroup.subsingleton_quotient_top
    exact (not_subsingleton_iff_nontrivial.mpr hnt) hsub
  have hNR' : (Subgroup.normalizer ((R.subgroupOf X : Subgroup ↥X) : Set ↥X)).map φ =
      Subgroup.centralizer ({Equiv.swap i j} : Set (Equiv.Perm (Fin 11))) := by
    have hsubgroup : (Subgroup.normalizer (R : Set G) ⊓ X).subgroupOf X =
        Subgroup.normalizer ((R.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
      rw [Subgroup.inf_subgroupOf_right]
      exact Subgroup.subgroupOf_normalizer_eq hRX
    rw [← hsubgroup]
    exact hNR
  have hnoX' : ¬ CFSG.AGLEmbedding.InClassXBlock (L.subgroupOf X) := by
    intro hbad
    have hIn1 : CFSG.RankThree.PartOne.InClassX ↥(L.subgroupOf X) :=
      CFSG.AGLEmbedding.NoXBlock.inClassX_of_inClassXBlock hbad
    have hIn2 : CFSG.RankThree.PartOne.InClassX ↥L :=
      (CFSG.CGT.PushingUpLit.inClassX_subgroupOf_iff hLX).mp hIn1
    exact hnoX L hLX ((CFSG.Open.IsSubnormal.iff_subgroupOf hLX).mpr hcomp.2.1)
      (CFSG.AGLEmbedding.LocalCGT.inClassXBlock_of_inClassX hIn2)
  obtain ⟨T₀', hT₀'ne, hT₀'R, hT₀'char, hT₀'norm⟩ :=
    exists_char_normal_of_s11 (X := ↥X) (L := L.subgroupOf X) (R := R.subgroupOf X)
      hC hLn hLodd' φ hφ hker' hLker' hQR' hR2' hij hNR' hnoX'
  obtain ⟨hT₀R, hT₀char⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.S15.map_subtype_characteristic hRX hT₀'R hT₀'char
  refine ⟨T₀'.map X.subtype, ?_, hT₀R, hT₀char, ?_⟩
  · intro hbot
    exact hT₀'ne ((Subgroup.map_eq_bot_iff_of_injective T₀' X.subtype_injective).mp hbot)
  ·
    intro x hx
    have hxn : (⟨x, hx⟩ : ↥X) ∈ Subgroup.normalizer (T₀' : Set ↥X) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hT₀'norm]
      exact Subgroup.mem_top _
    exact (CFSG.Glauberman.mem_normalizer_map_subtype_iff (M := X) T₀' ⟨x, hx⟩).mp hxn

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
