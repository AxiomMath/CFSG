module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivSUTag
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresFinal
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsSU
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.PLengthLemmas
public import CFSG.GroupTheory.QuasisimplePSolvable
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.LieType.SemisimpleCentralizers

open CFSG.Assembly CFSG.LieType.BorelTits CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.StandardType CFSG.LocalAnalysis.ComponentInitial

theorem isSolvable_unitary_centralizer_of_hasNormalPComplement_field
    {F : Type} [Field F] [Finite F] [CharP F 2] {f m : ℕ} (h : UnitaryFieldData 2 f F)
    (hF : Nat.card F = (2 ^ f) ^ 2) (hn : 4 ≤ m + 1)
    {G : Type} [Group G] [Finite G]
    {ψ : SU (unitaryInvolution F 2 f) (m + 1) →* G}
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) (m + 1)))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1)
    {E : Subgroup G} (hE : IsPGroup p E)
    (hdiag : ∀ e ∈ E, GGPsiInnerDiag (Unitary.rootDatum hF (m + 1)) ψ e)
    (hNPC : CFSG.HasNormalPComplement p
      ↥(⁅ψ.range ⊓ Subgroup.centralizer (E : Set G),
         ψ.range ⊓ Subgroup.centralizer (E : Set G)⁆)) :
    Group.IsSolvable ↥(ψ.range ⊓ Subgroup.centralizer (E : Set G)) := by
  classical
  let H : Subgroup G := ψ.range ⊓ Subgroup.centralizer (E : Set G)
  have hNPC' : CFSG.HasNormalPComplement p ↥(⁅H, H⁆) := by
    simpa [H] using hNPC
  have hlayer := CFSG.StandardType.LayerFacts.ggLayer_su_field
    (ggSUCentralizerCoreInput_holds) h hF hn hker hp hp2 hE hdiag
  have hno : ∀ K : Subgroup G, ¬ IsComponentOf K H := by
    intro K hK
    have hKq : CFSG.IsQuasisimple K :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native K).mp hK.2.2
    have hKperf : ⁅K, K⁆ = K := LayerFacts.ggCommutator_eq_of_isQuasisimple hKq
    have hKleD : K ≤ ⁅H, H⁆ := by
      rw [← hKperf]
      exact Subgroup.commutator_mono hK.1 hK.1
    have hNPCK : CFSG.HasNormalPComplement p ↥K :=
      CFSG.hasNormalPComplement_of_le p hKleD hNPC'
    have hpK : p ∣ Nat.card K :=
      LayerPDiv.dvd_card_of_isComponentOf_su_family_field h hF hn hker hp hp2 hpq hE hdiag hK
    haveI : Group.IsPerfect ↥K := LayerFacts.ggIsPerfect_of_commutator_eq hKperf
    haveI : Fact p.Prime := ⟨hp⟩
    exact (hp.coprime_iff_not_dvd).mp
      (CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.coprime_card_of_perfect hNPCK) hpK
  have hlayerbot : LargeEvenLayer H = ⊥ := by
    have hset : {K : Subgroup G | IsComponentOf K H} = ∅ := by
      ext K
      simp [hno K]
    show LargeEvenLayer H = ⊥
    rw [show LargeEvenLayer H = sSup {K : Subgroup G | IsComponentOf K H} from rfl, hset,
      sSup_empty]
  have hpc : CFSG.Quasithin.perfectCore H = ⊥ := by
    have hle : CFSG.Quasithin.perfectCore H ≤ LargeEvenLayer H :=
      hlayer.2 (CFSG.Quasithin.perfectCore H)
        (by simpa [H] using CFSG.Quasithin.perfectCore_le H)
        (CFSG.Quasithin.perfectCore_perfect H)
    rw [hlayerbot, le_bot_iff] at hle
    exact hle
  exact (CFSG.Quasithin.isSolvable_iff_perfectCore_eq_bot H).mpr hpc

end CFSG.LieType.SemisimpleCentralizers
