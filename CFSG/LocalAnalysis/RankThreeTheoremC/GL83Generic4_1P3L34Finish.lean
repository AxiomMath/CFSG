module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Config
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34End
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Final
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34KFacts3
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Abel
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Proper
import CFSG.LocalAnalysis.LargeEvenClassification.CoprimeCommutators
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34b

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup

variable {G : Type} [Group G] [Finite G]

theorem l34_false_of_config (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (hInn : KFactInnerAction) (hWC : KFactWeakClosure) (hK1 : KFactL34TwoSignalizer)
    (hK2 : KFactL34Three) (hK3 : KFactL34Unitary) (hK4 : KFactL34Borel) (hK5 : KFactL34Graph)
    (hK6 : KFactL34OutThree) (hK8 : KFactL34SylowCentralizer) (hK9 : KFactL34ThreeExponent)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G}
    (hM : IsCoreMaxLocal 3 P M) {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G}
    (hJ : IsL34Normal M x J) (hplane : L34PlaneData 3 P M x J) : False := by
  obtain ⟨U, S₁, T, hc⟩ := l34_config_exists hS hU0 hD1 hK1 hK2 hK3 hK4 hK5 hK8 hp hM hgen hJ hplane
  have hx1 : x ≠ 1 := hgen.2.1.2.1
  have hSc : (⁅S₁ ⊓ M, zpowers x⁆ : Subgroup G) ≠ ⊥ :=
    l34_hstarProper hS hx1 hgen.2.1.2.2.1 hc.x_mem hc.maximal hc.not_le hc.comm_eq
  have hUM : U ≤ M := hc.U_le.trans (sylow_le_of_isCoreMaxLocal hS hp hM).1
  have hUS₁ : U ≤ normalizer (S₁ : Set G) := hc.maximal.2.1
  have hS₁2 : IsPGroup 2 S₁ := hc.maximal.1
  have hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    p34_comm_of_isMulCommutative hc.U_elemAbelian.1 ha hb
  have hUx : U ≤ normalizer (zpowers x : Set G) := by
    intro u hu
    refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun g hg => ?_)
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    exact (Commute.zpow_left (hUab x hc.x_mem u hu) k).eq
  have hxS : zpowers x ≤ normalizer (S₁ : Set G) := zpowers_le.mpr (hUS₁ hc.x_mem)
  have hUSM : U ≤ normalizer ((S₁ ⊓ M : Subgroup G) : Set G) :=
    common_normalizer_le_normalizer_inf U S₁ M hUS₁ (hUM.trans Subgroup.le_normalizer)
  have hUSc : U ≤ normalizer ((⁅S₁ ⊓ M, zpowers x⁆ : Subgroup G) : Set G) :=
    CFSG.LargeEvenClassification.Helpers.normalizes_commutator_pair U (S₁ ⊓ M) (zpowers x) hUSM hUx
  have hScS₁ : (⁅S₁ ⊓ M, zpowers x⁆ : Subgroup G) ≤ S₁ := by
    rw [hc.comm_eq]
    exact CFSG.LargeEvenClassification.Helpers.commutator_le_of_normalized S₁ _ hxS
  have hSc2 : IsPGroup 2 (⁅S₁ ⊓ M, zpowers x⁆ : Subgroup G) := hS₁2.to_le hScS₁
  have hesc : ¬ normalizer ((⁅S₁ ⊓ M, zpowers x⁆ : Subgroup G) : Set G) ≤ M := fun h =>
    hc.not_le (hc.comm_normal.trans h)
  have hrank := l34_stepJ_rank hS hU0 hD1 hp hM hc.U_elemAbelian hc.U_card hc.U_le hSc2 hSc hUSc
    hesc
  have hUT : U ≤ normalizer (T : Set G) := hc.pair.1.2.2.1
  have hUN : U ≤ normalizer ((GLBPrimeCore 3 M : Subgroup G) : Set G) :=
    hUM.trans (le_normalizer_glbPrimeCore 3 M)
  have hUR₀ : U ≤ normalizer ((T ⊓ GLBPrimeCore 3 M ⊓ normalizer ((S₁ ⊓ M : Subgroup G) :
      Set G) : Subgroup G) : Set G) :=
    common_normalizer_le_normalizer_inf U _ _
      (common_normalizer_le_normalizer_inf U T _ hUT hUN)
      (hUSM.trans Subgroup.le_normalizer)
  have hFab := l34_stepL hS hU0 hD1 hK1 hK2 hK6 hK9 hp hM hgen hJ hplane.1 hc.U_elemAbelian
    hc.U_card hc.U_le hc.x_mem hc.U_inf_J hSc2 hSc hUSc hesc hrank
  have hend := l34_stepJ hS hU0 hD1 hInn hWC hp hM hplane.1 hc.U_elemAbelian hc.U_card hc.U_le
    hc.x_mem hx1 hc.lemma42 hSc2 hSc hUSc hesc hFab (inf_le_left.trans inf_le_right) hc.escape_le
    hUR₀ hc.escape_not
  obtain ⟨⟨r, hr⟩, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hend
  have hr1' : r ≠ 1 := fun h => hr1 (Subtype.ext h)
  have hrT : r ∈ T := hr.1.1.1
  obtain ⟨k, hk⟩ := hc.pair.1.2.1 ⟨r, hrT⟩
  exact l34_stepK hS hU0 hD1 hK1 hK2 hK3 hK4 hp hM hgen hJ hc.U_elemAbelian hc.U_card hc.U_le
    hc.x_mem hc.U_inf_J hUS₁ hc.sylow_two hc.comm_normal hUSc hrank (hc.escape_le hr.1)
    (hr.1.1.2) hr.2 ⟨k, congrArg Subtype.val hk⟩ hr1'

end CFSG.LocalAnalysis.RankThreeTheoremC
