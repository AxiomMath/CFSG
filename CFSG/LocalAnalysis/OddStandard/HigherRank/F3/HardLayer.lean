module

public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T23Basic
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.HardComp
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.ClassicalInvolution.Q3.Step
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.LocalAnalysis.ComponentClassification.CatalogSchreierCases
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesC
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35LieHalf
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T23Defs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36SporMult
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModels
public import CFSG.LocalAnalysis.ComponentClassification.OddSelector
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdFamilies
public import CFSG.Monster.B.TwoA.Base.FourNorm
public import CFSG.Monster.SteinbergMY443SimpleIsomorphism
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.Parabolic2CheckB
public import CFSG.YGroups.Y443.Native.Parabolic2CheckW
public import Certificates.Certificate10025
public import Certificates.Certificate7233Base
public import Certificates.Kernel.J4Count.FixC
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase
public import Certificates.Kernel.SporSch.J4S.NoCP

public section

namespace CFSG.OddStandard.HigherRank.F3

open Subgroup CFSG
open CFSG.ASVolI.ChIJK (IsComponentIn)

theorem le_layer_of_lBalance (hL : CFSG.StandardType.GGLBalanceInput) {G : Type} [Group G]
    [Finite G] {X : Subgroup G} (hX : CFSG.Open.lBalanceIsKGroup ↥X)
    (hO : pPrimeCore 2 ↥X = ⊥) {x : G} (hxX : x ∈ X) (hx2 : x ^ 2 = 1) {Q : Subgroup G}
    (hQ : ComponentClassification.HarrisLit.IsTwoComponentIn Q (X ⊓ centralizer {x})) :
    Q ≤ (layer ↥X).map X.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hlayer : CFSG.Open.lBalancePLayer 2 X = (layer ↥X).map X.subtype := by
    rw [CFSG.ComponentClassification.LBalance.Asm.lBalancePLayer_eq_map,
      ← CFSG.ComponentClassification.HarrisLit.L35.twoLayer_eq_pLayer,
      CFSG.ComponentClassification.HarrisLit.twoLayer_eq_layer hO]
  have hQPL : Q ≤ CFSG.Open.lBalancePLayer 2 (X ⊓ centralizer ({x} : Set G)) := by
    have hQP : IsPComponent 2 (Q.subgroupOf (X ⊓ centralizer ({x} : Set G))) :=
      (ComponentClassification.HarrisLit.isTwoComponentIn_iff hQ.1).mp hQ
    rw [CFSG.ComponentClassification.LBalance.Asm.lBalancePLayer_eq_map]
    calc Q = (Q.subgroupOf (X ⊓ centralizer ({x} : Set G))).map
          (X ⊓ centralizer ({x} : Set G)).subtype :=
          (map_subgroupOf_eq_of_le hQ.1).symm
      _ ≤ _ := map_mono (le_sSup (s := {M | IsPComponent 2 M}) hQP)
  have hle := CFSG.StandardType.lBalancePLayer_inf_centralizer_le_of_input hL Nat.prime_two hX
    hxX hx2
  rw [hlayer] at hle
  exact hQPL.trans hle

theorem exists_component_ge {G : Type} [Group G] [Finite G] {x v : G} (hv2 : orderOf v = 2)
    (hvx : v ∈ centralizer {x}) (hO : pPrimeCore 2 ↥(centralizer ({x} : Set G)) = ⊥)
    (hvE : v ∈ (layer ↥(centralizer ({x} : Set G))).map (centralizer ({x} : Set G)).subtype)
    {Q : Subgroup G}
    (hQ : ComponentClassification.HarrisLit.IsTwoComponentIn Q
      (centralizer {x} ⊓ centralizer {v})) :
    ∃ K : Subgroup G, IsComponentIn K (centralizer {x}) ∧ Q ≤ K := by
  obtain ⟨K₀, hK₀, -, hcases⟩ :=
    ComponentClassification.HarrisLit.T23.exists_pumpup (w := x) (v := v) hv2 hvx hQ
  have hKc : CFSG.IsComponent K₀ :=
    (ComponentClassification.HarrisLit.isTwoComponent_iff_isComponent hO K₀).mp hK₀
  refine ⟨K₀.map (centralizer ({x} : Set G)).subtype, isComponentIn_map_subtype hKc, ?_⟩
  rcases hcases with ⟨-, hQK⟩ | ⟨hne, -⟩
  ·
    calc Q = (Q.subgroupOf (centralizer ({x} : Set G))).map
          (centralizer ({x} : Set G)).subtype :=
          (map_subgroupOf_eq_of_le (hQ.1.trans inf_le_left)).symm
      _ ≤ K₀.map (centralizer ({x} : Set G)).subtype :=
          map_mono (hQK.1.trans inf_le_left)
  ·
    exfalso
    obtain ⟨a, haL, haeq⟩ := Subgroup.mem_map.mp hvE
    have hv'L : (⟨v, hvx⟩ : ↥(centralizer ({x} : Set G))) ∈
        layer ↥(centralizer ({x} : Set G)) := by
      have : a = (⟨v, hvx⟩ : ↥(centralizer ({x} : Set G))) := Subtype.ext haeq
      rwa [this] at haL
    have hnorm : (⟨v, hvx⟩ : ↥(centralizer ({x} : Set G))) ∈
        Subgroup.normalizer (K₀ : Set ↥(centralizer ({x} : Set G))) :=
      CFSG.LocalCores.layer_le_normalizer hKc hv'L
    exact hne (ComponentClassification.HarrisLit.L35.map_conj_eq_of_mem_normalizer hnorm)

end CFSG.OddStandard.HigherRank.F3
