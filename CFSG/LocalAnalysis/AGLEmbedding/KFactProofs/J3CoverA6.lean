module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPKFacts
public import CFSG.Sporadic.Bridge.TwoGen
public meta import Certificates.Data.CFSGNative.Bridge.SurjA
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3CoverGroup
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3CoverOver
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3SylowPrim
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3SylowGroup
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3Sylow
public import Certificates.Certificate9465
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.AGLEmbedding

open KFactProofs.J3Sylow KFactProofs.J3Cover CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen CFSG.Sporadic.Bridge.TwoGen.Native

theorem isSolvable_normalizer_of_facts {J : Type} [Group J] [Finite J] {T : Subgroup J}
    (hT : IsPGroup 3 T) (hF : J3SylowFacts J T) :
    Group.IsSolvable (Subgroup.normalizer (T : Set J)) := by
  set N := Subgroup.normalizer (T : Set J) with hN
  have hTN : T ≤ N := Subgroup.le_normalizer
  have hnorm : (T.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTN).2 le_rfl
  have h3 : IsPGroup 3 (T.subgroupOf N) :=
    hT.of_surjective (Subgroup.subgroupOfEquivOfLe hTN).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hTN).symm.surjective
  have h2 : IsPGroup 2 (N ⧸ T.subgroupOf N) := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨e, he⟩ := hF.two_top y.1 y.2
    refine ⟨e, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.2 he
  have hnil3 : Group.IsNilpotent (T.subgroupOf N) := h3.isNilpotent
  have hnil2 : Group.IsNilpotent (N ⧸ T.subgroupOf N) := h2.isNilpotent
  have : Group.IsSolvable (T.subgroupOf N) := inferInstance
  have : Group.IsSolvable (N ⧸ T.subgroupOf N) := inferInstance
  exact Group.isSolvable_of_subgroup_quotient (T.subgroupOf N)

theorem cover_check : ∀ (J : Type) [Group J] [Finite J],
    Nonempty (J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) → IsSimpleGroup J →
      Nat.card J = 50232960 → (∃ x d₁ d₂ g u : J, CoverData x d₁ d₂ g u) ∧
        ∀ T : Sylow 3 J, ∀ K : Subgroup J, (T : Subgroup J) ≤ K →
          K ≤ Subgroup.normalizer ((T : Subgroup J) : Set J) ∨ K = ⊤ :=
  Certificates.certificate9465

theorem j3CoverFacts
    (J : Type) [Group J] [Finite J]
    (hJ : Nonempty (J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group)) :
    (∃ x d₁ d₂ g u : J, CoverData x d₁ d₂ g u) ∧
      ∀ T : Sylow 3 J, ∀ K : Subgroup J, (T : Subgroup J) ≤ K →
        K ≤ Subgroup.normalizer ((T : Subgroup J) : Set J) ∨ K = ⊤ := by
  obtain ⟨eJ⟩ := hJ
  obtain ⟨b⟩ : Nonempty (Blueprint.NativeSporadic.Carrier .J3 ≃*
      (TauCeti.CFSGIndex.sporadic .J3).Group) := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  let f := eJ.trans b.symm
  have := CFSG.Sporadic.J3.isSimpleGroup_J3
  have hsimple : IsSimpleGroup J := MulEquiv.isSimpleGroup (H := Blueprint.NativeSporadic.J3) f
  have hJcard : Nat.card J = 50232960 := by
    rw [Nat.card_congr f.toEquiv]; exact CFSG.Sporadic.J3.card_J3
  exact cover_check J ⟨eJ⟩ hsimple hJcard

theorem kFactJ3CoverA6 :
    KFactJ3CoverA6 := by
  intro X _ _ hq he z hz hzo A L _ _ f _
  obtain ⟨hperf, -⟩ := hq
  have hπ : Function.Surjective (QuotientGroup.mk' (Subgroup.center X)) :=
    QuotientGroup.mk'_surjective _
  have hker : (QuotientGroup.mk' (Subgroup.center X)).ker = Subgroup.center X :=
    QuotientGroup.ker_mk' _
  obtain ⟨⟨x, d₁, d₂, g, u, hd⟩, hover⟩ := j3CoverFacts (X ⧸ Subgroup.center X) he
  obtain ⟨U, B, hUc, hU3, hUcard, hzU, hBU, ⟨t, htB, hto, htU⟩, hDB⟩ :=
    exists_cover_subgroups (QuotientGroup.mk' (Subgroup.center X)) hπ hker.le hd
      (by rw [hker]; exact hz) hzo
  refine ⟨U, B, ⟨hUc, hU3⟩, hUcard, hzU, hBU, ⟨t, htB, hto, htU⟩, ?_⟩
  rintro Y hBY ⟨S, hSY⟩
  have hDY : Subgroup.closure ({d₁, d₂} : Set (X ⧸ Subgroup.center X)) ≤
      Y.map (QuotientGroup.mk' (Subgroup.center X)) := hDB.trans (Subgroup.map_mono hBY)
  set T := S.mapSurjective hπ with hT
  have hTY : (T : Subgroup (X ⧸ Subgroup.center X)) ≤
      Y.map (QuotientGroup.mk' (Subgroup.center X)) := by
    rw [hT, Sylow.coe_mapSurjective]
    exact Subgroup.map_mono hSY
  rcases hover T _ hTY with hN | htop
  · exfalso
    have hsolv := isSolvable_normalizer_of_facts T.isPGroup' (kFactJ3Sylow _ he T)
    exact not_isSolvable_of_perfect (commutator_self_eq hd.rel₁ hd.rel₂ hd.rel₃ hd.rel₄)
      ⟨u, hd.u_mem, hd.u_ne_one⟩ (hDY.trans hN) hsolv
  · exact eq_top_of_map_eq_top hker.le hperf htop

end CFSG.AGLEmbedding
