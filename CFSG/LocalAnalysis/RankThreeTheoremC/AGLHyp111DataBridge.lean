module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

@[expose] def Hyp111B3 (p : ℕ) (H Q : Subgroup G)
    (J : Subgroup (H ⧸ primeComplementCore (G := H) p)) : Prop :=
  ∀ S : Subgroup G, IsPGroup 2 S → S ≤ H → Q ≤ Subgroup.normalizer (S : Set G) →
    S ≤ d1PlusCore p H J

structure Hyp111NineThree (p : ℕ) (M H : Subgroup G)
    (J : Subgroup (H ⧸ primeComplementCore (G := H) p)) : Prop where
  normal : J.Normal
  plusCore_le : d1PlusCore p H J ≤ M
  factor : ∀ x ∈ H, ∃ m ∈ H ⊓ M, ∃ k : H, QuotientGroup.mk' _ k ∈ J ∧ x = m * k

theorem le_normalizer_d1PlusCore {p : ℕ} {H : Subgroup G}
    {J : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hJ : J.Normal) :
    H ≤ Subgroup.normalizer (d1PlusCore p H J : Set G) := by
  haveI := hJ
  have hC : (Subgroup.centralizer (J : Set (H ⧸ primeComplementCore (G := H) p))).Normal :=
    inferInstance
  have hN : ((Subgroup.centralizer (J : Set (H ⧸ primeComplementCore (G := H) p))).comap
      (QuotientGroup.mk' (primeComplementCore (G := H) p))).Normal := hC.comap _
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp ?_
  have e : (((Subgroup.centralizer (J : Set (H ⧸ primeComplementCore (G := H) p))).comap
      (QuotientGroup.mk' (primeComplementCore (G := H) p))).map H.subtype).subgroupOf H =
      (Subgroup.centralizer (J : Set (H ⧸ primeComplementCore (G := H) p))).comap
        (QuotientGroup.mk' (primeComplementCore (G := H) p)) :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  rw [e]
  exact hN

theorem twoCore_inf_eq {p : ℕ} {M H Q : Subgroup G}
    {J : Subgroup (H ⧸ primeComplementCore (G := H) p)} (h93 : Hyp111NineThree p M H J)
    (hb3 : Hyp111B3 p H Q J) (hQH : Q ≤ H) (hQM : Q ≤ M) (hHM : pCoreOf 2 H ≤ M) :
    pCoreOf 2 (H ⊓ M) = pCoreOf 2 H := by
  set X := d1PlusCore p H J with hXdef
  have hXH : X ≤ H := Subgroup.map_subtype_le _
  have hXHM : X ≤ H ⊓ M := le_inf hXH h93.plusCore_le
  apply le_antisymm
  · have hSX : pCoreOf 2 (H ⊓ M) ≤ X :=
      hb3 _ (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)
        ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _).trans inf_le_left)
        ((le_inf hQH hQM).trans (localGroup_le_normalizer_pCoreOf 2 _))
    have hS : pCoreOf 2 (H ⊓ M) ≤ pCoreOf 2 X :=
      normal_pGroup_le_pCoreOf 2 _ X hSX
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hSX).mpr
          (hXHM.trans (localGroup_le_normalizer_pCoreOf 2 _)))
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)
    have hOX : pCoreOf 2 X ≤ H := (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 X).trans hXH
    refine hS.trans (normal_pGroup_le_pCoreOf 2 _ H hOX ?_
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _))
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hOX).mpr ?_
    exact (le_normalizer_d1PlusCore h93.normal).trans
      (CFSG.PreuniquenessRankFour.Helpers.normalizer_le_normalizer_characteristic (pCore 2 X)
        (CFSG.PreuniquenessRankFour.Helpers.pCore_characteristic (G := X) 2))
  · have hle : pCoreOf 2 H ≤ H ⊓ M :=
      le_inf (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H) hHM
    exact normal_pGroup_le_pCoreOf 2 _ _ hle
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr
        (inf_le_left.trans (localGroup_le_normalizer_pCoreOf 2 H)))
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _)

theorem map_primeComplementCore_eq (p : ℕ) (H : Subgroup G) :
    (primeComplementCore (G := H) p).map H.subtype = GLBPrimeCore p H := by
  rw [glbPrimeCore_eq_primeComplementCoreOf]
  rfl

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
