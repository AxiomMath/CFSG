module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi24ThreeChecks
public import Certificates.Certificate9417
public import Certificates.Certificate9500
public import Certificates.Certificate9501
import CFSG.LocalAnalysis.AGLEmbedding.ChevTwoKill
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Seed.McL
import CFSG.Sporadic.Bridge.SuzSurj
import CFSG.Sporadic.Bridge.Fi22Surj
import CFSG.Sporadic.Bridge.Fi24Surj
import all CFSG.Blueprint.NativeSporadic
public import CFSG.LocalAnalysis.AGLEmbedding.CoverWeakGenData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoverPointSound

public section

namespace CFSG.AGLEmbedding.KFactProofs.ThreeWeak

open CFSG.Open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native

theorem weakCore_rank_of_coverWeakGen {K X : Type} [Group K] [Finite K] [Group X]
    (hq : Open.IsQuasisimple K) (hZ : Subgroup.center K ≠ ⊥)
    (hZp : IsPGroup 3 (Subgroup.center K)) (hZc : IsCyclic (Subgroup.center K))
    (e : K ⧸ Subgroup.center K ≃* X) (h : CoverWeakGen X 3) (T : Sylow 3 K) :
    GLBWeakCore 3 (T : Subgroup K) = ⊤ ∧ 3 ≤ Open.pRank 3 (⊤ : Subgroup K) := by
  have hperf : Group.IsPerfect K := ⟨hq.1⟩
  let π : K →* X := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center K := by
    ext x
    simp [π]
  have hw : GLBWeakCore 3 (T : Subgroup K) = ⊤ := h K π hπ hker hperf hZ hZp hZc T
  have : Nontrivial K := by
    have hnt : Nontrivial (Subgroup.center K) := (Subgroup.nontrivial_iff_ne_bot _).2 hZ
    obtain ⟨x, hx⟩ := exists_ne (1 : Subgroup.center K)
    exact ⟨⟨x, 1, fun h1 => hx (Subtype.ext h1)⟩⟩
  exact ⟨hw, (three_le_pRank_of_weakCore_eq_top Nat.prime_three hw).trans
    (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 Nat.prime_three le_top)⟩

section McL

open CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.McLThree

theorem coverWeakGen_McL [Finite (NativeSporadic.Carrier .McL)] :
    CoverWeakGen (NativeSporadic.Carrier .McL) 3 :=
  coverWeakGen_of_coverPointDatum (X := NativeSporadic.McL) (by norm_num)
    (coverPointDatum_of_check (spec3 21) (D := cpSpec) Nat.prime_three
      Certificates.certificate9417.2.1 Certificates.certificate9417.2.2)

theorem weakCore_McL
    {K : Type} [Group K] [Finite K] (hq : Open.IsQuasisimple K)
    (hZ : Subgroup.center K ≠ ⊥) (hZp : IsPGroup 3 (Subgroup.center K))
    (hZc : IsCyclic (Subgroup.center K))
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .McL).Group) (T : Sylow 3 K) :
    GLBWeakCore 3 (T : Subgroup K) = ⊤ ∧ 3 ≤ Open.pRank 3 (⊤ : Subgroup K) := by
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hq.2
  have : IsSimpleGroup TauCeti.SporadicName.McL.Group := e.symm.isSimpleGroup
  obtain ⟨b⟩ := CFSG.QuasithinUnique.SQTK.nonempty_mulEquiv_carrier_McL
  have : Finite (NativeSporadic.Carrier .McL) :=
    Finite.of_equiv _ (e.trans b).toEquiv
  exact weakCore_rank_of_coverWeakGen hq hZ hZp hZc (e.trans b) coverWeakGen_McL T

end McL

section Suz

open CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.SuzThree

theorem coverWeakGen_Suz [Finite (NativeSporadic.Carrier .Suz)] :
    CoverWeakGen (NativeSporadic.Carrier .Suz) 3 :=
  coverWeakGen_of_coverPointDatum (X := NativeSporadic.Suz) (by norm_num)
    (coverPointDatum_of_check (spec3 64) (D := cpSpec) Nat.prime_three
      Certificates.certificate9500.2.1 Certificates.certificate9500.2.2)

theorem weakCore_Suz
    {K : Type} [Group K]
    [Finite K] (hq : Open.IsQuasisimple K) (hZ : Subgroup.center K ≠ ⊥)
    (hZp : IsPGroup 3 (Subgroup.center K)) (hZc : IsCyclic (Subgroup.center K))
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .Suz).Group) (T : Sylow 3 K) :
    GLBWeakCore 3 (T : Subgroup K) = ⊤ ∧ 3 ≤ Open.pRank 3 (⊤ : Subgroup K) := by
  obtain ⟨b⟩ : Nonempty (NativeSporadic.Carrier .Suz ≃*
      (TauCeti.CFSGIndex.sporadic .Suz).Group) := CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv
  have : Finite (NativeSporadic.Carrier .Suz) :=
    Finite.of_equiv _ (e.trans b.symm).toEquiv
  exact weakCore_rank_of_coverWeakGen hq hZ hZp hZc (e.trans b.symm) coverWeakGen_Suz T

end Suz

section Fi22

open CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.Fi22Three

theorem coverWeakGen_Fi22 [Finite (NativeSporadic.Carrier .Fi22)] :
    CoverWeakGen (NativeSporadic.Carrier .Fi22) 3 :=
  coverWeakGen_of_coverPointDatum (X := NativeSporadic.Fi22) (by norm_num)
    (coverPointDatum_of_check (spec3 77) (D := cpSpec) Nat.prime_three
      Certificates.certificate9501.2.1 Certificates.certificate9501.2.2)

theorem weakCore_Fi22
    {K : Type} [Group K]
    [Finite K] (hq : Open.IsQuasisimple K) (hZ : Subgroup.center K ≠ ⊥)
    (hZp : IsPGroup 3 (Subgroup.center K)) (hZc : IsCyclic (Subgroup.center K))
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .Fi22).Group) (T : Sylow 3 K) :
    GLBWeakCore 3 (T : Subgroup K) = ⊤ ∧ 3 ≤ Open.pRank 3 (⊤ : Subgroup K) := by
  obtain ⟨b⟩ : Nonempty (NativeSporadic.Carrier .Fi22 ≃*
      (TauCeti.CFSGIndex.sporadic .Fi22).Group) := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  have : Finite (NativeSporadic.Carrier .Fi22) :=
    Finite.of_equiv _ (e.trans b.symm).toEquiv
  exact weakCore_rank_of_coverWeakGen hq hZ hZp hZc (e.trans b.symm) coverWeakGen_Fi22 T

end Fi22

section Fi24

open CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.Fi24Three

theorem coverWeakGen_Fi24 [Finite (NativeSporadic.Carrier .Fi24Prime)] :
    CoverWeakGen (NativeSporadic.Carrier .Fi24Prime) 3 :=
  coverWeakGen_of_coverPointDatum (X := NativeSporadic.Fi24prime) (by norm_num)
    (coverPointDatum_of_check (CFSG.RankThree.Asc83Table.matOpsSpec 3 781) (D := cpSpec)
      Nat.prime_three cpCheck_Fi24 noFun_Fi24)

theorem weakCore_Fi24
    {K : Type} [Group K] [Finite K]
    (hq : Open.IsQuasisimple K) (hZ : Subgroup.center K ≠ ⊥)
    (hZp : IsPGroup 3 (Subgroup.center K)) (hZc : IsCyclic (Subgroup.center K))
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group)
    (T : Sylow 3 K) :
    GLBWeakCore 3 (T : Subgroup K) = ⊤ ∧ 3 ≤ Open.pRank 3 (⊤ : Subgroup K) := by
  obtain ⟨b⟩ : Nonempty (NativeSporadic.Carrier .Fi24Prime ≃*
      (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group) :=
    CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
  have : Finite (NativeSporadic.Carrier .Fi24Prime) :=
    Finite.of_equiv _ (e.trans b.symm).toEquiv
  exact weakCore_rank_of_coverWeakGen hq hZ hZp hZc (e.trans b.symm) coverWeakGen_Fi24 T

end Fi24

end CFSG.AGLEmbedding.KFactProofs.ThreeWeak
