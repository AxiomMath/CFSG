module

public import CFSG.LocalAnalysis.EvenBN.GMSK.QuasiCentreSporadicBase
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatSporadicBenderLarge
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModels
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporCaseB
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdFamilies
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.EvenBN.GMSK.Selector
public import CFSG.Milestones.CT_catalog_nonabelian_type_partition
public import CFSG.Monster.AxisCount.HSIdentBaby
public import CFSG.Monster.AxisCount.HSIdentRec0
public import CFSG.Monster.AxisCount.HSIdentRec1
public import CFSG.Monster.AxisCount.HSIdentRec2
public import CFSG.Monster.AxisCount.HSIdentRec3
public import CFSG.Monster.AxisCount.HSIdentRec4
public import CFSG.Monster.AxisCount.HSIdentRec5
public import CFSG.Monster.AxisCount.HSIdentRec6
public import CFSG.Monster.AxisCount.HSIdentRec7
public import CFSG.Monster.AxisCount.HSIdentSmall
public import CFSG.Monster.B.TwoA.Base.FourNorm
public import CFSG.Sporadic.Bridge.BOrder
public import CFSG.Sporadic.Bridge.BSurjInputs
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.HeldB.OuterFixed
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.ON.SimpleBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import CFSG.Sporadic.Th.CertificateBase
public import CFSG.Sporadic.Th.CertificateBase1
public import CFSG.Sporadic.ThSchreier.KernelAutBase
public import CFSG.Sporadic.ThSchreier.KernelAutBase1
public import CFSG.Sporadic.ThSchreier.ThSchreierCase
public import Certificates.Certificate10027
public import Certificates.Certificate10095
public import Certificates.Certificate10095Base
public import Certificates.Certificate10100
public import Certificates.Certificate10101
public import Certificates.Certificate10102
public import Certificates.Certificate10104
public import Certificates.Certificate10107
public import Certificates.Certificate10108
public import Certificates.Certificate10110
public import Certificates.Certificate10111
public import Certificates.Certificate16018
public import Certificates.Certificate2323
public import Certificates.Certificate3085Base
public import Certificates.Certificate6006
public import Certificates.Certificate9201

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.RestrictedStd.Spor (CompsSatisfy
  isoInvariant_card_quotient_center)
open SporadicBender (ne_of_check_U3 not_mem_singleton_of_ne not_mem_pair_of_ne
  not_two_part_forty_one)

namespace QSporadic

local notation "innerAut" => CFSG.ComponentClassification.OuterAutomorphisms.inner

open CFSG.ComponentClassification.RestrictedStd.Spor (hnLocalComponentsInput_holds
  compsSatisfy_perm_ten) in
theorem hn_qFree :
    QFree .HN := by
  have hin : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Nonempty (G ≃* NativeSporadic.Carrier .HN) → ∀ t : G, orderOf t = 2 →
        CompsSatisfy (centralizer ({t} : Set G))
          fun Y _ => Nat.card (Y ⧸ center Y) ∈ ({44352000} : Set ℕ) :=
    fun G _ _ _ ⟨e⟩ t ht B hB =>
      Set.mem_singleton_iff.2 (hnLocalComponentsInput_holds G e t ht B hB)
  have hout : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Nonempty (G ≃* NativeSporadic.Carrier .HN) → ∀ β : MulAut G, orderOf β = 2 →
        β ∉ innerAut G → CompsSatisfy (CFSG.Sporadic.Schreier.fixSub β)
          fun Y _ => Nat.card (Y ⧸ center Y) ∈ ({1814400} : Set ℕ) := by
    intro G _ _ _ ⟨e⟩ β hβ2 hβ
    obtain ⟨eS⟩ := CFSG.Sporadic.HNOddCore.hn_outer_involution_fixSub e β hβ2 hβ
    exact CompsSatisfy.of_mulEquiv (isoInvariant_card_quotient_center _) eS
      compsSatisfy_perm_ten
  refine qFree_of_card_quotient_center (fun _ _ _ _ hX => ⟨?_, ?_⟩) hin hout
  · exact not_mem_singleton_of_ne
      (ne_of_check_U3 hX (e := 9) (h := 86625) (by norm_num) (by decide) (by decide))
  · exact not_mem_singleton_of_ne
      (ne_of_check_U3 hX (e := 7) (h := 14175) (by norm_num) (by decide) (by decide))

open CFSG.ComponentClassification.RestrictedStd.Spor (compsSatisfy_of_charP) in
theorem th_qFree :
    QFree .Th := by
  have hinner : ∀ β : MulAut (NativeSporadic.Carrier .Th),
      β ∈ innerAut (NativeSporadic.Carrier .Th) := fun β => by
    have h : innerAut (NativeSporadic.Carrier .Th) = ⊤ := CFSG.Sporadic.ThSchreier.inner_Th
    rw [h]
    trivial
  have hin : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Nonempty (G ≃* NativeSporadic.Carrier .Th) → ∀ t : G, orderOf t = 2 →
        CompsSatisfy (centralizer ({t} : Set G)) fun _ _ => False :=
    fun G _ _ _ hG t ht => compsSatisfy_of_charP
      ((CFSG.Sporadic.ThSchreier.ctuc_Th_inner_involution_centralizers_characteristic_two.2.2
        G hG).1 t ht).1 _
  exact qFree_of_comps (Qi := fun _ _ => False) (Qo := fun _ _ => False)
    (fun _ _ _ _ _ h => h) (fun _ _ _ _ _ h => h) (fun _ _ _ _ _ => ⟨id, id⟩) hin
    (Sporadic.outer_comps_of_forall_inner hinner _)

theorem b_qFree :
    QFree .B := by
  have hinner : ∀ β : MulAut (NativeSporadic.Carrier .B),
      β ∈ innerAut (NativeSporadic.Carrier .B) :=
    CFSG.ComponentClassification.BMCase.inner_of_mulEquiv_pinnedB NativeSporadic.B
      ⟨MulEquiv.refl NativeSporadic.B⟩
  have hin : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Nonempty (G ≃* NativeSporadic.Carrier .B) → ∀ t : G, orderOf t = 2 →
        CompsSatisfy (centralizer ({t} : Set G)) fun Y _ => Nat.card (Y ⧸ center Y) ∈
          ({76532479683774853939200, 3311126603366400} : Set ℕ) := by
    intro G _ _ _ ⟨e⟩ t ht K hK
    obtain ⟨-, hiso, -⟩ :=
      CFSG.Monster.B.CTIB.involution_local_components_simple_quotient_divisible_by_seventeen
        ⟨e⟩ t ht K hK
    rcases hiso with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · left
      rw [Nat.card_congr φ.toEquiv, CFSG.LieType.Chevalley.C2E6Std.card_stdGroup]
    · right
      obtain ⟨ψ⟩ := CFSG.Monster.B.E6.StdF4Radical.nonempty_groupJ_mulEquiv_F4
      rw [Set.mem_singleton_iff, Nat.card_congr φ.toEquiv, ← Nat.card_congr ψ.toEquiv,
        CFSG.Monster.B.E6.FieldInvF4.card_groupJ]
  refine qFree_of_card_quotient_center (No := ∅)
    (fun _ _ _ _ hX => ⟨?_, Set.notMem_empty _⟩) hin
    (Sporadic.outer_comps_of_forall_inner hinner _)
  exact not_mem_pair_of_ne
    (ne_of_check_U3 hX (e := 36) (h := 1113694156575) (by norm_num) (by decide) (by decide))
    (ne_of_check_U3 hX (e := 24) (h := 197358525) (by norm_num) (by decide) (by decide))

theorem m_qFree
    :
    QFree .M := by
  intro D _ _ hD hs n α J d
  have hα : α ∈ innerAut D :=
    CFSG.ComponentClassification.CatLeafProof.monsterInnerInput D hD hs α
  refine false_of_inner_comps hD d hα
    (isoInvariant_card_quotient_center {N | 2 ^ 41 ∣ N ∧ ¬ 2 ^ 42 ∣ N}) ?_
    fun t ht B hB =>
      CFSG.ComponentClassification.CatLeafProof.monsterLocalComponentsInput D hD hs t ht B hB
  exact not_two_part_forty_one Nat.card_pos.ne' (factorization_two_card_of_lieModel_PSU3 d.model)
    (by omega)

end QSporadic

end CFSG.LocalAnalysis.EvenBN.GMSK
