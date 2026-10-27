module

public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCatalog
public import CFSG.RankThree.PartOne.S12.InputsSec15
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.LinTwo
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsIdent
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableBorel
import CFSG.LocalAnalysis.UniquenessCase.UC6K35Red2
import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
import CFSG.RankThree.PartOne.CTP.OutEmbed
import CFSG.Quasithin.H13.QRCEvenUnitarySuzukiSL2
import CFSG.HardMathSupport.Malle.OvergroupTransport.Transport
import CFSG.RankThree.PartOne.KE.A1Group
import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.RankOneA1
import CFSG.Dihedral.Glauberman.DicksonMaxDown
import CFSG.LocalAnalysis.SectionRank.CyclicQuotientRank
import CFSG.LocalAnalysis.UniquenessCase.UCKInputs
import CFSG.Quasithin.EmptyFaithful.S146zYOutComm

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFTwo

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Family

variable {p n : ℕ} [Fact p.Prime] {X : Type} [Group X] [Finite X]

open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (exists_sylow_glbCore_ne_top_of_isStronglyPEmbedded
    normalizer_subgroupOf_le_of_isStronglyPEmbedded isSolvable_of_isCoatom_normalizer)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive
  (isCoatom_normalizer_of_mulEquiv_psl2GF)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (normalizer_eq_sup_cyclic_of_equiv)
open CFSG.RankThree.PartOne.Sec1511 (spe_fstar)
open CFSG.LocalAnalysis.UniquenessCase.UCK (not_le_of_isStronglyPEmbedded)

theorem outer_comm_of_mulEquiv_psl2GF {K : Type} [Group K]
    (e : K ≃* CFSG.AGLEmbedding.PSL2GF p n) :
    ∀ x y : Outer K, x * y = y * x :=
  CFSG.Quasithin.S146zY.outer_comm_of_mulEquiv e.symm
    (CFSG.LocalAnalysis.ComponentInitial.OuterDerived.outer_psl2_mul_comm (GaloisField p n))

theorem isSolvable_of_mulEquiv_psl2GF (hp5 : 5 ≤ p) (hn : 1 ≤ n)
    (hO : CFSG.pPrimeCore p X = ⊥) {N : Subgroup X}
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N)
    (e : ↥(CFSG.generalizedFitting X) ≃* CFSG.AGLEmbedding.PSL2GF p n) :
    Group.IsSolvable ↥N := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hKs, -, hKn, hKC⟩ :=
    spe_fstar Fact.out hO hN
  let K : Subgroup X := CFSG.generalizedFitting X
  haveI : K.Normal := hKn
  haveI : IsSimpleGroup ↥K := hKs
  have hK1 : K ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot K).1 inferInstance
  obtain ⟨P, hPN, hPK, T, hT, -⟩ :=
    exists_sylow_glbCore_ne_top_of_isStronglyPEmbedded
      (K := K) hO hK1 hN
  have hle : Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) ≤ N.subgroupOf K := by
    rw [hT]
    exact normalizer_subgroupOf_le_of_isStronglyPEmbedded
      hN hPK (P.isPGroup'.to_le inf_le_left) (inf_le_left.trans hPN) inf_le_right
  have hne : N.subgroupOf K ≠ ⊤ := fun h =>
    not_le_of_isStronglyPEmbedded hN P hPN hPK T hT
      (Subgroup.subgroupOf_eq_top.mp h)
  obtain ⟨J, hJ, hJe⟩ :=
    normalizer_eq_sup_cyclic_of_equiv
      hp2 hn e T
  have hmax : IsCoatom (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)) :=
    isCoatom_normalizer_of_mulEquiv_psl2GF
      hp2 hn e T
  have hout : Group.IsSolvable (Outer ↥K) :=
    Group.isSolvable_of_comm (outer_comm_of_mulEquiv_psl2GF e)
  have hTn : (T.subgroupOf (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K))).Normal :=
    Subgroup.normal_in_normalizer
  letI : IsCyclic J := hJ
  have hsol : Group.IsSolvable (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)) :=
    CFSG.Quasithin.H13.QRC.isSolvable_of_le_sup_cyclic
      (B := Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K))
      (U := (T : Subgroup ↥K)) (T := J) Subgroup.le_normalizer
      (by rw [hJe]; exact le_sup_right) hTn T.isPGroup' hJe.symm
  exact isSolvable_of_isCoatom_normalizer
    hKC hout hmax hsol hle hne

theorem commutator_le_inf_of_mulEquiv_psl2GF (hO : CFSG.pPrimeCore p X = ⊥) {N : Subgroup X}
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N)
    (e : ↥(CFSG.generalizedFitting X) ≃* CFSG.AGLEmbedding.PSL2GF p n) :
    ⁅N, N⁆ ≤ N ⊓ CFSG.generalizedFitting X := by
  obtain ⟨-, -, hKn, hKC⟩ :=
    spe_fstar Fact.out hO hN
  let K : Subgroup X := CFSG.generalizedFitting X
  haveI : K.Normal := hKn
  have hOut : ∀ x y : Outer ↥K, x * y = y * x := outer_comm_of_mulEquiv_psl2GF e
  let φ : X ⧸ K →* Outer ↥K :=
    QuotientGroup.lift K (CFSG.RankThree.PartOne.CTP.outerHom K)
      (fun _ hg => (MonoidHom.mem_ker (f := CFSG.RankThree.PartOne.CTP.outerHom K)).mp
        ((CFSG.RankThree.PartOne.CTP.ker_outerHom K hKC).symm ▸ hg))
  have hφ : Function.Injective φ := CFSG.RankThree.PartOne.CTP.quotientOuterHom_injective K hKC
  have hcomm : ∀ a b : X ⧸ K, a * b = b * a := fun a b =>
    hφ (by rw [map_mul, map_mul]; exact hOut _ _)
  have hderK : commutator X ≤ K := by
    have h := CFSG.RankThree.PartOne.KE.commutator_le_ker_of_mul_comm (QuotientGroup.mk' K) hcomm
    rwa [QuotientGroup.ker_mk'] at h
  have hNN : ⁅N, N⁆ ≤ N := Subgroup.commutator_le_self N
  have hNX : ⁅N, N⁆ ≤ commutator X := by
    simpa [commutator] using Subgroup.commutator_mono (le_top : N ≤ ⊤) (le_top : N ≤ ⊤)
  exact le_inf hNN (hNX.trans hderK)

theorem pRank_three_le_one_inf_of_mulEquiv_psl2GF (hp5 : 5 ≤ p) (hn : 1 ≤ n)
    (hO : CFSG.pPrimeCore p X = ⊥) {N : Subgroup X}
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N)
    (e : ↥(CFSG.generalizedFitting X) ≃* CFSG.AGLEmbedding.PSL2GF p n) :
    CFSG.Open.pRank 3 (N ⊓ CFSG.generalizedFitting X) ≤ 1 := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  obtain ⟨hKs, -, hKn, -⟩ :=
    spe_fstar Fact.out hO hN
  let K : Subgroup X := CFSG.generalizedFitting X
  haveI : K.Normal := hKn
  haveI : IsSimpleGroup ↥K := hKs
  have hK1 : K ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot K).1 inferInstance
  obtain ⟨P, hPN, hPK, T, hT, -⟩ :=
    exists_sylow_glbCore_ne_top_of_isStronglyPEmbedded
      (K := K) hO hK1 hN
  have hle : Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) ≤ N.subgroupOf K := by
    rw [hT]
    exact normalizer_subgroupOf_le_of_isStronglyPEmbedded
      hN hPK (P.isPGroup'.to_le inf_le_left) (inf_le_left.trans hPN) inf_le_right
  have hne : N.subgroupOf K ≠ ⊤ := fun h =>
    not_le_of_isStronglyPEmbedded hN P hPN hPK T hT
      (Subgroup.subgroupOf_eq_top.mp h)
  have hmax : IsCoatom (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)) :=
    isCoatom_normalizer_of_mulEquiv_psl2GF
      hp2 hn e T
  have hNK : N.subgroupOf K = Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) :=
    (CFSG.Glauberman.Dickson.MaxDown.eq_of_isCoatom_le hmax hle hne).symm
  obtain ⟨J, hJ, hJe⟩ :=
    normalizer_eq_sup_cyclic_of_equiv
      hp2 hn e T
  have hrank : CFSG.Open.pRank 3
      (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)) ≤ 1 :=
    CFSG.SectionRank.pRank_le_one_of_isPGroup_sup_cyclic Nat.prime_three hp3 T.isPGroup' hJ
      hJe.symm le_rfl
  have hB : (N ⊓ K).subgroupOf K = N.subgroupOf K := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
  calc CFSG.Open.pRank 3 (N ⊓ K)
      = CFSG.Open.pRank 3 ((N ⊓ K).subgroupOf K) :=
        (CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_subgroupOf 3 inf_le_right).symm
    _ = CFSG.Open.pRank 3 (N.subgroupOf K) := by rw [hB]
    _ = CFSG.Open.pRank 3 (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)) := by rw [hNK]
    _ ≤ 1 := hrank

theorem pRank_three_commutator_le_one_of_mulEquiv_psl2GF (hp5 : 5 ≤ p) (hn : 1 ≤ n)
    (hO : CFSG.pPrimeCore p X = ⊥) {N : Subgroup X}
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N)
    (e : ↥(CFSG.generalizedFitting X) ≃* CFSG.AGLEmbedding.PSL2GF p n) :
    CFSG.Open.pRank 3 ⁅N, N⁆ ≤ 1 := by
  have hder : ⁅N, N⁆ ≤ N ⊓ CFSG.generalizedFitting X :=
    commutator_le_inf_of_mulEquiv_psl2GF hO hN e
  have hinf : CFSG.Open.pRank 3 (N ⊓ CFSG.generalizedFitting X) ≤ 1 :=
    pRank_three_le_one_inf_of_mulEquiv_psl2GF hp5 hn hO hN e
  exact (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) hder).trans hinf

theorem isSolvable_and_pRank_three_le_one_of_psl2GF {p n : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hn : 1 ≤ n) {X : Type} [Group X] [Finite X] (hO : CFSG.pPrimeCore p X = ⊥)
    {N : Subgroup X} (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N)
    (e : ↥(CFSG.generalizedFitting X) ≃* CFSG.AGLEmbedding.PSL2GF p n) :
    Group.IsSolvable ↥N ∧ CFSG.Open.pRank 3 ⁅N, N⁆ ≤ 1 :=
  ⟨isSolvable_of_mulEquiv_psl2GF hp5 hn hO hN e,
    pRank_three_commutator_le_one_of_mulEquiv_psl2GF hp5 hn hO hN e⟩

end Family

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFTwo
