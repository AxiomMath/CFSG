module

public import CFSG.GH74.Generic.BProg.B2.Thm2AssemblyList
public import CFSG.GH74.Generic.BProg.B2.TwoA7Syl
public import CFSG.GH74.Generic.BProg.B2.Thm2AssemblyBasic
import CFSG.GH74.Generic.BProg.B2.Thm2AssemblyRank1
import CFSG.GH74.Generic.BProg.B2.Thm2Comp
import CFSG.GH74.Generic.BProg.B2.T1Basic
import CFSG.GH74.Generic.BProg.B2.Prop31
import CFSG.GH74.Generic.BProg.B2.Lemma83Bar
import CFSG.GH74.Generic.BProg.B2.TwoA7
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.GH74.Generic.BProg.B1.PilotS4
public import CFSG.GH74.Generic.BProg.B2.PumpupTable
public import CFSG.GH74.Generic.S3.LeavesFine
public import CFSG.GH74.Generic.S3.Lem37
import CFSG.ClassicalInvolution.SmallCases.Sporadic.LyCert
import CFSG.GH74.AS16.Defs
import CFSG.GH74.E2.Components
import CFSG.GH74.E2.OddRankG
import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4Defs
import CFSG.GH74.GLS.Stage4.RestP93
import CFSG.GH74.GLS.Stage4.RestSetup
import CFSG.GH74.Generic.BProg.B2.TwoA7Comp
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
import CFSG.Quasithin.Background.A3Structure318Red
import CFSG.Quasithin.Background.A3Structure36A
import CFSG.Quasithin.Background.A3Structure36BAction
import CFSG.Quasithin.Background.A3Structure36BBase
import CFSG.Quasithin.Background.A3Structure36BCase3Base
import CFSG.Quasithin.Background.A3Structure36BCasesBase
import CFSG.Quasithin.Background.A3Structure36BCommonBase
import CFSG.Quasithin.Background.A3Structure36BFrattini
import CFSG.Quasithin.Background.A3Structure36BHeisBase
import CFSG.Quasithin.Background.A3Structure36BHomocyclic
import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
import CFSG.Quasithin.Background.A3Structure36BStarBase
import CFSG.Quasithin.Background.A3Structure36Base
import CFSG.Quasithin.Background.A3Structure37Base
import CFSG.Quasithin.Background.A3Structure37Comm
import CFSG.Quasithin.Background.A3Structure37Frattini
import CFSG.Quasithin.Background.A3Structure37KeyBase
import CFSG.Quasithin.Background.A3Structure37Schur
import CFSG.Quasithin.Background.A3Structure38Part3
import CFSG.Quasithin.Background.B1MoreElevenE
import CFSG.Quasithin.Background.B1MoreNineG
import CFSG.Quasithin.Background.B4ModelsAction
import CFSG.Quasithin.Background.B4ModelsIso
import CFSG.Quasithin.Background.C2Basic
import CFSG.Quasithin.Background.C2Inputs
import CFSG.Quasithin.Background.E1
import CFSG.Quasithin.Background.E1Sec4
import CFSG.Quasithin.Background.E1Sec5
import CFSG.Quasithin.Background.E1Sec8
import CFSG.Quasithin.Background.E1Solv
import CFSG.Quasithin.Background.E1Twelve
import CFSG.Quasithin.Background.E3Cent
import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
import CFSG.Quasithin.Vol2.Ch1Local
import CFSG.Sporadic.Schreier.LyFixedSet
import Certificates.Certificate5007
import Certificates.Kernel.J4Count.FixCE

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Uniqueness
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

namespace Thm2AssemblyC1

variable {G : Type} [Group G] [Finite G] {x : G} {K A M P Q H : Subgroup G}

theorem two_le_pRank_barIn_K (hs : Stage2Setup G x K A M P Q) (hKM : K ≤ M) :
    2 ≤ pRank 2 ↥(barIn M K) := by
  have hE := isE_inf_K hs
  have hel := hE.2.1
  have hD2 : IsPGroup 2 ↥(A ⊓ K) := CFSG.IsElementaryAbelian.isPGroup 2 _
  have hDM : A ⊓ K ≤ M := inf_le_right.trans hKM
  have hrank := Lemma83Bar.pRank_barIn hDM hD2
  have hle : barIn M (A ⊓ K) ≤ barIn M K := by
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨m, (inf_le_right : A ⊓ K ≤ K) hm, rfl⟩
  have h1 := C3.Layer1.Back.pRank_mono' hle
  have h2 := hE.2.2
  omega

theorem conjugate_eq_of_c1 (hs : Stage2Setup G x K A M P Q) (h1 : Stage2Concl1Core x K M Q H)
    (hc1 : barIn M H = barIn M K) (hr : pRank 2 ↥(CxK x K) ≤ 1) (hKc : IsComponent (barIn M K))
    (hother : ∀ J : Subgroup (Mbar M), IsComponent J → J ≠ barIn M K → J ≤ SD.centBarK M K)
    {J : Subgroup (Mbar M)} (hJ : IsComponent J) (d : Mbar M) : conjugate J d = J := by
  have isComponent_conjugate := @Thm2AssemblyBasic.isComponent_conjugate
  have hC1 : pRank 2 ↥(SD.centBarK M K) ≤ 1 := SD.pRank_centBarK_le_one_of_c1 hs h1 hc1 hr
  have hK2 := two_le_pRank_barIn_K hs h1.K_le
  by_cases hJK : J = barIn M K
  · subst hJK
    by_contra hne
    have hle := hother _ (isComponent_conjugate hKc d) hne
    have h2 := (C3.Layer1.Back.pRank_mono' hle).trans hC1
    rw [C3.Layer1.Back.pRank_conjugate'] at h2
    omega
  · have hJle := hother J hJ hJK
    have hJr : pRank 2 ↥J ≤ 1 := (C3.Layer1.Back.pRank_mono' hJle).trans hC1
    by_contra hne
    have hJ' := isComponent_conjugate hJ d
    have hJ'r : pRank 2 ↥(conjugate J d) ≤ 1 := by
      rw [C3.Layer1.Back.pRank_conjugate']; exact hJr
    have hne' : conjugate J d ≠ barIn M K := by
      intro h
      rw [h] at hJ'r
      omega
    have hle' := hother _ hJ' hne'
    have h2 := two_le_pRank_sup_of_rankOne hJ hJ' (Ne.symm hne) hJr hJ'r
    have h3 := (C3.Layer1.Back.pRank_mono' (sup_le hJle hle')).trans hC1
    omega

theorem qShapeNS_barIn_K (hs : Stage2Setup G x K A M P Q) (hKM : K ≤ M)
    (hKc : IsComponent (barIn M K)) : QShapeNS ↥(barIn M K) := by
  obtain ⟨Z, hZc, hZo, hZn, hZshape⟩ := Prop31.exists_shape hs hKM hKc.1
  have hcore : pPrimeCore 2 (Mbar M) = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hsub : (Z.map (barIn M K).subtype).IsSubnormal := by
    refine Subgroup.IsSubnormal.trans (Subgroup.map_subtype_le Z) ?_ hKc.2
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective (barIn M K).subtype_injective]
    exact hZn.isSubnormal
  have hodd : Odd (Nat.card ↥(Z.map (barIn M K).subtype)) := by
    rw [Subgroup.card_map_of_injective (barIn M K).subtype_injective]
    exact hZo
  have hbot := Walter.eq_bot_of_isSubnormal_of_odd hcore hsub hodd
  have hZ : Z = ⊥ := (Subgroup.map_eq_bot_iff_of_injective Z (barIn M K).subtype_injective).1 hbot
  subst hZ
  exact QShapeNS.of_mulEquiv (QuotientGroup.quotientBot (G := ↥(barIn M K))) hZshape

theorem listedRankOne_or_A7 (hRank1 : RankOneRecog) {Y : Type} [Group Y] [Finite Y] {J : Subgroup Y}
    (hq : IsQuasisimple ↥J) (hr : pRank 2 ↥J ≤ 1) :
    ListedRankOne ↥J ∨
      (Nonempty (↥J ⧸ center ↥J ≃* alternatingGroup (Fin 7)) ∧ center ↥J ≠ ⊥) := by
  rcases hRank1 ↥J hq hr with h | h
  · exact Or.inl ⟨hr, h⟩
  · exact Or.inr h

end Thm2AssemblyC1

theorem qbarSylow_of_isSylowOf {G : Type} [Group G] [Finite G] {K M Q : Subgroup G} (hKM : K ≤ M)
    (hQ : IsSylowOf 2 Q (CMbar M K)) : SD.TwoA7.QbarSylow M K Q := by
  have hCM : CMbar M K ≤ M := inf_le_left
  obtain ⟨S, hS⟩ := hQ.exists_sylow_eq_subgroupOf
  set ρ : ↥M →* Mbar M := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hρ
  set C : Subgroup (Mbar M) := SD.centBarK M K with hC
  let φ₀ : ↥(CMbar M K) →* Mbar M := ρ.comp (Subgroup.inclusion hCM)
  have hφmem : ∀ x : ↥(CMbar M K), φ₀ x ∈ C := fun x =>
    (Thm2Comp.mem_CMbar_iff hKM (Subgroup.inclusion hCM x)).1 x.2
  let φ : ↥(CMbar M K) →* ↥C := φ₀.codRestrict C hφmem
  have hφs : Function.Surjective φ := by
    rintro ⟨c, hc⟩
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥M) c
    refine ⟨⟨(m : G), (Thm2Comp.mem_CMbar_iff hKM m).2 hc⟩, ?_⟩
    apply Subtype.ext
    rfl
  refine ⟨S.mapSurjective hφs, ?_⟩
  rw [Sylow.coe_mapSurjective, hS]
  ext y
  constructor
  · rintro ⟨c, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨Subgroup.inclusion hCM x, ?_, rfl⟩
    exact hx
  · rintro ⟨m, hm, rfl⟩
    have hmM : (m : G) ∈ CMbar M K := hQ.le hm
    refine ⟨φ ⟨(m : G), hmM⟩, ⟨⟨(m : G), hmM⟩, hm, rfl⟩, rfl⟩

end CFSG.GH74.Generic.BProg.B2
