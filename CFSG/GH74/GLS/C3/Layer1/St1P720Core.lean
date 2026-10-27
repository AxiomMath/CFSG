module

public import CFSG.GH74.GLS.C3.Layer1.St1RigStep
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.GLS.Basic
public import CFSG.GH74.GLS.C3.Layer1.St1PumpClass
public import CFSG.GH74.GLS.TwoThin.G.Reduction
public import CFSG.GH74.E2.ComponentsBasic
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.GH74.E2.CaseIINoComp
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.McL
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import Certificates.Certificate3085Base
public import Certificates.Certificate3953
public import Certificates.Certificate5007
public import Certificates.Certificate5022
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.GH74.GLS.C3.Layer1.P720

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.ComponentClassification
  CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.C3.Layer1.PumpCalc
  CFSG.GH74.GLS.C3.Layer1.PumpRigid
open scoped commutatorElement

section Subnormal

theorem isSubnormal_subgroupOf_of_le {Z : Type*} [Group Z] {H A B : Subgroup Z} (hAB : A ≤ B)
    (h : (H.subgroupOf B).IsSubnormal) : (H.subgroupOf A).IsSubnormal := by
  have h1 := h.comap (Subgroup.inclusion hAB)
  have h2 : (H.subgroupOf B).comap (Subgroup.inclusion hAB) = H.subgroupOf A := by
    ext a
    simp [Subgroup.mem_subgroupOf]
  rwa [h2] at h1

theorem isSubnormal_map_subgroupOf {A B : Type*} [Group A] [Group B] (f : A →* B)
    {V S : Subgroup A} (hSV : S ≤ V) (hsub : (S.subgroupOf V).IsSubnormal) :
    ((S.map f).subgroupOf (V.map f)).IsSubnormal := by
  have hsurj := f.subgroupMap_surjective V
  have h1 := hsub.map hsurj
  have h2 : (S.subgroupOf V).map (f.subgroupMap V) = (S.map f).subgroupOf (V.map f) := by
    ext z
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hvS, hvz⟩
      refine ⟨⟨v, hSV hvS⟩, hvS, ?_⟩
      exact Subtype.ext hvz
  rwa [h2] at h1

end Subnormal

section Coprime

variable {G : Type} [Group G] [Finite G]

theorem centralizer_sbar_le_map {x t : G} (hxo : orderOf x = 2) (hxY : x ∈ centralizer ({t} : Set G)) :
    centralizer ({sbar x hxY} : Set (barQ ↥(centralizer ({t} : Set G)))) ≤
      (centralizer ({(⟨x, hxY⟩ : ↥(centralizer ({t} : Set G)))} :
        Set ↥(centralizer ({t} : Set G)))).map (barMk ↥(centralizer ({t} : Set G))) := by
  set Y' := centralizer ({t} : Set G) with hY'
  set x' : ↥Y' := ⟨x, hxY⟩ with hx'
  have hso : orderOf x' = 2 := orderOf_mk_centralizer hxY hxo
  have hxx : x' * x' = 1 := by
    have := pow_orderOf_eq_one x'
    rwa [hso, sq] at this
  intro y hy
  obtain ⟨y', rfl⟩ := barMk_surjective (Y := ↥Y') y
  let π : ↥Y' →* barQ ↥Y' := barMk ↥Y'
  let O : Subgroup ↥Y' := pPrimeCore 2 ↥Y'
  let Y₁ : Subgroup ↥Y' := (centralizer ({sbar x hxY} : Set (barQ ↥Y'))).comap π
  have hy₁ : y' ∈ Y₁ := hy
  have hOnorm : O.Normal := pPrimeCore_normal
  have hπO : ∀ o ∈ O, π o = 1 := fun o ho => (QuotientGroup.eq_one_iff o).2 ho
  have hOK : O ≤ Y₁ := by
    intro o ho
    show π o ∈ centralizer ({sbar x hxY} : Set (barQ ↥Y'))
    rw [hπO o ho]
    exact Subgroup.one_mem _
  have hcomm : ∀ k ∈ Y₁, ⁅k, x'⁆ ∈ O := by
    intro k hk
    have hk0 : π k ∈ centralizer ({sbar x hxY} : Set (barQ ↥Y')) := hk
    have hk' : π k * sbar x hxY = sbar x hxY * π k := Subgroup.mem_centralizer_singleton_iff.1 hk0
    rw [← QuotientGroup.eq_one_iff]
    show π ⁅k, x'⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 hk'
  obtain ⟨c, -, hcx, o, ho, hkc⟩ :=
    exists_commute_mul_mem_of_odd (K := Y₁) (O := O) (t := x') (odd_card_pPrimeCore ↥Y') hOK hxx
      (fun o ho => hOnorm.conj_mem o ho x') hcomm y' hy₁
  refine ⟨c, ?_, ?_⟩
  · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact hcx.symm
  · show π c = π y'
    rw [hkc, map_mul, hπO o ho, mul_one]

end Coprime

section Diagonal

variable {G : Type} [Group G] [Finite G] {x t : G}

theorem false_of_diagonal
    (hG : Generic.GenericKnownFacts) (hF : E2.E2ComponentFacts) (hgen4 : CFSG.GH74.Gen4 G)
    {K K' : Subgroup G} (hlt : PumpUpLT 2 x K t K') (hxY : x ∈ centralizer ({t} : Set G))
    (hU2 : InU2 (kBar K)) (hnC2 : ¬ InC2 (kBar K)) (hno34 : ¬ IsL34Quotient (kBar K))
    (hsimple : IsSimpleGroup (kBar K)) {Λ : Subgroup G} (hΛ : IsLam x t K Λ)
    {L : Subgroup (barQ ↥(centralizer ({t} : Set G)))}
    (himg : bar t K' = L ∨ bar t K' = conjSub (sbar x hxY)⁻¹ L)
    (hne : conjSub (sbar x hxY)⁻¹ L ≠ L) (hInC2 : InC2 ↥(bar t K')) : False := by
  have hxo : orderOf x = 2 := hlt.1.1
  have hto : orderOf t = 2 := hlt.2.1.1
  have hso : orderOf (sbar x hxY) = 2 := orderOf_sbar hxo hxY
  have hss : sbar x hxY * sbar x hxY = 1 := by
    have := pow_orderOf_eq_one (sbar x hxY)
    rwa [hso, sq] at this
  have hsinv : (sbar x hxY)⁻¹ = sbar x hxY := inv_eq_of_mul_eq_one_left hss
  have hdiag : x ∉ normalizer (K' : Set G) := by
    intro hxN
    have h1 := map_conj_bar_of_normalizes (u := t) (X := K') hxY hxN
    apply hne
    rcases himg with h | h
    · rw [h] at h1
      rw [hsinv]
      exact h1
    · rw [h] at h1
      exact ((conjSub_conjSub_inv (sbar x hxY) L).symm.trans h1).symm
  obtain ⟨e⟩ := kBar_equiv_quotient_of_diag hlt hΛ hxY hdiag hsimple
  by_cases hcen : center ↥(bar t K') = ⊥
  ·
    have e1 : (↥(bar t K') ⧸ center ↥(bar t K')) ≃* ↥(bar t K') :=
      (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
    exact hnC2 (E2.inC2_of_mulEquiv (e.trans e1).symm hInC2)
  · have hP : Gen4Comp ↥(bar t K') :=
      gen4Comp_of_gen4Cen (gen4Cen_barQ hgen4 hto) (bar t K')
    exact C3.Layer1.PumpClass.not_inU2_quotient_of_centre hG hF hP hInC2 hcen hU2 hno34 e

end Diagonal

end CFSG.GH74.GLS.C3.Layer1.P720
