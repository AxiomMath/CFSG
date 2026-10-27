module

public import CFSG.ClassicalInvolution.SmallCases.NDBE6S
public import CFSG.ClassicalInvolution.SmallCases.NDBE7Frame
import CFSG.ClassicalInvolution.Asc77.WP3CFCZT
import CFSG.ClassicalInvolution.Asc77.WP3FrameData
import CFSG.ClassicalInvolution.Asc77.WP3FramePSCNine
import CFSG.ClassicalInvolution.Asc77.WP3L52Main
import CFSG.ClassicalInvolution.Balance.BootstrapAlphaDelta
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952
import CFSG.ClassicalInvolution.Asc77.WP3ChainVGen3
import CFSG.ClassicalInvolution.Asc77.WP3S28WTag
import CFSG.ClassicalInvolution.MilestoneAssemblyCore
import CFSG.Sporadic.Bridge.M11CheckInputs
import Certificates.Certificate110
import Certificates.Certificate8046
import Certificates.Certificate8049
import Certificates.Certificate8052

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Assembly.LowTwoRank

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G}

theorem Exotic.hyp51At_zt {J K' : Subgroup G} {t z' : G} (hS : ExoticBase p f K z)
    (hnoT : ¬ HasTwin p f K z) (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A)
    (hfr : Asc77.ChainFrameData (𝒞 K) K J K' z t z') :
    Asc77.Hyp51At (Subgroup.closure ({z, t, z'} : Set G)) (z * t) := by
  have hΩ := Cover.hypOmegaMod hS.nonabelian hS.odd hS.five hS.member hS.below
  have hcore : Asc77.ChainFrameCore p f (𝒞 K) K J K' z t z' :=
    ⟨hS.odd, hS.five, hΩ, Exotic.noTwins hΩ hfr.hz hnoT, hS.below, hfr⟩
  exact Asc77.CFC.hyp51At_zt_of_third hcore (Exotic.thirdZT hS hnoT hnoF hfr)

namespace ExoticLiftS

variable {C : ExoticCtxS p f K z} (L : ExoticLiftS C)

theorem closure_swap : Subgroup.closure ({z, L.z', L.t} : Set G) = L.B := by
  have h : ({z, L.z', L.t} : Set G) = {z, L.t, L.z'} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [h]

theorem closure_prod : Subgroup.closure ({z, L.t * L.z', L.t} : Set G) = L.B := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact L.z_mem_B
    · exact mul_mem L.t_mem_B L.z'_mem_B
    · exact L.t_mem_B
  · rw [Subgroup.closure_le]
    have htz : L.t * L.z' ∈ Subgroup.closure ({z, L.t * L.z', L.t} : Set G) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    have ht : L.t ∈ Subgroup.closure ({z, L.t * L.z', L.t} : Set G) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
    rintro x (rfl | rfl | rfl)
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact ht
    · have h := mul_mem ht htz
      rwa [← mul_assoc, L.uJ.sq, one_mul] at h

theorem hyp51 (hres : SpinOuterKleinAlpha p) : Hyp51 L.B := by
  have hp2 := C.hS.odd
  have hΩ := C.X.hΩ
  refine ⟨L.B_elem, L.B_card, fun c hc hc1 => ?_⟩
  have hzt := L.frameData₁.comm_zt hp2 hΩ
  have hzz' := L.frameData₁.comm_zz' hp2 hΩ
  rcases ChainFrame.mem_closure_eight C.X.hz2 L.uJ.sq L.uK'.sq hzt hzz' L.htz' hc with
    h | h | h | h | h | h | h | h
  · exact absurd h hc1
  · rw [h]
    exact L.hyp51At_z
  · rw [h]
    exact L.hyp51At_t hres
  · rw [h]
    exact L.hyp51At_z' hres
  · rw [h]
    exact Exotic.hyp51At_zt C.hS C.hnoT C.hnoF L.frameData₁
  · rw [h]
    have h' := Exotic.hyp51At_zt C.hS C.hnoT C.hnoF L.frameData₂
    rwa [L.closure_swap] at h'
  · rw [h]
    exact L.hyp51At_tz' hres
  · rw [h]
    have h' := Exotic.hyp51At_zt C.hS C.hnoT C.hnoF L.frameData₃
    rwa [L.closure_prod] at h'

include L in
theorem quasisimple (hres : SpinOuterKleinAlpha p) : ∀ N ∈ 𝒞 K, CFSG.Open.IsQuasisimple N := by
  have hp2 := C.hS.odd
  have hq := C.hS.five
  have hnab := C.hS.nonabelian
  have hΩIn : InClass p f (𝒞 K) := inClass_conjugates C.hS.member
  have hIH := localLieSystems_of_citBelowU hΩIn C.hS.below
  have hbal : RankThreeBalance L.B := lemma52 G _ (L.hyp51 hres)
  have hcent := centralizes_of_frame hnab hp2 hq hΩIn C.hS.dconn (L.frameSide hres) C.hS.member
    L.z_mem_B (L.frameData₁.tq_B hp2 hq C.X.hΩ) hbal
  have hgen := rankTwoSpan_eq_top_of_dConnected_star hp2 hq hΩIn (L.frameSide hres) C.hS.dconn
  have hΔ := deltaCore_eq_bot_of_rankThreeBalance hbal
    (componentClassificationOddCore_eq_bot_of_simple hnab) hgen
  obtain ⟨F₀, hF₀⟩ := CFSG.SignalizerFunctor.Helpers.signalizerFunctorEk_nonempty 2 2
    Nat.prime_two _ hbal.elem (by rw [hbal.card]; norm_num)
  have hKq : CFSG.Open.IsQuasisimple K :=
    Theorem5.isQuasisimple_of_member_of_deltaCore_eq_bot hnab hp2 hq hΩIn hIH
      (CoreAssembly.mem_conjClass_self K) C.hS.member
      (CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 hbal.elem hF₀.1)
      (hcent.trans (Subgroup.centralizer_le hF₀.1)) (hΔ F₀ hF₀)
  exact Theorem5.isQuasisimple_of_mem_of_single_class (CoreAssembly.exists_single_class K)
    (CoreAssembly.mem_conjClass_self K) hKq

include L in
theorem localLeviComponent_z (hres : SpinOuterKleinAlpha p) : LocalLeviComponent p f (𝒞 K) z := by
  have h : centralizingMembers (exactFamily (𝒞 K) z) {z} = centralizingMembers (𝒞 K) {z} :=
    (centMembers_exactFamily (𝒞 K) z).trans
      (exactFamily_eq_centMembers_of_quasisimple C.X.hΩ.classical (L.quasisimple hres))
  have key : ∀ S₁ S₂ : Set (Subgroup G), S₁ = S₂ →
      ∀ D : LieSystemData p f (↥(⨆ L ∈ S₁, L) ⧸ classicalInvolutionOddCore ↥(⨆ L ∈ S₁, L))
        (oddQuotientFamily (restrictFamily S₁ (⨆ L ∈ S₁, L))), ∀ i : Fin D.card,
        HasA2Pairs (D.tag i) →
        ∃ D' : LieSystemData p f (↥(⨆ L ∈ S₂, L) ⧸ classicalInvolutionOddCore ↥(⨆ L ∈ S₂, L))
          (oddQuotientFamily (restrictFamily S₂ (⨆ L ∈ S₂, L))), ∃ i' : Fin D'.card,
          HasA2Pairs (D'.tag i') := by
    intro S₁ S₂ h D i hi
    subst h
    exact ⟨D, i, hi⟩
  have hA2 : HasA2Pairs (C.D.tag C.i₁) := by
    rcases C.tag₁ with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  obtain ⟨D', i', hi'⟩ := key _ _ h C.D C.i₁ hA2
  exact ⟨D', i', Or.inr (Or.inr (Or.inr (Or.inl hi')))⟩

theorem frameData (hres : SpinOuterKleinAlpha p) :
    FuzzyFrameDataStarE p f (𝒞 K) K z L.B {K, L.J} z where
  mem := CoreAssembly.mem_conjClass_self K
  cls := C.hS.member
  z₀A := L.z_mem_B
  tq := L.frameData₁.tq_B C.hS.odd C.hS.five C.X.hΩ
  frame := L.frameSide hres
  aA := L.z_mem_B
  a1 := C.X.hKz.ne_one
  aClassical := ⟨K, CoreAssembly.mem_conjClass_self K, C.hS.member⟩
  cover := fun _ hM _ => L.cover_z hM
  nine := fun _ => ⟨z, L.z_mem_B, C.X.hKz.ne_one, fun _ hM => L.cover_z hM,
    L.localLeviComponent_z hres⟩

end ExoticLiftS

theorem Exotic.spinFrame_exists (hres : SpinOuterKleinAlpha p) (hS : ExoticBase p f K z)
    (hnoT : ¬ HasTwin p f K z) (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A)
    (D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z) (i : Fin D.card)
    (hi : ExoticModel.SpinTag (D.tag i) (D.rank i)) :
    ∃ (L₀ : Subgroup G) (z₀ : G) (A : Subgroup G) (S : Set (Subgroup G)) (a : G),
      Asc77.FuzzyFrameDataStarE p f (𝒞 K) L₀ z₀ A S a ∧ Asc77.Hyp51 A := by
  obtain ⟨C⟩ := Exotic.exists_exoticCtxS hS hnoT hnoF D hi
  obtain ⟨L⟩ := C.exists_lift
  exact ⟨K, z, L.B, {K, L.J}, z, L.frameData hres, L.hyp51 hres⟩

end CFSG.ClassicalInvolution.NDB
