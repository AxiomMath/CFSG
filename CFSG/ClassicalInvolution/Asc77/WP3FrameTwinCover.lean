module

public import CFSG.ClassicalInvolution.Asc77.WP3FramePSCCover
public import CFSG.ClassicalInvolution.RouteD.TwinYP1Layer
public import CFSG.ClassicalInvolution.RouteD.TwinYP1Frame
import CFSG.ClassicalInvolution.Asc77.AscE187Img
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
import CFSG.ClassicalInvolution.Balance.PassTwoModelFacts
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
public import CFSG.ClassicalInvolution.MilestoneAssemblyCore
public import CFSG.ClassicalInvolution.RouteD.TriageP1Rows
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import Certificates.Certificate110
public import Certificates.Certificate8046
public import Certificates.Certificate8049
public import Certificates.Certificate8052
import CFSG.ClassicalInvolution.Asc77.AscE187Basic
import CFSG.ClassicalInvolution.Asc77.AscE187Cop
import CFSG.ClassicalInvolution.Asc77.AscThmABasic

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.RouteD
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD.TwinY

local notation "𝒞" => CoreAssembly.conjClass

section Conj

variable {G : Type} [Group G]

theorem conjSub_le_centralizer_singleton {N : Subgroup G} {a : G}
    (h : N ≤ Subgroup.centralizer ({a} : Set G)) (g : G) :
    conjSub g N ≤ Subgroup.centralizer ({g * a * g⁻¹} : Set G) := by
  intro y hy
  rw [mem_conjSub_iff] at hy
  have h1 := Subgroup.mem_centralizer_singleton_iff.mp (h hy)
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc y * (g * a * g⁻¹) = g * ((g⁻¹ * y * g) * a) * g⁻¹ := by group
    _ = g * (a * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
    _ = (g * a * g⁻¹) * y := by group

theorem conjSub_mem_centMembers_of_mem_centralizer {Ω : Set (Subgroup G)}
    (hΩ : ∀ (g : G) (L : Subgroup G), L ∈ Ω → conjSub g L ∈ Ω) {x : G} {N : Subgroup G}
    (hN : N ∈ centMembers Ω x) {h : G} (hh : h ∈ Subgroup.centralizer ({x} : Set G)) :
    conjSub h N ∈ centMembers Ω x := by
  refine ⟨hΩ h N hN.1, ?_⟩
  have e : h * x * h⁻¹ = x := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hh
    rw [this]
    group
  have := conjSub_le_centralizer_singleton hN.2 h
  rwa [e] at this

theorem mem_centralizer_singleton_of_conj_eq {h x : G} (e : h * x * h⁻¹ = x) :
    h ∈ Subgroup.centralizer ({x} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc h * x = (h * x * h⁻¹) * h := by group
    _ = x * h := by rw [e]

end Conj

section Lift

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_conj_commutes_of_comm_mod_odd (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (hIn : InClass p f Ω) (hex : ExactMembers Ω) {J : Subgroup G}
    (hJ : J ∈ Ω) {t : G} (hJt : IsUniqueInvolution J t) {x : G} {N : Subgroup G}
    (hN : N ∈ centMembers Ω x) (htx : t ∈ Subgroup.centralizer ({x} : Set G))
    (hcomm : ∀ j ∈ J, ∀ n ∈ N,
      j * n * j⁻¹ * n⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({x} : Set G))) :
    ∃ o ∈ oddCoreIn (Subgroup.centralizer ({x} : Set G)),
      conjSub o N = J ∨ (conjSub o N ∈ omegaNbr Ω J ∧ Commutes J (conjSub o N) ∧
        conjSub o N ≤ Subgroup.centralizer ({x} : Set G)) := by
  classical
  have ht2 : t * t = 1 := hJt.sq
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  set Cx := Subgroup.centralizer ({x} : Set G) with hCx
  set O := oddCoreIn Cx with hO
  have hOodd : Odd (Nat.card O) := odd_card_oddCoreIn Cx
  obtain ⟨R, hRset, hRN, -⟩ := exists_mem_RSet_ge hN.1
    (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G)) bot_le
  have hRC : ∀ y ∈ R, y ∈ Cx := fun y hy => hN.2 (hRN.1 hy)
  obtain ⟨n, hnO, hfix⟩ := exists_conj_fixed_of_isPGroup (A := R) (N := O) hRN.2.1 hOodd
    (fun y hy m hm => conj_mem_oddCoreIn (hRC y hy) hm) ht2
    (fun m hm => conj_mem_oddCoreIn htx hm)
    (fun y hy => by
      have h1 := hcomm t hJt.mem y (hRN.1 hy)
      rw [htinv] at h1
      simpa [mul_assoc] using h1)
  have hnC : n ∈ Cx := oddCoreIn_le _ hnO
  have hoO : n⁻¹ ∈ O := O.inv_mem hnO
  refine ⟨n⁻¹, hoO, ?_⟩
  set N' := conjSub n⁻¹ N with hN'
  have hN'Ω : N' ∈ Ω := hIn.conjInvariant n⁻¹ N hN.1
  have hN'x : N' ≤ Cx := by
    intro y hy
    have h1 : n * y * n⁻¹ ∈ N := by
      have := mem_conjSub_iff.mp hy
      simpa using this
    have h2 : n * y * n⁻¹ ∈ Cx := hN.2 h1
    have e : y = n⁻¹ * (n * y * n⁻¹) * n := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hnC) h2) hnC
  have hR'syl : IsSylow2In (conjSub n⁻¹ R) N' := IsSylow2In.conj hRN n⁻¹
  have hR'set : conjSub n⁻¹ R ∈ RSet Ω := mem_RSet_of_isSylow2In hN'Ω hR'syl
  have hR't : conjSub n⁻¹ R ≤ Subgroup.centralizer ({t} : Set G) := by
    intro y hy
    have h1 : n * y * n⁻¹ ∈ R := by
      have := mem_conjSub_iff.mp hy
      simpa using this
    have e1 : (n * y * n⁻¹) * (n * t * n⁻¹) = (n * t * n⁻¹) * (n * y * n⁻¹) := by
      have := hfix _ h1
      calc (n * y * n⁻¹) * (n * t * n⁻¹)
          = ((n * y * n⁻¹) * (n * t * n⁻¹) * (n * y * n⁻¹)⁻¹) * (n * y * n⁻¹) := by group
        _ = (n * t * n⁻¹) * (n * y * n⁻¹) := by rw [this]
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y * t = n⁻¹ * ((n * y * n⁻¹) * (n * t * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * t * n⁻¹) * (n * y * n⁻¹)) * n := by rw [e1]
      _ = t * y := by group
  by_cases hN'J : N' = J
  · exact Or.inl hN'J
  right
  have hN'nbr : N' ∈ omegaNbr Ω J :=
    mem_omegaNbr_of_sylow_le_centralizer hp hq hΩ hJ hN'Ω hN'J hJt hR'syl hR'set hR't
  exact ⟨hN'nbr, AscE186.commutes_of_mem_omegaNbr hp hq (hΩ.toExact hex) hJ hN'nbr, hN'x⟩

end Lift

section Twin

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K T J : Subgroup G} {z t : G}
  {tY : CFSG.Assembly.LowTwoRank.StatedLieTag} {nY : ℕ}

omit [Finite G] in
theorem conjSub_eq_of_mem_locLayer {Ω : Set (Subgroup G)} {K₀ : Subgroup G}
    (hK : K₀ ∈ centralizingMembers Ω {z})
    (hiso : ∀ N ∈ centralizingMembers Ω {z}, N ≠ K₀ → Commutes K₀ N) {y : G}
    (hy : y ∈ locLayer Ω z) : conjSub y K₀ = K₀ := by
  have hle : locLayer Ω z ≤ Subgroup.normalizer (K₀ : Set G) := by
    refine iSup₂_le fun N hN => ?_
    by_cases hNK : N = K₀
    · subst hNK
      exact Subgroup.le_normalizer
    · intro n hn
      have hc : n ∈ Subgroup.centralizer (K₀ : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        exact (hiso N hN hNK k hk n hn)
      exact Subgroup.centralizer_le_normalizer (K₀ : Set G) hc
  exact mem_normalizer_iff_conjSub_eq.mp (hle hy)

@[expose] def NoThreeFund (p f : ℕ) [Fact p.Prime] (tY : CFSG.Assembly.LowTwoRank.StatedLieTag)
    (nY : ℕ) : Prop :=
  ∀ A ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D,
    ∀ B ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D,
    ∀ C ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D,
    A ≠ B → A ≠ C → B ≠ C → Commutes A B → Commutes A C → Commutes B C → False

structure TwinCfg (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] (K T J : Subgroup G) (z t : G) :
    Prop where
  hT : T ∈ centralizingMembers (𝒞 K) {z}
  hKT : K ≠ T
  hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N
  hTiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N
  clsT : IsClassicalMember p f T z
  hJ : J ∈ centralizingMembers (𝒞 K) {z}
  hJK : J ≠ K
  hJT : J ≠ T
  hJt : IsClassicalMember p f J t
  htz : t ≠ z

namespace TwinCfg

omit [Finite G] in
theorem commutes_KJ (cfg : TwinCfg p f K T J z t) : Commutes K J :=
  cfg.hKiso J cfg.hJ cfg.hJK

omit [Finite G] in
theorem commutes_TJ (cfg : TwinCfg p f K T J z t) : Commutes T J :=
  cfg.hTiso J cfg.hJ cfg.hJT

theorem K_le_t (cfg : TwinCfg p f K T J z t) (S : RouteDSetup p f K z) :
    K ≤ Subgroup.centralizer ({t} : Set G) := fun k hk =>
  Subgroup.mem_centralizer_singleton_iff.mpr
    (cfg.commutes_KJ k hk t (ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five
      cfg.hJt).mem)

theorem T_le_t (cfg : TwinCfg p f K T J z t) (S : RouteDSetup p f K z) :
    T ≤ Subgroup.centralizer ({t} : Set G) := fun k hk =>
  Subgroup.mem_centralizer_singleton_iff.mpr
    (cfg.commutes_TJ k hk t (ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five
      cfg.hJt).mem)

theorem comm_zt (cfg : TwinCfg p f K T J z t) (S : RouteDSetup p f K z) : z * t = t * z :=
  (Subgroup.mem_centralizer_singleton_iff.mp (cfg.hJ.2
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five cfg.hJt).mem)).symm

end TwinCfg

namespace TwinCfg

variable (S : RouteDSetup p f K z) (rf : TwinRowFacts p f tY nY)
  (d : ShapeDictT2 p f tY nY (𝒞 K) z) (cfg : TwinCfg p f K T J z t)

include S rf d cfg

theorem exists_swap : ∃ s : G, conjSub s J = K ∧ s * z * s⁻¹ = t ∧ s * t * s⁻¹ = z := by
  have hUz := ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five S.cls
  have hUt := ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five cfg.hJt
  have hUT := ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five cfg.clsT
  have hKmem : K ∈ centralizingMembers (𝒞 K) {z} :=
    ⟨CoreAssembly.mem_conjClass_self K, le_centralizer_of_isClassicalMember S.cls⟩
  obtain ⟨g₀, hg₀⟩ := cfg.hJ.1
  have hg₀' : conjSub g₀ K = J := hg₀
  have hgt : t = g₀ * z * g₀⁻¹ := by
    have h1 := hUz.conj g₀
    rw [hg₀'] at h1
    exact hUt.eq h1
  have hΩc : centralizingMembers (𝒞 K) {t} = conjSub g₀ '' centralizingMembers (𝒞 K) {z} := by
    rw [hgt]
    exact centralizingMembers_conj S.inClass.conjInvariant g₀ z
  have hKt : K ∈ centralizingMembers (𝒞 K) {t} :=
    ⟨CoreAssembly.mem_conjClass_self K, cfg.K_le_t S⟩
  rw [hΩc] at hKt
  obtain ⟨K₂, hK₂, hK₂K⟩ := hKt
  have hK₂' : K₂ = conjSub g₀⁻¹ K := by
    rw [← hK₂K, conjSub_inv_conjSub]
  have hK₂K' : K₂ ≠ K := by
    intro h
    apply cfg.hJK
    rw [h] at hK₂K
    rw [← hg₀']
    exact hK₂K
  have hK₂T : K₂ ≠ T := by
    intro h
    rw [h] at hK₂K
    have h1 := hUT.conj g₀
    rw [hK₂K] at h1
    exact cfg.htz (by rw [hgt]; exact (hUz.eq h1).symm)
  obtain ⟨y, hy, hyK₂⟩ := link_big S.inClass S.exact S.p1 rf d hKmem cfg.hT cfg.hKT
    cfg.hKiso cfg.hTiso hK₂ hK₂K' hK₂T cfg.hJ cfg.hJK cfg.hJT
  have hyz : y * z * y⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp
      (centralizingLayer_le_centralizer (𝒞 K) {z} hy)
    rw [this]
    group
  have hyK : conjSub y K = K :=
    conjSub_eq_of_mem_locLayer hKmem cfg.hKiso hy
  refine ⟨y * g₀⁻¹, ?_, ?_, ?_⟩
  · rw [conjSub_mul, show conjSub g₀⁻¹ J = K by rw [← hg₀', conjSub_inv_conjSub], hyK]
  · have h1 := hUz.conj g₀⁻¹
    rw [← hK₂'] at h1
    have h2 := h1.conj y
    rw [hyK₂] at h2
    have h3 := hUt.eq h2
    rw [h3]
    group
  · have hgz : g₀⁻¹ * t * g₀ = z := by
      rw [hgt]
      group
    calc y * g₀⁻¹ * t * (y * g₀⁻¹)⁻¹ = y * (g₀⁻¹ * t * g₀) * y⁻¹ := by group
      _ = z := by rw [hgz, hyz]


theorem exists_swap_KT :
    ∃ c : G, conjSub c K = T ∧ c * z * c⁻¹ = z ∧ c * t * c⁻¹ = t ∧ conjSub c J = J := by
  have hUz := ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five S.cls
  have hUt := ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five cfg.hJt
  have hUT := ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five cfg.clsT
  have hKmem : K ∈ centralizingMembers (𝒞 K) {z} :=
    ⟨CoreAssembly.mem_conjClass_self K, le_centralizer_of_isClassicalMember S.cls⟩
  obtain ⟨c₀, hc₀⟩ := single_class K T cfg.hT.1
  have hc₀z : c₀ * z * c₀⁻¹ = z := by
    have h1 := hUz.conj c₀
    rw [← hc₀] at h1
    exact (hUT.eq h1).symm
  have hcomm₀ : z * c₀ = c₀ * z := by
    calc z * c₀ = (c₀ * z * c₀⁻¹) * c₀ := by rw [hc₀z]
      _ = c₀ * z := by group
  have hc₀z' : c₀⁻¹ * z * c₀ = z := by
    calc c₀⁻¹ * z * c₀ = c₀⁻¹ * (z * c₀) := by group
      _ = c₀⁻¹ * (c₀ * z) := by rw [hcomm₀]
      _ = z := by group
  have hJ₂mem : conjSub c₀ J ∈ centralizingMembers (𝒞 K) {z} := by
    refine ⟨S.inClass.conjInvariant c₀ J cfg.hJ.1, ?_⟩
    have := conjSub_le_centralizer_singleton cfg.hJ.2 c₀
    rwa [hc₀z] at this
  have hJ₂inv : IsUniqueInvolution (conjSub c₀ J) (c₀ * t * c₀⁻¹) := hUt.conj c₀
  have hne : c₀ * t * c₀⁻¹ ≠ z := by
    intro h
    apply cfg.htz
    calc t = c₀⁻¹ * (c₀ * t * c₀⁻¹) * c₀ := by group
      _ = z := by rw [h, hc₀z']
  have hJ₂K : conjSub c₀ J ≠ K := by
    intro h
    rw [h] at hJ₂inv
    exact hne (hJ₂inv.eq hUz)
  have hJ₂T : conjSub c₀ J ≠ T := by
    intro h
    rw [h] at hJ₂inv
    exact hne (hJ₂inv.eq hUT)
  obtain ⟨y, hy, hyJ⟩ := link_big S.inClass S.exact S.p1 rf d hKmem cfg.hT cfg.hKT cfg.hKiso
    cfg.hTiso hJ₂mem hJ₂K hJ₂T cfg.hJ cfg.hJK cfg.hJT
  have hyz : y * z * y⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp
      (centralizingLayer_le_centralizer (𝒞 K) {z} hy)
    rw [this]
    group
  have hyT : conjSub y T = T := conjSub_eq_of_mem_locLayer cfg.hT cfg.hTiso hy
  have hcJ : conjSub (y * c₀) J = J := by
    rw [conjSub_mul, hyJ]
  refine ⟨y * c₀, ?_, ?_, ?_, hcJ⟩
  · rw [conjSub_mul, ← hc₀, hyT]
  · calc y * c₀ * z * (y * c₀)⁻¹ = y * (c₀ * z * c₀⁻¹) * y⁻¹ := by group
      _ = z := by rw [hc₀z, hyz]
  · have h1 := hUt.conj (y * c₀)
    rw [hcJ] at h1
    exact (hUt.eq h1).symm

theorem mem_four_of_le_centralizer (hcen : Subgroup.center G = ⊥)
    (hno3 : NoThreeFund p f tY nY) {J' : Subgroup G} (hJ'Ω : J' ∈ 𝒞 K)
    (hJ'z : J' ≤ Subgroup.centralizer ({z} : Set G)) (hJ't : IsClassicalMember p f J' t)
    (hJJ' : J ≠ J') {N : Subgroup G} (hN : N ∈ 𝒞 K)
    (hNz : N ≤ Subgroup.centralizer ({z} : Set G))
    (hNt : N ≤ Subgroup.centralizer ({t} : Set G)) :
    N = K ∨ N = T ∨ N = J ∨ N = J' := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hNK, hNT, hNJ, hNJ'⟩ := hcon
  have hUz := ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five S.cls
  have hUT := ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five cfg.clsT
  have hUt' := ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five hJ't
  have hKmem : K ∈ centralizingMembers (𝒞 K) {z} :=
    ⟨CoreAssembly.mem_conjClass_self K, le_centralizer_of_isClassicalMember S.cls⟩
  have hNm : N ∈ centralizingMembers (𝒞 K) {z} := ⟨hN, hNz⟩
  have hJ'm : J' ∈ centralizingMembers (𝒞 K) {z} := ⟨hJ'Ω, hJ'z⟩
  have hJ'K : J' ≠ K := by
    intro h
    rw [h] at hUt'
    exact cfg.htz (hUz.eq hUt').symm
  have hJ'T : J' ≠ T := by
    intro h
    rw [h] at hUt'
    exact cfg.htz (hUT.eq hUt').symm
  obtain ⟨R₀, hR₀, h₀⟩ := big_of_ne S.inClass S.exact S.p1 rf d hKmem cfg.hT cfg.hKT cfg.hKiso
    cfg.hTiso cfg.hJ cfg.hJK cfg.hJT
  obtain ⟨R₁, hR₁, h₁⟩ := big_of_ne S.inClass S.exact S.p1 rf d hKmem cfg.hT cfg.hKT cfg.hKiso
    cfg.hTiso hJ'm hJ'K hJ'T
  obtain ⟨R₂, hR₂, h₂⟩ := big_of_ne S.inClass S.exact S.p1 rf d hKmem cfg.hT cfg.hKT cfg.hKiso
    cfg.hTiso hNm hNK hNT
  have c01 : Commutes J J' :=
    (S.cp_at_member hcen cfg.hJ.1 cfg.hJt (L := J')
      ⟨hJ'Ω, le_centralizer_of_isClassicalMember hJ't⟩).resolve_right (Ne.symm hJJ')
  have c02 : Commutes J N :=
    (S.cp_at_member hcen cfg.hJ.1 cfg.hJt (L := N) ⟨hN, hNt⟩).resolve_right hNJ
  have c12 : Commutes J' N :=
    (S.cp_at_member hcen hJ'Ω hJ't (L := N) ⟨hN, hNt⟩).resolve_right hNJ'
  have hinj : ∀ {L L' : Subgroup G} {R R' : Subgroup (modelUniv tY nY p f Fact.out).K},
      L ∈ centralizingMembers (𝒞 K) {z} → L' ∈ centralizingMembers (𝒞 K) {z} →
      locImg (𝒞 K) z L = R.map d.ψ → locImg (𝒞 K) z L' = R'.map d.ψ → L ≠ L' → R ≠ R' := by
    intro L L' R R' hL hL' hLR hLR' hne hR
    apply hne
    exact locImg_injOn S.inClass S.p1 hL hL' (hLR.trans ((congrArg (fun X => X.map d.ψ) hR).trans
      hLR'.symm))
  exact hno3 R₀ hR₀ R₁ hR₁ R₂ hR₂ (hinj cfg.hJ hJ'm h₀ h₁ hJJ')
    (hinj cfg.hJ hNm h₀ h₂ (Ne.symm hNJ)) (hinj hJ'm hNm h₁ h₂ (Ne.symm hNJ'))
    ((commutes_iff_fund S.inClass S.p1 rf d cfg.hJ hJ'm hR₀ h₀ h₁).mp c01)
    ((commutes_iff_fund S.inClass S.p1 rf d cfg.hJ hNm hR₀ h₀ h₂).mp c02)
    ((commutes_iff_fund S.inClass S.p1 rf d hJ'm hNm hR₁ h₁ h₂).mp c12)

theorem cover_twin [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hΩ : HypOmegaMod p f (𝒞 K)) (hno3 : NoThreeFund p f tY nY) :
    ∀ N ∈ centMembers (𝒞 K) (z * t), ∃ h : G, h ∈ Subgroup.centralizer ({z * t} : Set G) ∧
      InCommonComponent (z * t) N (conjSub h J) := by
  classical
  have hcen : Subgroup.center G = ⊥ := CoreAssembly.center_eq_bot hnab
  have hUz := ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five S.cls
  have hUt := ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five cfg.hJt
  have hUT := ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five cfg.clsT
  have hz2 : z * z = 1 := hUz.sq
  have ht2 : t * t = 1 := hUt.sq
  have hzt : z * t = t * z := cfg.comm_zt S
  obtain ⟨s, hsJ, hsz, hst⟩ := exists_swap S rf d cfg
  obtain ⟨c, hcK, hcz, hct, -⟩ := exists_swap_KT S rf d cfg
  have hx1 : z * t ≠ 1 := by
    intro h
    apply cfg.htz
    rw [eq_inv_of_mul_eq_one_right h]
    exact inv_eq_of_mul_eq_one_right hz2
  have hnc : ¬ ({z * t} : Set G) ⊆ Subgroup.center G := not_subset_center_of_ne_one hnab hx1
  have hcent : ∀ {L : Subgroup G} {a b : G}, L ≤ Subgroup.centralizer ({a} : Set G) →
      L ≤ Subgroup.centralizer ({b} : Set G) → L ≤ Subgroup.centralizer ({a * b} : Set G) := by
    intro L a b ha hb y hy
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (ha hy)
    have h2 := Subgroup.mem_centralizer_singleton_iff.mp (hb hy)
    rw [Subgroup.mem_centralizer_singleton_iff, ← mul_assoc, h1, mul_assoc, h2, mul_assoc]
  have hJx : J ∈ centMembers (𝒞 K) (z * t) :=
    ⟨cfg.hJ.1, hcent cfg.hJ.2 (le_centralizer_of_isClassicalMember cfg.hJt)⟩
  have hsx : s ∈ Subgroup.centralizer ({z * t} : Set G) := by
    refine mem_centralizer_singleton_of_conj_eq ?_
    calc s * (z * t) * s⁻¹ = (s * z * s⁻¹) * (s * t * s⁻¹) := by group
      _ = t * z := by rw [hsz, hst]
      _ = z * t := hzt.symm
  have hcx : c ∈ Subgroup.centralizer ({z * t} : Set G) := by
    refine mem_centralizer_singleton_of_conj_eq ?_
    calc c * (z * t) * c⁻¹ = (c * z * c⁻¹) * (c * t * c⁻¹) := by group
      _ = z * t := by rw [hcz, hct]
  have htx : t ∈ Subgroup.centralizer ({z * t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc t * (z * t) = (t * z) * t := by group
      _ = (z * t) * t := by rw [hzt]
  have hsz' : s⁻¹ * t * s = z := by
    calc s⁻¹ * t * s = s⁻¹ * (s * z * s⁻¹) * s := by rw [hsz]
      _ = z := by group
  have hst' : s⁻¹ * z * s = t := by
    calc s⁻¹ * z * s = s⁻¹ * (s * t * s⁻¹) * s := by rw [hst]
      _ = t := by group
  have hJ₃Ω : conjSub s⁻¹ T ∈ 𝒞 K := S.inClass.conjInvariant s⁻¹ T cfg.hT.1
  have hJ₃z : conjSub s⁻¹ T ≤ Subgroup.centralizer ({z} : Set G) := by
    have := conjSub_le_centralizer_singleton (cfg.T_le_t S) s⁻¹
    rwa [show s⁻¹ * t * s⁻¹⁻¹ = z by rw [inv_inv]; exact hsz'] at this
  have hJ₃t : IsClassicalMember p f (conjSub s⁻¹ T) t := by
    have := cfg.clsT.conj s⁻¹
    rwa [show s⁻¹ * z * s⁻¹⁻¹ = t by rw [inv_inv]; exact hst'] at this
  have hJJ₃ : J ≠ conjSub s⁻¹ T := by
    intro h
    apply cfg.hKT
    have h1 : conjSub s J = conjSub s (conjSub s⁻¹ T) := by rw [← h]
    rw [conjSub_conjSub_inv, hsJ] at h1
    exact h1
  have hDecomp := memberJoin_normal (a := z * t) S.inClass.conjInvariant
  obtain ⟨D⟩ := lieDecomposition_memberImages S.odd ModelFacts.modelClauseZero
    fundamentalWholeA1 S.inClass S.ih hnc
  have hQ : ∀ i, CFSG.IsComponent (D.Q i) := fun i =>
    (CFSG.isComponent_iff_open _).mpr (D.isComponentOf i)
  have hmem : ∀ L ∈ centMembers (𝒞 K) (z * t), ∃ i, modOdd (z * t) L ≤ D.Q i := fun L hL =>
    D.exists_le _ (⟨L, hL, rfl⟩ : modOdd (z * t) L ∈ memberImages (𝒞 K) (z * t))
  intro N hN
  by_cases hNJ : InCommonComponent (z * t) N J
  · exact ⟨1, one_mem _, by rw [conjSub_one]; exact hNJ⟩
  have hcomm := Balance.Theorem5.comm_mem_oddCoreIn_of_not_inCommonComponent S.odd S.inClass S.ih
    hnc hJx hN (fun ⟨Q, hQc, h1, h2⟩ => hNJ ⟨Q, hQc, h2, h1⟩)
  obtain ⟨o, ho, hcases⟩ := exists_conj_commutes_of_comm_mod_odd S.odd S.five hΩ S.inClass
    S.exact cfg.hJ.1 hUt hN htx hcomm
  have himg : modOdd (z * t) (conjSub o N) = modOdd (z * t) N :=
    modOdd_conjSub_of_mem_oddCoreIn ho
  have hsame : conjSub o N = J → False := by
    intro hoJ
    apply hNJ
    obtain ⟨a, ha⟩ := hmem J hJx
    exact ⟨D.Q a, hQ a, by rw [← himg, hoJ]; exact ha, ha⟩
  have key : ∃ h : G, h ∈ Subgroup.centralizer ({z * t} : Set G) ∧ conjSub o N = conjSub h J := by
    rcases hcases with hoJ | ⟨-, hcJ, hNx⟩
    · exact (hsame hoJ).elim
    have hN'Ω : conjSub o N ∈ 𝒞 K := S.inClass.conjInvariant o N hN.1
    have hN't : conjSub o N ≤ Subgroup.centralizer ({t} : Set G) := fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hcJ t hUt.mem y hy).symm
    have hN'z : conjSub o N ≤ Subgroup.centralizer ({z} : Set G) := by
      intro y hy
      have h1 : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp (hN't hy)
      have h2 : y * (z * t) = (z * t) * y := Subgroup.mem_centralizer_singleton_iff.mp (hNx hy)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hz' : (z * t) * t = z := by rw [mul_assoc z t t, ht2, mul_one]
      calc y * z = y * ((z * t) * t) := by rw [hz']
        _ = (y * (z * t)) * t := (mul_assoc _ _ _).symm
        _ = ((z * t) * y) * t := by rw [h2]
        _ = (z * t) * (y * t) := mul_assoc _ _ _
        _ = (z * t) * (t * y) := by rw [h1]
        _ = ((z * t) * t) * y := (mul_assoc _ _ _).symm
        _ = z * y := by rw [hz']
    rcases mem_four_of_le_centralizer S rf d cfg hcen hno3 hJ₃Ω hJ₃z hJ₃t hJJ₃ hN'Ω hN'z hN't with
      h | h | h | h
    · exact ⟨s, hsx, by rw [h, hsJ]⟩
    · exact ⟨c * s, mul_mem hcx hsx, by rw [h, conjSub_mul, hsJ, hcK]⟩
    · exact (hsame h).elim
    · refine ⟨s⁻¹ * (c * s), mul_mem (inv_mem hsx) (mul_mem hcx hsx), ?_⟩
      rw [h, conjSub_mul, conjSub_mul, hsJ, hcK]
  obtain ⟨h, hh, hconj⟩ := key
  refine ⟨h, hh, ?_⟩
  obtain ⟨a, ha⟩ := hmem _
    (conjSub_mem_centMembers_of_mem_centralizer S.inClass.conjInvariant hJx hh)
  exact ⟨D.Q a, hQ a, by rw [← himg, hconj]; exact ha, ha⟩

end TwinCfg

end Twin

end CFSG.ClassicalInvolution.Asc77
