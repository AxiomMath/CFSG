module

public import CFSG.ClassicalInvolution.RouteD.TWS8Layers
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

public section

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => CoreAssembly.conjClass

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.RouteD.TWS8

section Trans

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K T J : Subgroup G}
  {z t : G} {tY : StatedLieTag} {nY : ℕ}


theorem conjSub_mem_cm {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {x : G} {L : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) {y : G} (hy : y ∈ locLayer Ω x) :
    conjSub y L ∈ centralizingMembers Ω {x} := by
  have hyx : y ∈ Subgroup.centralizer ({x} : Set G) :=
    centralizingLayer_le_centralizer Ω {x} hy
  refine ⟨hΩ _ L hL.1, fun a ha => ?_⟩
  rw [mem_conjSub_iff] at ha
  have hx' := hL.2 ha
  have : a = y * (y⁻¹ * a * y) * y⁻¹ := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyx hx') ((Subgroup.inv_mem _) hyx)

theorem link_big' {Ω : Set (Subgroup G)} {x : G} (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    (hP1 : LocalOddCentral Ω {x}) {tY : StatedLieTag} {nY : ℕ}
    (rf : TwinRowFacts p f tY nY) (d : ShapeDictT2 p f tY nY Ω x) {K T L L' : Subgroup G}
    (hK : K ∈ centralizingMembers Ω {x}) (hT : T ∈ centralizingMembers Ω {x}) (hKT : K ≠ T)
    (hKiso : ∀ L'' ∈ centralizingMembers Ω {x}, L'' ≠ K → Commutes K L'')
    (hTiso : ∀ L'' ∈ centralizingMembers Ω {x}, L'' ≠ T → Commutes T L'')
    (hL : L ∈ centralizingMembers Ω {x}) (hLK : L ≠ K) (hLT : L ≠ T)
    (hL' : L' ∈ centralizingMembers Ω {x}) (hL'K : L' ≠ K) (hL'T : L' ≠ T) :
    ∃ y : G, ∃ hy : y ∈ locLayer Ω x, conjSub y L = L' ∧ locMk Ω x ⟨y, hy⟩ ∈ d.ψ.range := by
  obtain ⟨R, hR, hLR⟩ := big_of_ne hΩ hex hP1 rf d hK hT hKT hKiso hTiso hL hLK hLT
  obtain ⟨R', hR', hLR'⟩ := big_of_ne hΩ hex hP1 rf d hK hT hKT hKiso hTiso hL' hL'K hL'T
  obtain ⟨g, hg⟩ := rf.fsc R hR R' hR'
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (d.ψ g)
  have hconj : conjSub (y : G) L ∈ centralizingMembers Ω {x} :=
    conjSub_mem_cm hΩ.conjInvariant hL y.2
  refine ⟨(y : G), y.2, locImg_injOn hΩ hP1 hconj hL' ?_, ⟨g, hy.symm⟩⟩
  rw [locImg_conjSub_layer, hLR, hLR', show locMk Ω x y = d.ψ g from hy, hg]
  unfold conjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext a
  simp

theorem locImg_conjSub_eq (A : AtT p f K T J z t tY nY) {y : G} (hy : y ∈ locLayer (𝒞 K) t)
    {k : (modelUniv tY nY p f Fact.out).K} (hk : A.d.ψ k = locMk (𝒞 K) t ⟨y, hy⟩) :
    locImg (𝒞 K) t (conjSub y K) = (conjSub k A.RK).map A.d.ψ := by
  rw [locImg_conjSub_layer K ⟨y, hy⟩, A.hKR, ← hk]
  unfold conjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext a
  simp

theorem conjSub_eq_of_stab (S : RouteDSetup p f K z) (A : AtT p f K T J z t tY nY) {y : G}
    (hy : y ∈ locLayer (𝒞 K) t) {k : (modelUniv tY nY p f Fact.out).K}
    (hk : A.d.ψ k = locMk (𝒞 K) t ⟨y, hy⟩)
    (hkS : k ∈ G2D4Models.conjStabilizer
      ({A.RK, A.RT} : Set (Subgroup (modelUniv tY nY p f Fact.out).K))) :
    conjSub y K = K ∨ conjSub y K = T := by
  have himg := locImg_conjSub_eq A hy hk
  have hconj : conjSub y K ∈ centralizingMembers (𝒞 K) {t} :=
    conjSub_mem_cm S.inClass.conjInvariant A.hKt hy
  have hkR : conjSub k A.RK ∈ ({A.RK, A.RT} : Set (Subgroup (modelUniv tY nY p f Fact.out).K)) :=
    (G2D4Models.mem_conjStabilizer_iff.mp hkS A.RK).mpr (Set.mem_insert _ _)
  rcases hkR with h | h
  · left
    rw [h] at himg
    exact locImg_injOn S.inClass A.hP1 hconj A.hKt (himg.trans A.hKR.symm)
  · right
    rw [h] at himg
    exact locImg_injOn S.inClass A.hP1 hconj A.hTt (himg.trans A.hTR.symm)

theorem transfer_max (S : RouteDSetup p f K z) (A : AtT p f K T J z t tY nY)
    (hMax : IsCoatom (G2D4Models.conjStabilizer
      ({A.RK, A.RT} : Set (Subgroup (modelUniv tY nY p f Fact.out).K))))
    (𝒩 : Subgroup G)
    (hN : ∀ y ∈ locLayer (𝒞 K) t, (conjSub y K = K ∨ conjSub y K = T) → y ∈ 𝒩) :
    (∀ N ∈ centralizingMembers (𝒞 K) {t}, N ≠ J → N ≠ A.J₂ → N ≤ 𝒩) ∨
      ∀ y ∈ 𝒩, ∀ hy : y ∈ locLayer (𝒞 K) t,
        locMk (𝒞 K) t ⟨y, hy⟩ ∈ A.d.ψ.range → conjSub y K = K ∨ conjSub y K = T := by
  classical
  set Yt : Subgroup G := locLayer (𝒞 K) t with hYt
  set 𝒩' : Subgroup ↥Yt := 𝒩.subgroupOf Yt with h𝒩'
  set Sd : Subgroup (modelUniv tY nY p f Fact.out).K :=
    (𝒩'.map (locMk (𝒞 K) t)).comap A.d.ψ with hSd
  have hP : G2D4Models.conjStabilizer
      ({A.RK, A.RT} : Set (Subgroup (modelUniv tY nY p f Fact.out).K)) ≤ Sd := by
    intro k hk
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (A.d.ψ k)
    have hyk : A.d.ψ k = locMk (𝒞 K) t y := hy.symm
    have hyK := conjSub_eq_of_stab S A (y := (y : G)) y.2 (k := k) hyk hk
    have hy𝒩 : (y : G) ∈ 𝒩 := hN y y.2 hyK
    exact ⟨y, Subgroup.mem_subgroupOf.mpr hy𝒩, hy⟩
  rcases hMax.le_iff.mp hP with htop | hnorm
  · left
    intro N hNΩ hNJ hNJ₂
    obtain ⟨R, hR, hNR⟩ := big_of_ne S.inClass S.exact A.hP1 A.rf A.d A.hJt A.hJ₂t A.hJ₂J.symm
      A.hJiso A.hJ₂iso hNΩ hNJ hNJ₂
    obtain ⟨zN, hzN⟩ := S.inClass.classical N hNΩ.1
    have hperf : N.subgroupOf Yt ≤ ⁅N.subgroupOf Yt, N.subgroupOf Yt⁆ :=
      (commutator_eq_of_isClassicalMember (hzN.subgroupOf p f (le_centralizingLayer hNΩ))).ge
    have hle : N.subgroupOf Yt ≤ 𝒩' ⊔ classicalInvolutionOddCore ↥Yt := by
      intro a ha
      have ha' : locMk (𝒞 K) t a ∈ locImg (𝒞 K) t N := ⟨a, ha, rfl⟩
      rw [hNR] at ha'
      obtain ⟨k₀, -, hk₀⟩ := Subgroup.mem_map.mp ha'
      have hk₀S : k₀ ∈ Sd := by rw [htop]; trivial
      obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp hk₀S
      have hmem : b⁻¹ * a ∈ classicalInvolutionOddCore ↥Yt :=
        QuotientGroup.eq.mp (hba.trans hk₀)
      have : a = b * (b⁻¹ * a) := by group
      rw [this]
      exact Subgroup.mul_mem_sup hb hmem
    have hNle := le_of_perfect_of_le_sup_center (Z := classicalInvolutionOddCore ↥Yt) A.hP1
      hperf hle
    intro n hn
    have hnY : n ∈ Yt := le_centralizingLayer hNΩ hn
    have h1 : (⟨n, hnY⟩ : ↥Yt) ∈ N.subgroupOf Yt := Subgroup.mem_subgroupOf.mpr hn
    exact Subgroup.mem_subgroupOf.mp (hNle h1)
  · right
    intro y hy𝒩 hyY hyψ
    obtain ⟨k, hk⟩ := hyψ
    have hkS : k ∈ Sd := by
      show A.d.ψ k ∈ 𝒩'.map (locMk (𝒞 K) t)
      rw [hk]
      exact ⟨⟨y, hyY⟩, Subgroup.mem_subgroupOf.mpr hy𝒩, rfl⟩
    rw [hnorm] at hkS
    exact conjSub_eq_of_stab S A hyY hk hkS

end Trans

end CFSG.ClassicalInvolution.RouteD.TWS8
