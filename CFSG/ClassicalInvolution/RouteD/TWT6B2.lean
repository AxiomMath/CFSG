module

public import CFSG.ClassicalInvolution.RouteD.TWT4Hbad
public import CFSG.ClassicalInvolution.RouteD.TwinYR2Trans
public import CFSG.ClassicalInvolution.RouteD.SCRTwinGenSmall
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

local notation "LTag" => CFSG.Assembly.LowTwoRank.StatedLieTag

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.RouteD.TWT6

section Statement

variable (p f : ℕ) [Fact p.Prime]

@[expose] def TwinNoExtraOn (P : LTag → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ (tY : LTag) (nY : ℕ),
      TwinRow tY nY → P tY nY → LocalShapeT p f 2 tY nY (𝒞 K) z → ∀ T : Subgroup G,
      IsTwinAt (𝒞 K) K T z → IsClassicalMember p f T z →
      ∀ v : G, v * v = 1 → (∀ k ∈ K, v * k = k * v) →
        (∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → N ≠ T → ∀ n ∈ N, v * n = n * v) →
          v = 1 ∨ v = z

end Statement

section Conj

variable {G : Type} [Group G]

theorem isTwinAt_conj {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {K T : Subgroup G} {z : G}
    (h : IsTwinAt Ω K T z) (g : G) :
    IsTwinAt Ω (conjSub g K) (conjSub g T) (g * z * g⁻¹) where
  mem := by
    rw [centralizingMembers_conj hΩ g z]
    exact ⟨T, h.mem, rfl⟩
  ne := fun hEq => h.ne (conjSub_injective g hEq)
  comm_T := by
    intro N hN hNT
    rw [centralizingMembers_conj hΩ g z] at hN
    obtain ⟨N₀, hN₀, rfl⟩ := hN
    exact (commutes_conjSub_iff g).mpr (h.comm_T N₀ hN₀ fun hEq => hNT (by rw [hEq]))
  comm_K := by
    intro N hN hNK
    rw [centralizingMembers_conj hΩ g z] at hN
    obtain ⟨N₀, hN₀, rfl⟩ := hN
    exact (commutes_conjSub_iff g).mpr (h.comm_K N₀ hN₀ fun hEq => hNK (by rw [hEq]))

end Conj

section Reduction

variable {p f : ℕ} [Fact p.Prime] {P : LTag → ℕ → Prop}


theorem twinYNoCentralOn_of_noExtra
    (hMF : p ≠ 2 → 5 ≤ p ^ f → ∀ tY nY, P tY nY → TwinMFGeneration p f tY nY)
    (hNE : TwinNoExtraOn p f P) : TwinYNoCentralOn p f P := by
  classical
  intro G _ _ _ hnab K z S tY nY hrow hP hshape T hT clsT e M hM
  by_contra hcon
  have hcomm : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → N ≠ T → Commutes M N := by
    intro N hN hNK hNT
    by_contra hnc
    exact hcon ⟨N, hN, hNK, hNT, hnc⟩
  have hKΩ : K ∈ 𝒞 K := CoreAssembly.mem_conjClass_self K
  have hKT' : Commutes K T := hT.comm_K T hT.mem hT.ne
  have hz2 : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two S.cls.orderOf_eq_two
  have hodd : Odd (Nat.card (GaloisField p f)) := odd_natCard_galoisField S.odd S.five
  have hKex := S.exact K hKΩ
  have hu2 : e.u * e.u = 1 := e.u_mul_self hKT' hz2
  have hu1 : e.u ≠ 1 := e.u_ne_one S.cls hKex hodd hKT'
  have hKz : K ∈ centralizingMembers (𝒞 K) {z} :=
    ⟨hKΩ, le_centralizer_of_isClassicalMember S.cls⟩
  have hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  obtain ⟨hG2, hD4, hnA1⟩ := hrow.tag_facts
  have rf := LocalShapeT.twinRowFacts hshape S.odd S.five hG2 hD4 hnA1
  obtain ⟨d⟩ := LocalShapeT.nonempty_dictT2 hD4 rf.fsc S.inClass hKΩ S.cls hshape
  obtain ⟨g, hgM⟩ := CoreAssembly.single_class K M hM.1
  set w : G := g * z * g⁻¹ with hw
  have hclsw : IsClassicalMember p f M w := hgM ▸ S.cls.conj g
  have hMΩ : M ∈ 𝒞 K := hM.1
  have SM : RouteDSetup p f M w := S.of_mem_conjClass hMΩ hclsw
  have hclsM : 𝒞 M = 𝒞 K := conjClass_eq_of_mem hMΩ
  have hshapeM : LocalShapeT p f 2 tY nY (𝒞 M) w := by
    rw [hclsM]
    exact localShapeT_at_member S hMΩ hclsw hshape
  have hTM : IsTwinAt (𝒞 K) M (conjSub g T) w := by
    rw [hgM]
    exact isTwinAt_conj S.inClass.conjInvariant hT g
  have clsTM : IsClassicalMember p f (conjSub g T) w := clsT.conj g
  set Φ : Set (Subgroup G) :=
    {N | N ∈ centralizingMembers (𝒞 K) {z} ∧ N ≠ K ∧ N ≠ T} with hΦ
  set Φ' : Set (Subgroup G) :=
    {N | N ∈ centralizingMembers (𝒞 K) {w} ∧ N ≠ M ∧ N ≠ conjSub g T} with hΦ'
  have hMself : ¬ Commutes M M := by
    intro hc
    have hperf := hclsw.perfect
    have hbot : M = ⊥ := by
      have h1 : ⁅M, M⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact hc y hy x hx
      have h2 : ⁅M, M⁆ = M := Subgroup.commutator_eq_self
      rw [← h2, h1]
    have := hclsw.mem
    rw [hbot, Subgroup.mem_bot] at this
    exact ne_one_of_orderOf_eq_two hclsw.orderOf_eq_two this
  have hΦw : ∀ N ∈ Φ, N ∈ centralizingMembers (𝒞 K) {w} ∧ N ≠ M := by
    intro N hN
    refine ⟨⟨hN.1.1, fun n hn => ?_⟩, fun hEq => hMself (hEq ▸ hcomm N hN.1 hN.2.1 hN.2.2)⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcomm N hN.1 hN.2.1 hN.2.2 w hclsw.mem n hn).symm
  have hΦsub : Φ ⊆ Φ' := by
    intro N hN
    refine ⟨(hΦw N hN).1, (hΦw N hN).2, fun hEq => ?_⟩
    obtain ⟨L', hL', hL'N, hnc⟩ := exists_noncomm_of_ne S.inClass S.exact S.p1 rf d hKz hT.mem
      hT.ne.symm hKiso hTiso hN.1 hN.2.1 hN.2.2
    have hL'K : L' ≠ K := fun h => hnc (by
      rw [h]
      exact (hKiso N hN.1 hN.2.1).symm)
    have hL'T : L' ≠ T := fun h => hnc (by
      rw [h]
      exact (hTiso N hN.1 hN.2.2).symm)
    have hL'Φ : L' ∈ Φ := ⟨hL', hL'K, hL'T⟩
    exact hnc (by
      rw [hEq]
      exact hTM.comm_T L' (hΦw L' hL'Φ).1 (fun h => hL'N (by rw [hEq, h])))
  have hΦ'sub : Φ' ⊆ (fun N => conjSub g N) '' Φ := by
    intro N hN
    refine ⟨conjSub g⁻¹ N, ⟨⟨S.inClass.conjInvariant g⁻¹ N hN.1.1, ?_⟩, ?_, ?_⟩,
      conjSub_conjSub_inv g N⟩
    · have := conjSub_le_centralizer_singleton hN.1.2 g⁻¹
      rwa [show g⁻¹ * w * g⁻¹⁻¹ = z by rw [hw]; group] at this
    · intro h
      apply hN.2.1
      rw [hgM, ← h, conjSub_conjSub_inv]
    · intro h
      apply hN.2.2
      rw [← h, conjSub_conjSub_inv]
  have hΦeq : Φ = Φ' :=
    Set.eq_of_subset_of_ncard_le hΦsub
      ((Set.ncard_le_ncard hΦ'sub (Set.toFinite _)).trans (Set.ncard_image_le (Set.toFinite _)))
      (Set.toFinite _)
  have hMu : ∀ k ∈ M, e.u * k = k * e.u := fun k hk =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hM.2 hk)).symm
  have hΦu : ∀ N ∈ centralizingMembers (𝒞 K) {w}, N ≠ M → N ≠ conjSub g T →
      ∀ n ∈ N, e.u * n = n * e.u := by
    intro N hN hNM hNT n hn
    have hNΦ : N ∈ Φ := hΦeq ▸ (show N ∈ Φ' from ⟨hN, hNM, hNT⟩)
    have hNu := e.mem_centralizingMembers_u hNΦ.1.1 (hKiso N hNΦ.1 hNΦ.2.1).symm
      (hTiso N hNΦ.1 hNΦ.2.2).symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hNu.2 hn)).symm
  have hMtw : IsTwinAt (𝒞 M) M (conjSub g T) w := by
    rw [hclsM]
    exact hTM
  have key := hNE G hnab M w SM tY nY hrow hP hshapeM (conjSub g T) hMtw clsTM e.u hu2 hMu
    (by
      rw [hclsM]
      exact hΦu)
  rcases key with h1 | h2
  · exact hu1 h1
  · exact TWT4.false_of_member_containing_u hnab S hrow hshape hT clsT e
      (hMF S.odd S.five tY nY hP) hMΩ (h2 ▸ hclsw.mem)

theorem twinYNoCentralOn_odd3_of_noExtra
    (hNE : TwinNoExtraOn p f fun t n => t = .POmegaOdd ∧ n = 3) :
    TwinYNoCentralOn p f fun t n => t = .POmegaOdd ∧ n = 3 :=
  twinYNoCentralOn_of_noExtra (fun hp2 hq tY nY hl => by
    obtain ⟨rfl, rfl⟩ := hl
    exact twinMFGeneration_odd hp2 hq (le_refl 3)) hNE

theorem twinYNoCentralOn_minus4_of_noExtra
    (hNE : TwinNoExtraOn p f fun t n => t = .POmegaMinus ∧ n = 4) :
    TwinYNoCentralOn p f fun t n => t = .POmegaMinus ∧ n = 4 :=
  twinYNoCentralOn_of_noExtra (fun hp2 hq tY nY hl => by
    obtain ⟨rfl, rfl⟩ := hl
    exact twinMFGeneration_minus hp2 hq (le_refl 4)) hNE

end Reduction

end CFSG.ClassicalInvolution.RouteD.TWT6
