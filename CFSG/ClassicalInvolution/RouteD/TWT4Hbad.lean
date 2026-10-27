module

public import CFSG.ClassicalInvolution.RouteD.TWZGlobal
public import CFSG.ClassicalInvolution.Asc77.WP3FrameTwinCover
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

namespace CFSG.ClassicalInvolution.RouteD.TWT4

section Normalizer

variable {G : Type} [Group G]

theorem le_normalizer_iSup_of_forall {Φ : Set (Subgroup G)} {S : Subgroup G}
    (h : ∀ c ∈ S, ∀ N ∈ Φ, conjSub c N ∈ Φ) :
    S ≤ Subgroup.normalizer ((⨆ N ∈ Φ, N : Subgroup G) : Set G) := by
  refine TWZ.le_normalizer_of_forall_conj_mem fun c hc y hy => ?_
  have hle : conjSub c (⨆ N ∈ Φ, N : Subgroup G) ≤ (⨆ N ∈ Φ, N : Subgroup G) := by
    unfold conjSub
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun L hL l hl => ?_
    have : conjSub c L ≤ (⨆ N ∈ Φ, N : Subgroup G) :=
      le_iSup₂_of_le (conjSub c L) (h c hc L hL) le_rfl
    exact this (conj_mem_conjSub hl)
  exact hle (conj_mem_conjSub hy)

theorem mem_normalizer_iSup_of_forall {Φ : Set (Subgroup G)} {k : G}
    (hk : ∀ N ∈ Φ, ∀ n ∈ N, k * n = n * k) :
    k ∈ Subgroup.normalizer ((⨆ N ∈ Φ, N : Subgroup G) : Set G) := by
  have hc : (⨆ N ∈ Φ, N : Subgroup G) ≤ Subgroup.centralizer ({k} : Set G) := by
    refine iSup₂_le fun N hN n hn => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hk N hN n hn).symm
  have hk' : k ∈ Subgroup.centralizer ((⨆ N ∈ Φ, N : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hc hy)
  exact Subgroup.centralizer_le_normalizer ((⨆ N ∈ Φ, N : Subgroup G) : Set G) hk'

end Normalizer

section Main

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K T : Subgroup G} {z : G} {tY : StatedLieTag} {nY : ℕ}


theorem false_of_member_containing_u (hnab : ∃ x y : G, x * y ≠ y * x)
    (S : RouteDSetup p f K z) (hrow : TwinRow tY nY)
    (hshape : LocalShapeT p f 2 tY nY (𝒞 K) z) (hT : IsTwinAt (𝒞 K) K T z)
    (clsT : IsClassicalMember p f T z) (e : TwinElt K T z) (hMF : TwinMFGeneration p f tY nY)
    {M : Subgroup G} (hM : M ∈ 𝒞 K) (huM : e.u ∈ M) : False := by
  classical
  have hcen : Subgroup.center G = ⊥ := CoreAssembly.center_eq_bot hnab
  have hKΩ : K ∈ 𝒞 K := CoreAssembly.mem_conjClass_self K
  have hKT' : Commutes K T := hT.comm_K T hT.mem hT.ne
  have hodd : Odd (Nat.card (GaloisField p f)) := odd_natCard_galoisField S.odd S.five
  have hKex := S.exact K hKΩ
  have hz2 : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two S.cls.orderOf_eq_two
  have hz1 : z ≠ 1 := ne_one_of_orderOf_eq_two S.cls.orderOf_eq_two
  have hu2 : e.u * e.u = 1 := e.u_mul_self hKT' hz2
  have hu1 : e.u ≠ 1 := e.u_ne_one S.cls hKex hodd hKT'
  have hzu : z * e.u = e.u * z :=
    (e.u_comm_z (le_centralizer_of_isClassicalMember S.cls)
      (le_centralizer_of_isClassicalMember clsT)).symm
  have hKz : K ∈ centralizingMembers (𝒞 K) {z} :=
    ⟨hKΩ, le_centralizer_of_isClassicalMember S.cls⟩
  have hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  obtain ⟨hG2, hD4, hnA1⟩ := hrow.tag_facts
  have rf := LocalShapeT.twinRowFacts hshape S.odd S.five hG2 hD4 hnA1
  obtain ⟨d⟩ := LocalShapeT.nonempty_dictT2 hD4 rf.fsc S.inClass hKΩ S.cls hshape
  obtain ⟨J, J', t, hJ, hJK, hJT, hJt, htz, -, -, -⟩ :=
    exists_frameMembers hnab S hrow hshape hT clsT e
  obtain ⟨A⟩ := exists_atT S hrow hshape hT clsT hJ hJK hJT hJt htz
  have hKu : ¬ K ≤ Subgroup.centralizer ({e.u} : Set G) :=
    e.not_le_centralizer_left S.cls hKex hodd hKT'
  have hΦu : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → N ≠ T →
      N ∈ centralizingMembers (𝒞 K) {e.u} := fun N hN hNK hNT =>
    e.mem_centralizingMembers_u hN.1 (hKiso N hN hNK).symm (hTiso N hN hNT).symm
  obtain ⟨g, hgM⟩ := CoreAssembly.single_class K M hM
  have hUg := (ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five S.cls).conj g
  rw [← hgM] at hUg
  have hgz : g * z * g⁻¹ = e.u := by
    rcases hUg.unique e.u huM hu2 with h | h
    · exact absurd h hu1
    · exact h.symm
  set Φ : Set (Subgroup G) :=
    {N | N ∈ centralizingMembers (𝒞 K) {z} ∧ N ≠ K ∧ N ≠ T} with hΦ
  set X : Subgroup G := ⨆ N ∈ Φ, N with hX
  set H : Subgroup G := Subgroup.normalizer (X : Set G) with hH
  have hΦle : ∀ N ∈ Φ, N ≤ X := fun N hN => le_iSup₂_of_le N hN le_rfl
  have hΦH : ∀ N ∈ Φ, N ≤ H := fun N hN => (hΦle N hN).trans Subgroup.le_normalizer
  have hnotu : ∀ N ∈ Φ, e.u ∉ N := by
    intro N hN huN
    apply hKu
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hKiso N hN.1 hN.2.1 k hk e.u huN
  have hPhiSub : Φ ⊆ (fun N => conjSub g N) '' Φ := by
    intro N hN
    have hNu := hΦu N hN.1 hN.2.1 hN.2.2
    refine ⟨conjSub g⁻¹ N, ⟨⟨S.inClass.conjInvariant g⁻¹ N hN.1.1, ?_⟩, ?_, ?_⟩,
      conjSub_conjSub_inv g N⟩
    · have := conjSub_le_centralizer_singleton hNu.2 g⁻¹
      rwa [show g⁻¹ * e.u * g⁻¹⁻¹ = z by rw [← hgz]; group] at this
    · intro h
      apply hnotu N hN
      have : N = conjSub g K := by rw [← h, conjSub_conjSub_inv]
      rw [this, ← hgM]
      exact huM
    · intro h
      apply hnotu N hN
      have : N = conjSub g T := by rw [← h, conjSub_conjSub_inv]
      rw [this]
      have := conj_mem_conjSub (n := g) clsT.mem
      rwa [hgz] at this
  have hΦeq : Φ = (fun N => conjSub g N) '' Φ :=
    Set.eq_of_subset_of_ncard_le hPhiSub (Set.ncard_image_le (Set.toFinite _)) (Set.toFinite _)
  have hconjmem : ∀ c ∈ Subgroup.centralizer ({z} : Set G), ∀ L ∈ centralizingMembers (𝒞 K) {z},
      conjSub c L ∈ centralizingMembers (𝒞 K) {z} := by
    intro c hc L hL
    have hcz : c * z * c⁻¹ = z := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hc]
      group
    have := centralizingMembers_conj S.inClass.conjInvariant c z
    rw [hcz] at this
    rw [this]
    exact ⟨L, hL, rfl⟩
  have hconjz : ∀ c ∈ Subgroup.centralizer ({z} : Set G), ∀ B ∈ centralizingMembers (𝒞 K) {z},
      (∀ L ∈ centralizingMembers (𝒞 K) {z}, L ≠ B → Commutes B L) →
      ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → N ≠ T → conjSub c N ≠ B := by
    intro c hc B hB hiso N hN hNK hNT hEq
    obtain ⟨L', hL', hL'N, hnc⟩ := exists_noncomm_of_ne S.inClass S.exact S.p1 rf d hKz hT.mem
      hT.ne.symm hKiso hTiso hN hNK hNT
    have hne : conjSub c L' ≠ B := by
      intro h
      apply hL'N
      apply conjSub_injective c
      rw [h, ← hEq]
    have hcomm := hiso _ (hconjmem c hc L' hL') hne
    rw [← hEq] at hcomm
    exact hnc ((commutes_conjSub_iff c).mp hcomm)
  have hCz : ∀ c ∈ Subgroup.centralizer ({z} : Set G), ∀ N ∈ Φ, conjSub c N ∈ Φ := by
    intro c hc N hN
    exact ⟨hconjmem c hc N hN.1, hconjz c hc K hKz hKiso N hN.1 hN.2.1 hN.2.2,
      hconjz c hc T hT.mem hTiso N hN.1 hN.2.1 hN.2.2⟩
  have hHz : Subgroup.centralizer ({z} : Set G) ≤ H := le_normalizer_iSup_of_forall hCz
  have hCu : ∀ c ∈ Subgroup.centralizer ({e.u} : Set G), ∀ N ∈ Φ, conjSub c N ∈ Φ := by
    intro c hc N hN
    have hN' : N ∈ (fun N => conjSub g N) '' Φ := hΦeq ▸ hN
    obtain ⟨N₀, hN₀, rfl⟩ := hN'
    have hcu : c * e.u * c⁻¹ = e.u := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hc]
      group
    have hc' : g⁻¹ * c * g ∈ Subgroup.centralizer ({z} : Set G) := by
      refine mem_centralizer_singleton_of_conj_eq ?_
      calc g⁻¹ * c * g * z * (g⁻¹ * c * g)⁻¹ = g⁻¹ * (c * (g * z * g⁻¹) * c⁻¹) * g := by group
        _ = g⁻¹ * (c * e.u * c⁻¹) * g := by rw [hgz]
        _ = g⁻¹ * e.u * g := by rw [hcu]
        _ = z := by rw [← hgz]; group
    have h1 : conjSub c (conjSub g N₀) = conjSub g (conjSub (g⁻¹ * c * g) N₀) := by
      rw [← conjSub_mul, ← conjSub_mul]
      congr 1
      group
    have h2 : conjSub g (conjSub (g⁻¹ * c * g) N₀) ∈ (fun N => conjSub g N) '' Φ :=
      ⟨_, hCz _ hc' N₀ hN₀, rfl⟩
    rw [h1]
    rw [← hΦeq] at h2
    exact h2
  have hHu : Subgroup.centralizer ({e.u} : Set G) ≤ H := le_normalizer_iSup_of_forall hCu
  have hKH : K ≤ H := by
    intro k hk
    exact mem_normalizer_iSup_of_forall fun N hN n hn =>
      hKiso N hN.1 hN.2.1 k hk n hn
  have hTH : T ≤ H := by
    intro k hk
    exact mem_normalizer_iSup_of_forall fun N hN n hn =>
      hTiso N hN.1 hN.2.2 k hk n hn
  obtain ⟨n, hnK, hna⟩ := TWZ.exists_inv_conj_of_exact S.cls hKex hodd e.mem_a e.mul_self_a
  have hna' : n * e.a' = e.a' * n := hKT' n hnK e.a' e.mem_a'
  have h1 : z * e.a = e.a⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [mul_assoc, e.mul_self_a, hz2])
  have hnu : n * e.u * n⁻¹ = z * e.u := by
    have e1 : n * e.u * n⁻¹ = (n * e.a * n⁻¹) * (n * e.a' * n⁻¹) := by
      unfold TwinElt.u
      group
    have e2 : n * e.a' * n⁻¹ = e.a' := by rw [hna']; group
    rw [e1, hna, e2, ← h1]
    unfold TwinElt.u
    group
  have hHzu : Subgroup.centralizer ({z * e.u} : Set G) ≤ H := by
    intro c hc
    have hc' : c * (z * e.u) = (z * e.u) * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    have hn1 : n * e.u = z * e.u * n := by
      calc n * e.u = n * e.u * n⁻¹ * n := by group
        _ = z * e.u * n := by rw [hnu]
    have hn2 : n⁻¹ * (z * e.u) = e.u * n⁻¹ := by
      calc n⁻¹ * (z * e.u) = n⁻¹ * (z * e.u * n) * n⁻¹ := by group
        _ = n⁻¹ * (n * e.u) * n⁻¹ := by rw [hn1]
        _ = e.u * n⁻¹ := by group
    have hdu : n⁻¹ * c * n ∈ Subgroup.centralizer ({e.u} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc n⁻¹ * c * n * e.u = n⁻¹ * c * (n * e.u) := by group
        _ = n⁻¹ * c * (z * e.u * n) := by rw [hn1]
        _ = n⁻¹ * (c * (z * e.u)) * n := by group
        _ = n⁻¹ * ((z * e.u) * c) * n := by rw [hc']
        _ = (n⁻¹ * (z * e.u)) * c * n := by group
        _ = e.u * n⁻¹ * c * n := by rw [hn2]
        _ = e.u * (n⁻¹ * c * n) := by group
    have hceq : c = n * (n⁻¹ * c * n) * n⁻¹ := by group
    rw [hceq]
    exact H.mul_mem (H.mul_mem (hKH hnK) (hHu hdu)) (H.inv_mem (hKH hnK))
  have hJΦ : J ∈ Φ := ⟨hJ, hJK, hJT⟩
  have hJ₂Φ : A.J₂ ∈ Φ := ⟨A.hJ₂z, A.hJ₂K, A.hJ₂T⟩
  have hYt : centralizingLayer (𝒞 K) {t} ≤ H := by
    refine iSup₂_le fun N hN => ?_
    by_cases hNJ : N = J
    · rw [hNJ]; exact hΦH J hJΦ
    by_cases hNJ₂ : N = A.J₂
    · rw [hNJ₂]; exact hΦH A.J₂ hJ₂Φ
    exact TWZ.member_t_le_of_centralizers S e hMF A H hHz hHu hHzu hz2 hu2 hzu hN hNJ hNJ₂
  have hYz : centralizingLayer (𝒞 K) {z} ≤ H := by
    refine iSup₂_le fun N hN => ?_
    by_cases hNK : N = K
    · rw [hNK]; exact hKH
    by_cases hNT : N = T
    · rw [hNT]; exact hTH
    exact hΦH N ⟨hN, hNK, hNT⟩
  have hneighK : ∀ L ∈ 𝒞 K, L ≠ K → Commutes K L →
      ∃ y ∈ H, L = conjSub y K ∨ L = conjSub y J := by
    intro L hL hLK hc
    have hLz : L ∈ centralizingMembers (𝒞 K) {z} :=
      ⟨hL, fun l hl => Subgroup.mem_centralizer_singleton_iff.mpr (hc z S.cls.mem l hl).symm⟩
    by_cases hLT : L = T
    · have hLt : L ∈ centralizingMembers (𝒞 K) {t} := hLT ▸ A.hTt
      have hLJ : L ≠ J := by rw [hLT]; exact hJT.symm
      have hLJ₂ : L ≠ A.J₂ := by rw [hLT]; exact A.hJ₂T.symm
      obtain ⟨y, hy, hyeq⟩ := link_big S.inClass S.exact A.hP1 A.rf A.d (K := J) (T := A.J₂)
        (L := K) (L' := L) A.hJt A.hJ₂t A.hJ₂J.symm A.hJiso A.hJ₂iso A.hKt hJK.symm
        A.hJ₂K.symm hLt hLJ hLJ₂
      exact ⟨y, hYt hy, Or.inl hyeq.symm⟩
    · obtain ⟨y, hy, hyeq⟩ := link_big S.inClass S.exact S.p1 rf d hKz hT.mem hT.ne.symm hKiso
        hTiso (L := J) (L' := L) hJ hJK hJT hLz hLK hLT
      exact ⟨y, hYz hy, Or.inr hyeq.symm⟩
  have hneighJ : ∀ L ∈ 𝒞 K, L ≠ J → Commutes J L →
      ∃ y ∈ H, L = conjSub y K ∨ L = conjSub y J := by
    intro L hL hLJ hc
    have hLt : L ∈ centralizingMembers (𝒞 K) {t} :=
      ⟨hL, fun l hl => Subgroup.mem_centralizer_singleton_iff.mpr (hc t hJt.mem l hl).symm⟩
    by_cases hLJ₂ : L = A.J₂
    · obtain ⟨y, hy, hyeq⟩ := link_big S.inClass S.exact S.p1 rf d hKz hT.mem hT.ne.symm hKiso
        hTiso (L := J) (L' := L) hJ hJK hJT (hLJ₂ ▸ A.hJ₂z) (by rw [hLJ₂]; exact A.hJ₂K)
        (by rw [hLJ₂]; exact A.hJ₂T)
      exact ⟨y, hYz hy, Or.inr hyeq.symm⟩
    · obtain ⟨y, hy, hyeq⟩ := link_big S.inClass S.exact A.hP1 A.rf A.d (K := J) (T := A.J₂)
        (L := K) (L' := L) A.hJt A.hJ₂t A.hJ₂J.symm A.hJiso A.hJ₂iso A.hKt hJK.symm
        A.hJ₂K.symm hLt hLJ hLJ₂
      exact ⟨y, hYt hy, Or.inl hyeq.symm⟩
  have hHtop : H = ⊤ :=
    TWZ.eq_top_of_closure S.inClass S.conn hKΩ hKH (hΦH J hJΦ) hneighK hneighJ
  have hnormal : X.Normal := Subgroup.normalizer_eq_top_iff.mp hHtop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal X with h | h
  · have hmem : t ∈ X := hΦle J hJΦ hJt.mem
    rw [h, Subgroup.mem_bot] at hmem
    exact ne_one_of_orderOf_eq_two hJt.orderOf_eq_two hmem
  · have hzc : z ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g'
      have hg' : g' ∈ X := by rw [h]; trivial
      have hc : X ≤ Subgroup.centralizer ({z} : Set G) := by
        refine iSup₂_le fun N hN n hn => ?_
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hKiso N hN.1 hN.2.1 z S.cls.mem n hn).symm
      exact Subgroup.mem_centralizer_singleton_iff.mp (hc hg')
    rw [hcen, Subgroup.mem_bot] at hzc
    exact hz1 hzc

end Main

end CFSG.ClassicalInvolution.RouteD.TWT4
