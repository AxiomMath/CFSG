module

public import CFSG.ClassicalInvolution.RouteD.TWZConj
public import CFSG.ClassicalInvolution.RouteD.TWZLayer
public import CFSG.ClassicalInvolution.RouteD.TWZClosure
public import CFSG.ClassicalInvolution.RouteD.TwinYR2AtT
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

namespace CFSG.ClassicalInvolution.RouteD.TWZ

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => CoreAssembly.conjClass

set_option linter.unusedSectionVars false

section Member

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K T J : Subgroup G}
  {z t : G} {tY : StatedLieTag} {nY : ℕ}


theorem member_t_le_of_centralizers (S : RouteDSetup p f K z) (e : TwinElt K T z)
    (hMF : TwinMFGeneration p f tY nY) (A : AtT p f K T J z t tY nY) (H : Subgroup G)
    (hHz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hHu : Subgroup.centralizer ({e.u} : Set G) ≤ H)
    (hHzu : Subgroup.centralizer ({z * e.u} : Set G) ≤ H) (hz2 : z * z = 1)
    (hu2 : e.u * e.u = 1) (hzu : z * e.u = e.u * z) {N : Subgroup G}
    (hN : N ∈ centralizingMembers (𝒞 K) {t}) (hNJ : N ≠ J) (hNJ₂ : N ≠ A.J₂) : N ≤ H := by
  obtain ⟨ã, hãR, ã', hã'R, hsq, hsq', huY, hψu⟩ := exists_lifts A e
  obtain ⟨RN, hRN, hNR⟩ := big_of_ne S.inClass S.exact A.hP1 A.rf A.d A.hJt A.hJ₂t A.hJ₂J.symm
    A.hJiso A.hJ₂iso hN hNJ hNJ₂
  have hgen := hMF A.RK A.RT A.x A.x' A.hdat ã hãR ã' hã'R hsq hsq' RN hRN
  set w₁ : ↥(locLayer (𝒞 K) t) := ⟨z, A.hzY⟩ with hw₁
  set w₂ : ↥(locLayer (𝒞 K) t) := ⟨e.u, huY⟩ with hw₂
  have hzu2 : z * e.u * (z * e.u) = 1 := by
    calc z * e.u * (z * e.u) = z * (e.u * z) * e.u := by group
      _ = z * (z * e.u) * e.u := by rw [← hzu]
      _ = (z * z) * (e.u * e.u) := by group
      _ = 1 := by rw [hz2, hu2, one_mul]
  have hw₁₁ : w₁ * w₁ = 1 := Subtype.ext hz2
  have hw₂₂ : w₂ * w₂ = 1 := Subtype.ext hu2
  have hw₃₃ : w₁ * w₂ * (w₁ * w₂) = 1 := Subtype.ext hzu2
  have hψ₃ : A.d.ψ (A.x * (ã * ã')) = locMk (𝒞 K) t (w₁ * w₂) := by
    rw [map_mul, A.hxz, hψu, ← map_mul]
  have hloc : locImg (𝒞 K) t N ≤
      ((Subgroup.centralizer ({w₁} : Set ↥(locLayer (𝒞 K) t)) ⊔
        Subgroup.centralizer ({w₂} : Set ↥(locLayer (𝒞 K) t))) ⊔
        Subgroup.centralizer ({w₁ * w₂} : Set ↥(locLayer (𝒞 K) t))).map (locMk (𝒞 K) t) := by
    rw [hNR, Subgroup.map_sup, Subgroup.map_sup]
    refine (Subgroup.map_mono hgen).trans ?_
    rw [Subgroup.map_sup, Subgroup.map_sup]
    exact sup_le_sup (sup_le_sup (map_centralizer_le_locMk hw₁₁ A.d.ψ A.hxz)
      (map_centralizer_le_locMk hw₂₂ A.d.ψ hψu)) (map_centralizer_le_locMk hw₃₃ A.d.ψ hψ₃)
  have hsub := subgroupOf_le_of_locImg_le S.inClass A.hP1 hN hloc
  intro n hn
  have hnY : n ∈ locLayer (𝒞 K) t := le_centralizingLayer hN hn
  have hmem := hsub (Subgroup.mem_subgroupOf.mpr hn :
    (⟨n, hnY⟩ : ↥(locLayer (𝒞 K) t)) ∈ N.subgroupOf (locLayer (𝒞 K) t))
  have hle : ((Subgroup.centralizer ({w₁} : Set ↥(locLayer (𝒞 K) t)) ⊔
        Subgroup.centralizer ({w₂} : Set ↥(locLayer (𝒞 K) t))) ⊔
        Subgroup.centralizer ({w₁ * w₂} : Set ↥(locLayer (𝒞 K) t))) ≤
      H.comap (locLayer (𝒞 K) t).subtype := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro y hy
      refine hHz ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)
    · intro y hy
      refine hHu ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)
    · intro y hy
      refine hHzu ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)
  exact hle hmem

end Member

section Main

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K T : Subgroup G} {z : G} {tY : StatedLieTag} {nY : ℕ}


theorem false_of_layer_le_centralizer (hnab : ∃ x y : G, x * y ≠ y * x)
    (S : RouteDSetup p f K z) (hrow : TwinRow tY nY)
    (hshape : LocalShapeT p f 2 tY nY (𝒞 K) z) (hT : IsTwinAt (𝒞 K) K T z)
    (clsT : IsClassicalMember p f T z) (e : TwinElt K T z) (hMF : TwinMFGeneration p f tY nY)
    (hZ : ∀ N ∈ centralizingMembers (𝒞 K) {e.u}, N ≤ Subgroup.centralizer ({z} : Set G)) :
    False := by
  classical
  have hcen : Subgroup.center G = ⊥ := CoreAssembly.center_eq_bot hnab
  have hKΩ : K ∈ 𝒞 K := CoreAssembly.mem_conjClass_self K
  have hKT' : Commutes K T := hT.comm_K T hT.mem hT.ne
  have hodd : Odd (Nat.card (GaloisField p f)) := odd_natCard_galoisField S.odd S.five
  have hKex := S.exact K hKΩ
  have hTex := S.exact T hT.mem.1
  have hz2 : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two S.cls.orderOf_eq_two
  have hz1 : z ≠ 1 := ne_one_of_orderOf_eq_two S.cls.orderOf_eq_two
  have hu2 : e.u * e.u = 1 := e.u_mul_self hKT' hz2
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
  have hKu : K ∉ centralizingMembers (𝒞 K) {e.u} :=
    e.not_mem_centralizingMembers_left S.cls hKex hodd hKT'
  have hTu : T ∉ centralizingMembers (𝒞 K) {e.u} :=
    e.not_mem_centralizingMembers_right clsT hTex hodd hKT'
  have hΦu : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → N ≠ T →
      N ∈ centralizingMembers (𝒞 K) {e.u} := fun N hN hNK hNT =>
    e.mem_centralizingMembers_u hN.1 (hKiso N hN hNK).symm (hTiso N hN hNT).symm
  have hΩuz : ∀ N ∈ centralizingMembers (𝒞 K) {e.u},
      N ∈ centralizingMembers (𝒞 K) {z} ∧ N ≠ K ∧ N ≠ T := fun N hN =>
    ⟨⟨hN.1, hZ N hN⟩, fun h => hKu (h ▸ hN), fun h => hTu (h ▸ hN)⟩
  set Y : Subgroup G := centralizingLayer (𝒞 K) {e.u} with hY
  set H : Subgroup G := Subgroup.normalizer (Y : Set G) with hH
  have hHu : Subgroup.centralizer ({e.u} : Set G) ≤ H :=
    centralizer_le_normalizer_centralizingLayer S.inClass.conjInvariant e.u
  have hΦH : ∀ N ∈ centralizingMembers (𝒞 K) {e.u}, N ≤ H := fun N hN =>
    (le_centralizingLayer hN).trans Subgroup.le_normalizer
  have hKH : K ≤ H := by
    intro k hk
    refine mem_normalizer_centralizingLayer_of_forall fun N hN n hn => ?_
    obtain ⟨hNz, hNK, -⟩ := hΩuz N hN
    exact hKiso N hNz hNK k hk n hn
  have hTH : T ≤ H := by
    intro k hk
    refine mem_normalizer_centralizingLayer_of_forall fun N hN n hn => ?_
    obtain ⟨hNz, -, hNT⟩ := hΩuz N hN
    exact hTiso N hNz hNT k hk n hn
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
  have hHz : Subgroup.centralizer ({z} : Set G) ≤ H := by
    refine le_normalizer_centralizingLayer_of_forall fun c hc N hN => ?_
    obtain ⟨hNz, hNK, hNT⟩ := hΩuz N hN
    exact hΦu _ (hconjmem c hc N hNz) (hconjz c hc K hKz hKiso N hNz hNK hNT)
      (hconjz c hc T hT.mem hTiso N hNz hNK hNT)
  obtain ⟨n, hnK, hna⟩ := exists_inv_conj_of_exact S.cls hKex hodd e.mem_a e.mul_self_a
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
  have hJu : J ∈ centralizingMembers (𝒞 K) {e.u} := hΦu J hJ hJK hJT
  have hJ₂u : A.J₂ ∈ centralizingMembers (𝒞 K) {e.u} := hΦu A.J₂ A.hJ₂z A.hJ₂K A.hJ₂T
  have hYt : centralizingLayer (𝒞 K) {t} ≤ H := by
    refine iSup₂_le fun N hN => ?_
    by_cases hNJ : N = J
    · rw [hNJ]; exact hΦH J hJu
    by_cases hNJ₂ : N = A.J₂
    · rw [hNJ₂]; exact hΦH A.J₂ hJ₂u
    exact member_t_le_of_centralizers S e hMF A H hHz hHu hHzu hz2 hu2 hzu hN hNJ hNJ₂
  have hYz : centralizingLayer (𝒞 K) {z} ≤ H := by
    refine iSup₂_le fun N hN => ?_
    by_cases hNK : N = K
    · rw [hNK]; exact hKH
    by_cases hNT : N = T
    · rw [hNT]; exact hTH
    exact hΦH N (hΦu N hN hNK hNT)
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
  have hHtop : H = ⊤ := eq_top_of_closure S.inClass S.conn hKΩ hKH (hΦH J hJu) hneighK hneighJ
  have hnormal : Y.Normal := Subgroup.normalizer_eq_top_iff.mp hHtop
  have := hnormal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Y with h | h
  · have hmem : t ∈ Y := le_centralizingLayer hJu hJt.mem
    rw [h, Subgroup.mem_bot] at hmem
    exact ne_one_of_orderOf_eq_two hJt.orderOf_eq_two hmem
  · have hzc : z ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hgY : g ∈ Y := by rw [h]; trivial
      have hk : ∀ N ∈ centralizingMembers (𝒞 K) {e.u}, ∀ n ∈ N, z * n = n * z := fun N hN n hn =>
        (Subgroup.mem_centralizer_singleton_iff.mp (hZ N hN hn)).symm
      have h2 := conj_eq_of_forall_mem hk hgY
      calc g * z = z * g * z⁻¹ * z := by rw [h2]
        _ = z * g := by group
    rw [hcen, Subgroup.mem_bot] at hzc
    exact hz1 hzc

end Main

end CFSG.ClassicalInvolution.RouteD.TWZ
