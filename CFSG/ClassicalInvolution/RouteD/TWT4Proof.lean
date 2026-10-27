module

public import CFSG.ClassicalInvolution.RouteD.TWT4Final
public import CFSG.ClassicalInvolution.RouteD.TWT4Act
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
  CFSG.ClassicalInvolution.RouteD.TWZ CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Balance
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => CoreAssembly.conjClass

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.RouteD.TWT4

section Proof

variable {p f : ℕ} [Fact p.Prime]

theorem visible_wut_eq_one (hmod : (p ^ f) % 4 = 3) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x) {K T J : Subgroup G} {z t : G}
    (S : RouteDSetup p f K z) (hshape : LocalShapeT p f 2 .PSU 4 (𝒞 K) z)
    (hT : IsTwinAt (𝒞 K) K T z) (clsT : IsClassicalMember p f T z) (e : TwinElt K T z)
    (hJ : J ∈ centralizingMembers (𝒞 K) {z}) (hJK : J ≠ K) (hJT : J ≠ T)
    (hJt : IsClassicalMember p f J t) (A : AtT p f K T J z t .PSU 4) {M : Subgroup G}
    (hMu : M ∈ centralizingMembers (𝒞 K) {e.u}) (hMt : M ∈ centralizingMembers (𝒞 K) {t})
    (hMJ : M ≠ J) (hMJ₂ : M ≠ A.J₂) {w : G} (hw : IsClassicalMember p f M w) :
    w * e.u * t = 1 := by
  have hrow : TwinRow .PSU 4 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))))
  have htz : t ≠ z := involution_ne_of_member hnab S hrow hshape hT hJ hJK hJT hJt
  have hKT' : Commutes K T := hT.comm_K T hT.mem hT.ne
  have hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  have hΦu : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → N ≠ T →
      N ∈ centralizingMembers (𝒞 K) {e.u} := fun N hN hNK hNT =>
    e.mem_centralizingMembers_u hN.1 (hKiso N hN hNK).symm (hTiso N hN hNT).symm
  have hJu := hΦu J hJ hJK hJT
  have hJ₂u := hΦu A.J₂ A.hJ₂z A.hJ₂K A.hJ₂T
  have hcent := visible_involution_central hmod S e hT A hJu hJ₂u hMu hMt hMJ hMJ₂ hw
  have hz2 : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two S.cls.orderOf_eq_two
  have hu2 : e.u * e.u = 1 := e.u_mul_self hKT' hz2
  have hw2 : w * w = 1 := mul_self_eq_one_of_orderOf_eq_two hw.orderOf_eq_two
  have ht2 : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two hJt.orderOf_eq_two
  have hwu : w * e.u = e.u * w := Subgroup.mem_centralizer_singleton_iff.mp (hMu.2 hw.mem)
  have hwt : w * t = t * w := Subgroup.mem_centralizer_singleton_iff.mp (hMt.2 hw.mem)
  have hut : e.u * t = t * e.u :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hJu.2 hJt.mem)).symm
  have hdc : ∀ y ∈ centralizingLayer (𝒞 K) {t}, (w * e.u * t) * y = y * (w * e.u * t) := by
    intro y hy
    have h1 := hcent y hy
    have h2 : y * t = t * y :=
      Subgroup.mem_centralizer_singleton_iff.mp (centralizingLayer_le_centralizer (𝒞 K) {t} hy)
    calc (w * e.u * t) * y = (w * e.u) * (t * y) := by group
      _ = (w * e.u) * (y * t) := by rw [h2]
      _ = ((w * e.u) * y) * t := by group
      _ = (y * (w * e.u)) * t := by rw [h1]
      _ = y * (w * e.u * t) := by group
  obtain ⟨c, hcM, hcc, hcz⟩ := exists_sqrt_visible hmod S e A hMu hMt hMJ hMJ₂ hw
  have hc4 : c * c * (c * c) = 1 := by rw [hcc, hw2]
  have hcJ : ∀ j ∈ J, c * j = j * c := fun j hj => (A.hJiso M hMt hMJ j hj c hcM).symm
  have hcJ₂ : ∀ j ∈ A.J₂, c * j = j * c := fun j hj =>
    (A.hJ₂iso M hMt hMJ₂ j hj c hcM).symm
  have hΦ : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → N ≠ T → ∀ n ∈ N,
      n * e.u = e.u * n := fun N hN hNK hNT n hn =>
    Subgroup.mem_centralizer_singleton_iff.mp ((hΦu N hN hNK hNT).2 hn)
  have hfinish : ∀ s : G, (∀ N ∈ centralizingMembers (𝒞 K) {z}, ∀ n ∈ N, s * n = n * s) →
      (∀ y ∈ centralizingLayer (𝒞 K) {t}, s * y = y * s) → s = 1 := by
    intro s hsN hst
    have hle : centralizingLayer (𝒞 K) {z} ≤ Subgroup.centralizer ({s} : Set G) :=
      iSup₂_le fun N hN n hn =>
        Subgroup.mem_centralizer_singleton_iff.mpr (hsN N hN n hn).symm
    exact eq_one_of_centralizes_layers hnab S hrow hshape hT clsT hJ hJK hJT hJt s
      (fun y hy => (Subgroup.mem_centralizer_singleton_iff.mp (hle hy)).symm) hst
  have hKt' : ∀ n ∈ K, n ∈ centralizingLayer (𝒞 K) {t} := fun n hn =>
    le_centralizingLayer A.hKt hn
  have hTt' : ∀ n ∈ T, n ∈ centralizingLayer (𝒞 K) {t} := fun n hn =>
    le_centralizingLayer A.hTt hn
  have hd : (w * e.u * t = 1) ∨ (w * e.u * t = t) := by
    rcases sq_central_or_t S hrow (Or.inr (Or.inr ⟨rfl, rfl⟩)) hshape hT clsT hJ hJK hJT hJt
      htz A hcz hcJ hcJ₂ hc4 with hA | hB
    ·
      right
      have hs : w * e.u = 1 := by
        refine hfinish (w * e.u) ?_ hcent
        intro N hN n hn
        by_cases hNK : N = K
        · rw [hNK] at hn
          exact hcent n (hKt' n hn)
        by_cases hNT : N = T
        · rw [hNT] at hn
          exact hcent n (hTt' n hn)
        have hnw : n * w = w * n := by
          have := Subgroup.mem_centralizer_singleton_iff.mp (hA N hN hNK hNT hn)
          rwa [hcc] at this
        calc w * e.u * n = w * (e.u * n) := by group
          _ = w * (n * e.u) := by rw [hΦ N hN hNK hNT n hn]
          _ = (w * n) * e.u := by group
          _ = (n * w) * e.u := by rw [hnw]
          _ = n * (w * e.u) := by group
      rw [hs, one_mul]
    ·
      left
      refine hfinish (w * e.u * t) ?_ hdc
      intro N hN n hn
      by_cases hNK : N = K
      · rw [hNK] at hn
        exact hdc n (hKt' n hn)
      by_cases hNT : N = T
      · rw [hNT] at hn
        exact hdc n (hTt' n hn)
      have hnwt : n * (w * t) = (w * t) * n := by
        have := Subgroup.mem_centralizer_singleton_iff.mp (hB N hN hNK hNT hn)
        rwa [hcc] at this
      have hs : w * e.u * t = (w * t) * e.u := by
        calc w * e.u * t = w * (e.u * t) := by group
          _ = w * (t * e.u) := by rw [hut]
          _ = (w * t) * e.u := by group
      rw [hs]
      calc (w * t * e.u) * n = (w * t) * (e.u * n) := by group
        _ = (w * t) * (n * e.u) := by rw [hΦ N hN hNK hNT n hn]
        _ = ((w * t) * n) * e.u := by group
        _ = (n * (w * t)) * e.u := by rw [hnwt]
        _ = n * (w * t * e.u) := by group
  rcases hd with h1 | h2
  · exact h1
  ·
    exfalso
    have hwu1 : w * e.u = 1 := by
      simpa using congrArg (· * t⁻¹) h2
    have huM : e.u ∈ M := by
      rw [eq_inv_of_mul_eq_one_right hwu1]
      exact M.inv_mem hw.mem
    exact false_of_member_containing_u hnab S hrow hshape hT clsT e
      (twinMFGeneration_psu4 S.odd S.five) hMu.1 huM

theorem twinSU4Fusion_proved : TwinSU4Fusion p f := by
  intro hmod G _ _ _ hnab K z S hshape T hT clsT e J t hJ hJK hJT hJt
  have hrow : TwinRow .PSU 4 := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))))
  have htz : t ≠ z := involution_ne_of_member hnab S hrow hshape hT hJ hJK hJT hJt
  obtain ⟨A⟩ := exists_atT S hrow hshape hT clsT hJ hJK hJT hJt htz
  have hKΩ : K ∈ 𝒞 K := CoreAssembly.mem_conjClass_self K
  have hKT' : Commutes K T := hT.comm_K T hT.mem hT.ne
  have hodd : Odd (Nat.card (GaloisField p f)) := odd_natCard_galoisField S.odd S.five
  have hKex := S.exact K hKΩ
  have hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  have hΦu : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → N ≠ T →
      N ∈ centralizingMembers (𝒞 K) {e.u} := fun N hN hNK hNT =>
    e.mem_centralizingMembers_u hN.1 (hKiso N hN hNK).symm (hTiso N hN hNT).symm
  have hJu := hΦu J hJ hJK hJT
  have hz2 : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two S.cls.orderOf_eq_two
  have hu2 : e.u * e.u = 1 := e.u_mul_self hKT' hz2
  have ht2 : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two hJt.orderOf_eq_two
  have hut : e.u * t = t * e.u :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hJu.2 hJt.mem)).symm
  obtain ⟨M, M₂, hMu, -, hMt, -, hMJ, hMJ₂, -, -, -, -, -⟩ := exists_visible_three hmod S e A
  obtain ⟨w, hw⟩ := S.inClass.classical M hMu.1
  have h1 := visible_wut_eq_one hmod hnab S hshape hT clsT e hJ hJK hJT hJt A hMu hMt hMJ hMJ₂ hw
  have hwut : w = e.u * t := by
    have h : w * (e.u * t) = 1 := by rw [← mul_assoc]; exact h1
    have h' : w = (e.u * t)⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [h', mul_inv_rev, inv_eq_of_mul_eq_one_right ht2, inv_eq_of_mul_eq_one_right hu2]
    exact hut.symm
  have hMK : ¬ Commutes M K := by
    intro hc
    apply e.not_le_centralizer_left S.cls hKex hodd hKT'
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h3 : k * w = w * k := (hc w hw.mem k hk).symm
    have h4 : k * t = t * k := Subgroup.mem_centralizer_singleton_iff.mp (A.hKt.2 hk)
    have hu : e.u = w * t := by rw [hwut, mul_assoc, ht2, mul_one]
    rw [hu]
    calc k * (w * t) = (k * w) * t := by group
      _ = (w * k) * t := by rw [h3]
      _ = w * (k * t) := by group
      _ = w * (t * k) := by rw [h4]
      _ = (w * t) * k := by group
  exact fusion_of_visible_involution S e hT hJ hJK hJt A hMt hMK hw hwut

theorem twinSU4Three_proved (hΩall : HypOmegaModAll p f) (hAE : AEmptyTwinExact p f)
    (hcls : TwinInvolution p f) (hP4 : Ih8G2D4 p f) (hH : TwinFrameHyp51 p f) :
    TwinSU4Three p f :=
  twinSU4Three_of_fusion hΩall hAE hcls hP4 hH twinSU4Fusion_proved

end Proof

end CFSG.ClassicalInvolution.RouteD.TWT4
