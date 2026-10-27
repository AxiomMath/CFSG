module

public import CFSG.ClassicalInvolution.RouteD.TWZLinkAux
public import CFSG.ClassicalInvolution.RouteD.TWZSpinModel
public import CFSG.ClassicalInvolution.RouteD.TWZZt
public import CFSG.ClassicalInvolution.RouteD.TWSLinked
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
public import CFSG.ClassicalInvolution.RouteD.TWZPair

public section

namespace CFSG.ClassicalInvolution.RouteD.TWZ

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.RouteD.NonClassical CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Balance
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => CoreAssembly.conjClass

set_option linter.unusedSectionVars false

section Link

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K T : Subgroup G} {z : G} {tY : StatedLieTag} {nY : ℕ}


theorem linked_of_model (hnab : ∃ x y : G, x * y ≠ y * x) (S : RouteDSetup p f K z)
    (hrow : TwinRow tY nY) (hshape : LocalShapeT p f 2 tY nY (𝒞 K) z)
    (hT : IsTwinAt (𝒞 K) K T z) (clsT : IsClassicalMember p f T z) (e : TwinElt K T z)
    (hMF : TwinMFGeneration p f tY nY) (hP1 : LocalOddCentral (𝒞 K) {e.u})
    (D : LieSystemData p f (locQuot (𝒞 K) e.u) (locFamily (𝒞 K) e.u)) (hcard : D.card = 1)
    (i : Fin D.card) (hDi : D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4)
    (hnc : ¬ (D.tag i = .PSL ∧ D.rank i = 2))
    (hmodel : SqTrichotomyOn (D.tag i)
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out))
    {K₂ : Subgroup G} (hK₂ : K₂ ∈ centralizingMembers (𝒞 K) {z}) (hK₂K : K₂ ≠ K)
    (hK₂T : K₂ ≠ T) {w : G} (hw : IsClassicalMember p f K₂ w) :
    LinkedAtProduct (𝒞 K) K z w := by
  classical
  obtain ⟨hexp, hperf, hperfK, hsurj⟩ := component_package S.odd S.five D hcard i hDi
  have hΩ : InClass p f (𝒞 K) := S.inClass
  have hKΩ : K ∈ 𝒞 K := CoreAssembly.mem_conjClass_self K
  have hz2 : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two S.cls.orderOf_eq_two
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) := le_centralizer_of_isClassicalMember S.cls
  have hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  have hncs : ∀ L ∈ 𝒞 K, ¬ Commutes L L := fun L hL => not_commutes_self_of_mem S.inClass hL
  obtain ⟨J, J₂, t, hJ, hJK, hJT, hJt, htz, hJ₂t, hJ₂J, hJ₂cls, hJ₂K, hJ₂T, hJiso⟩ :=
    exists_twin_frame hnab S hrow hshape hT clsT e
  have hJ₂z : J₂ ∈ centralizingMembers (𝒞 K) {z} :=
    ⟨hJ₂t.1, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
      (hJ₂K.symm z S.cls.mem y hy).symm⟩
  have hJ₂K' : J₂ ≠ K := fun h => hncs K hKΩ (by rw [h] at hJ₂K; exact hJ₂K)
  have hJ₂T' : J₂ ≠ T := fun h => hncs T hT.mem.1 (by rw [h] at hJ₂T; exact hJ₂T)
  have hΦu : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → N ≠ T →
      N ∈ centralizingMembers (𝒞 K) {e.u} := fun N hN hNK hNT =>
    e.mem_centralizingMembers_u hN.1 (hKiso N hN hNK).symm (hTiso N hN hNT).symm
  have hJu := hΦu J hJ hJK hJT
  have hJ₂u := hΦu J₂ hJ₂z hJ₂K' hJ₂T'
  have hK₂u := hΦu K₂ hK₂ hK₂K hK₂T
  have hJJ₂ : Commutes J J₂ := hJiso J₂ hJ₂t hJ₂J
  have hty : t ∈ locLayer (𝒞 K) e.u := le_centralizingLayer hJu hJt.mem
  have hwY : w ∈ locLayer (𝒞 K) e.u := le_centralizingLayer hK₂u hw.mem
  obtain ⟨RJ, RJ₂, xJ, xJ₂, hRJ, hRJ₂, hxJ, hxJ₂, hpair⟩ :=
    exists_twinPairOn hΩ S.exact hP1 D hcard i hperf hnc hperfK hJu hJ₂u hJ₂J.symm hJJ₂ hJt
      hJ₂cls
  obtain ⟨R₂, hR₂⟩ := TWY.exists_corr_of_card_one hΩ S.exact D hcard i hK₂u
  obtain ⟨x₂, hx₂R, hx₂⟩ := exists_model_elt hR₂ hw.mem
  have hw2 : locMk (𝒞 K) e.u ⟨w, hwY⟩ * locMk (𝒞 K) e.u ⟨w, hwY⟩ = 1 := by
    rw [← map_mul]
    have : (⟨w, hwY⟩ : ↥(locLayer (𝒞 K) e.u)) * ⟨w, hwY⟩ = 1 :=
      Subtype.ext (mul_self_eq_one_of_orderOf_eq_two hw.orderOf_eq_two)
    rw [this, map_one]
  have hw1 : locMk (𝒞 K) e.u ⟨w, hwY⟩ ≠ 1 := locMk_involution_ne_one hK₂u hw
  obtain ⟨hx₂2, hx₂1⟩ := involution_lift D i hnc hR₂.2.1 hx₂R hw2 hw1 hx₂
  have hac : e.a * e.u = e.u * e.a := by
    have hc : e.a * e.a' = e.a' * e.a := hT.comm_K T hT.mem hT.ne _ e.mem_a _ e.mem_a'
    unfold TwinElt.u
    calc e.a * (e.a * e.a') = e.a * (e.a' * e.a) := by rw [hc]
      _ = (e.a * e.a') * e.a := by group
  have hcN : e.a ∈ Subgroup.normalizer (locLayer (𝒞 K) e.u : Set G) :=
    centralizer_le_normalizer_centralizingLayer hΩ.conjInvariant e.u
      (Subgroup.mem_centralizer_singleton_iff.mpr hac)
  have hc4 : e.a * e.a * (e.a * e.a) = 1 := by rw [e.mul_self_a, hz2]
  have hccN : e.a * e.a ∈ Subgroup.normalizer (locLayer (𝒞 K) e.u : Set G) :=
    Subgroup.mul_mem _ hcN hcN
  have hzu : z * e.u = e.u * z :=
    (e.u_comm_z (le_centralizer_of_isClassicalMember S.cls)
      (le_centralizer_of_isClassicalMember clsT)).symm
  have hzN : z ∈ Subgroup.normalizer (locLayer (𝒞 K) e.u : Set G) :=
    centralizer_le_normalizer_centralizingLayer hΩ.conjInvariant e.u
      (Subgroup.mem_centralizer_singleton_iff.mpr hzu)
  set α : MulAut (locQuot (𝒞 K) e.u) := actX e.a hcN with hα
  have hα4 : α * α * (α * α) = 1 := actX_four_eq_one hcN hc4
  have hαz : actX z hzN = α * α := by
    rw [← actX_mul e.a e.a hcN hcN hccN]
    exact actX_congr e.mul_self_a.symm hzN hccN
  have hαfix : ∀ {N : Subgroup G}, (∀ n ∈ N, e.a * n = n * e.a) →
      ∀ g ∈ locImg (𝒞 K) e.u N, α g = g := fun {N} h g hg => actX_fix_of_commutes hcN h g hg
  have hαR : ∀ r ∈ RJ, α (D.hom i r) = D.hom i r := fun r hr =>
    hαfix (fun j hj => hKiso J hJ hJK e.a e.mem_a j hj) _
      (by rw [hRJ.2.2]; exact Subgroup.mem_map_of_mem _ hr)
  have hαR' : ∀ r ∈ RJ₂, α (D.hom i r) = D.hom i r := fun r hr =>
    hαfix (fun j hj => (hJ₂K j hj e.a e.mem_a).symm) _
      (by rw [hRJ₂.2.2]; exact Subgroup.mem_map_of_mem _ hr)
  have hαR₂ : ∀ r ∈ R₂, α (D.hom i r) = D.hom i r := fun r hr =>
    hαfix (fun j hj => hKiso K₂ hK₂ hK₂K e.a e.mem_a j hj) _
      (by rw [hR₂.2.2]; exact Subgroup.mem_map_of_mem _ hr)
  have hsame : D.hom i xJ = D.hom i xJ₂ := hxJ.trans hxJ₂.symm
  have hres := hmodel (locQuot (𝒞 K) e.u) (D.hom i) hsurj (D.ker_le_center i) RJ RJ₂ R₂
    hRJ.2.1 hRJ₂.2.1 hR₂.2.1 hpair.ne xJ xJ₂ x₂ hpair.hx hpair.hx2 hpair.hx1 hpair.hx'
    hpair.hx'2 hpair.hx'1 hsame hx₂R hx₂2 hx₂1 α hα4 hαR hαR' hαR₂
  rcases hres with h | h | ⟨g, hg1, r₁, hr₁, hg2⟩
  ·
    exact (false_of_layer_le_centralizer hnab S hrow hshape hT clsT e hMF fun N hN =>
      centralizes_of_actX_fix hΩ S.exact hP1 hzu hzN hN fun n hn => by
        rw [hαz, h]; rfl).elim
  ·
    refine (false_of_layer_le_centralizer_tz S hrow hshape hT e hJ hJK hJT hJiso
      fun N hN => ?_).elim
    have htu : t * e.u = e.u * t :=
      Subgroup.mem_centralizer_singleton_iff.mp (centralizingLayer_le_centralizer _ _ hty)
    have htN : t ∈ Subgroup.normalizer (locLayer (𝒞 K) e.u : Set G) :=
      centralizer_le_normalizer_centralizingLayer hΩ.conjInvariant e.u
        (Subgroup.mem_centralizer_singleton_iff.mpr htu)
    have htzu : t * z * e.u = e.u * (t * z) := by
      calc t * z * e.u = t * (z * e.u) := by group
        _ = t * (e.u * z) := by rw [hzu]
        _ = (t * e.u) * z := by group
        _ = (e.u * t) * z := by rw [htu]
        _ = e.u * (t * z) := by group
    have htzN : t * z ∈ Subgroup.normalizer (locLayer (𝒞 K) e.u : Set G) :=
      Subgroup.mul_mem _ htN hzN
    refine centralizes_of_actX_fix hΩ S.exact hP1 htzu htzN hN fun n hn => ?_
    rw [actX_mul t z htN hzN htzN, MulAut.mul_apply, hαz, h, MulAut.conj_apply,
      actX_eq_conj_of_mem hty htN, hxJ]
    set τ := locMk (𝒞 K) e.u ⟨t, hty⟩ with hτ
    have hτ2 : τ * τ = 1 := by
      rw [hτ, ← map_mul]
      have : (⟨t, hty⟩ : ↥(locLayer (𝒞 K) e.u)) * ⟨t, hty⟩ = 1 :=
        Subtype.ext (mul_self_eq_one_of_orderOf_eq_two hJt.orderOf_eq_two)
      rw [this, map_one]
    have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ2
    rw [hτinv]
    calc τ * (τ * locMk (𝒞 K) e.u ⟨n, le_centralizingLayer hN hn⟩ * τ) * τ
        = (τ * τ) * locMk (𝒞 K) e.u ⟨n, le_centralizingLayer hN hn⟩ * (τ * τ) := by group
      _ = locMk (𝒞 K) e.u ⟨n, le_centralizingLayer hN hn⟩ := by rw [hτ2]; group
  ·
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (D.hom i g)
    obtain ⟨hNmem, -⟩ := conjSub_mem_and_image hΩ hK₂u y
    set N : Subgroup G := conjSub (y : G) K₂ with hN
    have hNimg : locImg (𝒞 K) e.u N = (R₂.map (MulAut.conj g).toMonoidHom).map (D.hom i) := by
      rw [hN, locImg_conjSub_layer, hR₂.2.2, show locMk (𝒞 K) e.u y = D.hom i g from hy]
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext a
      simp
    have hNelem : ∀ (n : G) (hn : n ∈ N), ∃ r ∈ R₂,
        locMk (𝒞 K) e.u ⟨n, le_centralizingLayer hNmem hn⟩ = D.hom i (g * r * g⁻¹) := by
      intro n hn
      have hmem : locMk (𝒞 K) e.u ⟨n, le_centralizingLayer hNmem hn⟩ ∈ locImg (𝒞 K) e.u N :=
        ⟨_, Subgroup.mem_subgroupOf.mpr hn, rfl⟩
      rw [hNimg] at hmem
      obtain ⟨r', ⟨r, hr, rfl⟩, hr'⟩ := hmem
      exact ⟨r, hr, by rw [← hr']; simp [MulAut.conj_apply]⟩
    have hNelem' : ∀ r ∈ R₂, ∃ (n : G) (hn : n ∈ N),
        locMk (𝒞 K) e.u ⟨n, le_centralizingLayer hNmem hn⟩ = D.hom i (g * r * g⁻¹) := by
      intro r hr
      have hmem : D.hom i (g * r * g⁻¹) ∈ locImg (𝒞 K) e.u N := by
        rw [hNimg]
        exact Subgroup.mem_map_of_mem _ ⟨r, hr, by simp [MulAut.conj_apply]⟩
      obtain ⟨y₁, hy₁, hy₁'⟩ := hmem
      exact ⟨y₁, Subgroup.mem_subgroupOf.mp hy₁, hy₁'⟩
    have hwN : w ∈ Subgroup.normalizer (locLayer (𝒞 K) e.u : Set G) :=
      Subgroup.le_normalizer hwY
    have hzwN : z * w ∈ Subgroup.normalizer (locLayer (𝒞 K) e.u : Set G) :=
      Subgroup.mul_mem _ hzN hwN
    have hwu : w * e.u = e.u * w :=
      Subgroup.mem_centralizer_singleton_iff.mp (centralizingLayer_le_centralizer _ _ hwY)
    have hzwu : z * w * e.u = e.u * (z * w) := by
      calc z * w * e.u = z * (w * e.u) := by group
        _ = z * (e.u * w) := by rw [hwu]
        _ = (z * e.u) * w := by group
        _ = (e.u * z) * w := by rw [hzu]
        _ = e.u * (z * w) := by group
    have hNle : N ≤ Subgroup.centralizer ({z * w} : Set G) := by
      refine centralizes_of_actX_fix hΩ S.exact hP1 hzwu hzwN hNmem fun n hn => ?_
      obtain ⟨r, hr, hrn⟩ := hNelem n hn
      rw [hrn, actX_mul z w hzN hwN hzwN, MulAut.mul_apply, hαz,
        actX_eq_conj_of_mem hwY hwN, ← hx₂]
      exact hg1 r hr
    have hnz : ¬ N ≤ Subgroup.centralizer ({z} : Set G) := by
      intro hle
      obtain ⟨n₁, hn₁, hmk⟩ := hNelem' r₁ hr₁
      have hfix := actX_fix_of_commutes hzN (N := N)
        (fun n hn => (Subgroup.mem_centralizer_singleton_iff.mp (hle hn)).symm)
        (locMk (𝒞 K) e.u ⟨n₁, le_centralizingLayer hNmem hn₁⟩)
        ⟨_, Subgroup.mem_subgroupOf.mpr hn₁, rfl⟩
      rw [hαz, hmk] at hfix
      exact hg2 hfix
    exact (TWS.linkedAtProduct_iff S.cls.mem hKz hKiso).mpr ⟨N, ⟨hNmem.1, hNle⟩, hnz⟩

end Link

end CFSG.ClassicalInvolution.RouteD.TWZ
