module

public import CFSG.ClassicalInvolution.Q3.Q3TLKAct
public import CFSG.ClassicalInvolution.RouteD.TWZSpinModel
public import CFSG.ClassicalInvolution.RouteD.TWSLinked
public import CFSG.ClassicalInvolution.Q3.Q3WAComp
public import CFSG.ClassicalInvolution.Q3.Q3WShape
public import CFSG.ClassicalInvolution.Q3.Q3WADict
public import CFSG.ClassicalInvolution.Q3.Q3WAEDict
public import CFSG.ClassicalInvolution.Q3.Q3WMain
public import CFSG.ClassicalInvolution.RouteD.TWZLinkAux
public import CFSG.ClassicalInvolution.RouteD.TWZPair

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TLK

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TWZ
  CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.RouteD.TwinY (IsTwinAt TwinElt TwinElt.u)
open CFSG.ClassicalInvolution.Generic.CoreAssembly (LinkedAtProduct)
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.LieType.Universal (LieUniversal)
open CFSG.ClassicalInvolution.Q3 (CompData IsClassicalMember3)

@[expose] def SqTrichotomyC (c : CompData) : Prop :=
  ∀ (X : Type) [Group X] (θ : c.G →* X), Function.Surjective θ → θ.ker ≤ Subgroup.center c.G →
    ∀ (R R' R₂ : Subgroup c.G), R ∈ c.fund → R' ∈ c.fund → R₂ ∈ c.fund → R ≠ R' →
      ∀ (x x' x₂ : c.G), x ∈ R → x * x = 1 → x ≠ 1 → x' ∈ R' → x' * x' = 1 → x' ≠ 1 →
        θ x = θ x' → x₂ ∈ R₂ → x₂ * x₂ = 1 → x₂ ≠ 1 →
        ∀ α : MulAut X, α * α * (α * α) = 1 → (∀ r ∈ R, α (θ r) = θ r) →
          (∀ r ∈ R', α (θ r) = θ r) → (∀ r ∈ R₂, α (θ r) = θ r) →
          α * α = 1 ∨ α * α = MulAut.conj (θ x) ∨
            ∃ g : c.G,
              (∀ r ∈ R₂, (α * α) (θ x₂ * θ (g * r * g⁻¹) * (θ x₂)⁻¹) = θ (g * r * g⁻¹)) ∧
                ∃ r ∈ R₂, (α * α) (θ (g * r * g⁻¹)) ≠ θ (g * r * g⁻¹)

theorem sqTrichotomyC_of_on {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {M : LieUniversal}
    (h : SqTrichotomyOn t M) : SqTrichotomyC ⟨M.K, fundamentalSubgroups t M.D⟩ := h


section Aux

theorem mul_self_eq_one_of_orderOf_eq_two3 {M : Type} [Group M] {g : M} (h : orderOf g = 2) :
    g * g = 1 := by
  rw [← pow_two]
  exact orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq h)

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G} {ι : Type}

theorem locMk_involution_ne_one3 {L : Subgroup G} {w : G}
    (hL : L ∈ centralizingMembers Ω {x}) (hw : IsClassicalMember3 L w) :
    locMk Ω x ⟨w, le_centralizingLayer hL hw.mem⟩ ≠ 1 := by
  intro h1
  set wY : ↥(locLayer Ω x) := ⟨w, le_centralizingLayer hL hw.mem⟩ with hwY
  have hwO : wY ∈ classicalInvolutionOddCore ↥(locLayer Ω x) := (QuotientGroup.eq_one_iff wY).mp h1
  have h2 : orderOf wY = 2 := by
    rw [hwY, Subgroup.orderOf_mk]
    exact hw.orderOf_eq_two
  have h3 : orderOf (⟨wY, hwO⟩ : classicalInvolutionOddCore ↥(locLayer Ω x)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact h2
  have h4 := orderOf_dvd_natCard (⟨wY, hwO⟩ : classicalInvolutionOddCore ↥(locLayer Ω x))
  rw [h3] at h4
  exact (Nat.not_even_iff_odd.mpr (CFSG.ComponentClassification.OddCore.odd_card _))
    (even_iff_two_dvd.mpr h4)

theorem involution_lift3 {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData3 ι X Φ) (i : ι)
    (hnc : ∀ R ∈ (D.kind i).fund, ∀ r ∈ R, r ∈ Subgroup.center (D.kind i).G → r = 1)
    {R : Subgroup (D.kind i).G} (hR : R ∈ (D.kind i).fund) {y : (D.kind i).G} (hy : y ∈ R)
    {g : X} (hg2 : g * g = 1) (hg1 : g ≠ 1) (h : D.hom i y = g) : y * y = 1 ∧ y ≠ 1 := by
  have h1 : D.hom i (y * y) = 1 := by rw [map_mul, h, hg2]
  have hker : y * y ∈ Subgroup.center (D.kind i).G :=
    D.ker_le_center i (MonoidHom.mem_ker.mpr h1)
  exact ⟨hnc R hR (y * y) (R.mul_mem hy hy) hker, fun h3 => hg1 (by rw [← h, h3, map_one])⟩

theorem exists_model_elt3 {D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)} {i : ι}
    {K : Subgroup G} {R : Subgroup (D.kind i).G} (hK : Corr3 Ω x D i K R) {z : G} (hz : z ∈ K) :
    ∃ k ∈ R, D.hom i k = locMk Ω x ⟨z, le_centralizingLayer hK.1 hz⟩ := by
  have hKY : z ∈ locLayer Ω x := le_centralizingLayer hK.1 hz
  have hmem : locMk Ω x ⟨z, hKY⟩ ∈ locImg Ω x K := ⟨_, Subgroup.mem_subgroupOf.mpr hz, rfl⟩
  have e := hK.2.2
  rw [e] at hmem
  obtain ⟨k, hkR, hk⟩ := hmem
  exact ⟨k, hkR, hk⟩

theorem hom_surjective_of_unique {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData3 ι X Φ) (i : ι) (hone : ∀ j : ι, j = i) :
    Function.Surjective (D.hom i) := by
  have h := D.generate
  have h2 : (⨆ j, (D.hom j).range) = (D.hom i).range := by
    refine le_antisymm (iSup_le fun j => ?_) (le_iSup (fun j => (D.hom j).range) i)
    rw [hone j]
  rw [h2] at h
  exact MonoidHom.range_eq_top.mp h

end Aux


section Main

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K T : Subgroup G} {z : G}

theorem linked_of_model3 (hR : RouteD3Setup K z) (hT : IsTwinAt (conjClass3 K) K T z)
    (clsT : IsClassicalMember3 T z) (e : TwinElt K T z) (hP1 : LocalOddCentral (conjClass3 K) {e.u})
    (hO3 : LocalOddThreeFree3 (conjClass3 K) e.u) {ι : Type}
    (D : LieSystemData3 ι (locQuot (conjClass3 K) e.u) (locFamily (conjClass3 K) e.u)) (i : ι)
    (hone : ∀ j : ι, j = i)
    (hnc : ∀ R ∈ (D.kind i).fund, ∀ r ∈ R, r ∈ Subgroup.center (D.kind i).G → r = 1)
    (hmodel : SqTrichotomyC (D.kind i))
    (hframe : ∃ (J J₂ : Subgroup G) (t : G), J ∈ centralizingMembers (conjClass3 K) {z} ∧
      J ≠ K ∧ J ≠ T ∧ IsClassicalMember3 J t ∧ t ≠ z ∧
      J₂ ∈ centralizingMembers (conjClass3 K) {t} ∧ J₂ ≠ J ∧ IsClassicalMember3 J₂ t ∧
      Commutes J₂ K ∧ Commutes J₂ T ∧
      (∀ L ∈ centralizingMembers (conjClass3 K) {t}, L ≠ J → Commutes J L))
    (hF1 : (∀ N ∈ centralizingMembers (conjClass3 K) {e.u},
      N ≤ Subgroup.centralizer ({z} : Set G)) → False)
    (hF2 : ∀ (J : Subgroup G) (t : G), J ∈ centralizingMembers (conjClass3 K) {z} → J ≠ K →
      J ≠ T → (∀ L ∈ centralizingMembers (conjClass3 K) {t}, L ≠ J → Commutes J L) →
      (∀ N ∈ centralizingMembers (conjClass3 K) {e.u},
        N ≤ Subgroup.centralizer ({t * z} : Set G)) → False)
    {K₂ : Subgroup G} (hK₂ : K₂ ∈ centralizingMembers (conjClass3 K) {z}) (hK₂K : K₂ ≠ K)
    (hK₂T : K₂ ≠ T) {w : G} (hw : IsClassicalMember3 K₂ w) :
    LinkedAtProduct (conjClass3 K) K z w := by
  classical
  have hΩ : InClass3 (conjClass3 K) := hR.inClass
  obtain ⟨hex, -⟩ := hR.setup
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hz2 : z * z = 1 := hR.cls.isCentralInvolution.sq
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) :=
    CFSG.ClassicalInvolution.isSubnormal_le hR.cls.subnormal
  have hKiso : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  have hncs : ∀ L ∈ conjClass3 K, ¬ Commutes L L := fun L hL => by
    obtain ⟨w', hw'⟩ := hΩ.classical L hL
    exact not_commutes_self3 hw'
  obtain ⟨J, J₂, t, hJ, hJK, hJT, hJt, htz, hJ₂t, hJ₂J, hJ₂cls, hJ₂K, hJ₂T, hJiso⟩ := hframe
  have hJ₂z : J₂ ∈ centralizingMembers (conjClass3 K) {z} :=
    ⟨hJ₂t.1, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
      (Commutes.symm hJ₂K z hR.cls.mem y hy).symm⟩
  have hJ₂K' : J₂ ≠ K := fun h => hncs K hKΩ (by rw [h] at hJ₂K; exact hJ₂K)
  have hJ₂T' : J₂ ≠ T := fun h => hncs T hT.mem.1 (by rw [h] at hJ₂T; exact hJ₂T)
  have hΦu : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ K → N ≠ T →
      N ∈ centralizingMembers (conjClass3 K) {e.u} := fun N hN hNK hNT =>
    e.mem_centralizingMembers_u hN.1 (Commutes.symm (hKiso N hN hNK))
      (Commutes.symm (hTiso N hN hNT))
  have hJu := hΦu J hJ hJK hJT
  have hJ₂u := hΦu J₂ hJ₂z hJ₂K' hJ₂T'
  have hK₂u := hΦu K₂ hK₂ hK₂K hK₂T
  have hJJ₂ : Commutes J J₂ := hJiso J₂ hJ₂t hJ₂J
  have hty : t ∈ locLayer (conjClass3 K) e.u := le_centralizingLayer hJu hJt.mem
  have hwY : w ∈ locLayer (conjClass3 K) e.u := le_centralizingLayer hK₂u hw.mem
  have hsurj : Function.Surjective (D.hom i) := hom_surjective_of_unique D i hone
  have hcomp : ∀ {N : Subgroup G}, N ∈ centralizingMembers (conjClass3 K) {e.u} →
      ∃ R, Corr3 (conjClass3 K) e.u D i N R := fun {N} hN =>
    exists_corr_left3 hΩ hex hP1 hO3 D ⟨hN, by
      rw [MonoidHom.range_eq_top.mpr hsurj]
      exact le_top⟩
  obtain ⟨RJ, hRJ⟩ := hcomp hJu
  obtain ⟨RJ₂, hRJ₂⟩ := hcomp hJ₂u
  obtain ⟨R₂, hR₂⟩ := hcomp hK₂u
  obtain ⟨xJ, hxJR, hxJ⟩ := exists_model_elt3 hRJ hJt.mem
  obtain ⟨xJ₂, hxJ₂R, hxJ₂⟩ := exists_model_elt3 hRJ₂ hJ₂cls.mem
  obtain ⟨x₂, hx₂R, hx₂⟩ := exists_model_elt3 hR₂ hw.mem
  have hsqt : locMk (conjClass3 K) e.u ⟨t, hty⟩ * locMk (conjClass3 K) e.u ⟨t, hty⟩ = 1 := by
    rw [← map_mul]
    have : (⟨t, hty⟩ : ↥(locLayer (conjClass3 K) e.u)) * ⟨t, hty⟩ = 1 :=
      Subtype.ext (mul_self_eq_one_of_orderOf_eq_two3 hJt.orderOf_eq_two)
    rw [this, map_one]
  have hnt : locMk (conjClass3 K) e.u ⟨t, hty⟩ ≠ 1 := locMk_involution_ne_one3 hJu hJt
  obtain ⟨hxJ2, hxJ1⟩ := involution_lift3 D i hnc hRJ.2.1 hxJR hsqt hnt hxJ
  obtain ⟨hxJ₂2, hxJ₂1⟩ := involution_lift3 D i hnc hRJ₂.2.1 hxJ₂R hsqt hnt hxJ₂
  have hw2 : locMk (conjClass3 K) e.u ⟨w, hwY⟩ * locMk (conjClass3 K) e.u ⟨w, hwY⟩ = 1 := by
    rw [← map_mul]
    have : (⟨w, hwY⟩ : ↥(locLayer (conjClass3 K) e.u)) * ⟨w, hwY⟩ = 1 :=
      Subtype.ext (mul_self_eq_one_of_orderOf_eq_two3 hw.orderOf_eq_two)
    rw [this, map_one]
  have hw1 : locMk (conjClass3 K) e.u ⟨w, hwY⟩ ≠ 1 := locMk_involution_ne_one3 hK₂u hw
  obtain ⟨hx₂2, hx₂1⟩ := involution_lift3 D i hnc hR₂.2.1 hx₂R hw2 hw1 hx₂
  have hne : RJ ≠ RJ₂ := fun h =>
    hJ₂J (corr_unique_right3 hΩ hex hP1 hO3 hRJ₂ (h ▸ hRJ))
  have hac : e.a * e.u = e.u * e.a := by
    have hc : e.a * e.a' = e.a' * e.a := hT.comm_K T hT.mem hT.ne _ e.mem_a _ e.mem_a'
    unfold TwinElt.u
    calc e.a * (e.a * e.a') = e.a * (e.a' * e.a) := by rw [hc]
      _ = (e.a * e.a') * e.a := by group
  have hcN : e.a ∈ Subgroup.normalizer (locLayer (conjClass3 K) e.u : Set G) :=
    centralizer_le_normalizer_centralizingLayer hΩ.conjInvariant e.u
      (Subgroup.mem_centralizer_singleton_iff.mpr hac)
  have hc4 : e.a * e.a * (e.a * e.a) = 1 := by rw [e.mul_self_a, hz2]
  have hccN : e.a * e.a ∈ Subgroup.normalizer (locLayer (conjClass3 K) e.u : Set G) :=
    Subgroup.mul_mem _ hcN hcN
  have hzu : z * e.u = e.u * z :=
    (e.u_comm_z (CFSG.ClassicalInvolution.isSubnormal_le hR.cls.subnormal)
      (CFSG.ClassicalInvolution.isSubnormal_le clsT.subnormal)).symm
  have hzN : z ∈ Subgroup.normalizer (locLayer (conjClass3 K) e.u : Set G) :=
    centralizer_le_normalizer_centralizingLayer hΩ.conjInvariant e.u
      (Subgroup.mem_centralizer_singleton_iff.mpr hzu)
  set α : MulAut (locQuot (conjClass3 K) e.u) := actX e.a hcN with hα
  have hα4 : α * α * (α * α) = 1 := actX_four_eq_one hcN hc4
  have hαz : actX z hzN = α * α := by
    rw [← actX_mul e.a e.a hcN hcN hccN]
    exact actX_congr e.mul_self_a.symm hzN hccN
  have hαfix : ∀ {N : Subgroup G}, (∀ n ∈ N, e.a * n = n * e.a) →
      ∀ g ∈ locImg (conjClass3 K) e.u N, α g = g := fun {N} h g hg =>
    actX_fix_of_commutes hcN h g hg
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
  have hres := hmodel (locQuot (conjClass3 K) e.u) (D.hom i) hsurj (D.ker_le_center i) RJ RJ₂ R₂
    hRJ.2.1 hRJ₂.2.1 hR₂.2.1 hne xJ xJ₂ x₂ hxJR hxJ2 hxJ1 hxJ₂R hxJ₂2 hxJ₂1 hsame hx₂R hx₂2 hx₂1
    α hα4 hαR hαR' hαR₂
  rcases hres with h | h | ⟨g, hg1, r₁, hr₁, hg2⟩
  ·
    exact (hF1 fun N hN =>
      centralizes_of_actX_fix3 hΩ hex hP1 hO3 hzu hzN hN fun n hn => by
        rw [hαz, h]; rfl).elim
  ·
    refine (hF2 J t hJ hJK hJT hJiso fun N hN => ?_).elim
    have htu : t * e.u = e.u * t :=
      Subgroup.mem_centralizer_singleton_iff.mp (centralizingLayer_le_centralizer _ _ hty)
    have htN : t ∈ Subgroup.normalizer (locLayer (conjClass3 K) e.u : Set G) :=
      centralizer_le_normalizer_centralizingLayer hΩ.conjInvariant e.u
        (Subgroup.mem_centralizer_singleton_iff.mpr htu)
    have htzu : t * z * e.u = e.u * (t * z) := by
      calc t * z * e.u = t * (z * e.u) := by group
        _ = t * (e.u * z) := by rw [hzu]
        _ = (t * e.u) * z := by group
        _ = (e.u * t) * z := by rw [htu]
        _ = e.u * (t * z) := by group
    have htzN : t * z ∈ Subgroup.normalizer (locLayer (conjClass3 K) e.u : Set G) :=
      Subgroup.mul_mem _ htN hzN
    refine centralizes_of_actX_fix3 hΩ hex hP1 hO3 htzu htzN hN fun n hn => ?_
    rw [actX_mul t z htN hzN htzN, MulAut.mul_apply, hαz, h, MulAut.conj_apply,
      actX_eq_conj_of_mem hty htN, hxJ]
    set τ := locMk (conjClass3 K) e.u ⟨t, hty⟩ with hτ
    have hτ2 : τ * τ = 1 := hsqt
    have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ2
    rw [hτinv]
    calc τ * (τ * locMk (conjClass3 K) e.u ⟨n, le_centralizingLayer hN hn⟩ * τ) * τ
        = (τ * τ) * locMk (conjClass3 K) e.u ⟨n, le_centralizingLayer hN hn⟩ * (τ * τ) := by group
      _ = locMk (conjClass3 K) e.u ⟨n, le_centralizingLayer hN hn⟩ := by rw [hτ2]; group
  ·
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (D.hom i g)
    obtain ⟨hNmem, -⟩ := conjSub_mem_and_image3 hΩ hK₂u y
    set N : Subgroup G := conjSub (y : G) K₂ with hN
    have hNimg : locImg (conjClass3 K) e.u N =
        (R₂.map (MulAut.conj g).toMonoidHom).map (D.hom i) := by
      rw [hN, locImg_conjSub_layer, hR₂.2.2,
        show locMk (conjClass3 K) e.u y = D.hom i g from hy]
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext a
      simp
    have hNelem : ∀ (n : G) (hn : n ∈ N), ∃ r ∈ R₂,
        locMk (conjClass3 K) e.u ⟨n, le_centralizingLayer hNmem hn⟩ = D.hom i (g * r * g⁻¹) := by
      intro n hn
      have hmem : locMk (conjClass3 K) e.u ⟨n, le_centralizingLayer hNmem hn⟩ ∈
          locImg (conjClass3 K) e.u N := ⟨_, Subgroup.mem_subgroupOf.mpr hn, rfl⟩
      rw [hNimg] at hmem
      obtain ⟨r', ⟨r, hr, rfl⟩, hr'⟩ := hmem
      exact ⟨r, hr, by rw [← hr']; simp [MulAut.conj_apply]⟩
    have hNelem' : ∀ r ∈ R₂, ∃ (n : G) (hn : n ∈ N),
        locMk (conjClass3 K) e.u ⟨n, le_centralizingLayer hNmem hn⟩ = D.hom i (g * r * g⁻¹) := by
      intro r hr
      have hmem : D.hom i (g * r * g⁻¹) ∈ locImg (conjClass3 K) e.u N := by
        rw [hNimg]
        exact Subgroup.mem_map_of_mem _ ⟨r, hr, by simp [MulAut.conj_apply]⟩
      obtain ⟨y₁, hy₁, hy₁'⟩ := hmem
      exact ⟨y₁, Subgroup.mem_subgroupOf.mp hy₁, hy₁'⟩
    have hwN : w ∈ Subgroup.normalizer (locLayer (conjClass3 K) e.u : Set G) :=
      Subgroup.le_normalizer hwY
    have hzwN : z * w ∈ Subgroup.normalizer (locLayer (conjClass3 K) e.u : Set G) :=
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
      refine centralizes_of_actX_fix3 hΩ hex hP1 hO3 hzwu hzwN hNmem fun n hn => ?_
      obtain ⟨r, hr, hrn⟩ := hNelem n hn
      rw [hrn, actX_mul z w hzN hwN hzwN, MulAut.mul_apply, hαz,
        actX_eq_conj_of_mem hwY hwN, ← hx₂]
      exact hg1 r hr
    have hnz : ¬ N ≤ Subgroup.centralizer ({z} : Set G) := by
      intro hle
      obtain ⟨n₁, hn₁, hmk⟩ := hNelem' r₁ hr₁
      have hfix := actX_fix_of_commutes hzN (N := N)
        (fun n hn => (Subgroup.mem_centralizer_singleton_iff.mp (hle hn)).symm)
        (locMk (conjClass3 K) e.u ⟨n₁, le_centralizingLayer hNmem hn₁⟩)
        ⟨_, Subgroup.mem_subgroupOf.mpr hn₁, rfl⟩
      rw [hαz, hmk] at hfix
      exact hg2 hfix
    exact (TWS.linkedAtProduct_iff hR.cls.mem hKz hKiso).mpr ⟨N, ⟨hNmem.1, hNle⟩, hnz⟩

end Main

end CFSG.ClassicalInvolution.Q3.Q3TLK
