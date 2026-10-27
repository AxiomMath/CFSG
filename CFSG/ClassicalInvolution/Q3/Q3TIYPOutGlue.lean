module

public import CFSG.ClassicalInvolution.Q3.Q3TIYPOutGen
public import CFSG.ClassicalInvolution.Q3.Q3TLKGlobal
public import CFSG.ClassicalInvolution.Q3.Q3TLKMF
public import CFSG.ClassicalInvolution.Q3.Q3TLKLink

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TWZ
  CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TLK
open CFSG.ClassicalInvolution.RouteD.TwinY (IsTwinAt TwinElt TwinElt.u TwinRow)
open CFSG.ClassicalInvolution.Q3 (CompData IsClassicalMember3)


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K T : Subgroup G} {z : G}

theorem false_of_sqDichotomy3 (h3 : OddThreeFreeInput) (hnab : ∃ x y : G, x * y ≠ y * x)
    (hR : RouteD3Setup K z)
    (hshape : LocalShapeC3 2 (CompData.model .PSp 2) (conjClass3 K) z)
    (hT : IsTwinAt (conjClass3 K) K T z) (clsT : IsClassicalMember3 T z) (e : TwinElt K T z)
    (hP1 : LocalOddCentral (conjClass3 K) {e.u}) (hO3 : LocalOddThreeFree3 (conjClass3 K) e.u)
    {ι : Type}
    (D : LieSystemData3 ι (locQuot (conjClass3 K) e.u) (locFamily (conjClass3 K) e.u)) (i : ι)
    (hone : ∀ j : ι, j = i)
    (hnc : ∀ R ∈ (D.kind i).fund, ∀ r ∈ R, r ∈ Subgroup.center (D.kind i).G → r = 1)
    (hdich : SqDichotomyC (D.kind i)) : False := by
  classical
  have hrow : TwinRow .PSp 2 := Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
  have hΩ : InClass3 (conjClass3 K) := hR.inClass
  obtain ⟨hex, -⟩ := hR.setup
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hz2 : z * z = 1 := hR.cls.isCentralInvolution.sq
  have hKiso : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  have hncs : ∀ L ∈ conjClass3 K, ¬ Commutes L L := fun L hL => by
    obtain ⟨w', hw'⟩ := hΩ.classical L hL
    exact not_commutes_self3 hw'
  obtain ⟨J, J₂, t, hJ, hJK, hJT, hJt, htz, hJ₂t, hJ₂J, hJ₂cls, hJ₂K, hJ₂T, hJiso⟩ :=
    exists_twin_frame3 h3 hnab hR hrow hshape hT clsT
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
  have hJJ₂ : Commutes J J₂ := hJiso J₂ hJ₂t hJ₂J
  have hty : t ∈ locLayer (conjClass3 K) e.u := le_centralizingLayer hJu hJt.mem
  have hsurj : Function.Surjective (D.hom i) := hom_surjective_of_unique D i hone
  have hcomp : ∀ {N : Subgroup G}, N ∈ centralizingMembers (conjClass3 K) {e.u} →
      ∃ R, Corr3 (conjClass3 K) e.u D i N R := fun {N} hN =>
    exists_corr_left3 hΩ hex hP1 hO3 D ⟨hN, by
      rw [MonoidHom.range_eq_top.mpr hsurj]
      exact le_top⟩
  obtain ⟨RJ, hRJ⟩ := hcomp hJu
  obtain ⟨RJ₂, hRJ₂⟩ := hcomp hJ₂u
  obtain ⟨xJ, hxJR, hxJ⟩ := exists_model_elt3 hRJ hJt.mem
  obtain ⟨xJ₂, hxJ₂R, hxJ₂⟩ := exists_model_elt3 hRJ₂ hJ₂cls.mem
  have hsqt : locMk (conjClass3 K) e.u ⟨t, hty⟩ * locMk (conjClass3 K) e.u ⟨t, hty⟩ = 1 := by
    rw [← map_mul]
    have : (⟨t, hty⟩ : ↥(locLayer (conjClass3 K) e.u)) * ⟨t, hty⟩ = 1 :=
      Subtype.ext (mul_self_eq_one_of_orderOf_eq_two3 hJt.orderOf_eq_two)
    rw [this, map_one]
  have hnt : locMk (conjClass3 K) e.u ⟨t, hty⟩ ≠ 1 := locMk_involution_ne_one3 hJu hJt
  obtain ⟨hxJ2, hxJ1⟩ := involution_lift3 D i hnc hRJ.2.1 hxJR hsqt hnt hxJ
  obtain ⟨hxJ₂2, hxJ₂1⟩ := involution_lift3 D i hnc hRJ₂.2.1 hxJ₂R hsqt hnt hxJ₂
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
  have hsame : D.hom i xJ = D.hom i xJ₂ := hxJ.trans hxJ₂.symm
  have hres := hdich (locQuot (conjClass3 K) e.u) (D.hom i) hsurj (D.ker_le_center i) RJ RJ₂
    hRJ.2.1 hRJ₂.2.1 hne xJ xJ₂ hxJR hxJ2 hxJ1 hxJ₂R hxJ₂2 hxJ₂1 hsame α hα4 hαR hαR'
  rcases hres with h | h
  ·
    exact false_of_layer_le_centralizer3 h3 hnab hR hrow hshape hT clsT e
      twinMFGenerationOn3_psp2 fun N hN =>
        centralizes_of_actX_fix3 hΩ hex hP1 hO3 hzu hzN hN fun n hn => by
          rw [hαz, h]; rfl
  ·
    refine false_of_layer_le_centralizer_tz3 h3 hR hrow hshape hT e hJ hJK hJT hJiso fun N hN => ?_
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

end CFSG.ClassicalInvolution.Q3.Q3TIY
