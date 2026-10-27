module

public import CFSG.ClassicalInvolution.Q3.Q3TIYPMinCount
public import CFSG.ClassicalInvolution.Q3.Q3TIYPOutGlue
public import CFSG.ClassicalInvolution.Q3.Q3TIYAtT
public import CFSG.ClassicalInvolution.Q3.Q3ZModel
public import CFSG.ClassicalInvolution.Q3.Q3EXTwin
public import CFSG.ClassicalInvolution.RouteD.TWZPlanes
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TWZ
  CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TLK
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.ClassicalInvolution.Q3.Q3TIV CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.RouteD.TwinY (IsTwinAt TwinElt TwinElt.u TwinRow)
open CFSG.ClassicalInvolution.Q3 (CompData IsClassicalMember3)

local notation "GFund" => CFSG.ClassicalInvolution.Generic.fundamentalSubgroups


theorem ncard_fund_psp2_le3 :
    (GFund .PSp (modelUniv .PSp 2 3 1 Nat.prime_three).D).ncard ≤ 2160 := by
  have hcard : Nat.card (GaloisField 3 1) = 3 := Q3W.card_gf3
  have hadm : StatedLieAdmissible .PSp 2 3 1 := Q3Z.statedLieAdmissible_psp2
  have hsub : GFund .PSp (modelUniv .PSp 2 3 1 Nat.prime_three).D ⊆
      (fun P : Submodule (GaloisField 3 1) (Fin 2 ⊕ Fin 2 → GaloisField 3 1) => planeGroup P) ''
        {P | IsHyperbolicPlane P} := by
    intro R hR
    obtain ⟨P, hP, rfl⟩ := (mem_fundamentalSubgroups_PSp_iff hadm R).mp hR
    exact ⟨P, hP, rfl⟩
  have hfin : {P : Submodule (GaloisField 3 1) (Fin 2 ⊕ Fin 2 → GaloisField 3 1) |
      IsHyperbolicPlane P}.Finite := Set.toFinite _
  have hle := card_planes_le (K := GaloisField 3 1)
  rw [hcard] at hle
  calc _ ≤ ((fun P : Submodule (GaloisField 3 1) (Fin 2 ⊕ Fin 2 → GaloisField 3 1) =>
          planeGroup P) '' {P | IsHyperbolicPlane P}).ncard :=
        Set.ncard_le_ncard hsub (hfin.image _)
    _ ≤ {P : Submodule (GaloisField 3 1) (Fin 2 ⊕ Fin 2 → GaloisField 3 1) |
          IsHyperbolicPlane P}.ncard := Set.ncard_image_le hfin
    _ = Nat.card {P : Submodule (GaloisField 3 1) (Fin 2 ⊕ Fin 2 → GaloisField 3 1) //
          IsHyperbolicPlane P} := (Nat.card_coe_set_eq _).symm
    _ ≤ 2160 := by simpa using hle

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K T : Subgroup G} {z : G}

theorem false_of_minus_component3 (h3 : OddThreeFreeInput) (hnab : ∃ x y : G, x * y ≠ y * x)
    (hR : RouteD3Setup K z)
    (hshape : LocalShapeC3 2 (CompData.model .PSp 2) (conjClass3 K) z)
    (hT : IsTwinAt (conjClass3 K) K T z) (clsT : IsClassicalMember3 T z) (e : TwinElt K T z)
    (hP1 : LocalOddCentral (conjClass3 K) {e.u}) (hO3 : LocalOddThreeFree3 (conjClass3 K) e.u)
    {ι : Type}
    (D : LieSystemData3 ι (locQuot (conjClass3 K) e.u) (locFamily (conjClass3 K) e.u)) (i : ι)
    (hone : ∀ j : ι, j = i) (hk : D.kind i = CompData.model .POmegaMinus 4) : False := by
  classical
  have hrow : TwinRow .PSp 2 := Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
  have hadmM : StatedLieAdmissible .POmegaMinus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have hnc : ∀ R ∈ (D.kind i).fund, ∀ r ∈ R, r ∈ Subgroup.center (D.kind i).G → r = 1 := by
    rw [hk]
    exact fundNoncentral_model3 trivial hadmM (by decide)
  have hsc := EX.singleClass_of_kind hk (trivial : IsFundTag .POmegaMinus) hadmM (by decide)
    (by decide)
  have hpc := EX.powCop3_of_kind hk (trivial : IsFundTag .POmegaMinus) hadmM (by decide)
    (by decide)
  have hcount : SqCountC (D.kind i) 2160 := by
    rw [hk]
    exact sqCountC_minus4
  obtain ⟨c⟩ := TwinLoc3.of_setup (twinRowFacts3_of_row hrow) h3 hR hshape
  have hΩ : InClass3 (conjClass3 K) := hR.inClass
  obtain ⟨hex, -⟩ := hR.setup
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hz2 : z * z = 1 := hR.cls.isCentralInvolution.sq
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) :=
    CFSG.ClassicalInvolution.isSubnormal_le hR.cls.subnormal
  have hKT : Commutes K T := hT.comm_K T hT.mem hT.ne
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
  have hres := hcount (locQuot (conjClass3 K) e.u) (D.hom i) hsurj (D.ker_le_center i) RJ RJ₂
    hRJ.2.1 hRJ₂.2.1 hne xJ xJ₂ hxJR hxJ2 hxJ1 hxJ₂R hxJ₂2 hxJ₂1 hsame α hα4 hαR hαR'
  rcases hres with h | h | hbig
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
  ·
    have hKnu : K ∉ centralizingMembers (conjClass3 K) {e.u} := fun h =>
      twinElt_not_le_centralizer_left3 e hR.cls (hex K hKΩ) hKT h.2
    have hTnu : T ∉ centralizingMembers (conjClass3 K) {e.u} := fun h =>
      twinElt_not_le_centralizer_right3 e clsT (hex T hT.mem.1) hKT h.2
    let Fx := {S' : Subgroup (D.kind i).G // S' ∈ (D.kind i).fund ∧
      ∀ r ∈ S', (α * α) (D.hom i r) = D.hom i r}
    have hbig' : 2160 < Nat.card Fx := hbig
    choose Nf hNf using fun S' : Fx => exists_corr_right3 hΩ D hsc S'.2.1
    have hNfz : ∀ S' : Fx, Nf S' ∈ centralizingMembers (conjClass3 K) {z} := by
      intro S'
      have hNu : Nf S' ∈ centralizingMembers (conjClass3 K) {e.u} := (hNf S').1
      have hNimg : locImg (conjClass3 K) e.u (Nf S') = S'.1.map (D.hom i) := (hNf S').2.2
      refine ⟨hNu.1, centralizes_of_actX_fix3 hΩ hex hP1 hO3 hzu hzN hNu fun n hn => ?_⟩
      have hmem : locMk (conjClass3 K) e.u ⟨n, le_centralizingLayer hNu hn⟩ ∈
          locImg (conjClass3 K) e.u (Nf S') := ⟨_, Subgroup.mem_subgroupOf.mpr hn, rfl⟩
      rw [hNimg] at hmem
      obtain ⟨r, hr, hrn⟩ := hmem
      rw [hαz, ← hrn]
      exact S'.2.2 r hr
    have hKmem : K ∈ centralizingMembers (conjClass3 K) {z} := ⟨hKΩ, hKz⟩
    have hNfK : ∀ S' : Fx, Nf S' ≠ K := fun S' h => by
      have := (hNf S').1
      rw [h] at this
      exact hKnu this
    have hNfT : ∀ S' : Fx, Nf S' ≠ T := fun S' h => by
      have := (hNf S').1
      rw [h] at this
      exact hTnu this
    let ψ : Fx → Subgroup (locQuot (conjClass3 K) z) := fun S' =>
      locImg (conjClass3 K) z (Nf S')
    have hψinj : Function.Injective ψ := by
      intro S₁ S₂ h
      have hN : Nf S₁ = Nf S₂ := locImg_injOn3 hΩ hex c.hP1 c.hO3 (hNfz S₁) (hNfz S₂) h
      apply Subtype.ext
      exact corr_unique_left3 hpc (hNf S₁) (by rw [hN]; exact hNf S₂)
    have hψK : ∀ S' : Fx, ψ S' ≠ locImg (conjClass3 K) z K := fun S' h =>
      hNfK S' (locImg_injOn3 hΩ hex c.hP1 c.hO3 (hNfz S') hKmem h)
    have hψT : ∀ S' : Fx, ψ S' ≠ locImg (conjClass3 K) z T := fun S' h =>
      hNfT S' (locImg_injOn3 hΩ hex c.hP1 c.hO3 (hNfz S') hT.mem h)
    have hKT' : locImg (conjClass3 K) z K ≠ locImg (conjClass3 K) z T := fun h =>
      hT.ne (locImg_injOn3 hΩ hex c.hP1 c.hO3 hKmem hT.mem h).symm
    let g : Fx ⊕ Bool → ↥(locFamily (conjClass3 K) z)
      | Sum.inl S' => ⟨ψ S', mem_locFamily_iff.mpr ⟨Nf S', hNfz S', rfl⟩⟩
      | Sum.inr true => ⟨locImg (conjClass3 K) z K, mem_locFamily_iff.mpr ⟨K, hKmem, rfl⟩⟩
      | Sum.inr false => ⟨locImg (conjClass3 K) z T, mem_locFamily_iff.mpr ⟨T, hT.mem, rfl⟩⟩
    have hg : Function.Injective g := by
      rintro (a | a) (b | b) h
      · exact congrArg Sum.inl (hψinj (congrArg Subtype.val h))
      · exfalso
        cases b
        · exact hψT a (congrArg Subtype.val h)
        · exact hψK a (congrArg Subtype.val h)
      · exfalso
        cases a
        · exact hψT b (congrArg Subtype.val h).symm
        · exact hψK b (congrArg Subtype.val h).symm
      · cases a <;> cases b
        · rfl
        · exact absurd (congrArg Subtype.val h) (Ne.symm hKT')
        · exact absurd (congrArg Subtype.val h) hKT'
        · rfl
    have hFxfin : Finite Fx := Nat.finite_of_card_ne_zero (by omega)
    have hlt := Nat.card_le_card_of_injective g hg
    rw [Nat.card_sum, Nat.card_coe_set_eq] at hlt
    have hbool : Nat.card Bool = 2 := by simp
    have hlf := hshape.ncard_locFamily_le Q3Z.finite_psp2
    have hfund := ncard_fund_psp2_le3
    have hcf : (CompData.model .PSp 2).fund.ncard ≤ 2160 := hfund
    omega

end CFSG.ClassicalInvolution.Q3.Q3TIY
