module

public import CFSG.ClassicalInvolution.RouteD.TWZSmall
public import CFSG.ClassicalInvolution.RouteD.TWZSpinMinus
public import CFSG.ClassicalInvolution.RouteD.TWZPlanes
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
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.ClassicalInvolution.RouteD.TWZ

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.RouteD.NonClassical CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Balance
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => CoreAssembly.conjClass

local notation "GFund" => CFSG.ClassicalInvolution.Generic.fundamentalSubgroups

set_option linter.unusedSectionVars false

section Minus

variable (p f : ℕ) [Fact p.Prime]

theorem twinYSp2NoMinus : TwinYSp2NoMinus p f := by
  intro G _ _ _ hnab K z S hshape T hT clsT e hP1 D hcard i hmin
  classical
  have hrow : TwinRow .PSp 2 := Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
  have hMF : TwinMFGeneration p f .PSp 2 := twinMFGeneration_psp2 S.odd (le_trans (by norm_num : 3 ≤ 5) S.five)
  have hDi : D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4 := by
    rw [hmin.1]
    exact ⟨by decide, by decide⟩
  have hnc : ¬ (D.tag i = .PSL ∧ D.rank i = 2) := by
    rintro ⟨h1, -⟩
    rw [hmin.1] at h1
    exact absurd h1 (by decide)
  obtain ⟨hexp, hperf, hperfK, hsurj⟩ := component_package S.odd S.five D hcard i hDi
  have hcount : SqCountOn (D.tag i)
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out) (((p ^ f) ^ 4 - 1) * (p ^ f) ^ 3) := by
    have hadm := D.admissible i
    have h1 := hmin.1
    have h2 := hmin.2
    rw [h1, h2, hexp] at hadm ⊢
    exact sqCount_minus4 S.odd S.five hadm
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
  have hJJ₂ : Commutes J J₂ := hJiso J₂ hJ₂t hJ₂J
  have hty : t ∈ locLayer (𝒞 K) e.u := le_centralizingLayer hJu hJt.mem
  obtain ⟨RJ, RJ₂, xJ, xJ₂, hRJ, hRJ₂, hxJ, hxJ₂, hpair⟩ :=
    exists_twinPairOn hΩ S.exact hP1 D hcard i hperf hnc hperfK hJu hJ₂u hJ₂J.symm hJJ₂ hJt
      hJ₂cls
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
  have hsame : D.hom i xJ = D.hom i xJ₂ := hxJ.trans hxJ₂.symm
  have hres := hcount (locQuot (𝒞 K) e.u) (D.hom i) hsurj (D.ker_le_center i) RJ RJ₂ hRJ.2.1
    hRJ₂.2.1 hpair.ne xJ xJ₂ hpair.hx hpair.hx2 hpair.hx1 hpair.hx' hpair.hx'2 hpair.hx'1 hsame
    α hα4 hαR hαR'
  rcases hres with h | h | hbig
  ·
    exact false_of_layer_le_centralizer hnab S hrow hshape hT clsT e hMF fun N hN =>
      centralizes_of_actX_fix hΩ S.exact hP1 hzu hzN hN fun n hn => by
        rw [hαz, h]; rfl
  ·
    refine false_of_layer_le_centralizer_tz S hrow hshape hT e hJ hJK hJT hJiso fun N hN => ?_
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
    have hq5 : 5 ≤ p ^ f := S.five
    have hf1 : 1 ≤ f := by
      rcases Nat.eq_zero_or_pos f with h0 | h0
      · rw [h0] at hq5
        simp at hq5
      · exact h0
    have hadmP : StatedLieAdmissible .PSp 2 p f :=
      ⟨Fact.out, hf1, le_rfl, fun h' => by
        have := congrArg Prod.snd h'
        simp only at this
        omega⟩
    have hodd : Odd (Nat.card (GaloisField p f)) := by
      rw [GaloisField.card p f (by omega)]
      exact (Nat.Prime.odd_of_ne_two Fact.out S.odd).pow
    have hKT : Commutes K T := hT.comm_K T hT.mem hT.ne
    have hKnu : K ∉ centralizingMembers (𝒞 K) {e.u} :=
      e.not_mem_centralizingMembers_left S.cls (S.exact K hKΩ) hodd hKT
    have hTnu : T ∉ centralizingMembers (𝒞 K) {e.u} :=
      e.not_mem_centralizingMembers_right clsT (S.exact T hT.mem.1) hodd hKT
    have hsc := fundamentalSingleClass_of_ne D i hDi.1 hDi.2
    let Fx := {S' : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K //
      S' ∈ GFund (D.tag i) (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D ∧
        ∀ r ∈ S', (α * α) (D.hom i r) = D.hom i r}
    have hbig' : ((p ^ f) ^ 4 - 1) * (p ^ f) ^ 3 < Nat.card Fx := hbig
    choose Nf hNf using fun S' : Fx => exists_corr_right hΩ D hsc S'.2.1
    have hNfz : ∀ S' : Fx, Nf S' ∈ centralizingMembers (𝒞 K) {z} := by
      intro S'
      have hNu : Nf S' ∈ centralizingMembers (𝒞 K) {e.u} := (hNf S').1
      have hNimg : locImg (𝒞 K) e.u (Nf S') = S'.1.map (D.hom i) := (hNf S').2.2
      refine ⟨hNu.1, centralizes_of_actX_fix hΩ S.exact hP1 hzu hzN hNu fun n hn => ?_⟩
      have hmem : locMk (𝒞 K) e.u ⟨n, le_centralizingLayer hNu hn⟩ ∈
          locImg (𝒞 K) e.u (Nf S') := ⟨_, Subgroup.mem_subgroupOf.mpr hn, rfl⟩
      rw [hNimg] at hmem
      obtain ⟨r, hr, hrn⟩ := hmem
      rw [hαz, ← hrn]
      exact S'.2.2 r hr
    have hKmem : K ∈ centralizingMembers (𝒞 K) {z} := ⟨hKΩ, hKz⟩
    have hNfK : ∀ S' : Fx, Nf S' ≠ K := fun S' h => by
      have := (hNf S').1
      rw [h] at this
      exact hKnu this
    have hNfT : ∀ S' : Fx, Nf S' ≠ T := fun S' h => by
      have := (hNf S').1
      rw [h] at this
      exact hTnu this
    let ψ : Fx → Subgroup (locQuot (𝒞 K) z) := fun S' => locImg (𝒞 K) z (Nf S')
    have hψinj : Function.Injective ψ := by
      intro S₁ S₂ h
      have hN : Nf S₁ = Nf S₂ := locImg_injOn hΩ S.p1 (hNfz S₁) (hNfz S₂) h
      apply Subtype.ext
      exact corr_unique_left hperf (hNf S₁) (by rw [hN]; exact hNf S₂)
    have hψK : ∀ S' : Fx, ψ S' ≠ locImg (𝒞 K) z K := fun S' h =>
      hNfK S' (locImg_injOn hΩ S.p1 (hNfz S') hKmem h)
    have hψT : ∀ S' : Fx, ψ S' ≠ locImg (𝒞 K) z T := fun S' h =>
      hNfT S' (locImg_injOn hΩ S.p1 (hNfz S') hT.mem h)
    have hKT' : locImg (𝒞 K) z K ≠ locImg (𝒞 K) z T := fun h =>
      hT.ne (locImg_injOn hΩ S.p1 hKmem hT.mem h).symm
    let g : Fx ⊕ Bool → ↥(locFamily (𝒞 K) z)
      | Sum.inl S' => ⟨ψ S', mem_locFamily_iff.mpr ⟨Nf S', hNfz S', rfl⟩⟩
      | Sum.inr true => ⟨locImg (𝒞 K) z K, mem_locFamily_iff.mpr ⟨K, hKmem, rfl⟩⟩
      | Sum.inr false => ⟨locImg (𝒞 K) z T, mem_locFamily_iff.mpr ⟨T, hT.mem, rfl⟩⟩
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
    have hfin : Finite (modelUniv .PSp 2 p f Fact.out).K :=
      CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv S.odd Fact.out trivial hadmP
    have hlf := LocalShapeT.ncard_locFamily_le hshape (by decide : StatedLieTag.PSp ≠ .trialityD4)
      hfin
    have hfund := ncard_fund_psp2_le (p := p) (f := f) S.five
    omega

theorem twinSp2Linked (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩall : HypOmegaModAll p f)
    (hAE : AEmptyTwinExact p f) (hcls : TwinInvolution p f) (hP4 : Ih8G2D4 p f)
    (hH : TwinFrameHyp51 p f) : TwinSp2Linked p f :=
  twinSp2Linked_of_noMinus p f hp2 hq hΩall hAE hcls hP4 hH (twinYSp2NoMinus p f)

end Minus

end CFSG.ClassicalInvolution.RouteD.TWZ
