module

public import CFSG.ClassicalInvolution.RouteD.TWT4Rank
public import CFSG.ClassicalInvolution.RouteD.TWT4Link
public import CFSG.ClassicalInvolution.RouteD.TwinYR2XO
public import CFSG.ClassicalInvolution.RouteD.TwinYP1Main
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

section Helpers

variable {G : Type} [Group G]

theorem conjSub_inj {g : G} {A B : Subgroup G} (h : conjSub g A = conjSub g B) : A = B := by
  have := congrArg (conjSub g⁻¹) h
  rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this

theorem le_centralizer_mul {N : Subgroup G} {a b : G}
    (ha : N ≤ Subgroup.centralizer ({a} : Set G)) (hb : N ≤ Subgroup.centralizer ({b} : Set G)) :
    N ≤ Subgroup.centralizer ({a * b} : Set G) := by
  intro y hy
  have h1 := Subgroup.mem_centralizer_singleton_iff.mp (ha hy)
  have h2 := Subgroup.mem_centralizer_singleton_iff.mp (hb hy)
  rw [Subgroup.mem_centralizer_singleton_iff, ← mul_assoc, h1, mul_assoc, h2, mul_assoc]

end Helpers

section Fusion

variable (p f : ℕ) [Fact p.Prime]


@[expose] def TwinSU4Fusion : Prop :=
  (p ^ f) % 4 = 3 →
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
      ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → LocalShapeT p f 2 .PSU 4 (𝒞 K) z →
        ∀ T : Subgroup G, IsTwinAt (𝒞 K) K T z → IsClassicalMember p f T z →
          ∀ e : TwinElt K T z, ∀ (J : Subgroup G) (t : G), J ∈ centralizingMembers (𝒞 K) {z} →
            J ≠ K → J ≠ T → IsClassicalMember p f J t →
              ∃ g : G, g * t = t * g ∧ conjSub g J = J ∧ g * (z * t) * g⁻¹ = e.u

end Fusion

section Main

variable {p f : ℕ} [Fact p.Prime]


theorem fusion_visible_eq (hmod : (p ^ f) % 4 = 3) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] {K T J : Subgroup G} {z t : G} (S : RouteDSetup p f K z) (e : TwinElt K T z)
    (hT : IsTwinAt (𝒞 K) K T z) (A : AtT p f K T J z t .PSU 4) {g : G} (hgt : g * t = t * g)
    (hgJ : conjSub g J = J) (hgu : g * (z * t) * g⁻¹ = e.u) (hJK : J ≠ K) (hJT : J ≠ T) :
    conjSub g K ∈ centralizingMembers (𝒞 K) {e.u} ∧
      conjSub g T ∈ centralizingMembers (𝒞 K) {e.u} ∧ conjSub g K ≠ conjSub g T ∧
      ∀ N ∈ centralizingMembers (𝒞 K) {e.u}, N ∈ centralizingMembers (𝒞 K) {t} → N ≠ J →
        N ≠ A.J₂ → N = conjSub g K ∨ N = conjSub g T := by
  obtain ⟨M₁, M₂, hM₁u, hM₂u, hM₁t, hM₂t, hM₁J, hM₁J₂, hM₂J, hM₂J₂, hM₁₂, -, huniq⟩ :=
    exists_visible_three hmod S e A
  have hKΩ : K ∈ 𝒞 K := CoreAssembly.mem_conjClass_self K
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) := le_centralizer_of_isClassicalMember S.cls
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := hT.mem.2
  have hKzt := le_centralizer_mul hKz A.hKt.2
  have hTzt := le_centralizer_mul hTz A.hTt.2
  have hgt' : g * t * g⁻¹ = t := by rw [hgt]; group
  have hconj : ∀ N : Subgroup G, N ∈ 𝒞 K → N ≤ Subgroup.centralizer ({z * t} : Set G) →
      N ≤ Subgroup.centralizer ({t} : Set G) →
      conjSub g N ∈ centralizingMembers (𝒞 K) {e.u} ∧
        conjSub g N ∈ centralizingMembers (𝒞 K) {t} := by
    intro N hN h1 h2
    refine ⟨⟨S.inClass.conjInvariant g N hN, ?_⟩, ⟨S.inClass.conjInvariant g N hN, ?_⟩⟩
    · have := conjSub_le_centralizer_singleton h1 g
      rwa [hgu] at this
    · have := conjSub_le_centralizer_singleton h2 g
      rwa [hgt'] at this
  obtain ⟨hK'u, hK't⟩ := hconj K hKΩ hKzt A.hKt.2
  obtain ⟨hT'u, hT't⟩ := hconj T hT.mem.1 hTzt A.hTt.2
  have hne_J : ∀ N : Subgroup G, N ≠ J → conjSub g N ≠ J := fun N hN h =>
    hN (conjSub_inj (h.trans hgJ.symm))
  have hiso_not : ∀ (N : Subgroup G) (R : Subgroup (modelUniv .PSU 4 p f Fact.out).K),
      N ∈ centralizingMembers (𝒞 K) {t} →
      R ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 p f Fact.out).D →
      locImg (𝒞 K) t N = R.map A.d.ψ → conjSub g N ≠ A.J₂ := by
    intro N R hNt hR hNR h
    refine not_fund_of_isolated S.inClass A.hP1 A.rf A.d hNt ?_ hR hNR
    intro L hL hLN
    have hL' : conjSub g L ∈ centralizingMembers (𝒞 K) {t} := by
      refine ⟨S.inClass.conjInvariant g L hL.1, ?_⟩
      have := conjSub_le_centralizer_singleton hL.2 g
      rwa [hgt'] at this
    have hne : conjSub g L ≠ A.J₂ := by
      rw [← h]
      exact fun h' => hLN (conjSub_inj h')
    have hc := A.hJ₂iso (conjSub g L) hL' hne
    rw [← h] at hc
    exact (commutes_conjSub_iff g).mp hc
  have hK'J : conjSub g K ≠ J := hne_J K hJK.symm
  have hT'J : conjSub g T ≠ J := hne_J T hJT.symm
  have hK'J₂ := hiso_not K A.RK A.hKt A.hRK A.hKR
  have hT'J₂ := hiso_not T A.RT A.hTt A.hRT A.hTR
  have hK'T' : conjSub g K ≠ conjSub g T := fun h => hT.ne (conjSub_inj h).symm
  have hK'M := huniq _ hK'u hK't hK'J hK'J₂
  have hT'M := huniq _ hT'u hT't hT'J hT'J₂
  refine ⟨hK'u, hT'u, hK'T', ?_⟩
  intro N hNu hNt hNJ hNJ₂
  rcases huniq N hNu hNt hNJ hNJ₂ with hN1 | hN2
  · rw [hN1]
    rcases hK'M with h | h
    · exact Or.inl h.symm
    · rcases hT'M with h' | h'
      · exact Or.inr h'.symm
      · exact absurd (h.trans h'.symm) hK'T'
  · rw [hN2]
    rcases hK'M with h | h
    · rcases hT'M with h' | h'
      · exact absurd (h.trans h'.symm) hK'T'
      · exact Or.inr h'.symm
    · exact Or.inl h.symm

theorem twinYVisibleOn_of_fusion (hF : TwinSU4Fusion p f) (hmod : (p ^ f) % 4 = 3) :
    TwinYVisibleOn p f fun t n => t = .PSU ∧ n = 4 := by
  intro G _ _ _ hnab K z S tY nY hrow hP hshape T hT clsT e J t hJ hJK hJT hJt M hM hMt hMJ
  obtain ⟨rfl, rfl⟩ := hP
  have htz : t ≠ z := involution_ne_of_member hnab S hrow hshape hT hJ hJK hJT hJt
  obtain ⟨A⟩ := exists_atT S hrow hshape hT clsT hJ hJK hJT hJt htz
  obtain ⟨g, hgt, hgJ, hgu⟩ := hF hmod G hnab K z S hshape T hT clsT e J t hJ hJK hJT hJt
  by_cases hM2 : M = A.J₂
  · have hXO := twinYXOrbit p f G hnab K z S .PSU 4 hrow hshape T hT clsT e
    obtain ⟨y, hy, hyJ⟩ := hXO J hJ hJK hJT A.J₂ A.hJ₂z A.hJ₂K A.hJ₂T
    exact ⟨y, centralizingLayer_le_centralizer (𝒞 K) {e.u} hy, by rw [hyJ, hM2]⟩
  · have hMtm : M ∈ centralizingMembers (𝒞 K) {t} := ⟨hM.1, hMt⟩
    obtain ⟨-, -, -, hcl⟩ := fusion_visible_eq hmod S e hT A hgt hgJ hgu hJK hJT
    obtain ⟨hG2, hD4, hnA1⟩ := hrow.tag_facts
    obtain ⟨d⟩ := LocalShapeT.nonempty_dictT2 hD4 A.rf.fsc S.inClass
      (CoreAssembly.mem_conjClass_self K) S.cls hshape
    have hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N :=
      fun N hN hNK => hT.comm_K N hN hNK
    have hTiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N :=
      fun N hN hNT => hT.comm_T N hN hNT
    have cfg : TwinCfg p f K T J z t :=
      ⟨hT.mem, fun h => hT.ne h.symm, hKiso, hTiso, clsT, hJ, hJK, hJT, hJt, htz⟩
    obtain ⟨s, hsJ, hsz, hst⟩ := TwinCfg.exists_swap S A.rf d cfg
    obtain ⟨c, hcK, hcz, hct, -⟩ := TwinCfg.exists_swap_KT S A.rf d cfg
    have hzt : z * t = t * z := cfg.comm_zt S
    have hgu' : g⁻¹ * e.u * g = z * t := by rw [← hgu]; group
    have hgJ' : conjSub g⁻¹ J = J := by rw [← hgJ, conjSub_inv_conjSub, hgJ]
    have hcu : ∀ s' : G, s' * (z * t) * s'⁻¹ = z * t →
        g * s' * g⁻¹ ∈ Subgroup.centralizer ({e.u} : Set G) := by
      intro s' hs'
      refine mem_centralizer_singleton_of_conj_eq ?_
      calc g * s' * g⁻¹ * e.u * (g * s' * g⁻¹)⁻¹
          = g * s' * (g⁻¹ * e.u * g) * s'⁻¹ * g⁻¹ := by group
        _ = g * s' * (z * t) * s'⁻¹ * g⁻¹ := by rw [hgu']
        _ = g * (s' * (z * t) * s'⁻¹) * g⁻¹ := by group
        _ = g * (z * t) * g⁻¹ := by rw [hs']
        _ = e.u := hgu
    have hcJ : ∀ s' : G, conjSub (g * s' * g⁻¹) J = conjSub g (conjSub s' J) := by
      intro s'
      rw [conjSub_mul, conjSub_mul, hgJ']
    have hs_zt : s * (z * t) * s⁻¹ = z * t := by
      calc s * (z * t) * s⁻¹ = (s * z * s⁻¹) * (s * t * s⁻¹) := by group
        _ = t * z := by rw [hsz, hst]
        _ = z * t := hzt.symm
    have hcs_zt : (c * s) * (z * t) * (c * s)⁻¹ = z * t := by
      calc (c * s) * (z * t) * (c * s)⁻¹ = c * (s * (z * t) * s⁻¹) * c⁻¹ := by group
        _ = c * (z * t) * c⁻¹ := by rw [hs_zt]
        _ = (c * z * c⁻¹) * (c * t * c⁻¹) := by group
        _ = z * t := by rw [hcz, hct]
    rcases hcl M hM hMtm hMJ hM2 with h | h
    · refine ⟨g * s * g⁻¹, hcu s hs_zt, ?_⟩
      rw [hcJ, hsJ, h]
    · refine ⟨g * (c * s) * g⁻¹, hcu (c * s) hcs_zt, ?_⟩
      rw [hcJ, conjSub_mul, hsJ, hcK, h]

theorem twinYNoCentralOn_of_fusion (hF : TwinSU4Fusion p f) (hmod : (p ^ f) % 4 = 3) :
    TwinYNoCentralOn p f fun t n => t = .PSU ∧ n = 4 := by
  intro G _ _ _ hnab K z S tY nY hrow hP hshape T hT clsT e M hM
  obtain ⟨rfl, rfl⟩ := hP
  by_contra hno
  push Not at hno
  obtain ⟨J, J', t, hJ, hJK, hJT, hJt, htz, -, -, -⟩ :=
    exists_frameMembers hnab S hrow hshape hT clsT e
  obtain ⟨A⟩ := exists_atT S hrow hshape hT clsT hJ hJK hJT hJt htz
  obtain ⟨g, hgt, hgJ, hgu⟩ := hF hmod G hnab K z S hshape T hT clsT e J t hJ hJK hJT hJt
  obtain ⟨-, -, -, hcl⟩ := fusion_visible_eq hmod S e hT A hgt hgJ hgu hJK hJT
  have hncs : ∀ L ∈ 𝒞 K, ¬ Commutes L L := fun L hL => not_commutes_self_of_mem S.inClass hL
  have hMJ : Commutes M J := hno J hJ hJK hJT
  have hMJ₂ : Commutes M A.J₂ := hno A.J₂ A.hJ₂z A.hJ₂K A.hJ₂T
  have hMt : M ∈ centralizingMembers (𝒞 K) {t} :=
    ⟨hM.1, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hMJ y hy t hJt.mem)⟩
  have hMJne : M ≠ J := fun h => hncs J hJ.1 (by rw [h] at hMJ; exact hMJ)
  have hMJ₂ne : M ≠ A.J₂ := fun h => hncs A.J₂ A.hJ₂t.1 (by rw [h] at hMJ₂; exact hMJ₂)
  obtain ⟨hG2, hD4, hnA1⟩ := hrow.tag_facts
  obtain ⟨d⟩ := LocalShapeT.nonempty_dictT2 hD4 A.rf.fsc S.inClass
    (CoreAssembly.mem_conjClass_self K) S.cls hshape
  have hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  have hKmem : K ∈ centralizingMembers (𝒞 K) {z} :=
    ⟨CoreAssembly.mem_conjClass_self K, le_centralizer_of_isClassicalMember S.cls⟩
  obtain ⟨L', hL'z, hL'J, hL'nc⟩ := exists_noncomm_of_ne S.inClass S.exact S.p1 A.rf d hKmem
    hT.mem hT.ne.symm hKiso hTiso hJ hJK hJT
  have hL'K : L' ≠ K := fun h => hL'nc (by rw [h]; exact (hKiso J hJ hJK).symm)
  have hL'T : L' ≠ T := fun h => hL'nc (by rw [h]; exact (hTiso J hJ hJT).symm)
  have hML' : Commutes M L' := hno L' hL'z hL'K hL'T
  have hL'u : L' ∈ centralizingMembers (𝒞 K) {e.u} :=
    e.mem_centralizingMembers_u hL'z.1 (hKiso L' hL'z hL'K).symm (hTiso L' hL'z hL'T).symm
  have hgu' : g⁻¹ * e.u * g = z * t := by rw [← hgu]; group
  have hgt' : g * t * g⁻¹ = t := by rw [hgt]; group
  have hL''zt : conjSub g⁻¹ L' ≤ Subgroup.centralizer ({z * t} : Set G) := by
    have := conjSub_le_centralizer_singleton hL'u.2 g⁻¹
    rwa [show g⁻¹ * e.u * g⁻¹⁻¹ = z * t by rw [inv_inv]; exact hgu'] at this
  have key : ∀ X : Subgroup G, z ∈ X → M = conjSub g X → False := by
    intro X hzX hMX
    have hXL'' : Commutes X (conjSub g⁻¹ L') := by
      have := (commutes_conjSub_iff g⁻¹).mpr hML'
      rwa [hMX, conjSub_inv_conjSub] at this
    have hL''z : conjSub g⁻¹ L' ≤ Subgroup.centralizer ({z} : Set G) := fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hXL'' z hzX y hy).symm
    have hL''t : conjSub g⁻¹ L' ≤ Subgroup.centralizer ({t} : Set G) := by
      intro y hy
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hL''z hy)
      have h2 := Subgroup.mem_centralizer_singleton_iff.mp (hL''zt hy)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h3 : z * (y * t) = z * (t * y) := by
        calc z * (y * t) = (z * y) * t := by group
          _ = (y * z) * t := by rw [h1]
          _ = y * (z * t) := by group
          _ = (z * t) * y := h2
          _ = z * (t * y) := by group
      exact mul_left_cancel h3
    have hL''Ω : conjSub g⁻¹ L' ∈ centralizingMembers (𝒞 K) {t} :=
      ⟨S.inClass.conjInvariant g⁻¹ L' hL'z.1, hL''t⟩
    have hL''J : conjSub g⁻¹ L' ≠ J := by
      intro h
      apply hL'J
      have := congrArg (conjSub g) h
      rwa [conjSub_conjSub_inv, hgJ] at this
    have hJL'' := A.hJiso _ hL''Ω hL''J
    have := (commutes_conjSub_iff g).mpr hJL''
    rw [hgJ, conjSub_conjSub_inv] at this
    exact hL'nc this
  rcases hcl M hM hMt hMJne hMJ₂ne with h | h
  · exact key K S.cls.mem h
  · exact key T clsT.mem h

theorem fusion_of_visible_involution {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {K T J : Subgroup G} {z t : G} (S : RouteDSetup p f K z) (e : TwinElt K T z)
    (hT : IsTwinAt (𝒞 K) K T z) (hJ : J ∈ centralizingMembers (𝒞 K) {z}) (hJK : J ≠ K)
    (hJt : IsClassicalMember p f J t) (A : AtT p f K T J z t .PSU 4) {M : Subgroup G}
    (hM : M ∈ centralizingMembers (𝒞 K) {t}) (hMK : ¬ Commutes M K) {w : G}
    (hw : IsClassicalMember p f M w) (hwut : w = e.u * t) :
    ∃ g : G, g * t = t * g ∧ conjSub g J = J ∧ g * (z * t) * g⁻¹ = e.u := by
  have hKJ : Commutes K J := hT.comm_K J hJ hJK
  have hKJ₂ : Commutes K A.J₂ := hT.comm_K A.J₂ A.hJ₂z A.hJ₂K
  have hMJ : M ≠ J := fun h => hMK (by rw [h]; exact hKJ.symm)
  have hMJ₂ : M ≠ A.J₂ := fun h => hMK (by rw [h]; exact hKJ₂.symm)
  obtain ⟨y, hy, hyK⟩ := link_big S.inClass S.exact A.hP1 A.rf A.d (K := J) (T := A.J₂)
    (L := K) (L' := M) A.hJt A.hJ₂t A.hJ₂J.symm A.hJiso A.hJ₂iso A.hKt hJK.symm A.hJ₂K.symm hM
    hMJ hMJ₂
  have hyt : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp
    (centralizingLayer_le_centralizer (𝒞 K) {t} hy)
  have hUz := ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five S.cls
  have hUt := ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five hJt
  have hUw := ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five hw
  have hyz : y * z * y⁻¹ = w := by
    have h1 := hUz.conj y
    rw [hyK] at h1
    exact (hUw.eq h1).symm
  have ht2 : t * t = 1 := hUt.sq
  refine ⟨y, hyt, conjSub_eq_of_mem_locLayer A.hJt A.hJiso hy, ?_⟩
  calc y * (z * t) * y⁻¹ = (y * z * y⁻¹) * (y * t * y⁻¹) := by group
    _ = w * t := by rw [hyz, hyt]; group
    _ = e.u := by rw [hwut, mul_assoc, ht2, mul_one]

end Main

end CFSG.ClassicalInvolution.RouteD.TWT4
