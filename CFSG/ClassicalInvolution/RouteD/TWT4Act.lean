module

public import CFSG.ClassicalInvolution.RouteD.TWT4Sq
public import CFSG.ClassicalInvolution.RouteD.TWT4Hol
public import CFSG.ClassicalInvolution.RouteD.TWT4Clos
public import CFSG.ClassicalInvolution.RouteD.TWT4Hbad
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

section Act

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K T J : Subgroup G}
  {z t : G} {tY : StatedLieTag} {nY : ℕ}


theorem isClassical_J₂ (S : RouteDSetup p f K z) (hT : IsTwinAt (𝒞 K) K T z)
    (clsT : IsClassicalMember p f T z) (hJ : J ∈ centralizingMembers (𝒞 K) {z}) (hJK : J ≠ K)
    (hJT : J ≠ T) (hJt : IsClassicalMember p f J t) (htz : t ≠ z)
    (A : AtT p f K T J z t tY nY) : IsClassicalMember p f A.J₂ t := by
  have hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  obtain ⟨J', hJ't, hJ'J, hJ'cls, -, -, -, hJ'iso⟩ :=
    exists_twin_iso_at_t S hT.ne.symm hT.mem hKiso hTiso clsT hJ hJK hJT hJt htz
  have hQ : ∀ L ∈ centralizingMembers (𝒞 K) {t},
      (∀ L' ∈ centralizingMembers (𝒞 K) {t}, L' ≠ L → Commutes L L') →
      locImg (𝒞 K) t L ≤ A.d.Q₀ ∨ locImg (𝒞 K) t L ≤ A.d.Q₁ := by
    intro L hL hiso
    rcases members_cases A.d hL with h | h | ⟨R, hR, hLR⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact (not_fund_of_isolated S.inClass A.hP1 A.rf A.d hL hiso hR hLR).elim
  have e0 : ∀ {L L' : Subgroup G}, L ∈ centralizingMembers (𝒞 K) {t} →
      L' ∈ centralizingMembers (𝒞 K) {t} → locImg (𝒞 K) t L ≤ A.d.Q₀ →
      locImg (𝒞 K) t L' ≤ A.d.Q₀ → L = L' := fun hL hL' h h' =>
    eq_of_le_Q S.inClass S.exact A.hP1 A.d.card_le₀ hL hL' h h'
  have e1 : ∀ {L L' : Subgroup G}, L ∈ centralizingMembers (𝒞 K) {t} →
      L' ∈ centralizingMembers (𝒞 K) {t} → locImg (𝒞 K) t L ≤ A.d.Q₁ →
      locImg (𝒞 K) t L' ≤ A.d.Q₁ → L = L' := fun hL hL' h h' =>
    eq_of_le_Q S.inClass S.exact A.hP1 A.d.card_le₁ hL hL' h h'
  have hJ' : locImg (𝒞 K) t J' ≤ A.d.Q₀ ∨ locImg (𝒞 K) t J' ≤ A.d.Q₁ := hQ J' hJ't hJ'iso
  have hJ₂ : locImg (𝒞 K) t A.J₂ ≤ A.d.Q₀ ∨ locImg (𝒞 K) t A.J₂ ≤ A.d.Q₁ :=
    hQ A.J₂ A.hJ₂t A.hJ₂iso
  have hJ0 : locImg (𝒞 K) t J ≤ A.d.Q₀ ∨ locImg (𝒞 K) t J ≤ A.d.Q₁ := hQ J A.hJt A.hJiso
  have hEq : J' = A.J₂ := by
    rcases hJ0 with h0 | h0
    · have h1 : locImg (𝒞 K) t J' ≤ A.d.Q₁ := by
        rcases hJ' with h | h
        · exact (hJ'J (e0 hJ't A.hJt h h0)).elim
        · exact h
      have h2 : locImg (𝒞 K) t A.J₂ ≤ A.d.Q₁ := by
        rcases hJ₂ with h | h
        · exact (A.hJ₂J (e0 A.hJ₂t A.hJt h h0)).elim
        · exact h
      exact e1 hJ't A.hJ₂t h1 h2
    · have h1 : locImg (𝒞 K) t J' ≤ A.d.Q₀ := by
        rcases hJ' with h | h
        · exact h
        · exact (hJ'J (e1 hJ't A.hJt h h0)).elim
      have h2 : locImg (𝒞 K) t A.J₂ ≤ A.d.Q₀ := by
        rcases hJ₂ with h | h
        · exact h
        · exact (A.hJ₂J (e1 A.hJ₂t A.hJt h h0)).elim
      exact e0 hJ't A.hJ₂t h1 h2
  rw [← hEq]
  exact hJ'cls

theorem top_le_iSup_fund (rf : TwinRowFacts p f tY nY)
    (hqs : CFSG.Open.IsQuasisimple (modelUniv tY nY p f Fact.out).K) :
    (⊤ : Subgroup (modelUniv tY nY p f Fact.out).K) ≤
      ⨆ R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D, R := by
  set S' := ⨆ R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D, R with hS
  have hnormal : S'.Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hmapS : S'.map (MulAut.conj g).toMonoidHom ≤ S' := by
      rw [hS, Subgroup.map_iSup]
      refine iSup_le fun R => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hR => ?_
      exact le_iSup₂_of_le (conjSub g R) (conjSub_mem_fundamentalSubgroups hR g) le_rfl
    exact hmapS ⟨x, hx, rfl⟩
  obtain ⟨R₀, hR₀⟩ := rf.nonempty
  obtain ⟨R₁, hR₁, -, hnc⟩ := rf.nc R₀ hR₀
  refine Gaps.top_le_of_normal_of_not_le_center hqs hnormal fun hle => ?_
  have hR₀S : R₀ ≤ Subgroup.center (modelUniv tY nY p f Fact.out).K :=
    (le_iSup₂_of_le _ hR₀ le_rfl).trans hle
  exact hnc fun a _ b hb => Subgroup.mem_center_iff.mp (hR₀S hb) a

theorem range_le_iSup_fund (rf : TwinRowFacts p f tY nY)
    (hqs : CFSG.Open.IsQuasisimple (modelUniv tY nY p f Fact.out).K) {X : Type} [Group X]
    (ψ : (modelUniv tY nY p f Fact.out).K →* X) :
    ψ.range ≤ ⨆ R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D, R.map ψ := by
  have h := Subgroup.map_mono (f := ψ) (top_le_iSup_fund rf hqs)
  rw [← MonoidHom.range_eq_map, Subgroup.map_iSup] at h
  refine h.trans (iSup_le fun R => ?_)
  rw [Subgroup.map_iSup]
  exact iSup_le fun hR => le_iSup₂_of_le R hR le_rfl

theorem sq_central_or_t (S : RouteDSetup p f K z) (hrow : TwinRow tY nY)
    (hsh : (tY = .PSp ∧ nY = 2) ∨ (tY = .PSL ∧ nY = 4) ∨ (tY = .PSU ∧ nY = 4))
    (hshape : LocalShapeT p f 2 tY nY (𝒞 K) z) (hT : IsTwinAt (𝒞 K) K T z)
    (clsT : IsClassicalMember p f T z) (hJ : J ∈ centralizingMembers (𝒞 K) {z}) (hJK : J ≠ K)
    (hJT : J ≠ T) (hJt : IsClassicalMember p f J t) (htz : t ≠ z) (A : AtT p f K T J z t tY nY)
    {c : G} (hcz : c * z = z * c) (hcJ : ∀ j ∈ J, c * j = j * c)
    (hcJ₂ : ∀ j ∈ A.J₂, c * j = j * c) (hc4 : c * c * (c * c) = 1) :
    (∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → N ≠ T →
        N ≤ Subgroup.centralizer ({c * c} : Set G)) ∨
      (∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → N ≠ T →
        N ≤ Subgroup.centralizer ({c * c * t} : Set G)) := by
  classical
  obtain ⟨hG2, hD4, hnA1⟩ := hrow.tag_facts
  have rf := LocalShapeT.twinRowFacts hshape S.odd S.five hG2 hD4 hnA1
  obtain ⟨hfund, hadm⟩ :=
    CFSG.ClassicalInvolution.RouteD.Exotic.admissible_of_localShapeT hshape hD4
  have hfund' : CFSG.ClassicalInvolution.ModelFacts.IsFundTag tY := by
    cases tY <;> trivial
  have hqs : CFSG.Open.IsQuasisimple (modelUniv tY nY p f Fact.out).K :=
    (ModelFacts.modelClauseZero tY nY p f Fact.out hfund' hadm).1
  have hΩ : InClass p f (𝒞 K) := S.inClass
  have hKΩ : K ∈ 𝒞 K := CoreAssembly.mem_conjClass_self K
  have hKiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  have hKz : K ∈ centralizingMembers (𝒞 K) {z} :=
    ⟨hKΩ, le_centralizer_of_isClassicalMember S.cls⟩
  obtain ⟨d⟩ := LocalShapeT.nonempty_dictT2 hD4 rf.fsc hΩ hKΩ S.cls hshape
  have hJ₂cls : IsClassicalMember p f A.J₂ t := isClassical_J₂ S hT clsT hJ hJK hJT hJt htz A
  obtain ⟨RJ, hRJ, hJR⟩ := big_of_ne hΩ S.exact S.p1 rf d hKz hT.mem hT.ne.symm hKiso hTiso hJ
    hJK hJT
  obtain ⟨RJ₂, hRJ₂, hJ₂R⟩ := big_of_ne hΩ S.exact S.p1 rf d hKz hT.mem hT.ne.symm hKiso hTiso
    A.hJ₂z A.hJ₂K A.hJ₂T
  have htY : t ∈ locLayer (𝒞 K) z := le_centralizingLayer hJ hJt.mem
  have ht2 : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two hJt.orderOf_eq_two
  set ty : ↥(locLayer (𝒞 K) z) := ⟨t, htY⟩ with hty
  set tb : locQuot (𝒞 K) z := locMk (𝒞 K) z ty with htb
  have htb2 : tb * tb = 1 := by
    rw [htb, ← map_mul]
    have : ty * ty = 1 := Subtype.ext ht2
    rw [this, map_one]
  have htb1 : tb ≠ 1 := locMk_involution_ne_one hJ hJt
  obtain ⟨x, hxR, hxt⟩ : ∃ x ∈ RJ, d.ψ x = tb := by
    have : tb ∈ locImg (𝒞 K) z J := ⟨ty, Subgroup.mem_subgroupOf.mpr hJt.mem, rfl⟩
    rw [hJR] at this
    exact Subgroup.mem_map.mp this
  obtain ⟨x', hx'R, hx't⟩ : ∃ x' ∈ RJ₂, d.ψ x' = tb := by
    have : tb ∈ locImg (𝒞 K) z A.J₂ := ⟨ty, Subgroup.mem_subgroupOf.mpr hJ₂cls.mem, rfl⟩
    rw [hJ₂R] at this
    exact Subgroup.mem_map.mp this
  have hne2 : ¬ (tY = .PSL ∧ nY = 2) := by
    rintro ⟨h1, h2⟩
    rcases hsh with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩
    · rw [h1] at h3
      exact absurd h3 (by decide)
    · omega
    · rw [h1] at h3
      exact absurd h3 (by decide)
  have hMFZ := Gaps.fundNoncentral p
  have hsq1 : ∀ R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D,
      ∀ r ∈ R, d.ψ r * d.ψ r = 1 → r * r = 1 := by
    intro R hR r hrR hr
    have h1 : r * r ∈ Subgroup.center (modelUniv tY nY p f Fact.out).K :=
      d.ker_le (MonoidHom.mem_ker.mpr (by rw [map_mul]; exact hr))
    refine hMFZ tY nY f hfund hadm hne2 R hR (r * r) (R.mul_mem hrR hrR) fun y => ?_
    have hc : r * r * y = y * (r * r) := (Subgroup.mem_center_iff.mp h1 y).symm
    have h2 : r * r * y * (r * r)⁻¹ * y⁻¹ = 1 := by rw [hc]; group
    rw [h2]
    exact Subgroup.one_mem _
  have hx2 : x * x = 1 := hsq1 RJ hRJ x hxR (by rw [hxt, htb2])
  have hx'2 : x' * x' = 1 := hsq1 RJ₂ hRJ₂ x' hx'R (by rw [hx't, htb2])
  have hx1 : x ≠ 1 := fun h => htb1 (by rw [← hxt, h, map_one])
  have hx'1 : x' ≠ 1 := fun h => htb1 (by rw [← hx't, h, map_one])
  have hpair : TwinPairOn tY (modelUniv tY nY p f Fact.out) d.ψ RJ RJ₂ x x' := by
    refine ⟨d.ker_le, hRJ, hRJ₂, ?_, ?_, hxR, hx2, hx1, hx'R, hx'2, hx'1, by rw [hxt, hx't]⟩
    · intro h
      apply A.hJ₂J
      exact locImg_injOn hΩ S.p1 A.hJ₂z hJ (by rw [hJ₂R, hJR, h])
    · exact (commutes_iff_fund hΩ S.p1 rf d hJ A.hJ₂z hRJ hJR hJ₂R).mp
        (A.hJiso A.J₂ A.hJ₂t A.hJ₂J)
  have hcz' : c * z * c⁻¹ = z := mul_inv_eq_iff_eq_mul.mpr hcz
  have hcc'' : (c * c) * z = z * (c * c) := by
    rw [mul_assoc, hcz, ← mul_assoc, hcz, mul_assoc]
  have hcc' : c * c * z * (c * c)⁻¹ = z := mul_inv_eq_iff_eq_mul.mpr hcc''
  have htz' : t * z = z * t := Subgroup.mem_centralizer_singleton_iff.mp (hJ.2 hJt.mem)
  have hcct'' : (c * c * t) * z = z * (c * c * t) := by
    rw [mul_assoc, htz', ← mul_assoc, hcc'', mul_assoc]
  have hcct : c * c * t * z * (c * c * t)⁻¹ = z := mul_inv_eq_iff_eq_mul.mpr hcct''
  set σ := locAut hΩ.conjInvariant hcz' with hσdef
  have hσmk : ∀ y : ↥(locLayer (𝒞 K) z), σ (locMk (𝒞 K) z y) =
      locMk (𝒞 K) z (layerAut hΩ.conjInvariant hcz' y) := fun y => rfl
  have hfix : ∀ N ∈ centralizingMembers (𝒞 K) {z}, (∀ n ∈ N, c * n = n * c) →
      ∀ a ∈ locImg (𝒞 K) z N, σ a = a := fun N hN hcN =>
    (locAut_fixed_iff hΩ S.p1 hcz' hN).mp fun n hn =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hcN n hn).symm
  have hσR : ∀ r ∈ RJ, σ (d.ψ r) = d.ψ r := by
    intro r hr
    have : d.ψ r ∈ locImg (𝒞 K) z J := by
      rw [hJR]
      exact Subgroup.mem_map_of_mem _ hr
    exact hfix J hJ hcJ _ this
  have hσR' : ∀ r ∈ RJ₂, σ (d.ψ r) = d.ψ r := by
    intro r hr
    have : d.ψ r ∈ locImg (𝒞 K) z A.J₂ := by
      rw [hJ₂R]
      exact Subgroup.mem_map_of_mem _ hr
    exact hfix A.J₂ A.hJ₂z hcJ₂ _ this
  have hconjz : ∀ B ∈ centralizingMembers (𝒞 K) {z},
      (∀ L ∈ centralizingMembers (𝒞 K) {z}, L ≠ B → Commutes B L) →
      ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → N ≠ T → conjSub c N ≠ B := by
    intro B hB hiso N hN hNK hNT hEq
    obtain ⟨L', hL', hL'N, hnc⟩ := exists_noncomm_of_ne hΩ S.exact S.p1 rf d hKz hT.mem
      hT.ne.symm hKiso hTiso hN hNK hNT
    have hne : conjSub c L' ≠ B := by
      intro h
      apply hL'N
      apply conjSub_injective c
      rw [h, ← hEq]
    have hcomm := hiso _ (conjSub_mem_centralizingMembers hΩ.conjInvariant hcz' hL') hne
    rw [← hEq] at hcomm
    exact hnc ((commutes_conjSub_iff c).mp hcomm)
  have hmapfund : ∀ R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D,
      ∀ l ∈ R.map d.ψ, σ l ∈ d.ψ.range := by
    intro R hR l hl
    obtain ⟨N, hN, hNR⟩ := mem_locFamily_iff.mp (d.mem_fam R hR)
    have hNK : N ≠ K := by
      rintro rfl
      exact not_fund_of_isolated hΩ S.p1 rf d hN hKiso hR hNR
    have hNT : N ≠ T := by
      rintro rfl
      exact not_fund_of_isolated hΩ S.p1 rf d hN hTiso hR hNR
    have hN' := conjSub_mem_centralizingMembers hΩ.conjInvariant hcz' hN
    have hN'K : conjSub c N ≠ K := hconjz K hKz hKiso N hN hNK hNT
    have hN'T : conjSub c N ≠ T := hconjz T hT.mem hTiso N hN hNK hNT
    obtain ⟨R', hR', hN'R⟩ := big_of_ne hΩ S.exact S.p1 rf d hKz hT.mem hT.ne.symm hKiso hTiso
      hN' hN'K hN'T
    have hl' : l ∈ locImg (𝒞 K) z N := hNR ▸ hl
    have h1 : σ l ∈ locImg (𝒞 K) z (conjSub c N) := by
      rw [← locAut_locImg hΩ.conjInvariant hcz' N]
      exact Subgroup.mem_map_of_mem _ hl'
    rw [hN'R] at h1
    obtain ⟨k, -, hk⟩ := Subgroup.mem_map.mp h1
    exact ⟨k, hk⟩
  have hσL : ∀ l ∈ d.ψ.range, σ l ∈ d.ψ.range := by
    have hgen := range_le_iSup_fund rf hqs d.ψ
    have h1 : (⨆ R ∈ fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D, R.map d.ψ) ≤
        d.ψ.range.comap σ.toMonoidHom :=
      iSup₂_le fun R hR l hl => hmapfund R hR l hl
    exact fun l hl => h1 (hgen hl)
  have hσ4 : ∀ l : locQuot (𝒞 K) z, σ (σ (σ (σ l))) = l := by
    intro l
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective l
    show σ (σ (σ (σ (locMk (𝒞 K) z y)))) = locMk (𝒞 K) z y
    rw [hσmk, hσmk, hσmk, hσmk]
    congr 1
    apply Subtype.ext
    show c * (c * (c * (c * (y : G) * c⁻¹) * c⁻¹) * c⁻¹) * c⁻¹ = y
    calc c * (c * (c * (c * (y : G) * c⁻¹) * c⁻¹) * c⁻¹) * c⁻¹
        = (c * c * (c * c)) * (y : G) * (c * c * (c * c))⁻¹ := by group
      _ = y := by rw [hc4]; group
  have hV := ModelFacts.Orth15.twinOuterVac_of_small S.odd S.five hadm hsh
  have hres := sq_aut_of_twinOuterVac hV d.ψ hpair σ hσL hσR hσR' fun l _ => hσ4 l
  have hτσσ : ∀ a : locQuot (𝒞 K) z,
      locAut hΩ.conjInvariant hcc' a = σ (σ a) := by
    intro a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective a
    show locMk (𝒞 K) z (layerAut hΩ.conjInvariant hcc' y) =
      σ (σ (locMk (𝒞 K) z y))
    rw [hσmk, hσmk]
    congr 1
    apply Subtype.ext
    show c * c * (y : G) * (c * c)⁻¹ = c * (c * (y : G) * c⁻¹) * c⁻¹
    group
  have hmemR : ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ K → N ≠ T →
      ∀ a ∈ locImg (𝒞 K) z N, a ∈ d.ψ.range := by
    intro N hN hNK hNT a ha
    obtain ⟨R', hR', hNR'⟩ := big_of_ne hΩ S.exact S.p1 rf d hKz hT.mem hT.ne.symm hKiso hTiso
      hN hNK hNT
    rw [hNR'] at ha
    obtain ⟨k, -, hk⟩ := Subgroup.mem_map.mp ha
    exact ⟨k, hk⟩
  rcases hres with hA | hB
  · left
    intro N hN hNK hNT
    refine (locAut_fixed_iff hΩ S.p1 hcc' hN).mpr fun a ha => ?_
    rw [hτσσ]
    exact hA a (hmemR N hN hNK hNT a ha)
  · right
    intro N hN hNK hNT
    refine (locAut_fixed_iff hΩ S.p1 hcct hN).mpr fun a ha => ?_
    have haR := hmemR N hN hNK hNT a ha
    obtain ⟨y, hy, rfl⟩ := ha
    have hxr : tb ∈ d.ψ.range := ⟨x, hxt⟩
    have hb : locMk (𝒞 K) z (ty * y * ty⁻¹) = tb * locMk (𝒞 K) z y * tb⁻¹ := by
      rw [htb, map_mul, map_mul, map_inv]
    have hbR : tb * locMk (𝒞 K) z y * tb⁻¹ ∈ d.ψ.range :=
      (d.ψ.range).mul_mem ((d.ψ.range).mul_mem hxr haR) ((d.ψ.range).inv_mem hxr)
    show locMk (𝒞 K) z (layerAut hΩ.conjInvariant hcct y) = locMk (𝒞 K) z y
    have h1 : layerAut hΩ.conjInvariant hcct y =
        layerAut hΩ.conjInvariant hcc' (ty * y * ty⁻¹) := by
      apply Subtype.ext
      show c * c * t * (y : G) * (c * c * t)⁻¹ = c * c * (t * (y : G) * t⁻¹) * (c * c)⁻¹
      group
    rw [h1, ← locAut_mk, hτσσ, hb, hB _ hbR, hxt]
    calc tb * (tb * locMk (𝒞 K) z y * tb⁻¹) * tb⁻¹
        = (tb * tb) * locMk (𝒞 K) z y * (tb * tb)⁻¹ := by group
      _ = locMk (𝒞 K) z y := by rw [htb2]; group

end Act

end CFSG.ClassicalInvolution.RouteD.TWT4
