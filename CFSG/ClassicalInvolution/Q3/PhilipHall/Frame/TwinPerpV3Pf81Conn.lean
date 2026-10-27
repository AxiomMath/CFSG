module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf80Trans
public import CFSG.ClassicalInvolution.SmallCases.A7T22Sig

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Balance (oddQuotMk)

section Gen

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem mem_coreAt_of_unique {J : Subgroup G} {z : G} (hz : IsUniqueInvolution J z)
    (hzC : z ∈ Subgroup.centralizer ({c} : Set G)) : z ∈ TwinADescent.coreAt c J := by
  have hle : Subgroup.zpowers z ≤ J ⊓ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.zpowers_le.mpr ⟨hz.mem, hzC⟩
  exact le_tightCore_of_isPGroup hle
    (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hz.sq)
    (Subgroup.mem_zpowers z)

theorem mem_coreHull_of_unique {J : Subgroup G} (hJ : J ∈ tqMembers3 Ω c) {z : G}
    (hz : IsUniqueInvolution J z) (hzC : z ∈ Subgroup.centralizer ({c} : Set G)) :
    (⟨z, hzC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈ coreHull Ω c :=
  le_coreHull hJ (Subgroup.mem_subgroupOf.mpr (mem_coreAt_of_unique hz hzC))

theorem isUniqueInvolution_secImg_mk {J : Subgroup G} (hJ : J ∈ tqMembers3 Ω c)
    (hex : ∃ u' : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c),
      IsUniqueInvolution (secImg Ω c J) u')
    {z : G} (hz : IsUniqueInvolution J z) (hzC : z ∈ Subgroup.centralizer ({c} : Set G)) :
    IsUniqueInvolution (secImg Ω c J)
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c))
        (⟨⟨z, hzC⟩, mem_coreHull_of_unique hJ hz hzC⟩ : ↥(coreHull Ω c))) := by
  obtain ⟨u', hinv⟩ := hex
  have htH := mem_coreHull_of_unique hJ hz hzC
  have hsq' : (⟨z, hzC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) * ⟨z, hzC⟩ = 1 :=
    Subtype.ext hz.sq
  have hmem : QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c))
      (⟨⟨z, hzC⟩, htH⟩ : ↥(coreHull Ω c)) ∈ secImg Ω c J :=
    ⟨⟨⟨z, hzC⟩, htH⟩, Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_subgroupOf.mpr (mem_coreAt_of_unique hz hzC)), rfl⟩
  have htb1 : QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c))
      (⟨⟨z, hzC⟩, htH⟩ : ↥(coreHull Ω c)) ≠ 1 := by
    intro h1
    have h1' : (⟨⟨z, hzC⟩, htH⟩ : ↥(coreHull Ω c)) ∈
        classicalInvolutionOddCore ↥(coreHull Ω c) := (QuotientGroup.eq_one_iff _).mp h1
    have hord : orderOf (⟨⟨z, hzC⟩, htH⟩ : ↥(coreHull Ω c)) = 2 := by
      refine orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext hsq') ?_
      intro e
      exact hz.ne_one (congrArg (fun w : ↥(coreHull Ω c) =>
        (((w : ↥(Subgroup.centralizer ({c} : Set G)))) : G)) e)
    have hdvd := Subgroup.orderOf_dvd_natCard _ h1'
    rw [hord] at hdvd
    exact absurd ((CFSG.ComponentClassification.OddCore.odd_card _).of_dvd_nat hdvd) (by decide)
  have htb2 : QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c))
      (⟨⟨z, hzC⟩, htH⟩ : ↥(coreHull Ω c)) *
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c))
        (⟨⟨z, hzC⟩, htH⟩ : ↥(coreHull Ω c)) = 1 := by
    rw [← map_mul]
    have : (⟨⟨z, hzC⟩, htH⟩ : ↥(coreHull Ω c)) * ⟨⟨z, hzC⟩, htH⟩ = 1 := Subtype.ext hsq'
    rw [this, map_one]
  have heq := (hinv.unique _ hmem htb2).resolve_left htb1
  rw [heq]
  exact hinv

theorem sec_mk_conj_odd (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {t : G}
    (htC : t ∈ Subgroup.centralizer ({c} : Set G))
    (htH : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈ coreHull Ω c) {n : G}
    (hn : n ∈ oddCoreOf (Subgroup.centralizer ({c} : Set G)))
    (hnt : n * t * n⁻¹ ∈ Subgroup.centralizer ({c} : Set G))
    (hntH : (⟨n * t * n⁻¹, hnt⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈ coreHull Ω c) :
    QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c))
        (⟨⟨n * t * n⁻¹, hnt⟩, hntH⟩ : ↥(coreHull Ω c)) =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c))
        (⟨⟨t, htC⟩, htH⟩ : ↥(coreHull Ω c)) := by
  apply TwinExitPf6.secMap_injective hΩ hc2
  rw [TwinExitPf6.secMap_mk, TwinExitPf6.secMap_mk]
  obtain ⟨n', hn', rfl⟩ := hn
  have e : (⟨(n' : G) * t * (n' : G)⁻¹, hnt⟩ : ↥(Subgroup.centralizer ({c} : Set G))) =
      n' * ⟨t, htC⟩ * n'⁻¹ := Subtype.ext rfl
  show oddQuotMk c (⟨(n' : G) * t * (n' : G)⁻¹, hnt⟩ : ↥(Subgroup.centralizer ({c} : Set G))) =
    oddQuotMk c ⟨t, htC⟩
  have h1 : oddQuotMk c n' = 1 := (QuotientGroup.eq_one_iff _).mpr hn'
  rw [e, map_mul, map_mul, map_inv, h1]
  group

theorem allMembers_involution_of_connected (hΩ : HypOmegaGen Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hex : ∀ J ∈ tqMembers3 Ω c, ∃ u' : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c),
      IsUniqueInvolution (secImg Ω c J) u')
    {K₃ : Subgroup G} (hK₃ : K₃ ∈ tqMembers3 Ω c) {t : G} (hz : IsUniqueInvolution K₃ t)
    (htC : t ∈ Subgroup.centralizer ({c} : Set G))
    (htH : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈ coreHull Ω c)
    (hSig : ∀ J ∈ dstarComp Ω K₃, J ∈ twinSet Ω K₃)
    (hconn : ∀ M ∈ TwinDisc.secFam Ω c, M ∈ dstarComp (TwinDisc.secFam Ω c) (secImg Ω c K₃)) :
    ∀ M ∈ TwinDisc.secFam Ω c, IsUniqueInvolution M
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c))
        (⟨⟨t, htC⟩, htH⟩ : ↥(coreHull Ω c))) := by
  intro M hM
  obtain ⟨J, hJ, rfl⟩ := exists_of_mem_secFam hM
  obtain ⟨n, hn, J', hJ', hJ'd, hJeq⟩ := exists_conj_tq_of_connected hΩ hc2 hK₃ hconn J hJ
  have hJ't : IsUniqueInvolution J' t := isUniqueInvolution_of_mem_twinSet hz (hSig J' hJ'd)
  have hnC : n ∈ Subgroup.centralizer ({c} : Set G) := by
    obtain ⟨n', -, rfl⟩ := hn
    exact n'.2
  have hJt : IsUniqueInvolution J (n * t * n⁻¹) := by
    rw [hJeq]
    exact hJ't.conj n
  have hntC : n * t * n⁻¹ ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hnC htC) (Subgroup.inv_mem _ hnC)
  have hntH := mem_coreHull_of_unique hJ hJt hntC
  have h1 := isUniqueInvolution_secImg_mk hJ (hex J hJ) hJt hntC
  have h2 := sec_mk_conj_odd hΩ hc2 htC htH hn hntC hntH
  rw [h2] at h1
  exact h1

theorem central_of_allMembers (hS : omegaGen (TwinDisc.secFam Ω c) = ⊤)
    {tb : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)}
    (hall : ∀ M ∈ TwinDisc.secFam Ω c, IsUniqueInvolution M tb)
    (y : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) : y * tb = tb * y := by
  have hle : omegaGen (TwinDisc.secFam Ω c) ≤ Subgroup.centralizer ({tb} : Set _) := by
    refine iSup₂_le fun M hM x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    have := (hall M hM).conj_eq (conjSub_eq_self_of_mem hx)
    calc tb * x = (x * tb * x⁻¹) * x := by rw [this]
      _ = x * tb := by group
  have hy : y ∈ omegaGen (TwinDisc.secFam Ω c) := by rw [hS]; trivial
  have := Subgroup.mem_centralizer_iff.mp (hle hy) tb (Set.mem_singleton _)
  exact this.symm

end Gen

section Gen2

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem mem_zStarOf_of_allMembers (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {K₃ : Subgroup G} (hK₃ : K₃ ∈ tqMembers3 Ω c) {t : G}
    (htC : t ∈ Subgroup.centralizer ({c} : Set G))
    (htH : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈ coreHull Ω c)
    (hall : ∀ M ∈ TwinDisc.secFam Ω c, IsUniqueInvolution M
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c))
        (⟨⟨t, htC⟩, htH⟩ : ↥(coreHull Ω c)))) :
    t ∈ zStarOf (Subgroup.centralizer ({c} : Set G)) := by
  refine ⟨⟨t, htC⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_center_iff]
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
    (classicalInvolutionOddCore ↥(Subgroup.centralizer ({c} : Set G))) q
  set tb := QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c))
    (⟨⟨t, htC⟩, htH⟩ : ↥(coreHull Ω c)) with htb
  have hA := secImg_mem_secFam hK₃
  have hmap := TwinExitPf10.secAut_map_secFam hΩ hc2 g hA
  have h1 := isUniqueInvolution_map_mulEquiv (TwinExitPf6.secAut Ω c hΩ hc2 g) (hall _ hA)
  have h3 : TwinExitPf6.secAut Ω c hΩ hc2 g tb = tb := h1.eq (hall _ hmap)
  have h5 := TwinExitPf6.secMap_secAut hΩ hc2 g tb
  rw [h3] at h5
  have hmk : TwinExitPf6.secMap Ω c hΩ hc2 tb = oddQuotMk c ⟨t, htC⟩ := rfl
  show oddQuotMk c g * oddQuotMk c ⟨t, htC⟩ = oddQuotMk c ⟨t, htC⟩ * oddQuotMk c g
  rw [← hmk]
  calc oddQuotMk c g * TwinExitPf6.secMap Ω c hΩ hc2 tb
      = oddQuotMk c g * TwinExitPf6.secMap Ω c hΩ hc2 tb * (oddQuotMk c g)⁻¹ * oddQuotMk c g := by group
    _ = TwinExitPf6.secMap Ω c hΩ hc2 tb * oddQuotMk c g := by rw [← h5]

end Gen2

section Reduction

variable {n : ℕ}

theorem dstarComp_subset_twinSet_of_conn {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    (hP : Q3CL.PartIHypG Ω) {L : Subgroup G} (hL : L ∈ Ω) {z : G} (hz : IsUniqueInvolution L z)
    (hperp : KPerp Ω L = twinSet Ω L) {W : Subgroup G} (hW : W ∈ WSet Ω)
    (hconn : DbarConnected Ω W) : ∀ J ∈ dstarComp Ω L, J ∈ twinSet Ω L := by
  have heq : dComp Ω L = dstarComp Ω L := by
    by_contra hne
    exact Q3T6.Mu.thompsonGraphAll hP hL hne hW hconn
  intro J hJ
  rw [← heq] at hJ
  exact A7T22.dComp_subset_twinSet hP.hyp hL hz hperp hJ

end Reduction

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
