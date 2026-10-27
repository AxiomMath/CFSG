module

public import CFSG.ClassicalInvolution.Q3.Q3TLTDatum
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComponentLayerCentralizesSolvableNormalized

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution

section Layer

variable {G : Type*} [Group G]

theorem componentLayerOf_subgroupOf_normal (C : Subgroup G) :
    ((GorensteinWalter.componentLayerOf C).subgroupOf C).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    (GorensteinWalter.componentLayerOf_isNormalIn C).1).mpr
    (GorensteinWalter.le_normalizer_of_isNormalIn (GorensteinWalter.componentLayerOf_isNormalIn C))

theorem isSubnormal_of_isSubnormal_inf_layer {C J : Subgroup G}
    (hJ : CFSG.Open.IsSubnormal J
      (C ⊓ Subgroup.centralizer (GorensteinWalter.componentLayerOf C : Set G))) :
    CFSG.Open.IsSubnormal J C :=
  isSubnormal_of_inf_centralizer (GorensteinWalter.componentLayerOf_isNormalIn C).1
    (componentLayerOf_subgroupOf_normal C) hJ

theorem le_of_isSubnormal {A B : Subgroup G} (h : CFSG.Open.IsSubnormal A B) : A ≤ B :=
  h.le

theorem isComponentOf_of_open {A C : Subgroup G} (h : CFSG.Open.IsComponentOf A C) :
    GorensteinWalter.IsComponentOf A C := by
  obtain ⟨hAC, hsub, hperf, hsimple⟩ := h
  have h2 := CFSG.ClassicalInvolution.isSubnormal_subgroupOf hsub C
  rw [Subgroup.subgroupOf_self] at h2
  have : IsSimpleGroup (↥A ⧸ Subgroup.center ↥A) := hsimple
  refine ⟨hAC, CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain h2
    Subgroup.IsSubnormal.top, ?_, hperf, hsimple⟩
  exact (QuotientGroup.mk'_surjective (Subgroup.center ↥A)).nontrivial

theorem componentLayerOf_inf_centralizer_eq_bot (C : Subgroup G) :
    GorensteinWalter.componentLayerOf
      (C ⊓ Subgroup.centralizer (GorensteinWalter.componentLayerOf C : Set G)) = ⊥ := by
  set E := GorensteinWalter.componentLayerOf C with hE
  have hEn := GorensteinWalter.componentLayerOf_isNormalIn C
  have hYn : GorensteinWalter.IsNormalIn (C ⊓ Subgroup.centralizer (E : Set G)) C := by
    refine ⟨inf_le_left, fun c hc y hy => Subgroup.mem_inf.mpr
      ⟨C.mul_mem (C.mul_mem hc (Subgroup.mem_inf.mp hy).1) (C.inv_mem hc), ?_⟩⟩
    refine Subgroup.mem_centralizer_iff.mpr fun e he => ?_
    have hce : c⁻¹ * e * c ∈ E := by simpa using hEn.2 c⁻¹ (C.inv_mem hc) e he
    have := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2 _ hce
    calc e * (c * y * c⁻¹) = c * ((c⁻¹ * e * c) * y) * c⁻¹ := by group
      _ = c * (y * (c⁻¹ * e * c)) * c⁻¹ := by rw [this]
      _ = c * y * c⁻¹ * e := by group
  rw [GorensteinWalter.componentLayerOf]
  refine le_bot_iff.mp (sSup_le fun K hK => ?_)
  exfalso
  obtain ⟨hKY, hKsub, hKq⟩ := hK
  have hKC : (K.subgroupOf C).IsSubnormal :=
    GorensteinWalter.fstar_isSubnormal_subgroupOf_of_subnormal_subgroupOf_normal hKY hKsub
      inf_le_left hYn
  have hKE : K ≤ E :=
    le_sSup (s := {K : Subgroup G | GorensteinWalter.IsComponentOf K C})
      ⟨hKY.trans inf_le_left, hKC, hKq⟩
  have hKcent : K ≤ Subgroup.centralizer (E : Set G) := hKY.trans inf_le_right
  obtain ⟨hnt, hperf, -⟩ := hKq
  have : Nontrivial ↥K := hnt
  have hbot : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a _ b _
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hKcent a.2) b (hKE b.2))
  rw [← commutator_def, hperf] at hbot
  obtain ⟨x, hx⟩ := exists_ne (1 : ↥K)
  have hx1 : x ∈ (⊥ : Subgroup ↥K) := by
    rw [← hbot]
    exact Subgroup.mem_top x
  exact hx (Subgroup.mem_bot.mp hx1)

theorem not_isComponentOf_inf_layer {C A : Subgroup G}
    (hA : CFSG.Open.IsComponentOf A
      (C ⊓ Subgroup.centralizer (GorensteinWalter.componentLayerOf C : Set G))) : False := by
  have hgw := isComponentOf_of_open hA
  have hle : A ≤ GorensteinWalter.componentLayerOf
      (C ⊓ Subgroup.centralizer (GorensteinWalter.componentLayerOf C : Set G)) :=
    le_sSup hgw
  rw [componentLayerOf_inf_centralizer_eq_bot] at hle
  obtain ⟨-, -, hnt, -, -⟩ := hgw
  have : Nontrivial ↥A := hnt
  obtain ⟨x, hx⟩ := exists_ne (1 : ↥A)
  exact hx (Subtype.ext (Subgroup.mem_bot.mp (hle x.2)))

end Layer

namespace TightDatum

variable {G : Type*} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G}

theorem isSolvable (h : TightDatum R S t) : Group.IsSolvable R := by
  have hO : Group.IsSolvable (classicalInvolutionOddCore R) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (CFSG.ComponentClassification.OddCore.odd_card R)
  have hq : Group.IsSolvable (R ⧸ classicalInvolutionOddCore R) :=
    have := h.twoGroup.isNilpotent
    inferInstance
  exact Group.isSolvable_of_subgroup_quotient (classicalInvolutionOddCore R)

theorem commutator_layer_eq_bot (h : TightDatum R S t) :
    ⁅GorensteinWalter.componentLayerOf (Subgroup.centralizer ({t} : Set G)), R⁆ = ⊥ :=
  GorensteinWalter.componentLayerOf_centralizes_solvable_of_le_normalizer _ R h.cent
    h.isSolvable ((GorensteinWalter.componentLayerOf_isNormalIn _).1.trans h.le_normalizer)

theorem le_centralizer_layer (h : TightDatum R S t) :
    R ≤ Subgroup.centralizer
      (GorensteinWalter.componentLayerOf (Subgroup.centralizer ({t} : Set G)) : Set G) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (by rw [Subgroup.commutator_comm]; exact h.commutator_layer_eq_bot)

theorem le_inf_centralizer_layer (h : TightDatum R S t) :
    R ≤ Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer
      (GorensteinWalter.componentLayerOf (Subgroup.centralizer ({t} : Set G)) : Set G) :=
  le_inf h.cent h.le_centralizer_layer

theorem le_centralizer_isComponentOf (h : TightDatum R S t) {E : Subgroup G}
    (hE : GorensteinWalter.IsComponentOf E (Subgroup.centralizer ({t} : Set G))) :
    R ≤ Subgroup.centralizer (E : Set G) := by
  have hEle : E ≤ GorensteinWalter.componentLayerOf (Subgroup.centralizer ({t} : Set G)) :=
    le_sSup hE
  exact fun _ hr => Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hEle)
    (h.le_centralizer_layer hr)

theorem le_centralizer_of_isSubnormal (h : TightDatum R S t) {A : Subgroup G}
    (hAC : CFSG.Open.IsSubnormal A (Subgroup.centralizer ({t} : Set G)))
    (hA : CFSG.Open.IsQuasisimple ↥A) : R ≤ Subgroup.centralizer (A : Set G) := by
  exact h.le_centralizer_isComponentOf
    (isComponentOf_of_open ⟨le_of_isSubnormal hAC, hAC, hA⟩)

end TightDatum

end CFSG.ClassicalInvolution.Q3
