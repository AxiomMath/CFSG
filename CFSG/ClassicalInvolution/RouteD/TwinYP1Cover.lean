module

public import CFSG.ClassicalInvolution.RouteD.TwinYP1Frame
public import CFSG.ClassicalInvolution.Asc77.AscIHSectI
public import CFSG.ClassicalInvolution.Asc77.AscIHSectB
public import CFSG.ClassicalInvolution.Asc77.AscIHSectC
public import CFSG.ClassicalInvolution.Balance.PassTwoLocal
public import CFSG.ClassicalInvolution.Balance.BootstrapQ27Decomp
public import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
public import CFSG.ClassicalInvolution.Balance.PassTwoModelFacts
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
public import CFSG.ClassicalInvolution.Asc77.AscIHSectG

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinY

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.Open (classicalInvolutionOddCore)

section Trans

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {u : G}

omit [Finite G] in
theorem layerHull_centralizer_eq (Ω : Set (Subgroup G)) (u : G) :
    layerHull Ω (Subgroup.centralizer ({u} : Set G)) = locLayer Ω u := by
  apply le_antisymm
  · exact iSup₂_le fun L hL => iSup_le fun hLY => le_centralizingLayer ⟨hL, hLY⟩
  · exact iSup₂_le fun L hL => le_layerHull hL.1 hL.2

omit [Finite G] in
theorem locFamily_eq (Ω : Set (Subgroup G)) (u : G) :
    oddQuotientFamily (restrictFamily Ω (locLayer Ω u)) = locFamily Ω u := by
  unfold locFamily
  congr 1
  ext L'
  constructor
  · rintro ⟨L, hL, hLY, rfl⟩
    exact ⟨L, ⟨hL, hLY.trans (centralizingLayer_le_centralizer Ω {u})⟩, hLY, rfl⟩
  · rintro ⟨L, hL, hLY, rfl⟩
    exact ⟨L, hL.1, hLY, rfl⟩

theorem transSection_of_loc (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hA : ∀ L ∈ Ω, AEmpty Ω L)
    (htrans : ∀ K ∈ locFamily Ω u, ∀ L ∈ locFamily Ω u, ∃ g : locQuot Ω u, conjSub g K = L) :
    TransSection p f (locFamily Ω u) := by
  have hS := genSection_layerHull hp hq hΩ hA (Subgroup.centralizer ({u} : Set G))
  rw [layerHull_centralizer_eq, locFamily_eq] at hS
  exact hS.toTrans htrans

theorem card_locQuot_lt (hu : ¬ ({u} : Set G) ⊆ Subgroup.center G) :
    Nat.card (locQuot Ω u) < Nat.card G := by
  have h1 : Nat.card (locQuot Ω u) ≤ Nat.card ↥(locLayer Ω u) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (classicalInvolutionOddCore ↥(locLayer Ω u))
    exact h ▸ Nat.le_mul_of_pos_right _ Nat.card_pos
  have h2 : Nat.card ↥(locLayer Ω u) ≤ Nat.card ↥(Subgroup.centralizer ({u} : Set G)) :=
    Subgroup.card_le_of_le (centralizingLayer_le_centralizer Ω {u})
  have hne : Subgroup.centralizer ({u} : Set G) ≠ ⊤ := fun h =>
    hu (Subgroup.centralizer_eq_top_iff_subset.mp h)
  have h3 := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hne)
  rw [Subgroup.card_top] at h3
  omega

end Trans

section OneComp

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {u : G}

theorem twin_locFamily (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {J J' : Subgroup G} {t : G}
    (hJ : J ∈ centralizingMembers Ω {u}) (hJ' : J' ∈ centralizingMembers Ω {u})
    (hUt : IsUniqueInvolution J t) (hUt' : IsUniqueInvolution J' t)
    (hcomm : Commutes J J') :
    ∃ K ∈ locFamily Ω u, ∃ K' ∈ twinSet (locFamily Ω u) K, K' ≠ K := by
  have hJY : J ≤ locLayer Ω u := le_centralizingLayer hJ
  have hJ'Y : J' ≤ locLayer Ω u := le_centralizingLayer hJ'
  have hO : Odd (Nat.card (classicalInvolutionOddCore ↥(locLayer Ω u))) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥(locLayer Ω u)
  refine ⟨locImg Ω u J, mem_locFamily_iff.mpr ⟨J, hJ, rfl⟩, locImg Ω u J',
    ⟨mem_locFamily_iff.mpr ⟨J', hJ', rfl⟩, QuotientGroup.mk' _ ⟨t, hJY hUt.mem⟩, ?_, ?_⟩, ?_⟩
  · exact isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hO _)
      (isUniqueInvolution_subgroupOf hUt hJY)
  · have h := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hO _)
      (isUniqueInvolution_subgroupOf hUt' hJ'Y)
    have e : (⟨t, hJY hUt.mem⟩ : ↥(locLayer Ω u)) = ⟨t, hJ'Y hUt'.mem⟩ := rfl
    rw [e]
    exact h
  · intro h
    have hc := commutes_locImg_of_commutes (x := u) (Ω := Ω) hcomm
    rw [h] at hc
    exact locImg_not_commutative hΩ hex hJ hc

theorem exists_orthLie_of_trans (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hA : ∀ L ∈ Ω, AEmpty Ω L) (hP4 : Ih8G2D4 p f) (hn : CITBelowU p f (Nat.card G))
    (hu : ¬ ({u} : Set G) ⊆ Subgroup.center G)
    (htrans : ∀ K ∈ locFamily Ω u, ∀ L ∈ locFamily Ω u, ∃ g : locQuot Ω u, conjSub g K = L)
    (htwin : ∃ K ∈ locFamily Ω u, ∃ K' ∈ twinSet (locFamily Ω u) K, K' ≠ K) :
    ∃ D : LieSystemData p f (locQuot Ω u) (locFamily Ω u), D.card = 1 ∧ ∃ i : Fin D.card,
      ∃ (d : ℕ) (ε : Bool), 5 ≤ d ∧ IsOrthTag d ε (D.tag i) (D.rank i) := by
  have hS := transSection_of_loc hp hq hΩ hA htrans
  obtain ⟨K, hK, htw⟩ := htwin
  obtain ⟨d, ε, hd, t, n, hdt, hLie⟩ := thm7SectBelow_of hP4 hn hp hq (locQuot Ω u)
    (card_locQuot_lt hu) (locFamily Ω u) hS K hK htw
  obtain ⟨D, hcard, i, ht, hr⟩ := LieSystemData.exists_of_hasLieType hS.gen hLie
  exact ⟨D, hcard, i, d, ε, hd, by rw [ht, hr]; exact hdt⟩

theorem inCommonComponent_of_card_one (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (D : LieSystemData p f (locQuot Ω u) (locFamily Ω u)) (hD : D.card = 1)
    {K' J : Subgroup G} (hK' : K' ∈ centMembers Ω u) (hJ : J ∈ centMembers Ω u) :
    InCommonComponent u K' J := by
  have hθ := layerQuotientHom_injective (a := u) hΩ.conjInvariant
  have hnc : ∀ L ∈ locFamily Ω u, ¬ L ≤ Subgroup.center (locQuot Ω u) := by
    intro L hL
    obtain ⟨L₀, hL₀, rfl⟩ := mem_locFamily_iff.mp hL
    exact not_le_center_of_mem hΩ hL₀
  have hΨ : Subgroup.map (layerQuotientHom hΩ.conjInvariant u) '' locFamily Ω u =
      memberImages Ω u := map_layerQuotientHom_family hΩ.conjInvariant
  have hY : (layerQuotientHom hΩ.conjInvariant u).range = memberJoin Ω u :=
    range_layerQuotientHom hΩ.conjInvariant
  obtain ⟨D', κ, hQ, -⟩ := lieDecomposition_of_lieSystemData_idx hp
    CFSG.ClassicalInvolution.ModelFacts.modelClauseZero fundamentalWholeA1 hq D
    (layerQuotientHom hΩ.conjInvariant u) hθ hnc hΨ hY
  have hsub : Subsingleton (Fin D.card) := Fin.subsingleton_iff_le_one.mpr hD.le
  obtain ⟨i₀⟩ : Nonempty (Fin D.card) := ⟨⟨0, by omega⟩⟩
  have hQ0 : ∀ i, D'.Q i = ((layerQuotientHom hΩ.conjInvariant u).comp (D.hom i₀)).range :=
    fun i => by
      rw [hQ i, hsub.elim (κ i) i₀]
      rfl
  have := memberJoin_normal (a := u) hΩ.conjInvariant
  obtain ⟨iK, hiK⟩ := D'.exists_le _ (⟨K', hK', rfl⟩ : modOdd u K' ∈ memberImages Ω u)
  obtain ⟨iJ, hiJ⟩ := D'.exists_le _ (⟨J, hJ, rfl⟩ : modOdd u J ∈ memberImages Ω u)
  refine ⟨D'.Q iJ, (CFSG.isComponent_iff_open _).mpr (D'.isComponentOf iJ), ?_, hiJ⟩
  rw [hQ0 iJ, ← hQ0 iK]
  exact hiK

end OneComp

end CFSG.ClassicalInvolution.RouteD.TwinY
