module

public import CFSG.ClassicalInvolution.Asc77.AscE184Sub
public import CFSG.ClassicalInvolution.Asc77.AscT3Basic

public section

namespace CFSG.ClassicalInvolution.Asc77.T3Core

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem omegaStarNbr_subgroupOf [Finite G] (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω)
    {Y K J : Subgroup G} (hKY : K ≤ Y) (hJY : J ≤ Y) (hJ : J ∈ omegaStarNbr Ω K) :
    J.subgroupOf Y ∈ omegaStarNbr (restrictFamily Ω Y) (K.subgroupOf Y) := by
  obtain ⟨hJΩ, hne, U, hU, hUJ, hUN⟩ := hJ
  obtain ⟨R, -, J₁, hJ₁, hRJ₁, hUR, hcyc, hcard, -⟩ := hΩ.exists_data_of_mem_USet hp hU
  have hJ₁J : J₁ = J := hΩ.eq_of_mem_USet hp hU hJ₁ hJΩ (hUR.trans hRJ₁.1) hUJ
  rw [hJ₁J] at hRJ₁
  have hUY : U ≤ Y := hUJ.trans hJY
  have hRY : R ≤ Y := hRJ₁.1.trans hJY
  have hrel : U.relIndex R = 2 := by
    have h1 := Subgroup.relIndex_mul_card U R
    rw [inf_eq_left.mpr hUR, hcard] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hrel' : (U.subgroupOf Y).relIndex (R.subgroupOf Y) = 2 := by
    have h2 := Subgroup.relIndex_map_map_of_injective (U.subgroupOf Y) (R.subgroupOf Y)
      Y.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hUY, Subgroup.map_subgroupOf_eq_of_le hRY] at h2
    rw [← h2]
    exact hrel
  refine ⟨subgroupOf_mem_restrictFamily hJΩ hJY, subgroupOf_ne_of_ne hKY hJY hne,
    U.subgroupOf Y, ⟨R.subgroupOf Y, mem_RSet_restrict hJΩ hJY hRJ₁,
      Subgroup.subgroupOf_mono Y hUR, ?_, hrel'⟩, Subgroup.subgroupOf_mono Y hUJ, ?_⟩
  · exact (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hUY)).mpr hcyc
  · intro u hu
    exact (mem_normalizer_subgroupOf_iff hKY).mp (hUN (Subgroup.mem_subgroupOf.mp hu))

theorem map_pairNormalizers_subgroupOf_le {Y K J : Subgroup G} (hKY : K ≤ Y) (hJY : J ≤ Y)
    (zK zJ : Y) :
    (pairNormalizers (K.subgroupOf Y) (J.subgroupOf Y) zK zJ).map Y.subtype ≤
      pairNormalizers K J (zK : G) (zJ : G) := by
  have hZ := map_closure_pair_subtype zK zJ
  have hZY : Subgroup.closure ({(zK : G), (zJ : G)} : Set G) ≤ Y := by
    rw [← hZ]
    exact Subgroup.map_subtype_le _
  have hN : ∀ {A : Subgroup G}, A ≤ Y →
      (A.subgroupOf Y ⊓ Subgroup.normalizer
        ((Subgroup.closure ({zK, zJ} : Set Y) : Subgroup Y) : Set Y)).map Y.subtype ≤
        A ⊓ Subgroup.normalizer
          ((Subgroup.closure ({(zK : G), (zJ : G)} : Set G) : Subgroup G) : Set G) := by
    intro A _ x hx
    obtain ⟨x', hx', rfl⟩ := hx
    have hx'' : x' ∈ A.subgroupOf Y ⊓ Subgroup.normalizer
        ((Subgroup.closure ({zK, zJ} : Set Y) : Subgroup Y) : Set Y) := hx'
    rw [Subgroup.mem_inf] at hx''
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hx''.1, ?_⟩
    have hxN : x' ∈ Subgroup.normalizer
        (((Subgroup.closure ({(zK : G), (zJ : G)} : Set G) : Subgroup G).subgroupOf Y :
          Subgroup Y) : Set Y) := by
      rw [← hZ, subgroupOf_map_subtype']
      exact hx''.2
    exact (mem_normalizer_subgroupOf_iff hZY).mpr hxN
  unfold pairNormalizers
  rw [Subgroup.map_sup]
  exact sup_le_sup (hN hKY) (hN hJY)

theorem aViol_restrict [Finite G] (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {Y K J : Subgroup G}
    {zK zJ : G} (hKY : K ≤ Y) (hJY : J ≤ Y) (hv : AViol Ω K J zK zJ) :
    AViol (restrictFamily Ω Y) (K.subgroupOf Y) (J.subgroupOf Y) (⟨zK, hKY hv.hzK.mem⟩ : Y)
      (⟨zJ, hJY hv.hzJ.mem⟩ : Y) := by
  have hstar := omegaStarNbr_subgroupOf hp hΩ hKY hJY hv.star
  have hnbr : J.subgroupOf Y ∉ omegaNbr (restrictFamily Ω Y) (K.subgroupOf Y) :=
    fun h => hv.not_nbr (omegaNbr_of_restrict hKY hJY h)
  have hzK := isUniqueInvolution_subgroupOf hv.hzK hKY
  have hzJ := isUniqueInvolution_subgroupOf hv.hzJ hJY
  refine ⟨hstar, hnbr, hzK, hzJ, ?_⟩
  intro g hg hcon
  have hmem : (g : G) ∈ pairNormalizers K J zK zJ :=
    map_pairNormalizers_subgroupOf_le hKY hJY ⟨zK, hKY hv.hzK.mem⟩ ⟨zJ, hJY hv.hzJ.mem⟩
      (Subgroup.mem_map_of_mem Y.subtype hg)
  have h1 : conjSub (g : G) K ≤ Y := by
    have := conjSub_mono (n := (g : G)) hKY
    rwa [conjSub_eq_self_of_mem g.2] at this
  have hconj : conjSub (g : G) K = J := by
    rw [conjSub_subgroupOf Y g K] at hcon
    have := Subgroup.subgroupOf_inj.mp hcon
    rwa [inf_eq_left.mpr h1, inf_eq_left.mpr hJY] at this
  exact hv.no_conj _ hmem hconj

end CFSG.ClassicalInvolution.Asc77.T3Core
