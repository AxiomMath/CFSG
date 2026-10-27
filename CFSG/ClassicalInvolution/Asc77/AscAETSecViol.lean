module

public import CFSG.ClassicalInvolution.Asc77.AscAETCyc
public import CFSG.ClassicalInvolution.Asc77.AscT3CoreRestrict
public import CFSG.ClassicalInvolution.Asc77.AscT7HC4
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Section
public import CFSG.ClassicalInvolution.ModelFacts.Orth15STrans

public section

namespace CFSG.ClassicalInvolution.Asc77.AscAET

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
open scoped commutatorElement

section Helpers

variable {G : Type} [Group G] [Finite G]

theorem relIndex_eq_two_of_card {U R : Subgroup G} (hUR : U ≤ R)
    (h : Nat.card R = 2 * Nat.card U) : U.relIndex R = 2 := by
  have h1 := Subgroup.relIndex_mul_card U R
  rw [inf_eq_left.mpr hUR, h] at h1
  have h2 : U.relIndex R * Nat.card U = 2 * Nat.card U := by
    rw [h1]
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2

omit [Finite G] in
theorem mem_USet_restrict_of_sylow {Φ : Set (Subgroup G)} {Y J R U : Subgroup G} (hJ : J ∈ Φ)
    (hJY : J ≤ Y) (hR : IsSylow2In R J) (hUR : U ≤ R) (hcyc : IsCyclic ↥U)
    (hidx : U.relIndex R = 2) : U.subgroupOf Y ∈ USet (restrictFamily Φ Y) := by
  have hRY : R ≤ Y := hR.1.trans hJY
  have hUY : U ≤ Y := hUR.trans hRY
  have hrel' : (U.subgroupOf Y).relIndex (R.subgroupOf Y) = 2 := by
    have h2 := Subgroup.relIndex_map_map_of_injective (U.subgroupOf Y) (R.subgroupOf Y)
      Y.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hUY, Subgroup.map_subgroupOf_eq_of_le hRY] at h2
    rw [← h2]
    exact hidx
  exact ⟨R.subgroupOf Y, mem_RSet_restrict hJ hJY hR, Subgroup.subgroupOf_mono Y hUR,
    (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hUY)).mpr hcyc, hrel'⟩

theorem mem_normalizer_exactCore {M : Subgroup G} {c g : G}
    (hgM : g ∈ Subgroup.normalizer (M : Set G)) (hgc : g ∈ Subgroup.centralizer ({c} : Set G)) :
    g ∈ Subgroup.normalizer ((exactCore c M : Subgroup G) : Set G) := by
  have h1 := exactCore_conjSub g c M
  have hgc' : g * c = c * g := Subgroup.mem_centralizer_singleton_iff.mp hgc
  have e : g * c * g⁻¹ = c := by rw [hgc']; group
  rw [e, mem_normalizer_iff_conjSub_eq.mp hgM] at h1
  exact mem_normalizer_iff_conjSub_eq.mpr h1.symm

omit [Finite G] in
theorem pairNormalizers_mono {K K' J J' : Subgroup G} {zK zJ : G} (hK : K ≤ K') (hJ : J ≤ J') :
    pairNormalizers K J zK zJ ≤ pairNormalizers K' J' zK zJ :=
  sup_le_sup (inf_le_inf_right _ hK) (inf_le_inf_right _ hJ)

end Helpers

section Main

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_aViol_exactPair (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {c : G}
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {M J : Subgroup G} {zM zJ : G} (hM : M ∈ Ω)
    (hv : AViol Ω M J zM zJ) (hMc : c ∈ trivialOnQuot M) (hJc : c ∈ trivialOnQuot J) :
    ∃ zK zL : ↥(exLayer Ω c),
      AViol (restrictFamily (centralizingMembers (exactFamily Ω c) {c}) (exLayer Ω c))
        ((exactCore c M).subgroupOf (exLayer Ω c)) ((exactCore c J).subgroupOf (exLayer Ω c))
        zK zL := by
  have hJΩ : J ∈ Ω := hv.mem
  have hKt : M ∈ tqMembers Ω c := ⟨hM, hMc⟩
  have hJt : J ∈ tqMembers Ω c := ⟨hJΩ, hJc⟩
  have hKcm : exactCore c M ∈ centralizingMembers (exactFamily Ω c) {c} :=
    ⟨exactCore_mem_exactFamily hKt, exactCore_le_centralizer c M⟩
  have hJcm : exactCore c J ∈ centralizingMembers (exactFamily Ω c) {c} :=
    ⟨exactCore_mem_exactFamily hJt, exactCore_le_centralizer c J⟩
  have hKY : exactCore c M ≤ exLayer Ω c := le_centLayer hKcm
  have hJY : exactCore c J ≤ exLayer Ω c := le_centLayer hJcm
  have hΛ : HypOmegaMod p f
      (restrictFamily (centralizingMembers (exactFamily Ω c) {c}) (exLayer Ω c)) :=
    hypOmegaMod_restrictFamily_congr (centMembers_exactFamily Ω c).symm rfl
      (hypOmegaMod_exactPair hp hq hΩ hc2)
  have hzM : IsUniqueInvolution (exactCore c M) zM :=
    T7H.isUniqueInvolution_exactCore hp hΩ hc2 hKt hv.hzK
  have hzJ : IsUniqueInvolution (exactCore c J) zJ :=
    T7H.isUniqueInvolution_exactCore hp hΩ hc2 hJt hv.hzJ
  have hne : exactCore c J ≠ exactCore c M := exactCore_ne_of_twin hp hq hΩ hc2 hKt hJt hv.ne
  have hJmem : (exactCore c J).subgroupOf (exLayer Ω c) ∈
      restrictFamily (centralizingMembers (exactFamily Ω c) {c}) (exLayer Ω c) :=
    subgroupOf_mem_restrictFamily hJcm hJY
  obtain ⟨-, -, U₀, hU₀, hU₀J, hU₀N⟩ := hv.star
  obtain ⟨R₀, hR₀rs, hU₀R₀, hcyc₀, hidx₀⟩ := id hU₀
  obtain ⟨J₁, hJ₁, hR₀J₁⟩ := exists_isSylow2In_of_mem_RSet hR₀rs
  have hJ₁J : J₁ = J := hΩ.eq_of_mem_USet hp hU₀ hJ₁ hJΩ (hU₀R₀.trans hR₀J₁.1) hU₀J
  rw [hJ₁J] at hR₀J₁
  have hU₀2 : IsPGroup 2 U₀ := hR₀J₁.2.1.to_le hU₀R₀
  obtain ⟨x, hx, hxc⟩ := exists_conj_centralized hc2 hJc hMc.1 hU₀2 hU₀J hU₀N
  have hxJ : x ∈ J := hx.1
  have hxM : x ∈ Subgroup.normalizer (M : Set G) := hx.2
  have hR₁ : IsSylow2In (conjSub x R₀) J := by
    have := hR₀J₁.conj x
    rwa [conjSub_eq_self_of_mem hxJ] at this
  have hU₁R₁ : conjSub x U₀ ≤ conjSub x R₀ := conjSub_mono hU₀R₀
  have hcard₁ : Nat.card (conjSub x R₀) = 2 * Nat.card (conjSub x U₀) := by
    rw [natCard_conjSub, natCard_conjSub]
    have h1 := Subgroup.relIndex_mul_card U₀ R₀
    rw [inf_eq_left.mpr hU₀R₀, hidx₀] at h1
    omega
  have hrel₁ : (conjSub x U₀).relIndex (conjSub x R₀) = 2 := relIndex_eq_two_of_card hU₁R₁ hcard₁
  have hcyc₁ : IsCyclic ↥(conjSub x U₀) :=
    (MulEquiv.isCyclic (Subgroup.equivMapOfInjective U₀ (MulAut.conj x).toMonoidHom
      (MulAut.conj x).injective)).mp hcyc₀
  obtain ⟨P, hPJ, hU₁P, hPc⟩ := exists_sylow_centralized_over hc2 hJc hR₁ hU₁R₁ hrel₁ hxc
  have hPJc : IsSylow2In P (exactCore c J) :=
    (isSylow2In_exactCore_iff hΩ hc2 hJΩ hJc).mpr ⟨hPJ, hPc⟩
  have hcardP : Nat.card P = 2 * Nat.card (conjSub x U₀) := by
    rw [hPJ.natCard_eq hR₁]
    exact hcard₁
  have hrelP : (conjSub x U₀).relIndex P = 2 := relIndex_eq_two_of_card hU₁P hcardP
  have hUΛ : (conjSub x U₀).subgroupOf (exLayer Ω c) ∈
      USet (restrictFamily (centralizingMembers (exactFamily Ω c) {c}) (exLayer Ω c)) :=
    mem_USet_restrict_of_sylow hJcm hJY hPJc hU₁P hcyc₁ hrelP
  have hUJ : (conjSub x U₀).subgroupOf (exLayer Ω c) ≤ (exactCore c J).subgroupOf (exLayer Ω c) :=
    Subgroup.subgroupOf_mono _ (hU₁P.trans hPJc.1)
  have hUN : (conjSub x U₀).subgroupOf (exLayer Ω c) ≤
      Subgroup.normalizer (((exactCore c M).subgroupOf (exLayer Ω c) : Subgroup ↥(exLayer Ω c)) :
        Set ↥(exLayer Ω c)) := by
    intro u hu
    have hu1 : (u : G) ∈ conjSub x U₀ := Subgroup.mem_subgroupOf.mp hu
    have hN : (u : G) ∈ Subgroup.normalizer (M : Set G) := by
      have h0 : x⁻¹ * (u : G) * x ∈ U₀ := mem_conjSub_iff.mp hu1
      have e : (u : G) = x * (x⁻¹ * (u : G) * x) * x⁻¹ := by group
      rw [e]
      exact (Subgroup.normalizer (M : Set G)).mul_mem
        ((Subgroup.normalizer (M : Set G)).mul_mem hxM (hU₀N h0))
        ((Subgroup.normalizer (M : Set G)).inv_mem hxM)
    exact (mem_normalizer_subgroupOf_iff hKY).mp (mem_normalizer_exactCore hN (hxc hu1))
  have hnot : (exactCore c J).subgroupOf (exLayer Ω c) ∉
      omegaNbr (restrictFamily (centralizingMembers (exactFamily Ω c) {c}) (exLayer Ω c))
        ((exactCore c M).subgroupOf (exLayer Ω c)) := by
    rintro ⟨-, -, R', hR', hR'J, hR'N⟩
    have hR'syl : IsSylow2In R' ((exactCore c J).subgroupOf (exLayer Ω c)) :=
      hΛ.isSylow2In_of_mem_RSet_of_le hp hJmem hR' hR'J
    have hmap : IsSylow2In (R'.map (exLayer Ω c).subtype) (exactCore c J) := by
      have h1 := isSylow2In_map_subtype_iff.mpr hR'syl
      rwa [Subgroup.map_subgroupOf_eq_of_le hJY] at h1
    have hRN : R'.map (exLayer Ω c).subtype ≤
        Subgroup.normalizer ((exactCore c M : Subgroup G) : Set G) := by
      have h1 := map_le_normalizer_map hR'N
      rwa [Subgroup.map_subgroupOf_eq_of_le hKY] at h1
    have hRz : R'.map (exLayer Ω c).subtype ≤ Subgroup.centralizer ({zM} : Set G) :=
      T3.le_centralizer_of_le_normalizer' hzM hRN
    have hRJ : IsSylow2In (R'.map (exLayer Ω c).subtype) J :=
      ((isSylow2In_exactCore_iff hΩ hc2 hJΩ hJc).mp hmap).1
    have h8 := hΩ.eight_le_of_mem_RSet hp (mem_RSet_of_isSylow2In hJΩ hRJ)
    have hRM : R'.map (exLayer Ω c).subtype ≤ Subgroup.normalizer (M : Set G) :=
      hΩ.le_normalizer_of_le_centralizer hp hq hM hJΩ hv.ne.symm hv.hzK hRJ.1 hRJ.2.1
        (by omega) hRz
    exact hv.not_nbr ⟨hJΩ, hv.ne, _, mem_RSet_of_isSylow2In hJΩ hRJ, hRJ.1, hRM⟩
  have hnoc : ∀ g ∈ pairNormalizers ((exactCore c M).subgroupOf (exLayer Ω c))
      ((exactCore c J).subgroupOf (exLayer Ω c)) ⟨zM, hKY hzM.mem⟩ ⟨zJ, hJY hzJ.mem⟩,
      conjSub g ((exactCore c M).subgroupOf (exLayer Ω c)) ≠
        (exactCore c J).subgroupOf (exLayer Ω c) := by
    intro g hg hgK
    have hgG : (g : G) ∈ pairNormalizers M J zM zJ := by
      have h1 := T3Core.map_pairNormalizers_subgroupOf_le hKY hJY ⟨zM, hKY hzM.mem⟩
        ⟨zJ, hJY hzJ.mem⟩ ⟨g, hg, rfl⟩
      exact pairNormalizers_mono (exactCore_le_left c M) (exactCore_le_left c J) h1
    have hcgY : conjSub (g : G) (exactCore c M) ≤ exLayer Ω c := by
      have := conjSub_mono (n := (g : G)) hKY
      rwa [conjSub_eq_self_of_mem g.2] at this
    have h2 : conjSub (g : G) (exactCore c M) = exactCore c J := by
      have h3 : (conjSub (g : G) (exactCore c M)).subgroupOf (exLayer Ω c) =
          (exactCore c J).subgroupOf (exLayer Ω c) := by
        rw [← conjSub_subgroupOf]
        exact hgK
      have h4 := Subgroup.subgroupOf_inj.mp h3
      rwa [inf_eq_left.mpr hcgY, inf_eq_left.mpr hJY] at h4
    have hgc : (g : G) ∈ Subgroup.centralizer ({c} : Set G) :=
      exactLayer_le_centralizer Ω c g.2
    have h5 := exactCore_conjSub (g : G) c M
    have e : (g : G) * c * (g : G)⁻¹ = c := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp hgc]
      group
    rw [e, h2] at h5
    have hgt : conjSub (g : G) M ∈ tqMembers Ω c :=
      conjSub_mem_tqMembers hΩ.conjInvariant hgc hKt
    have heq : conjSub (g : G) M = J := by
      by_contra hne'
      exact exactCore_ne_of_twin hp hq hΩ hc2 hJt hgt hne' h5
    exact hv.no_conj g hgG heq
  exact ⟨⟨zM, hKY hzM.mem⟩, ⟨zJ, hJY hzJ.mem⟩,
    { star := ⟨hJmem, subgroupOf_ne_of_ne hKY hJY hne, _, hUΛ, hUJ, hUN⟩
      not_nbr := hnot
      hzK := isUniqueInvolution_subgroupOf hzM hKY
      hzJ := isUniqueInvolution_subgroupOf hzJ hJY
      no_conj := hnoc }⟩

end Main

end CFSG.ClassicalInvolution.Asc77.AscAET
