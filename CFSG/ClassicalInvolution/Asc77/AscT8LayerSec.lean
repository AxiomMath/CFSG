module

public import CFSG.ClassicalInvolution.Asc77.AscT8LayerRes
public import CFSG.ClassicalInvolution.Asc77.AscE184OddQuot

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

namespace T8

section Restrict

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime]

theorem hypOmegaMod_restrict_of {𝔏 : Set (Subgroup G)} {H : Subgroup G}
    (hle : ∀ L ∈ 𝔏, L ≤ H) (hconj : ∀ n ∈ H, ∀ L ∈ 𝔏, conjSub n L ∈ 𝔏)
    (hcl : ∀ L ∈ 𝔏, ∃ z, IsSectionMember p f H L z)
    (h4 : ∀ K ∈ 𝔏, ∀ J ∈ 𝔏, K ≠ J →
      padicValNat 2 (Nat.card ↥(K ⊓ J)) ≤ 1 ∧
        (padicValNat 2 (Nat.card ↥(K ⊓ J)) = 1 → ⁅K, J⁆ ≤ oddCoreOf K ⊓ oddCoreOf J))
    (h5 : ∀ K ∈ 𝔏, ∀ J ∈ 𝔏, K ≠ J → ∀ z : G, IsUniqueInvolution K z → ∀ v ∈ J,
      (¬ ∀ w ∈ J, v * w = w * v) → IsPGroup 2 (Subgroup.zpowers v) → v * z = z * v →
        v ∈ Subgroup.normalizer (K : Set G)) :
    HypOmegaMod p f (restrictFamily 𝔏 H) where
  conjInvariant := by
    rintro n _ ⟨L, hL, hLY, rfl⟩
    exact ⟨conjSub (n : G) L, hconj n n.2 L hL, hle _ (hconj n n.2 L hL),
      conjSub_subgroupOf H n L⟩
  classical := by
    rintro _ ⟨L, hL, hLY, rfl⟩
    obtain ⟨z, hz⟩ := hcl L hL
    obtain ⟨hzH, hcm⟩ := hz.toIn
    exact ⟨⟨z, hzH⟩, hcm⟩
  omega4 := by
    rintro _ ⟨K, hK, hKY, rfl⟩ _ ⟨J, hJ, hJY, rfl⟩ hne
    have hKJ : K ≠ J := fun h => hne (by rw [h])
    obtain ⟨h1, h2⟩ := h4 K hK J hJ hKJ
    have hcard : Nat.card ↥(K.subgroupOf H ⊓ J.subgroupOf H) = Nat.card ↥(K ⊓ J) := by
      rw [inf_subgroupOf_eq]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hKY)).toEquiv
    rw [hcard]
    refine ⟨h1, fun h => ?_⟩
    have hle := h2 h
    rw [oddCoreOf_subgroupOf hKY, oddCoreOf_subgroupOf hJY]
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    have hab : (⁅(a : G), (b : G)⁆) ∈ ⁅K, J⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp ha)
        (Subgroup.mem_subgroupOf.mp hb)
    exact ⟨Subgroup.mem_subgroupOf.mpr (hle hab).1, Subgroup.mem_subgroupOf.mpr (hle hab).2⟩
  omega5 := by
    rintro _ ⟨K, hK, hKY, rfl⟩ _ ⟨J, hJ, hJY, rfl⟩ hne z' hz' v hv hnc hv2 hvz
    have hKJ : K ≠ J := fun h => hne (by rw [h])
    have hzK : IsUniqueInvolution K (z' : G) := isUniqueInvolution_of_subgroupOf hz' hKY
    have hvJ : (v : G) ∈ J := Subgroup.mem_subgroupOf.mp hv
    have hnc' : ¬ ∀ w ∈ J, (v : G) * w = w * (v : G) := by
      intro h
      apply hnc
      rintro ⟨w, hw⟩ hw'
      exact Subtype.ext (h w (Subgroup.mem_subgroupOf.mp hw'))
    have hv2' : IsPGroup 2 (Subgroup.zpowers (v : G)) := isPGroup_zpowers_coe_iff.mpr hv2
    have hn := h5 K hK J hJ hKJ (z' : G) hzK (v : G) hvJ hnc' hv2' (congrArg Subtype.val hvz)
    exact (mem_normalizer_subgroupOf_iff hKY).mp hn

end Restrict

section Join

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

@[expose] def layerJoin (Ω : Set (Subgroup G)) (x : G) : Subgroup G :=
  ⨆ L ∈ layerSet Ω x, L

omit [Finite G] in
theorem le_layerJoin {x : G} {L : Subgroup G} (hL : L ∈ layerSet Ω x) : L ≤ layerJoin Ω x :=
  le_iSup₂ (f := fun (L : Subgroup G) (_ : L ∈ layerSet Ω x) => L) L hL

omit [Finite G] in
theorem layerSet_le_cenZ {x : G} {L : Subgroup G} (hL : L ∈ layerSet Ω x) : L ≤ cenZ x := by
  obtain ⟨K, -, rfl⟩ := hL
  exact layerRes_le_cenZ x K

omit [Finite G] in
theorem layerJoin_le_cenZ (x : G) : layerJoin Ω x ≤ cenZ x :=
  iSup₂_le fun _ hL => layerSet_le_cenZ hL

theorem hypOmegaMod_layer (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {x : G}
    (hx : x * x = 1) :
    HypOmegaMod p f (restrictFamily (layerSet Ω x) (layerJoin Ω x)) := by
  refine hypOmegaMod_restrict_of (fun L hL => le_layerJoin hL)
    (fun n hn L hL => layerSet_conj hΩ hL (layerJoin_le_cenZ x hn)) ?_ ?_ ?_
  · rintro _ ⟨K, hK, rfl⟩
    obtain ⟨z, hz⟩ := hΩ.classical K hK.1
    exact ⟨z, (hK.isSectionMember hp hq hΩ hx hz).restrict (layerJoin_le_cenZ x)
      (le_layerJoin ⟨K, hK, rfl⟩)⟩
  · rintro _ ⟨K, hK, rfl⟩ _ ⟨J, hJ, rfl⟩ hne
    exact layerRes_omega4 hp hq hΩ hx hK hJ hne
  · rintro _ ⟨K, hK, rfl⟩ _ ⟨J, hJ, rfl⟩ hne z hz v hv hnc hv2 hvz
    exact layerRes_omega5 hp hq hΩ hx hK hJ hne hz hv hnc hv2 hvz

theorem noTwins_layer (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) {x : G} (hx : x * x = 1) :
    ∀ L ∈ restrictFamily (layerSet Ω x) (layerJoin Ω x),
      ∀ L' ∈ twinSet (restrictFamily (layerSet Ω x) (layerJoin Ω x)) L, L' = L := by
  rintro _ ⟨_, ⟨K, hK, rfl⟩, hKY, rfl⟩ _ ⟨⟨_, ⟨J, hJ, rfl⟩, hJY, rfl⟩, z, hzK, hzJ⟩
  have h1 := isUniqueInvolution_of_subgroupOf hzK hKY
  have h2 := isUniqueInvolution_of_subgroupOf hzJ hJY
  have hJK : J = K := hnt K hK.1 J (layerRes_twin hp hq hΩ hx hK hJ h1 h2)
  rw [hJK]

end Join

section Quot

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

abbrev LayerQuot (Ω : Set (Subgroup G)) (x : G) : Type :=
  ↥(layerJoin Ω x) ⧸ classicalInvolutionOddCore ↥(layerJoin Ω x)

@[expose] def layerFamQ (Ω : Set (Subgroup G)) (x : G) : Set (Subgroup (LayerQuot Ω x)) :=
  quotFamily (restrictFamily (layerSet Ω x) (layerJoin Ω x))
    (classicalInvolutionOddCore ↥(layerJoin Ω x))

theorem hypOmegaMod_layerQuot (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {x : G}
    (hx : x * x = 1) : HypOmegaMod p f (layerFamQ Ω x) :=
  oddQuotHyp p f hp hq ↥(layerJoin Ω x) _ (hypOmegaMod_layer hp hq hΩ hx)
    (classicalInvolutionOddCore ↥(layerJoin Ω x))
    (CFSG.ComponentClassification.OddCore.odd_card ↥(layerJoin Ω x))

theorem noTwins_layerQuot (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hnt : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K) {x : G} (hx : x * x = 1) :
    ∀ M ∈ layerFamQ Ω x, ∀ M' ∈ twinSet (layerFamQ Ω x) M, M' = M := by
  rintro _ ⟨K', hK', rfl⟩ _ ⟨⟨J', hJ', rfl⟩, w, hwM, hwM'⟩
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥(layerJoin Ω x))) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥(layerJoin Ω x)
  have hΛ := hypOmegaMod_layer hp hq hΩ hx
  obtain ⟨zK, hzK⟩ := hΛ.exists_uniqueInvolution hp hq hK'
  obtain ⟨zJ, hzJ⟩ := hΛ.exists_uniqueInvolution hp hq hJ'
  have hzKb := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hodd K') hzK
  have hzJb := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hodd J') hzJ
  have hmk : QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerJoin Ω x)) zK =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerJoin Ω x)) zJ :=
    (hwM.eq hzKb).symm.trans (hwM'.eq hzJb)
  obtain ⟨n, hn, hnz⟩ := exists_conj_eq_of_map_eq hodd hzK.sq hzJ.sq hmk
  have hJn : conjSub n J' ∈ restrictFamily (layerSet Ω x) (layerJoin Ω x) :=
    hΛ.conjInvariant n J' hJ'
  have hzJn : IsUniqueInvolution (conjSub n J') zK := by
    have := hzJ.conj n
    rwa [hnz] at this
  have heq : conjSub n J' = K' :=
    noTwins_layer hp hq hΩ hnt hx K' hK' _ ⟨hJn, zK, hzK, hzJn⟩
  have hn1 : QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerJoin Ω x)) n = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hn
  beta_reduce
  rw [← heq, AscQuot.map_conjSub, hn1, conjSub_one]

end Quot



end T8

end CFSG.ClassicalInvolution.Asc77
