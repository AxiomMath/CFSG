module

public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent
public import CFSG.Foundations.Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.ReducedLayer
import CFSG.LocalAnalysis.RankThreeTheoremC.GaschutzTransfer
import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionElements
import CFSG.LocalAnalysis.AGLEmbedding.ReducedQuotient
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.ReducedComponentStructure
import CFSG.LocalAnalysis.ComponentClassification.LocalComponents
import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

structure ZLayerData3 (X : Type) [Group X] [Finite X] (P : Sylow 3 X) (z : X) : Prop where
  cat : CFSG.AGLEmbedding.CatalogSimpleSections X
  rank : CFSG.twoLocalOddRank X ≤ 3
  core : primeComplementCore (G := X) 3 = ⊥
  prank : CFSG.Open.pRank 3 (P : Subgroup X) = 3
  ord : orderOf z = 3
  norm : (zpowers z).Normal
  memP : z ∈ (P : Subgroup X)
  cent : z ∈ centralizer ((P : Subgroup X) : Set X)
  layer : z ∈ rankThreeLayer (⊤ : Subgroup X)
  cyc : IsCyclic (CFSG.pCore 3 X)

namespace ZLayerData3

variable {X : Type} [Group X] [Finite X] {P : Sylow 3 X} {z : X}

theorem commute_layer (h : ZLayerData3 X P z) {e : X} (he : e ∈ rankThreeLayer (⊤ : Subgroup X)) :
    z * e = e * z :=
  commute_of_mem_layer h.norm he

private theorem ne_one' (h : ZLayerData3 X P z) : z ≠ 1 := by
  intro h1
  have h3 := h.ord
  rw [h1, orderOf_one] at h3
  omega

theorem exists_component_center_ne_bot (h : ZLayerData3 X P z) :
    ∃ K : Subgroup X, IsComponentOf K ⊤ ∧ center K ≠ ⊥ :=
  exists_component_center_ne_bot_of_mem_layer h.layer h.ne_one' fun _ he => h.commute_layer he

private theorem zpowers_eq_of_mem_of_isCyclic {C : Subgroup X} (hC : IsCyclic C) {a b : X}
    (ha : a ∈ C) (hb : b ∈ C) (ha3 : orderOf a = 3) (hb3 : orderOf b = 3) :
    zpowers a = zpowers b := by
  have key : zpowers (⟨a, ha⟩ : C) = zpowers (⟨b, hb⟩ : C) := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
      Subgroup.orderOf_mk, Subgroup.orderOf_mk, ha3, hb3]
  have := congrArg (Subgroup.map C.subtype) key
  simpa [MonoidHom.map_zpowers] using this

private theorem center_component_le_pCore (hcore : primeComplementCore (G := X) 3 = ⊥)
    {K : Subgroup X} (hK : IsComponentOf K ⊤) :
    (center K).map K.subtype ≤ CFSG.pCore 3 X := by
  have hcoreK := cfsg_subnormal_primeComplementCore_eq_bot 3 K hK.2.1 hcore
  have hZ := trivial_primeComplementCore_center_le_pCore 3 Nat.prime_three hcoreK
  have hsub := cfsg_subnormal_pCoreOf_le 3 hK.2.1
  rw [pCoreOf_top_eq_pCore] at hsub
  exact (Subgroup.map_mono hZ).trans hsub

theorem component_center (h : ZLayerData3 X P z) {K : Subgroup X} (hK : IsComponentOf K ⊤)
    (hZ : center K ≠ ⊥) :
    z ∈ K ∧ (∀ k ∈ K, z * k = k * z) ∧
      ∀ w ∈ K, (∀ k ∈ K, w * k = k * w) → orderOf w = 3 → w ∈ zpowers z := by
  have hle := center_component_le_pCore h.core hK
  have hzC : z ∈ CFSG.pCore 3 X := by
    have hpg : IsPGroup 3 (zpowers z) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.ord, pow_one])
    have hle' : zpowers z ≤ CFSG.pCore 3 X :=
      le_sSup (show zpowers z ∈ {N : Subgroup X | N.Normal ∧ IsPGroup 3 N} from ⟨h.norm, hpg⟩)
    exact hle' (mem_zpowers z)
  have hunique : ∀ w ∈ K, (∀ k ∈ K, w * k = k * w) → orderOf w = 3 → zpowers w = zpowers z := by
    intro w hwK hw hw3
    refine zpowers_eq_of_mem_of_isCyclic h.cyc ?_ hzC hw3 h.ord
    exact hle ⟨⟨w, hwK⟩, mem_center_iff.2 fun k => Subtype.ext (hw k k.2).symm, rfl⟩
  have hp3 : IsPGroup 3 (center K) :=
    CFSG.AGLEmbedding.isPGroup_center_of_isComponentOf Nat.prime_three h.core hK
  have hnt : Nontrivial (center K) := (nontrivial_iff_ne_bot _).2 hZ
  obtain ⟨n, hn, hcard⟩ := hp3.nontrivial_iff_card.1 hnt
  obtain ⟨w₀, hw₀⟩ := exists_prime_orderOf_dvd_card' (G := center K) 3
    (hcard ▸ dvd_pow_self 3 hn.ne')
  have hw₀K : ((w₀ : K) : X) ∈ K := (w₀ : K).2
  have hw₀c : ∀ k ∈ K, ((w₀ : K) : X) * k = k * ((w₀ : K) : X) := fun k hk =>
    congrArg Subtype.val (mem_center_iff.1 w₀.2 ⟨k, hk⟩).symm
  have hw₀3 : orderOf ((w₀ : K) : X) = 3 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw₀]
  have hzw : z ∈ zpowers ((w₀ : K) : X) := by
    rw [hunique _ hw₀K hw₀c hw₀3]
    exact mem_zpowers z
  obtain ⟨m, hm⟩ := mem_zpowers_iff.1 hzw
  refine ⟨?_, ?_, ?_⟩
  · rw [← hm]
    exact zpow_mem hw₀K m
  · intro k hk
    rw [← hm]
    exact ((Commute.zpow_left (hw₀c k hk) m)).eq
  · intro w hwK hw hw3
    rw [← hunique w hwK hw hw3]
    exact mem_zpowers w

theorem isPGroup_center (h : ZLayerData3 X P z) {K : Subgroup X} (hK : IsComponentOf K ⊤) :
    IsPGroup 3 (center K) :=
  CFSG.AGLEmbedding.isPGroup_center_of_isComponentOf Nat.prime_three h.core hK

theorem isCyclic_center (h : ZLayerData3 X P z) {K : Subgroup X} (hK : IsComponentOf K ⊤) :
    IsCyclic (center K) := by
  have hle := center_component_le_pCore h.core hK
  have := h.cyc
  let φ : ↥(center K) →* ↥(CFSG.pCore 3 X) :=
    (K.subtype.comp (center K).subtype).codRestrict (CFSG.pCore 3 X) fun w => hle ⟨w, w.2, rfl⟩
  have hφ : Function.Injective φ := by
    intro a b hab
    have h1 : (φ a).1 = (φ b).1 := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h1)
  exact isCyclic_of_injective φ hφ

theorem exists_inf_ne_of_center_ne_bot (h : ZLayerData3 X P z) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hZ : center K ≠ ⊥) :
    ∃ d ∈ (P : Subgroup X) ⊓ K, orderOf d = 3 ∧ d ∉ zpowers z := by
  obtain ⟨hzK, hzc, -⟩ := h.component_center hK hZ
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal P
    (CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain hK.2.1
      Subgroup.IsSubnormal.top)
  have hperf : Group.IsPerfect K := ⟨hK.2.2.1⟩
  have hzcen : (⟨z, hzK⟩ : K) ∈ center K :=
    mem_center_iff.2 fun k => Subtype.ext (hzc k k.2).symm
  have hz3 : z ^ 3 = 1 := by rw [← h.ord]; exact pow_orderOf_eq_one z
  have hnc : ¬ IsCyclic (T : Subgroup K) :=
    not_isCyclic_sylow_of_isPerfect hperf T hzcen (fun h1 => h.ne_one' (congrArg Subtype.val h1))
      (Subtype.ext hz3)
  have h2 : 2 ≤ CFSG.Open.pRank 3 (T : Subgroup K) :=
    two_le_pRank_of_not_isCyclic Nat.prime_three (by norm_num) T.isPGroup' hnc
  obtain ⟨E, hET, hE, hEcard⟩ := pRank_attained 3 (T : Subgroup K) (by omega)
  have hbig : 3 < Nat.card E := by
    rw [hEcard]
    calc 3 < 3 ^ 2 := by norm_num
      _ ≤ 3 ^ CFSG.Open.pRank 3 (T : Subgroup K) := Nat.pow_le_pow_right (by norm_num) h2
  have hnle : ¬ E ≤ zpowers (⟨z, hzK⟩ : K) := fun hle =>
    absurd (Subgroup.card_le_of_le hle) (by
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, h.ord]; omega)
  obtain ⟨d, hdE, hdz⟩ := IsConcreteLE.not_le_iff_exists.1 hnle
  have hd1 : d ≠ 1 := fun h1 => hdz (h1 ▸ one_mem _)
  have hd3 : orderOf d = 3 := orderOf_eq_prime (hE.2 d hdE) hd1
  refine ⟨(d : X), ?_, ?_, ?_⟩
  · rw [← hT]
    exact Subgroup.mem_map_of_mem K.subtype (hET hdE)
  · rw [Subgroup.orderOf_coe, hd3]
  · intro hd
    obtain ⟨m, hm⟩ := mem_zpowers_iff.1 hd
    exact hdz (mem_zpowers_iff.2 ⟨m, Subtype.ext (by simpa using hm)⟩)

theorem exists_inf_of_center_eq_bot (h : ZLayerData3 X P z) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hZ : center K = ⊥) :
    ∃ t ∈ (P : Subgroup X) ⊓ K, orderOf t = 3 := by
  have hdvd := CFSG.AGLEmbedding.prime_dvd_card_center_quotient_of_isComponentOf Nat.prime_three
    h.core hK
  have hK3 : 3 ∣ Nat.card K := by
    rw [hZ, ← Subgroup.index_eq_card, Subgroup.index_bot] at hdvd
    exact hdvd
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal P
    (CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain hK.2.1
      Subgroup.IsSubnormal.top)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := (T : Subgroup K)) 3
    (T.dvd_card_of_dvd_card hK3)
  refine ⟨((t : K) : X), ?_, ?_⟩
  · rw [← hT]
    exact Subgroup.mem_map_of_mem K.subtype t.2
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, ht]

end ZLayerData3

section Components

variable {X : Type} [Group X] [Finite X]

set_option linter.unusedSectionVars false in
theorem isComponentOf_map_conj {K : Subgroup X} (hK : IsComponentOf K ⊤) (g : X) :
    IsComponentOf (K.map (MulAut.conj g).toMonoidHom) ⊤ :=
  (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) K).2 hK

theorem commute_of_isComponentOf_ne {K L : Subgroup X} (hK : IsComponentOf K ⊤)
    (hL : IsComponentOf L ⊤) (hne : K ≠ L) : ∀ x ∈ K, ∀ y ∈ L, x * y = y * x := by
  intro x hx y hy
  have hcomm := CFSG.ComponentClassification.LocalComponents.commute_of_ne K L hK hL hne
  exact (mem_centralizer_iff.1 ((commutator_eq_bot_iff_le_centralizer.1 hcomm) hx) y hy).symm

end Components

end CFSG.LocalAnalysis.RankThreeTheoremC
