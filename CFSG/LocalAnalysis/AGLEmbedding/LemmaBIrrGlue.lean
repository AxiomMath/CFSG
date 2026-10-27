module

import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltInner
import CFSG.LocalAnalysis.SteinbergCCSQTKTwoCoreQuotient
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem eq_of_mk_eq_of_pGroup {M Y : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hYp : IsPGroup p Y) {a b : M} (ha : (a : G) ∈ Y) (hb : (b : G) ∈ Y)
    (hab : QuotientGroup.mk' (CFSG.pCore 2 ↥M) a = QuotientGroup.mk' (CFSG.pCore 2 ↥M) b) :
    a = b := by
  have hinj :=
    CFSG.PreuniquenessRankFour.Helpers.pGroup_quotient_subgroupMap_injective_of_coprime_kernel p
      hp (CFSG.pCore 2 ↥M) (LocalAnalysis.SQTKTwoCoreQuotient.not_dvd_card_pCore_two hp hp2) _
      (hYp.comap_subtype (K := M))
  exact congrArg Subtype.val (@hinj ⟨a, Subgroup.mem_subgroupOf.mpr ha⟩
    ⟨b, Subgroup.mem_subgroupOf.mpr hb⟩ (Subtype.ext hab))

theorem relIndex_barM_of_pGroup {M Y Z : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hYM : Y ≤ M) (hYp : IsPGroup p Y) (hZY : Z ≤ Y) :
    (barM M Z).relIndex (barM M Y) = Z.relIndex Y := by
  have hcard : ∀ X : Subgroup G, X ≤ Y → Nat.card (barM M X) = Nat.card X := fun X hXY => by
    have hinj :=
      CFSG.PreuniquenessRankFour.Helpers.pGroup_quotient_subgroupMap_injective_of_coprime_kernel
        p hp (CFSG.pCore 2 ↥M) (LocalAnalysis.SQTKTwoCoreQuotient.not_dvd_card_pCore_two hp hp2)
        _ ((hYp.to_le hXY).comap_subtype (K := M))
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hXY.trans hYM)).toEquiv]
    exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj,
      MonoidHom.subgroupMap_surjective _ _⟩)).symm
  have h1 := Subgroup.relIndex_mul_card (barM M Z) (barM M Y)
  have h2 := Subgroup.relIndex_mul_card Z Y
  rw [inf_of_le_left (barM_mono hZY), hcard Z hZY, hcard Y le_rfl] at h1
  rw [inf_of_le_left hZY] at h2
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h2.symm)

omit [Finite G] in
theorem barM_le_centralizer_barM {M Y Z : Subgroup G}
    (hZc : Z ≤ Subgroup.centralizer (Y : Set G)) :
    barM M Z ≤ Subgroup.centralizer (barM M Y : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  rintro _ ⟨z, hz, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  have h1 := Subgroup.mem_centralizer_iff.mp (hZc (Subgroup.mem_subgroupOf.mp hz)) y
    (Subgroup.mem_subgroupOf.mp hy)
  rw [← map_mul, ← map_mul]
  exact congrArg (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) (Subtype.ext h1)

omit [Finite G] in
theorem pow_mem_barM {M Y Z : Subgroup G} {n : ℕ} (hpow : ∀ y ∈ Y, y ^ n ∈ Z) :
    ∀ u ∈ barM M Y, u ^ n ∈ barM M Z := by
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨y ^ n, Subgroup.mem_subgroupOf.mpr ?_, map_pow _ _ _⟩
  simpa using hpow y (Subgroup.mem_subgroupOf.mp hy)

omit [Finite G] in
theorem barM_inf_centralizer_le {M L Y Z : Subgroup G} (hCZ : Y ⊓ blockCentralizer M L ≤ Z) :
    barM M Y ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤ barM M Z := by
  rintro _ ⟨⟨y, hy, rfl⟩, hc⟩
  exact ⟨y, Subgroup.mem_subgroupOf.mpr
    (hCZ ⟨Subgroup.mem_subgroupOf.mp hy, (mem_blockCentralizer_iff y).mpr hc⟩), rfl⟩

omit [Finite G] in
theorem conj_commutator_mem_barM {M Y Z : Subgroup G} {t : G} (htM : t ∈ M) {n : ℕ}
    (htn : ∀ y ∈ Y, t ^ n * y * (t ^ n)⁻¹ * y⁻¹ ∈ Z) :
    ∀ u ∈ barM M Y, QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨t, htM⟩ ^ n * u *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨t, htM⟩ ^ n)⁻¹ * u⁻¹ ∈ barM M Z := by
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨(⟨t, htM⟩ : M) ^ n * y * ((⟨t, htM⟩ : M) ^ n)⁻¹ * y⁻¹,
    Subgroup.mem_subgroupOf.mpr ?_, by simp only [map_mul, map_pow, map_inv]⟩
  simpa using htn y (Subgroup.mem_subgroupOf.mp hy)

theorem exists_conj_commutator_not_mem_barM {M Y Z : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hYM : Y ≤ M) (hYp : IsPGroup p Y) (hZY : Z ≤ Y) {t : G} (htM : t ∈ M)
    (htY : t ∈ Subgroup.normalizer (Y : Set G)) (htnt : ∃ y ∈ Y, t * y * t⁻¹ * y⁻¹ ∉ Z) :
    ∃ u ∈ barM M Y, QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨t, htM⟩ * u *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨t, htM⟩)⁻¹ * u⁻¹ ∉ barM M Z := by
  obtain ⟨y, hy, hne⟩ := htnt
  refine ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨y, hYM hy⟩,
    ⟨⟨y, hYM hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩, ?_⟩
  rintro ⟨z, hz, hzeq⟩
  set c : M := (⟨t, htM⟩ : M) * ⟨y, hYM hy⟩ * (⟨t, htM⟩ : M)⁻¹ * (⟨y, hYM hy⟩ : M)⁻¹ with hc
  have hcY : (c : G) ∈ Y := by
    simp only [hc, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Y.mul_mem ((Subgroup.mem_normalizer_iff.mp htY y).mp hy) (Y.inv_mem hy)
  have hcz : QuotientGroup.mk' (CFSG.pCore 2 ↥M) c = QuotientGroup.mk' (CFSG.pCore 2 ↥M) z := by
    rw [hzeq]
    simp only [hc, map_mul, map_inv]
  have h1 := eq_of_mk_eq_of_pGroup hp hp2 hYp hcY (hZY (Subgroup.mem_subgroupOf.mp hz)) hcz
  apply hne
  have hct : (c : G) = t * y * t⁻¹ * y⁻¹ := by simp [hc]
  rw [← hct, h1]
  exact Subgroup.mem_subgroupOf.mp hz

omit [Finite G] in
theorem eq_or_eq_barM_of_irreducible {M Y Z : Subgroup G} {t : G} (hYM : Y ≤ M) (hZY : Z ≤ Y)
    (htM : t ∈ M) (htY : t ∈ Subgroup.normalizer (Y : Set G))
    (hirr : ∀ V : Subgroup G, Z ≤ V → V ≤ Y → t ∈ Subgroup.normalizer (V : Set G) →
      V = Z ∨ V = Y)
    (V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) (hZV : barM M Z ≤ V) (hVY : V ≤ barM M Y)
    (htV : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨t, htM⟩ ∈
      Subgroup.normalizer (V : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    V = barM M Z ∨ V = barM M Y := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set W : Subgroup G := Y ⊓ (V.comap mk).map M.subtype with hW
  have hmemW : ∀ m : M, (m : G) ∈ Y → ((m : G) ∈ W ↔ mk m ∈ V) := by
    intro m hm
    constructor
    · rintro ⟨-, m', hm', hmm'⟩
      rw [show m' = m from Subtype.ext hmm'] at hm'
      exact hm'
    · exact fun h => ⟨hm, m, h, rfl⟩
  have hZW : Z ≤ W := by
    intro z hz
    have hzM : z ∈ M := hYM (hZY hz)
    exact (hmemW ⟨z, hzM⟩ (hZY hz)).mpr (hZV ⟨⟨z, hzM⟩, Subgroup.mem_subgroupOf.mpr hz, rfl⟩)
  have hWY : W ≤ Y := inf_le_left
  have hconj : ∀ g : G, (hgM : g ∈ M) →
      mk ((⟨t, htM⟩ : M) * ⟨g, hgM⟩ * (⟨t, htM⟩ : M)⁻¹) =
        mk ⟨t, htM⟩ * mk ⟨g, hgM⟩ * (mk ⟨t, htM⟩)⁻¹ := fun g hgM => by
    simp only [map_mul, map_inv]
  have htW : t ∈ Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      have hgY : g ∈ Y := hWY hg
      have hgM : g ∈ M := hYM hgY
      have htgY : t * g * t⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp htY g).mp hgY
      have h2 : mk ⟨t, htM⟩ * mk ⟨g, hgM⟩ * (mk ⟨t, htM⟩)⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp htV _).mp ((hmemW ⟨g, hgM⟩ hgY).mp hg)
      have h3 := (hmemW ((⟨t, htM⟩ : M) * ⟨g, hgM⟩ * (⟨t, htM⟩ : M)⁻¹)
        (by simpa using htgY)).mpr (by rw [hconj g hgM]; exact h2)
      simpa using h3
    · intro hg
      have htgY : t * g * t⁻¹ ∈ Y := hWY hg
      have hgY : g ∈ Y := (Subgroup.mem_normalizer_iff.mp htY g).mpr htgY
      have hgM : g ∈ M := hYM hgY
      have h1 := (hmemW ((⟨t, htM⟩ : M) * ⟨g, hgM⟩ * (⟨t, htM⟩ : M)⁻¹)
        (by simpa using htgY)).mp (by simpa using hg)
      rw [hconj g hgM] at h1
      exact (hmemW ⟨g, hgM⟩ hgY).mpr ((Subgroup.mem_normalizer_iff.mp htV _).mpr h1)
  rcases hirr W hZW hWY htW with hWZ | hWY'
  · left
    refine le_antisymm (fun x hx => ?_) hZV
    obtain ⟨m, hm, rfl⟩ := hVY hx
    have hmW : (m : G) ∈ W := (hmemW m (Subgroup.mem_subgroupOf.mp hm)).mpr hx
    exact ⟨m, Subgroup.mem_subgroupOf.mpr (hWZ ▸ hmW), rfl⟩
  · right
    refine le_antisymm hVY ?_
    rintro _ ⟨m, hm, rfl⟩
    have hmY := Subgroup.mem_subgroupOf.mp hm
    exact (hmemW m hmY).mp (hWY' ▸ hmY)

theorem pCoreOf_two_le_of_asc81bHyp {M S : Subgroup G} (hA : Asc81bHyp M S) :
    pCoreOf 2 M ≤ S :=
  le_of_two_radical hA.twoRadical.1 hA.twoRadical.2.2
    (RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M)
    (RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
    (inf_le_left.trans (RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M))

theorem barM_normalizer_inf_ne_of_asc81bHyp {M S L : Subgroup G} (hA : Asc81bHyp M S)
    (hL : IsWeakSBlock M S L) : barM M (Subgroup.normalizer (S : Set G) ⊓ L) ≠ barM M L := by
  intro heq
  apply hL.not_le_normalizer
  intro l hl
  have hlM : l ∈ M := hL.le hl
  have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l, hlM⟩ ∈ barM M L :=
    ⟨⟨l, hlM⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
  rw [← heq] at hmem
  exact coe_mem_of_mk_mem_barM ((pCoreOf_two_le_of_asc81bHyp hA).trans Subgroup.le_normalizer)
    ⟨l, hlM⟩ (barM_mono inf_le_left hmem)

theorem ne_inf_normalizer_of_asc81bHyp {M S L : Subgroup G} (hA : Asc81bHyp M S)
    (hL : IsWeakSBlock M S L) (hS : ¬ IsSylowTwoOf (S ⊓ L) L) (h2 : NineThreeTwo M S L) :
    ∀ T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsSylowTwoOf T (barM M L) →
      barM M (Subgroup.normalizer (S : Set G) ⊓ L) ≠
        barM M L ⊓ Subgroup.normalizer (T : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
  ne_inf_normalizer_of_nineThreeTwo h2 fun hsyl => hS (isSylowTwoOf_inf_of_barM hL.le
    (pCoreOf_two_le_of_asc81bHyp hA) hA.twoRadical.isPGroup hsyl)

end CFSG.AGLEmbedding
