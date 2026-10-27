module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductN2
public import CFSG.LocalAnalysis.EvenBN.GMSK.LayerRankOne
import CFSG.LocalAnalysis.EvenBN.TrialityD4.FieldCaseSylow
import CFSG.LocalAnalysis.EvenBN.Common.StandardNormalClosure
import CFSG.LocalAnalysis.SteinbergBKOddNormalQuotientStandard
import CFSG.LocalAnalysis.EvenBN.GMSK.ConsumerSections
import CFSG.LocalAnalysis.SeitzReduction.F4PilotBLiftGomi

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.LocalAnalysis.EvenBN.Common
open CFSG.ABGLocalTools (IsSylowOf)
open scoped MatrixGroups

section Defs

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {q : ℕ}

noncomputable abbrev H1bar (d : TrialityD4Data L q) (t : G) : Type :=
  NormalizerQuotient.Bar (yamadaD₅ d t)

noncomputable abbrev H1hat (d : TrialityD4Data L q) (t : G) : Type :=
  H1bar d t ⧸ CFSG.oddCore (H1bar d t)

@[expose] noncomputable def piHat (d : TrialityD4Data L q) (t : G) : H1bar d t →* H1hat d t :=
  QuotientGroup.mk' (CFSG.oddCore (H1bar d t))

open Classical in
@[expose] noncomputable def tBar (d : TrialityD4Data L q) (t : G) : H1bar d t :=
  if ht : t ∈ normalizer ((yamadaD₅ d t : Subgroup G) : Set G) then
    NormalizerQuotient.proj (yamadaD₅ d t) ⟨t, ht⟩ else 1

@[expose] noncomputable def kBar (d : TrialityD4Data L q) (t : G) : Subgroup (H1bar d t) :=
  NormalizerQuotient.bar (yamadaD₅ d t) (cLV d)

@[expose] noncomputable def pBar (d : TrialityD4Data L q) (t : G) : Subgroup (H1bar d t) :=
  NormalizerQuotient.bar (yamadaD₅ d t) (yamadaP d t)

@[expose] noncomputable def jSixBar (d : TrialityD4Data L q) (t : G) : Subgroup (H1bar d t) :=
  NormalizerQuotient.bar (yamadaD₅ d t) (d.J₆.map L.subtype)

end Defs

namespace ProductN1HatAux

section BarToolkit

variable {G : Type*} [Group G]

theorem bar_sup_left {A X : Subgroup G} (hX : X ≤ normalizer (A : Set G)) :
    NormalizerQuotient.bar A (A ⊔ X) = NormalizerQuotient.bar A X := by
  refine le_antisymm ?_ (NormalizerQuotient.bar_mono le_sup_right)
  intro y hy
  obtain ⟨x, rfl⟩ := NormalizerQuotient.proj_surjective y
  rw [NormalizerQuotient.mem_bar_iff le_sup_left] at hy
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left A X hX, Set.mem_mul] at hy
  obtain ⟨a, ha, z, hz, hxz⟩ := hy
  have hzN : z ∈ normalizer (A : Set G) := hX hz
  have e : NormalizerQuotient.proj A x = NormalizerQuotient.proj A ⟨z, hzN⟩ := by
    rw [NormalizerQuotient.proj_eq_proj_iff]
    show (x : G)⁻¹ * z ∈ A
    rw [← hxz, show (a * z)⁻¹ * z = z⁻¹ * a⁻¹ * z by group]
    have := (mem_normalizer_iff.1 (inv_mem hzN) a⁻¹).1 (inv_mem ha)
    simpa [mul_assoc] using this
  rw [e]
  exact NormalizerQuotient.proj_mem_bar hz

theorem bar_inf {A X Y : Subgroup G} (hAX : A ≤ X) (hAY : A ≤ Y) :
    NormalizerQuotient.bar A (X ⊓ Y) = NormalizerQuotient.bar A X ⊓ NormalizerQuotient.bar A Y := by
  ext y
  obtain ⟨x, rfl⟩ := NormalizerQuotient.proj_surjective y
  rw [NormalizerQuotient.mem_bar_iff (le_inf hAX hAY), Subgroup.mem_inf, Subgroup.mem_inf,
    NormalizerQuotient.mem_bar_iff hAX, NormalizerQuotient.mem_bar_iff hAY]

theorem bar_zpowers {A : Subgroup G} {t : G} (ht : t ∈ normalizer (A : Set G)) :
    NormalizerQuotient.bar A (zpowers t) = zpowers (NormalizerQuotient.proj A ⟨t, ht⟩) := by
  have h1 : (zpowers t).subgroupOf (normalizer (A : Set G)) =
      zpowers (⟨t, ht⟩ : normalizer (A : Set G)) := by
    have h0 : (zpowers (⟨t, ht⟩ : normalizer (A : Set G))).map (normalizer (A : Set G)).subtype =
        zpowers t := MonoidHom.map_zpowers _ _
    rw [Subgroup.subgroupOf, ← h0, comap_map_eq_self_of_injective
      (normalizer (A : Set G)).subtype_injective]
  rw [NormalizerQuotient.bar, h1, MonoidHom.map_zpowers]

theorem centralizer_zpowers_eq {M : Type*} [Group M] (x : M) :
    centralizer ((zpowers x : Subgroup M) : Set M) = centralizer ({x} : Set M) := by
  rw [zpowers_eq_closure, centralizer_closure]

theorem commutator_subgroupOf {N X Y : Subgroup G} (hX : X ≤ N) (hY : Y ≤ N) :
    ⁅X.subgroupOf N, Y.subgroupOf N⁆ = (⁅X, Y⁆).subgroupOf N := by
  have hXY : ⁅X, Y⁆ ≤ N := by
    rw [commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact N.mul_mem (N.mul_mem (N.mul_mem (hX hx) (hY hy)) (N.inv_mem (hX hx)))
      (N.inv_mem (hY hy))
  apply Subgroup.map_injective N.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_of_le_left hX, inf_of_le_left hY, inf_of_le_left hXY]

theorem bar_commutator {A X Y : Subgroup G} (hX : X ≤ normalizer (A : Set G))
    (hY : Y ≤ normalizer (A : Set G)) :
    NormalizerQuotient.bar A ⁅X, Y⁆ = ⁅NormalizerQuotient.bar A X, NormalizerQuotient.bar A Y⁆ := by
  unfold NormalizerQuotient.bar
  rw [← Subgroup.map_commutator, commutator_subgroupOf hX hY]

theorem card_bar [Finite G] {A X : Subgroup G} (hAX : A ≤ X) (hXN : X ≤ normalizer (A : Set G)) :
    Nat.card (NormalizerQuotient.bar A X) = A.relIndex X := by
  have h1 := NormalizerQuotient.card_bar_mul hAX hXN
  have h2 := Subgroup.relIndex_mul_card A X
  rw [inf_of_le_left hAX] at h2
  have hpos : 0 < Nat.card A := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)

theorem isSylowOf_zpowers_of_forall {M : Type*} [Group M] [Finite M] {Y : Subgroup M} {s : M}
    (hs : s ∈ Y) (hs2 : orderOf s = 2)
    (h : ∀ y ∈ Y, (∃ a : ℕ, y ^ (2 ^ a) = 1) → y ∈ zpowers s) :
    IsSylowOf 2 (zpowers s) Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow 2 Y))
  have hTle : (T : Subgroup Y).map Y.subtype ≤ zpowers s := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, hk⟩ := T.isPGroup' ⟨x, hx⟩
    have hk' : (x : Y) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    exact h x x.2 ⟨k, by simpa using congrArg Subtype.val hk'⟩
  have h1 : Nat.card T ≤ 2 := by
    have := Subgroup.card_le_of_le hTle
    rwa [Subgroup.card_map_of_injective Y.subtype_injective, Nat.card_zpowers, hs2] at this
  have h2 : 2 ∣ Nat.card Y := by
    have := orderOf_dvd_natCard (⟨s, hs⟩ : Y)
    rwa [Subgroup.orderOf_mk, hs2] at this
  have hcard : Nat.card T = 2 ^ (Nat.card Y).factorization 2 := Sylow.card_eq_multiplicity T
  have hv : 1 ≤ (Nat.card Y).factorization 2 := by
    have hne : Nat.card Y ≠ 0 := Nat.card_pos.ne'
    exact (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hne).1 h2
  have hv1 : (Nat.card Y).factorization 2 = 1 := by
    by_contra hne
    have h3 : 2 ≤ (Nat.card Y).factorization 2 := by omega
    have : 2 ^ 2 ≤ 2 ^ (Nat.card Y).factorization 2 := Nat.pow_le_pow_right (by norm_num) h3
    omega
  refine CFSG.ABGLocalTools.isSylowOf_of_card (zpowers_le.2 hs) ?_
  rw [Nat.card_zpowers, hs2, hv1, pow_one]

end BarToolkit

section D1Basics

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

abbrev NCV (d : TrialityD4Data L (2 ^ f)) (t : G) : Subgroup G :=
  centralizer ({t} : Set G) ⊓ normalizer ((d.V.map L.subtype : Subgroup G) : Set G)

theorem yamada525 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    ⁅yamadaC₅ d t, yamadaC₅ d t⁆ = yamadaD₁ d t ∧
      normalizer (yamadaC₅ d t : Set G) = yamadaC₅ d t ⊔ NCV d t := by
  obtain ⟨-, h2, h3, -⟩ := h.yamada_5_25 d (h.normalizerHyp_of_layerHyp d hlay)
    (h.yamada_5_6_1 d hlay) (h.yamada_5_6_2 d hlay) (h.yamada_5_9_1 d hlay)
    (h.yamada_5_9_2 d hlay) (h.yamada_5_9_3 d hlay) (h.yamada_5_10_1 d hlay)
    (h.yamada_5_10_2 d hlay) (h.yamadaY₂_eq d hlay) (h.yamada_5_20 d hlay)
    (h.yamada_5_22_1 d hlay) (h.yamada_5_21 d hlay)
  exact ⟨h2, h3⟩

theorem normalizer_C5_le (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    normalizer (yamadaC₅ d t : Set G) ≤ normalizer (yamadaD₅ d t : Set G) := by
  intro g hg
  have hgD₁ : g ∈ normalizer (yamadaD₁ d t : Set G) := by
    rw [← (yamada525 h d hlay).1]
    exact Setup.normalizer_le_normalizer_commutator_C8 _ hg
  have hgV₁ := normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t hgD₁
  exact Common.mem_normalizer_inf hg (Setup.mem_normalizer_centralizer_C8 hgV₁)

theorem t_mem_NCV (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) : t ∈ NCV d t := by
  refine ⟨mem_centralizer_singleton_iff.2 rfl, mem_normalizer_fintype fun w hw => ?_⟩
  obtain ⟨w', hw', rfl⟩ := hw
  have : t * L.subtype w' * t⁻¹ = L.subtype w' := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (mem_centralizer_iff.1 h.htL w' w'.2).symm
  rw [SetLike.mem_coe, this]
  exact ⟨w', hw', rfl⟩

theorem normalizer_C5_eq_sup (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : normalizer (yamadaC₅ d t : Set G) = yamadaD₅ d t ⊔ NCV d t := by
  have h520 := h.yamada_5_20 d hlay
  have hN := (yamada525 h d hlay).2
  have hD₅C₅ : yamadaD₅ d t ≤ yamadaC₅ d t := h520.1 ▸ le_sup_left
  refine le_antisymm ?_ (sup_le (hD₅C₅.trans le_normalizer) (hN ▸ le_sup_right))
  rw [hN]
  refine sup_le ?_ le_sup_right
  rw [h520.1]
  exact sup_le le_sup_left ((zpowers_le.2 (t_mem_NCV h d)).trans le_sup_right)

theorem NCV_le_normalizer_D5 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : NCV d t ≤ normalizer (yamadaD₅ d t : Set G) := by
  have hN := (yamada525 h d hlay).2
  exact (le_sup_right.trans hN.ge).trans (normalizer_C5_le h d hlay)

theorem tBar_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    tBar d t = NormalizerQuotient.proj (yamadaD₅ d t) ⟨t, h.t_mem_normalizer_yamadaD₅_C9 d⟩ := by
  unfold tBar
  rw [dif_pos (h.t_mem_normalizer_yamadaD₅_C9 d)]

theorem lift_centralizer_tBar (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    NormalizerQuotient.lift (centralizer ({tBar d t} : Set (H1bar d t))) =
      normalizer (yamadaC₅ d t : Set G) := by
  have ht := h.t_mem_normalizer_yamadaD₅_C9 d
  have h520 := h.yamada_5_20 d hlay
  have hle := normalizer_C5_le h d hlay
  have htC5 : t ∈ yamadaC₅ d t := by rw [h520.1]; exact mem_sup_right (mem_zpowers t)
  ext g
  rw [NormalizerQuotient.mem_lift_iff]
  constructor
  · rintro ⟨hg, hgc⟩
    rw [tBar_eq h d, mem_centralizer_singleton_iff] at hgc
    have key := (commutator_mem_iff_proj hg ht).1 hgc.symm
    refine mem_normalizer_fintype fun x hx => ?_
    rw [SetLike.mem_coe, h520.1] at hx ⊢
    rcases (mem_sup_zpowers_iff_of_D4 h.t_mul_t ht).1 hx with hx | ⟨b, hb, rfl⟩
    · exact mem_sup_left ((mem_normalizer_iff.1 hg x).1 hx)
    · refine (mem_sup_zpowers_iff_of_D4 h.t_mul_t ht).2 (Or.inr
        ⟨g * b * g⁻¹ * (g * t * g⁻¹ * t⁻¹), mul_mem ((mem_normalizer_iff.1 hg b).1 hb) key, ?_⟩)
      group
  · intro hg
    have hg' := hle hg
    refine ⟨hg', ?_⟩
    rw [tBar_eq h d, mem_centralizer_singleton_iff]
    refine ((commutator_mem_iff_proj hg' ht).2 ?_).symm
    have hgt : g * t * g⁻¹ ∈ yamadaC₅ d t := (mem_normalizer_iff.1 hg t).1 htC5
    rw [h520.1] at hgt
    rcases (mem_sup_zpowers_iff_of_D4 h.t_mul_t ht).1 hgt with h1 | ⟨a, ha, e⟩
    · exfalso
      apply h520.2.1
      have := (mem_normalizer_iff.1 (inv_mem hg') _).1 h1
      rwa [show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t by group] at this
    · rw [e, show a * t * t⁻¹ = a by group]
      exact ha

theorem centralizer_tBar_eq_bar (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    centralizer ({tBar d t} : Set (H1bar d t)) =
      NormalizerQuotient.bar (yamadaD₅ d t) (normalizer (yamadaC₅ d t : Set G)) := by
  conv_lhs => rw [← NormalizerQuotient.bar_lift (centralizer ({tBar d t} : Set (H1bar d t)))]
  rw [lift_centralizer_tBar h d hlay]

theorem centralizer_tBar_eq_bar_NCV (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    centralizer ({tBar d t} : Set (H1bar d t)) =
      NormalizerQuotient.bar (yamadaD₅ d t) (NCV d t) := by
  rw [centralizer_tBar_eq_bar h d hlay, normalizer_C5_eq_sup h d hlay,
    bar_sup_left (NCV_le_normalizer_D5 h d hlay)]

theorem orderOf_tBar (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    orderOf (tBar d t) = 2 := by
  have h520 := h.yamada_5_20 d hlay
  rw [tBar_eq h d]
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow]
    have : (⟨t, h.t_mem_normalizer_yamadaD₅_C9 d⟩ :
        normalizer ((yamadaD₅ d t : Subgroup G) : Set G)) ^ 2 = 1 := by
      apply Subtype.ext
      simp only [pow_two]
      exact h.t_mul_t
    rw [this, map_one]
  · rw [Ne, NormalizerQuotient.proj_eq_one_iff]
    exact h520.2.1

theorem D5_inf_L_le (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    yamadaD₅ d t ⊓ L ≤ d.D.map L.subtype := by
  have h512 := h.yamada_5_12 d (h.normalizerHyp_of_layerHyp d hlay) (h.yamada_5_6_1 d hlay)
    (h.yamada_5_6_2 d hlay) (h.yamada_5_9_1 d hlay) (h.yamada_5_9_2 d hlay)
    (h.yamada_5_9_3 d hlay)
  have hC5C : yamadaC₅ d t ⊓ centralizer ({t} : Set G) = d.D.map L.subtype ⊔ zpowers t :=
    h512.1.2.2.2
  have h520 := h.yamada_5_20 d hlay
  have hD5C5 : yamadaD₅ d t ≤ yamadaC₅ d t := h520.1 ▸ le_sup_left
  rintro x ⟨hx5, hxL⟩
  have hx : x ∈ d.D.map L.subtype ⊔ zpowers t := hC5C ▸ ⟨hD5C5 hx5, h.L_le_centralizer hxL⟩
  rcases (h.mem_sup_zpowers_iff (map_subtype_le _)).1 hx with h1 | h1
  · exact h1
  · exfalso
    apply h.t_not_mem_L
    have := mul_mem (map_subtype_le _ h1) (inv_mem hxL)
    rwa [mul_inv_cancel_right] at this

theorem cLV_le_L (d : TrialityD4Data L (2 ^ f)) : cLV d ≤ L := map_subtype_le _

theorem cLV_le_normalizer_D5 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : cLV d ≤ normalizer (yamadaD₅ d t : Set G) := by
  rintro _ ⟨l, hl, rfl⟩
  exact (h.coe_mem_normalizer_yamadaD₅_C9 d (h.yamada_5_6_1 d hlay)
    (centralizer_le_normalizer _ hl)).2.2

theorem kBar_le_centralizer_tBar (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    kBar d t ≤ centralizer ({tBar d t} : Set (H1bar d t)) := by
  have ht := h.t_mem_normalizer_yamadaD₅_C9 d
  rintro _ ⟨⟨x, hxN⟩, hx, rfl⟩
  rw [mem_centralizer_singleton_iff, tBar_eq h d]
  refine ((commutator_mem_iff_proj hxN ht).2 ?_).symm
  have hxL : x ∈ L := cLV_le_L d (mem_subgroupOf.1 hx)
  rw [mem_centralizer_iff.1 h.htL x hxL, show t * x * x⁻¹ * t⁻¹ = 1 by group]
  exact one_mem _

theorem D_map_le_D5 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    d.D.map L.subtype ≤ yamadaD₅ d t :=
  le_inf ((h.D_map_le_yamadaC₁ d).trans (yamadaC₁_le_yamadaC₅ d t))
    ((map_mono d.D_le_S).trans (h.S_map_le_centralizer_yamadaV₁ d hlay))

theorem exists_leviToBar (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    ∃ ψ : d.leviShort →* H1bar d t, Function.Injective ψ ∧ ψ.range = kBar d t := by
  have hmem : ∀ s : d.leviShort, ((s : L) : G) ∈ cLV d := fun s =>
    ⟨s.1, d.leviShort_le_centralizer_V s.2, rfl⟩
  have hN : ∀ s : d.leviShort, ((s : L) : G) ∈ normalizer (yamadaD₅ d t : Set G) := fun s =>
    cLV_le_normalizer_D5 h d hlay (hmem s)
  let j : d.leviShort →* normalizer (yamadaD₅ d t : Set G) :=
    MonoidHom.codRestrict (L.subtype.comp d.leviShort.subtype) _ hN
  refine ⟨(NormalizerQuotient.proj (yamadaD₅ d t)).comp j, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro s hs
    have hs' : ((s : L) : G) ∈ yamadaD₅ d t := NormalizerQuotient.proj_eq_one_iff.1 hs
    obtain ⟨n, hn, hns⟩ := D5_inf_L_le h d hlay ⟨hs', (s : L).2⟩
    have hn' : n = (s : L) := Subtype.ext hns
    have : (s : L) ∈ d.D ⊓ d.leviShort := ⟨hn' ▸ hn, s.2⟩
    rw [d.D_inf_leviShort, mem_bot] at this
    exact Subtype.ext this
  · ext y
    constructor
    · rintro ⟨s, rfl⟩
      exact NormalizerQuotient.proj_mem_bar (hmem s)
    · rintro ⟨⟨x, hxN⟩, hx, rfl⟩
      obtain ⟨l, hl, rfl⟩ := mem_subgroupOf.1 hx
      rw [d.centralizer_V_eq] at hl
      obtain ⟨n, hn, s, hs, rfl⟩ := d.exists_mul_of_mem_D_sup_leviShort hl
      refine ⟨⟨s, hs⟩, ?_⟩
      show NormalizerQuotient.proj (yamadaD₅ d t) ⟨((s : L) : G), hN ⟨s, hs⟩⟩ =
        NormalizerQuotient.proj (yamadaD₅ d t) ⟨L.subtype (n * s), hxN⟩
      rw [NormalizerQuotient.proj_eq_proj_iff]
      show ((s : L) : G)⁻¹ * ((n * s : L) : G) ∈ yamadaD₅ d t
      rw [show ((s : L) : G)⁻¹ * ((n * s : L) : G) = ((s : L) : G)⁻¹ * (n : G) * (s : G) by
        simp [mul_assoc]]
      have h1 := (mem_normalizer_iff.1 (inv_mem (hN ⟨s, hs⟩)) (n : G)).1
        (D_map_le_D5 h d hlay ⟨n, hn, rfl⟩)
      simpa using h1

theorem kBar_equiv (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    Nonempty (↥(kBar d t) ≃* SL(2, d.Γ)) := by
  obtain ⟨ψ, hinj, hrange⟩ := exists_leviToBar h d hlay
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm.trans
    d.leviShortEquiv⟩

theorem J₁_pow_eq_one {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q) {j : X}
    (hj : j ∈ d.J₁) : j ^ (q - 1) = 1 := by
  obtain ⟨⟨l, m⟩, rfl, hm⟩ := d.mem_J₁.1 hj
  dsimp only at hm
  subst hm
  have : Fintype d.Γ₀ := Fintype.ofFinite _
  have h1 : Fintype.card d.Γ₀ = q := by rw [← Nat.card_eq_fintype_card]; exact d.card_Γ₀
  have h2 : (l : d.Γ₀) ^ (q - 1) = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one (l : d.Γ₀) l.ne_zero
    rwa [h1] at this
  have hl : l ^ (q - 1) = 1 := Units.ext (by simpa using h2)
  rw [← map_pow]
  have : ((l, (1 : d.Γˣ)) ^ (q - 1) : (d.Γ₀)ˣ × d.Γˣ) = 1 :=
    Prod.ext (by simpa using hl) (by simp)
  rw [this, map_one]

theorem mem_zpowers_tBar_of_two_element (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {y : H1bar d t}
    (hyt : y ∈ centralizer ({tBar d t} : Set (H1bar d t)))
    (hyK : y ∈ centralizer ((kBar d t : Subgroup (H1bar d t)) : Set (H1bar d t)))
    {a : ℕ} (hya : y ^ (2 ^ a) = 1) : y ∈ zpowers (tBar d t) := by
  have ht := h.t_mem_normalizer_yamadaD₅_C9 d
  have hyt' := hyt
  rw [centralizer_tBar_eq_bar_NCV h d hlay] at hyt'
  obtain ⟨⟨n, hnN⟩, hn, rfl⟩ := hyt'
  have hn : n ∈ NCV d t := mem_subgroupOf.1 hn
  have hnC : n ∈ centralizer ({t} : Set G) := hn.1
  have hV : ∀ v ∈ d.V, h.act ⟨n, hnC⟩ v ∈ d.V := by
    intro v hv
    rw [← h.conj_mem_map_iff hnC]
    exact (mem_normalizer_iff.1 hn.2 _).1 ⟨v, hv, rfl⟩
  have hα : ∀ s ∈ d.leviShort, h.act ⟨n, hnC⟩ s * s⁻¹ ∈ d.D := by
    intro s hs
    have hsc : ((s : L) : G) ∈ cLV d := ⟨s, d.leviShort_le_centralizer_V hs, rfl⟩
    have hsN := cLV_le_normalizer_D5 h d hlay hsc
    have hcomm := mem_centralizer_iff.1 hyK _
      (NormalizerQuotient.proj_mem_bar (x := ⟨((s : L) : G), hsN⟩) hsc)
    have hcomm' := (commutator_mem_iff_proj hnN hsN).1 hcomm
    have hmem : ((h.act ⟨n, hnC⟩ s * s⁻¹ : L) : G) ∈ d.D.map L.subtype := by
      apply D5_inf_L_le h d hlay
      refine ⟨?_, (h.act ⟨n, hnC⟩ s * s⁻¹ : L).2⟩
      rw [Subgroup.coe_mul, h.coe_act_apply, Subgroup.coe_inv]
      exact hcomm'
    obtain ⟨w, hw, hw'⟩ := hmem
    have : w = h.act ⟨n, hnC⟩ s * s⁻¹ := L.subtype_injective hw'
    exact this ▸ hw
  obtain ⟨n₀, hn₀, j, hj, hnj⟩ := d.eq_conj_of_trivial_mod_D hV hα
  obtain ⟨c, hc, hnc⟩ := h.exists_mul_zpowers_of_act_eq_conj d hnC hnj
  have hjN : ((j : L) : G) ∈ normalizer (yamadaD₅ d t : Set G) :=
    (h.coe_mem_normalizer_yamadaD₅_C9 d (h.yamada_5_6_1 d hlay) (d.J_le_normalizer_V hj.1)).2.2
  have hn₀D : ((n₀ : L) : G) ∈ yamadaD₅ d t := D_map_le_D5 h d hlay ⟨n₀, hn₀, rfl⟩
  have hcN : c ∈ normalizer (yamadaD₅ d t : Set G) := (zpowers_le.2 ht) hc
  have hy_eq : NormalizerQuotient.proj (yamadaD₅ d t) ⟨n, hnN⟩ =
      NormalizerQuotient.proj (yamadaD₅ d t) ⟨((j : L) : G), hjN⟩ *
        NormalizerQuotient.proj (yamadaD₅ d t) ⟨c, hcN⟩ := by
    have h1 : (⟨n, hnN⟩ : normalizer (yamadaD₅ d t : Set G)) =
        ⟨((n₀ : L) : G), le_normalizer hn₀D⟩ * ⟨((j : L) : G), hjN⟩ * ⟨c, hcN⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [hnc]
      rfl
    rw [h1, map_mul, map_mul, NormalizerQuotient.proj_eq_one_iff.2 hn₀D, one_mul]
  have hcb : NormalizerQuotient.proj (yamadaD₅ d t) ⟨c, hcN⟩ ∈ zpowers (tBar d t) := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
    refine ⟨k, ?_⟩
    show (tBar d t) ^ k = _
    rw [tBar_eq h d, ← map_zpow]
    congr 1
  set cb := NormalizerQuotient.proj (yamadaD₅ d t) ⟨c, hcN⟩ with hcbdef
  set jb := NormalizerQuotient.proj (yamadaD₅ d t) ⟨((j : L) : G), hjN⟩ with hjbdef
  set y := NormalizerQuotient.proj (yamadaD₅ d t) ⟨n, hnN⟩ with hydef
  have ht2 : tBar d t ^ 2 = 1 := by
    have := pow_orderOf_eq_one (tBar d t)
    rwa [orderOf_tBar h d hlay] at this
  have hcb2 : cb ^ 2 = 1 := by
    obtain ⟨k, hk⟩ := hcb
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht2, one_zpow]
  have hcomm : Commute y cb⁻¹ := by
    obtain ⟨k, hk⟩ := hcb
    have hc0 : Commute y (tBar d t) := mem_centralizer_singleton_iff.1 hyt
    rw [← hk]
    exact (hc0.zpow_right k).inv_right
  have hjy : jb = y * cb⁻¹ := by
    rw [hy_eq, mul_inv_cancel_right]
  have hj1 : jb ^ (2 ^ f - 1) = 1 := by
    rw [hjbdef, ← map_pow]
    have : (⟨((j : L) : G), hjN⟩ : normalizer (yamadaD₅ d t : Set G)) ^ (2 ^ f - 1) = 1 := by
      apply Subtype.ext
      have := J₁_pow_eq_one d hj
      simpa using congrArg Subtype.val this
    rw [this, map_one]
  have hb : jb ^ (2 ^ (a + 1)) = 1 := by
    have e1 : y ^ (2 ^ (a + 1)) = 1 := by rw [pow_succ, pow_mul, hya, one_pow]
    have e2 : (cb⁻¹) ^ (2 ^ (a + 1)) = 1 := by
      rw [pow_succ', pow_mul, inv_pow, hcb2, inv_one, one_pow]
    rw [hjy, hcomm.mul_pow, e1, e2, one_mul]
  have hodd : Nat.Coprime (2 ^ (a + 1)) (2 ^ f - 1) := by
    apply Nat.Coprime.pow_left
    rw [Nat.coprime_two_left]
    exact odd_sub_one_of_even d.even_q Nat.one_le_two_pow
  have hjb1 : jb = 1 := by
    have h1 : orderOf jb ∣ 2 ^ (a + 1) := orderOf_dvd_of_pow_eq_one hb
    have h2 : orderOf jb ∣ 2 ^ f - 1 := orderOf_dvd_of_pow_eq_one hj1
    have h3 : orderOf jb ∣ Nat.gcd (2 ^ (a + 1)) (2 ^ f - 1) := Nat.dvd_gcd h1 h2
    rw [Nat.Coprime.gcd_eq_one hodd] at h3
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  rw [hy_eq, hjb1, one_mul]
  exact hcb

theorem isSylowOf_tBar (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    IsSylowOf 2 (zpowers (tBar d t))
      (centralizer ({tBar d t} : Set (H1bar d t)) ⊓
        centralizer ((kBar d t : Subgroup (H1bar d t)) : Set (H1bar d t))) := by
  refine isSylowOf_zpowers_of_forall ?_ (orderOf_tBar h d hlay) ?_
  · exact ⟨mem_centralizer_singleton_iff.2 rfl, mem_centralizer_iff.2 fun y hy =>
      mem_centralizer_singleton_iff.1 (kBar_le_centralizer_tBar h d hy)⟩
  · rintro y ⟨hyt, hyK⟩ ⟨a, ha⟩
    exact mem_zpowers_tBar_of_two_element h d hlay hyt hyK ha

theorem commutator_le_of_le {M : Type*} [Group M] {N X Y : Subgroup M} (hX : X ≤ N) (hY : Y ≤ N) :
    ⁅X, Y⁆ ≤ N := by
  rw [commutator_le]
  intro x hx y hy
  rw [commutatorElement_def]
  exact N.mul_mem (N.mul_mem (N.mul_mem (hX hx) (hY hy)) (N.inv_mem (hX hx))) (N.inv_mem (hY hy))

theorem P_le_normalizer_D5 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaP d t ≤ normalizer (yamadaD₅ d t : Set G) := by
  intro x hx
  refine mem_normalizer_fintype fun z hz => ?_
  have hzP : z ∈ yamadaP d t := yamadaD₅_le_yamadaP d t hz
  have := mul_mem (Setup.yamadaF₄_le_yamadaD₅_PA d
    (h.commutator_mem_yamadaF₄_of_mem_yamadaP d hlay hx hzP)) hz
  rwa [show x * z * x⁻¹ * z⁻¹ * z = x * z * x⁻¹ by group] at this

theorem pBar_basic (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    IsElemAbelian 2 (pBar d t) ∧ Nat.card (pBar d t) = (2 ^ f) ^ 6 ∧
      Nat.card (pBar d t) =
        (Nat.card ↥(pBar d t ⊓ centralizer ({tBar d t} : Set (H1bar d t)))) ^ 2 ∧
      pBar d t ⊓ centralizer ({tBar d t} : Set (H1bar d t)) =
        NormalizerQuotient.bar (yamadaD₅ d t) (d.S.map L.subtype) ∧
      Nat.card (NormalizerQuotient.bar (yamadaD₅ d t) (d.S.map L.subtype)) = (2 ^ f) ^ 3 := by
  have hlay := hp.layer
  have ht := h.t_mem_normalizer_yamadaD₅_C9 d
  obtain ⟨-, -, -, -, -, -, hPC, hD5card, -, hPcard, -, -, -, -, -, ⟨hAB, hfree, hfix⟩, -, -⟩ :=
    T4_series_free h d hp
  have hPN := P_le_normalizer_D5 h d hlay
  have hD5P : yamadaD₅ d t ≤ yamadaP d t := hAB.le
  have hSP : d.S.map L.subtype ≤ yamadaP d t := h.S_map_le_yamadaP d hlay
  have hCM : centralizerMod (yamadaD₅ d t) (zpowers t) =
      NormalizerQuotient.lift (centralizer ({tBar d t} : Set (H1bar d t))) := by
    unfold centralizerMod
    rw [bar_zpowers ht, ← tBar_eq h d, centralizer_zpowers_eq]
  have hD5CM : yamadaD₅ d t ≤ centralizerMod (yamadaD₅ d t) (zpowers t) := by
    rw [hCM]; exact NormalizerQuotient.le_lift _
  have hbarinf : NormalizerQuotient.bar (yamadaD₅ d t)
      (yamadaP d t ⊓ centralizerMod (yamadaD₅ d t) (zpowers t)) =
        pBar d t ⊓ centralizer ({tBar d t} : Set (H1bar d t)) := by
    rw [bar_inf hD5P hD5CM, hCM, NormalizerQuotient.bar_lift]
    rfl
  have hbarS : NormalizerQuotient.bar (yamadaD₅ d t)
      (yamadaP d t ⊓ centralizerMod (yamadaD₅ d t) (zpowers t)) =
        NormalizerQuotient.bar (yamadaD₅ d t) (d.S.map L.subtype) := by
    rw [hfix, hPC, sup_comm]
    exact bar_sup_left (hSP.trans hPN)
  have hcard1 : Nat.card (pBar d t) = (2 ^ f) ^ 6 := by
    have hc := NormalizerQuotient.card_bar_mul hD5P hPN
    rw [hD5card, hPcard] at hc
    have h24 : ((2 : ℕ) ^ f) ^ 24 = (2 ^ f) ^ 6 * (2 ^ f) ^ 18 := by rw [← pow_add]
    exact Nat.eq_of_mul_eq_mul_right (by positivity) (hc.trans h24)
  have hcard2 : Nat.card (pBar d t) =
      (Nat.card ↥(pBar d t ⊓ centralizer ({tBar d t} : Set (H1bar d t)))) ^ 2 := by
    have hPCM : yamadaP d t ⊓ centralizerMod (yamadaD₅ d t) (zpowers t) ≤
        normalizer (yamadaD₅ d t : Set G) := inf_le_left.trans hPN
    have e1 : Nat.card (pBar d t) = (yamadaD₅ d t).relIndex (yamadaP d t) := card_bar hD5P hPN
    have e2 := card_bar (le_inf hD5P hD5CM) hPCM
    rw [hbarinf] at e2
    rw [e1, hfree, e2]
  have hcard3 : Nat.card (NormalizerQuotient.bar (yamadaD₅ d t) (d.S.map L.subtype)) =
      (2 ^ f) ^ 3 := by
    have hh : Nat.card (NormalizerQuotient.bar (yamadaD₅ d t) (d.S.map L.subtype)) ^ 2 =
        ((2 ^ f) ^ 3) ^ 2 := by
      rw [← pow_mul, show 3 * 2 = 6 by norm_num, ← hcard1, hcard2, ← hbarS, hbarinf]
    exact Nat.pow_left_injective (by norm_num) hh
  refine ⟨?_, hcard1, hcard2, hbarinf.symm.trans hbarS, hcard3⟩
  refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · obtain ⟨⟨a, haN⟩, ha, hxa⟩ := x.2
    obtain ⟨⟨b, hbN⟩, hb, hyb⟩ := y.2
    apply Subtype.ext
    show (x : H1bar d t) * y = y * x
    rw [← hxa, ← hyb]
    exact ((commutator_mem_iff_proj haN hbN).2
      (hAB.commutator_mem a (mem_subgroupOf.1 ha) b (mem_subgroupOf.1 hb))).symm
  · rintro _ ⟨⟨a, haN⟩, ha, rfl⟩
    rw [← map_pow]
    refine NormalizerQuotient.proj_eq_one_iff.2 ?_
    show a ^ 2 ∈ yamadaD₅ d t
    rw [pow_two]
    exact hAB.mul_self_mem a (mem_subgroupOf.1 ha)

theorem J6_le_normalizer_P (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : d.J₆.map L.subtype ≤ normalizer (yamadaP d t : Set G) := by
  intro x hx
  have hxJ : x ∈ d.J.map L.subtype := map_mono inf_le_left hx
  have hxS : x ∈ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) :=
    Setup.map_le_normalizer_map d.J_le_normalizer_S hxJ
  have hxC : x ∈ centralizer ({t} : Set G) := h.L_le_centralizer (map_subtype_le _ hx)
  exact ncs_le_normalizer_yamadaP h d hlay ⟨hxC, hxS⟩

theorem J6_le_normalizer_D5 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : d.J₆.map L.subtype ≤ normalizer (yamadaD₅ d t : Set G) := by
  rintro _ ⟨j, hj, rfl⟩
  exact (h.coe_mem_normalizer_yamadaD₅_C9 d (h.yamada_5_6_1 d hlay)
    (d.J_le_normalizer_V hj.1)).2.2

theorem fpf_commutator {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q) {a : d.Γ} {n : X}
    (hn : n ∈ d.D) (b : d.Γˣ)
    (h : (d.x₁ a * n) * d.hBCD b * (d.x₁ a * n)⁻¹ * (d.hBCD b)⁻¹ ∈ d.D) :
    (1 + (b : d.Γ) ^ 2) * a = 0 := by
  have hjJ : d.hBCD b ∈ d.J := by
    have : d.hBCD b ∈ d.J₆ := by rw [d.J₆_eq_range_hBCD]; exact ⟨b, rfl⟩
    exact this.1
  have hjD : d.hBCD b ∈ normalizer (d.D : Set X) := d.J_le_normalizer_D hjJ
  have huD : d.x₁ a ∈ normalizer (d.D : Set X) :=
    d.S_le_normalizer_D (d.U₁_le_S (d.x₁_mem_U₁ a))
  have hn' : n * (d.hBCD b * n⁻¹ * (d.hBCD b)⁻¹) ∈ d.D :=
    mul_mem hn ((mem_normalizer_iff.1 hjD n⁻¹).1 (inv_mem hn))
  have hm : d.x₁ a * (n * (d.hBCD b * n⁻¹ * (d.hBCD b)⁻¹)) * (d.x₁ a)⁻¹ ∈ d.D :=
    (mem_normalizer_iff.1 huD _).1 hn'
  have hconj := d.hBCD_conj_x₁ b a
  have e : (d.x₁ a * n) * d.hBCD b * (d.x₁ a * n)⁻¹ * (d.hBCD b)⁻¹ =
      (d.x₁ a * (n * (d.hBCD b * n⁻¹ * (d.hBCD b)⁻¹)) * (d.x₁ a)⁻¹) *
        (d.x₁ a * (d.hBCD b * (d.x₁ a)⁻¹ * (d.hBCD b)⁻¹)) := by group
  rw [e] at h
  have h2 : d.hBCD b * (d.x₁ a)⁻¹ * (d.hBCD b)⁻¹ = d.x₁ ((b : d.Γ) ^ 2 * a) := by
    rw [d.x₁_inv, hconj]
  rw [h2, ← d.x₁_add] at h
  have h3 : d.x₁ (a + (b : d.Γ) ^ 2 * a) ∈ d.D := by
    have := mul_mem (inv_mem hm) h
    rwa [inv_mul_cancel_left] at this
  have h4 : d.x₁ (a + (b : d.Γ) ^ 2 * a) ∈ d.D ⊓ d.leviShort :=
    ⟨h3, d.x₁_mem_leviShort _⟩
  rw [d.D_inf_leviShort, mem_bot, ← d.x₁_zero] at h4
  have := d.x₁_injective h4
  calc (1 + (b : d.Γ) ^ 2) * a = a + (b : d.Γ) ^ 2 * a := by ring
    _ = 0 := this

theorem exists_unit_one_add_sq_ne_zero {X : Type*} [Group X] {f : ℕ}
    (d : TrialityD4Data X (2 ^ f)) (hf : 1 ≤ f) : ∃ b : d.Γˣ, 1 + (b : d.Γ) ^ 2 ≠ 0 := by
  have hcard : Nat.card d.Γˣ = (2 ^ f) ^ 3 - 1 := by
    rw [Nat.card_units, d.card_Γ]
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h1 : 1 < Nat.card d.Γˣ := by
    rw [hcard]
    have : 2 ^ 3 ≤ (2 ^ f) ^ 3 := Nat.pow_le_pow_left hq 3
    omega
  have : Nontrivial d.Γˣ := Finite.one_lt_card_iff_nontrivial.1 h1
  obtain ⟨b, hb⟩ := exists_ne (1 : d.Γˣ)
  refine ⟨b, fun h0 => hb ?_⟩
  have h2 : (b : d.Γ) ^ 2 = 1 ^ 2 := by
    have : (b : d.Γ) ^ 2 = -1 := eq_neg_of_add_eq_zero_right h0
    rw [this, CharTwo.neg_eq, one_pow]
  exact Units.ext (by rw [Units.val_one]; exact d.sq_injective h2)

theorem fpf_S (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d)
    (hf : 1 ≤ f) :
    (yamadaD₅ d t ⊔ d.S.map L.subtype) ⊓
        centralizerMod (yamadaD₅ d t) (d.J₆.map L.subtype) ≤ yamadaD₅ d t := by
  have hSN : d.S.map L.subtype ≤ normalizer (yamadaD₅ d t : Set G) := by
    rintro _ ⟨σ, hσ, rfl⟩
    exact (h.coe_mem_normalizer_yamadaD₅_C9 d (h.yamada_5_6_1 d hlay)
      (d.S_le_normalizer_V hσ)).2.2
  intro x hx
  obtain ⟨hxS, hxC⟩ := Subgroup.mem_inf.1 hx
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hSN,
    Set.mem_mul] at hxS
  obtain ⟨δ, hδ, s, hs, rfl⟩ := hxS
  obtain ⟨σ, hσ, rfl⟩ := hs
  obtain ⟨a, n, hn, rfl⟩ := d.mem_S_iff.1 hσ
  obtain ⟨b, hb⟩ := exists_unit_one_add_sq_ne_zero d hf
  have hjJ6 : d.hBCD b ∈ d.J₆ := by rw [d.J₆_eq_range_hBCD]; exact ⟨b, rfl⟩
  have hjmem : ((d.hBCD b : L) : G) ∈ d.J₆.map L.subtype := ⟨_, hjJ6, rfl⟩
  have hjN := J6_le_normalizer_D5 h d hlay hjmem
  have hcomm := (mem_centralizerMod_iff.1 hxC).2 _ hjmem hjN
  have hsc : L.subtype (d.x₁ a * n) * ((d.hBCD b : L) : G) * (L.subtype (d.x₁ a * n))⁻¹ *
      ((d.hBCD b : L) : G)⁻¹ ∈ yamadaD₅ d t := by
    have e : L.subtype (d.x₁ a * n) * ((d.hBCD b : L) : G) * (L.subtype (d.x₁ a * n))⁻¹ *
        ((d.hBCD b : L) : G)⁻¹ = δ⁻¹ * (δ * L.subtype (d.x₁ a * n) * ((d.hBCD b : L) : G) *
          (δ * L.subtype (d.x₁ a * n))⁻¹ * ((d.hBCD b : L) : G)⁻¹) *
          (((d.hBCD b : L) : G) * δ * ((d.hBCD b : L) : G)⁻¹) := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hδ) hcomm) ((mem_normalizer_iff.1 hjN δ).1 hδ)
  obtain ⟨w, hw, hw'⟩ := D5_inf_L_le h d hlay
    (⟨hsc, ((d.x₁ a * n) * d.hBCD b * (d.x₁ a * n)⁻¹ * (d.hBCD b)⁻¹ : L).2⟩ :
      _ ∈ yamadaD₅ d t ⊓ L)
  have hwD : w = (d.x₁ a * n) * d.hBCD b * (d.x₁ a * n)⁻¹ * (d.hBCD b)⁻¹ :=
    L.subtype_injective hw'
  have ha : a = 0 := by
    have := fpf_commutator d hn b (hwD ▸ hw)
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 hb
    · exact h0
  subst ha
  show δ * L.subtype (d.x₁ 0 * n) ∈ yamadaD₅ d t
  rw [d.x₁_zero, one_mul]
  exact mul_mem hδ (D_map_le_D5 h d hlay ⟨n, hn, rfl⟩)

theorem pBar_eq_commutator (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) : pBar d t = ⁅pBar d t, jSixBar d t⁆ := by
  have hlay := hp.layer
  have ht := h.t_mem_normalizer_yamadaD₅_C9 d
  obtain ⟨-, -, -, -, -, -, hPC, -, -, -, -, -, -, -, -, ⟨hAB, hfree, hfix⟩, -, -⟩ :=
    T4_series_free h d hp
  have hPN := P_le_normalizer_D5 h d hlay
  have hD5P : yamadaD₅ d t ≤ yamadaP d t := hAB.le
  have hJN := J6_le_normalizer_P h d hlay
  have hJD5 := J6_le_normalizer_D5 h d hlay
  have hodd : Odd (Nat.card (d.J₆.map L.subtype)) := by
    rw [Subgroup.card_map_of_injective L.subtype_injective, d.card_J₆]
    exact odd_sub_one_of_even ((Nat.even_pow' (by norm_num)).2 d.even_q)
      (Nat.one_le_pow _ _ (by positivity))
  have hJτ : d.J₆.map L.subtype ≤ centralizer ({t} : Set G) :=
    (map_subtype_le _).trans h.L_le_centralizer
  obtain ⟨hdecomp, -, hfreeCM⟩ := T3_fixed hAB h.t_mul_t (h.t_mem_normalizer_yamadaP d hlay) ht
    hfree hodd hJτ hJN hJD5
  have hD5CM : ∀ B : Subgroup G, yamadaD₅ d t ≤ centralizerMod (yamadaD₅ d t) B := fun B => by
    unfold centralizerMod
    exact NormalizerQuotient.le_lift _
  have hfix6 : yamadaP d t ⊓ centralizerMod (yamadaD₅ d t) (d.J₆.map L.subtype) ≤
      yamadaD₅ d t := by
    have hfx : (yamadaP d t ⊓ centralizerMod (yamadaD₅ d t) (d.J₆.map L.subtype)) ⊓
        centralizerMod (yamadaD₅ d t) (zpowers t) = yamadaD₅ d t := by
      refine le_antisymm ?_ (le_inf (le_inf hD5P (hD5CM _)) (hD5CM _))
      calc (yamadaP d t ⊓ centralizerMod (yamadaD₅ d t) (d.J₆.map L.subtype)) ⊓
            centralizerMod (yamadaD₅ d t) (zpowers t)
          = (yamadaP d t ⊓ centralizerMod (yamadaD₅ d t) (zpowers t)) ⊓
              centralizerMod (yamadaD₅ d t) (d.J₆.map L.subtype) := inf_right_comm _ _ _
        _ = (yamadaD₅ d t ⊔ d.S.map L.subtype) ⊓
              centralizerMod (yamadaD₅ d t) (d.J₆.map L.subtype) := by
            rw [hfix, hPC, sup_comm]
        _ ≤ yamadaD₅ d t := fpf_S h d hlay (by have := hp.two_le; omega)
    have hrel := hfreeCM
    unfold IsFreeSection at hrel
    rw [hfx, Subgroup.relIndex_self] at hrel
    exact Subgroup.relIndex_eq_one.1 (by simpa using hrel)
  have hcommP : ⁅yamadaP d t, d.J₆.map L.subtype⁆ ≤ yamadaP d t := by
    rw [commutator_le]
    intro p hp j hj
    rw [commutatorElement_def, show p * j * p⁻¹ * j⁻¹ = p * (j * p⁻¹ * j⁻¹) by group]
    exact mul_mem hp ((mem_normalizer_iff.1 (hJN hj) p⁻¹).1 (inv_mem hp))
  have hcommN : ⁅yamadaP d t, d.J₆.map L.subtype⁆ ≤ normalizer (yamadaD₅ d t : Set G) :=
    commutator_le_of_le hPN hJD5
  have hP : yamadaP d t = yamadaD₅ d t ⊔ ⁅yamadaP d t, d.J₆.map L.subtype⁆ := by
    refine le_antisymm ?_ (sup_le hD5P hcommP)
    calc yamadaP d t
        = (yamadaP d t ⊓ centralizerMod (yamadaD₅ d t) (d.J₆.map L.subtype)) ⊔
            (⁅yamadaP d t, d.J₆.map L.subtype⁆ ⊔ yamadaD₅ d t) := hdecomp
      _ ≤ yamadaD₅ d t ⊔ (⁅yamadaP d t, d.J₆.map L.subtype⁆ ⊔ yamadaD₅ d t) :=
          sup_le_sup_right hfix6 _
      _ = yamadaD₅ d t ⊔ ⁅yamadaP d t, d.J₆.map L.subtype⁆ := by
          rw [sup_comm ⁅yamadaP d t, d.J₆.map L.subtype⁆, ← sup_assoc, sup_idem]
  have hbar : NormalizerQuotient.bar (yamadaD₅ d t) (yamadaP d t) =
      NormalizerQuotient.bar (yamadaD₅ d t) ⁅yamadaP d t, d.J₆.map L.subtype⁆ := by
    rw [← bar_sup_left hcommN]
    exact congrArg _ hP
  show NormalizerQuotient.bar (yamadaD₅ d t) (yamadaP d t) =
    ⁅NormalizerQuotient.bar (yamadaD₅ d t) (yamadaP d t),
      NormalizerQuotient.bar (yamadaD₅ d t) (d.J₆.map L.subtype)⁆
  rw [← bar_commutator hPN hJD5]
  exact hbar

theorem jSixBar_le_kBar (d : TrialityD4Data L (2 ^ f)) : jSixBar d t ≤ kBar d t := by
  have : d.J₆.map L.subtype ≤ cLV d := by
    rintro _ ⟨j, hj, rfl⟩
    exact ⟨j, hj.2, rfl⟩
  exact NormalizerQuotient.bar_mono this

end D1Basics

end ProductN1HatAux

section Statements

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem D1_centralizer_tbar (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) :
    normalizer ((yamadaC₅ d t : Subgroup G) : Set G) ≤
        normalizer ((yamadaD₅ d t : Subgroup G) : Set G) ∧
    (centralizer ({tBar d t} : Set (H1bar d t)) =
        NormalizerQuotient.bar (yamadaD₅ d t) (normalizer ((yamadaC₅ d t : Subgroup G) : Set G)) ∧
      NormalizerQuotient.bar (yamadaD₅ d t) (normalizer ((yamadaC₅ d t : Subgroup G) : Set G)) =
        NormalizerQuotient.bar (yamadaD₅ d t)
          (centralizer ({t} : Set G) ⊓ normalizer ((d.V.map L.subtype : Subgroup G) : Set G)) ∧
      orderOf (tBar d t) = 2) ∧
    (Nonempty (↥(kBar d t) ≃* SL(2, d.Γ)) ∧
      IsSylowOf 2 (zpowers (tBar d t))
        (centralizer ({tBar d t} : Set (H1bar d t)) ⊓
          centralizer ((kBar d t : Subgroup (H1bar d t)) : Set (H1bar d t)))) ∧
    (IsElemAbelian 2 (pBar d t) ∧ Nat.card (pBar d t) = (2 ^ f) ^ 6 ∧
      Nat.card (pBar d t) =
        (Nat.card ↥(pBar d t ⊓ centralizer ({tBar d t} : Set (H1bar d t)))) ^ 2 ∧
      pBar d t ⊓ centralizer ({tBar d t} : Set (H1bar d t)) =
        NormalizerQuotient.bar (yamadaD₅ d t) (d.S.map L.subtype) ∧
      Nat.card (NormalizerQuotient.bar (yamadaD₅ d t) (d.S.map L.subtype)) = (2 ^ f) ^ 3 ∧
      pBar d t = ⁅pBar d t, jSixBar d t⁆) := by
  have hlay := hp.layer
  refine ⟨ProductN1HatAux.normalizer_C5_le h d hlay,
    ⟨ProductN1HatAux.centralizer_tBar_eq_bar h d hlay, ?_,
      ProductN1HatAux.orderOf_tBar h d hlay⟩,
    ⟨ProductN1HatAux.kBar_equiv h d hlay, ProductN1HatAux.isSylowOf_tBar h d hlay⟩, ?_⟩
  · rw [← ProductN1HatAux.centralizer_tBar_eq_bar h d hlay]
    exact ProductN1HatAux.centralizer_tBar_eq_bar_NCV h d hlay
  · obtain ⟨h1, h2, h3, h4, h5⟩ := ProductN1HatAux.pBar_basic h d hp
    exact ⟨h1, h2, h3, h4, h5, ProductN1HatAux.pBar_eq_commutator h d hp⟩

end Statements

end CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
