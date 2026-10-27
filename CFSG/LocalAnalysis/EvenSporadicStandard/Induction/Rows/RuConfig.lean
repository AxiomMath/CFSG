module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuLocal
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Contra

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.RuStd
open scoped commutatorElement

section Config

variable {H : Type} [Group H] [Finite H]

theorem ruConfig_of_balance (hsimple : IsSimpleGroup H) (hna : ∃ a b : H, a * b ≠ b * a)
    {L : Subgroup H} {t : H} (hL : IsSporadic ↥L .Ru) (ht2 : orderOf t = 2)
    (htL : t ∈ centralizer (L : Set H)) (hbal : centralizer ({t} : Set H) = L ⊔ zpowers t) :
    Config H L t where
  simple := hsimple
  nonabelian := hna
  z_sq := sq_eq_one_of_orderOf_two ht2
  z_ne_one := ne_one_of_orderOf_eq_two ht2
  comm := fun l hl => mem_centralizer_iff.1 htL l hl
  z_not_mem := by
    intro htL'
    have hZ : center ↥L = ⊥ := center_eq_bot_of_isSporadic_ru hL
    have hz : (⟨t, htL'⟩ : ↥L) ∈ center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (mem_centralizer_iff.1 htL g g.2)
    rw [hZ, Subgroup.mem_bot] at hz
    have h1 : t = 1 := congrArg Subtype.val hz
    have := ht2
    rw [h1, orderOf_one] at this
    omega
  centralizer_eq := hbal

end Config

section KNormal

variable {H : Type} [Group H]

theorem map_derivedCentralizer_eq {L : Subgroup H} (v : ↥L) :
    (derivedCentralizer v).map L.subtype =
      ⁅L ⊓ centralizer ({(v : H)} : Set H), L ⊓ centralizer ({(v : H)} : Set H)⁆ := by
  unfold derivedCentralizer
  rw [Subgroup.map_map, _root_.commutator_def, Subgroup.map_commutator]
  have h2 : (⊤ : Subgroup ↥(centralizer ({v} : Set ↥L))).map
      (L.subtype.comp (centralizer ({v} : Set ↥L)).subtype) =
        L ⊓ centralizer ({(v : H)} : Set H) := by
    rw [← MonoidHom.range_eq_map, MonoidHom.range_comp, Subgroup.range_subtype]
    exact map_centralizer_subtype_eq L v
  rw [h2]

variable [Finite H]

theorem ruKNormal_of_pair (hf : RuLocalFacts) {L K : Subgroup H} {u : H}
    (hL : IsSporadic ↥L .Ru) (hQ : RuPair H L K u)
    (hK : ∀ d ∈ centralizer ({u} : Set H), ∀ k ∈ K, d * k * d⁻¹ ∈ K) : KNormal L := by
  intro u₀ hu₀2 hu₀c d hd k hk
  have hQ' := hQ
  obtain ⟨huL, hu2, hKL, hKu, hcard⟩ := hQ
  set u' : ↥L := ⟨u, huL⟩ with hu'
  have hu'2 : orderOf u' = 2 := by rw [Subgroup.orderOf_mk]; exact hu2
  have hF := ruFacts_of_isSporadic hL
  have hu'c : Nat.card ↥(centralizer ({u'} : Set ↥L)) = 116480 := by
    rw [card_centralizer_subtype L u']
    exact card_centralizer_of_ruPair hL hQ'
  obtain ⟨g, hg⟩ := isConj_iff.1 (hF.isConj_B u' u₀ hu'2 hu₀2 hu'c hu₀c)
  have hgu : (g : H) * u * (g : H)⁻¹ = (u₀ : H) := congrArg Subtype.val hg
  have hKder := ruPair_eq_derived hf hL hQ'
  set A : Subgroup H := L ⊓ centralizer ({u} : Set H) with hA
  have hA₀ : L ⊓ centralizer ({(u₀ : H)} : Set H) = A.map (conjHom (g : H)) := by
    ext x
    constructor
    · rintro ⟨hxL, hxc⟩
      have hxc' : x * (u₀ : H) = (u₀ : H) * x := mem_centralizer_singleton_iff.1 hxc
      refine ⟨(g : H)⁻¹ * x * (g : H), ⟨?_, ?_⟩, ?_⟩
      · exact L.mul_mem (L.mul_mem (L.inv_mem g.2) hxL) g.2
      · refine mem_centralizer_singleton_iff.2 ?_
        rw [← hgu] at hxc'
        calc (g : H)⁻¹ * x * (g : H) * u = (g : H)⁻¹ * (x * ((g : H) * u * (g : H)⁻¹)) * g := by
              group
          _ = (g : H)⁻¹ * (((g : H) * u * (g : H)⁻¹) * x) * g := by rw [hxc']
          _ = u * ((g : H)⁻¹ * x * (g : H)) := by group
      · show (g : H) * ((g : H)⁻¹ * x * (g : H)) * (g : H)⁻¹ = x
        group
    · rintro ⟨y, ⟨hyL, hyc⟩, rfl⟩
      have hyc' : y * u = u * y := mem_centralizer_singleton_iff.1 hyc
      refine ⟨?_, mem_centralizer_singleton_iff.2 ?_⟩
      · exact L.mul_mem (L.mul_mem g.2 hyL) (L.inv_mem g.2)
      · show (g : H) * y * (g : H)⁻¹ * (u₀ : H) = (u₀ : H) * ((g : H) * y * (g : H)⁻¹)
        rw [← hgu]
        calc (g : H) * y * (g : H)⁻¹ * ((g : H) * u * (g : H)⁻¹) =
            (g : H) * (y * u) * (g : H)⁻¹ := by group
          _ = (g : H) * (u * y) * (g : H)⁻¹ := by rw [hyc']
          _ = (g : H) * u * (g : H)⁻¹ * ((g : H) * y * (g : H)⁻¹) := by group
  rw [map_derivedCentralizer_eq] at hk ⊢
  rw [hA₀, ← Subgroup.map_commutator] at hk ⊢
  obtain ⟨k₁, hk₁, rfl⟩ := hk
  have hd₁ : (g : H)⁻¹ * d * (g : H) ∈ centralizer ({u} : Set H) := by
    have hd' : d * (u₀ : H) = (u₀ : H) * d := mem_centralizer_singleton_iff.1 hd
    rw [← hgu] at hd'
    refine mem_centralizer_singleton_iff.2 ?_
    calc (g : H)⁻¹ * d * (g : H) * u = (g : H)⁻¹ * (d * ((g : H) * u * (g : H)⁻¹)) * g := by
          group
      _ = (g : H)⁻¹ * (((g : H) * u * (g : H)⁻¹) * d) * g := by rw [hd']
      _ = u * ((g : H)⁻¹ * d * (g : H)) := by group
  have hk₁K : k₁ ∈ K := by rw [hKder]; exact hk₁
  have h1 := hK _ hd₁ k₁ hk₁K
  rw [hKder] at h1
  refine ⟨(g : H)⁻¹ * d * (g : H) * k₁ * ((g : H)⁻¹ * d * (g : H))⁻¹, h1, ?_⟩
  show (g : H) * ((g : H)⁻¹ * d * (g : H) * k₁ * ((g : H)⁻¹ * d * (g : H))⁻¹) * (g : H)⁻¹ =
    d * ((g : H) * k₁ * (g : H)⁻¹) * d⁻¹
  group

theorem mem_of_hyp35 {K : Subgroup H} {u : H} (h : K = componentProduct K u) :
    ∀ d ∈ centralizer ({u} : Set H), ∀ k ∈ K, d * k * d⁻¹ ∈ K := by
  intro d hd k hk
  have hug : d * u * d⁻¹ = u := by
    have := mem_centralizer_singleton_iff.1 hd
    rw [this]
    group
  have h1 := componentProduct_conj K u d
  rw [hug, ← h] at h1
  have : d * k * d⁻¹ ∈ K.map (conjHom d) := ⟨k, hk, rfl⟩
  rwa [← h1] at this

theorem ru_false_of_simple (hf : RuLocalFacts) (hsimple : IsSimpleGroup H)
    (hna : ∃ a b : H, a * b ≠ b * a) {L K : Subgroup H} {t u : H} (hL : IsSporadic ↥L .Ru)
    (hQ : RuPair H L K u) (ht2 : orderOf t = 2) (htL : t ∈ centralizer (L : Set H))
    (hbal : centralizer ({t} : Set H) = L ⊔ zpowers t)
    (hK : ∀ d ∈ centralizer ({u} : Set H), ∀ k ∈ K, d * k * d⁻¹ ∈ K) : False :=
  (ruConfig_of_balance hsimple hna hL ht2 htL hbal).false_of_normal (ruFacts_of_isSporadic hL)
    (ruKNormal_of_pair hf hL hQ hK)

end KNormal

section Reduction

variable {H : Type} [Group H] [Finite H]

theorem le_of_perfect_of_index_le_four {N P : Subgroup H} (hn : N.Normal) (hi : N.index ≤ 4)
    (hp : _root_.commutator ↥P = ⊤) : P ≤ N := by
  refine (le_commutator_of_isPerfect hp).trans ?_
  have hc : IsMulCommutative (H ⧸ N) :=
    isMulCommutative_of_card_le_four (by rw [← Subgroup.index_eq_card]; exact hi)
  rw [_root_.commutator_def, Subgroup.commutator_le]
  intro a _ b _
  have hmk : (QuotientGroup.mk' N) ⁅a, b⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hc.is_comm.comm _ _)
  exact (QuotientGroup.eq_one_iff _).1 hmk

theorem ruPair_subgroupOf {N L K : Subgroup H} {u : H} (hLN : L ≤ N) (hQ : RuPair H L K u) :
    RuPair ↥N (L.subgroupOf N) (K.subgroupOf N) ⟨u, hLN hQ.1⟩ := by
  obtain ⟨huL, hu2, hKL, hKu, hcard⟩ := hQ
  refine ⟨mem_subgroupOf.2 huL, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_mk]; exact hu2
  · intro k hk
    exact mem_subgroupOf.2 (hKL (mem_subgroupOf.1 hk))
  · intro k hk
    exact Subtype.ext (hKu k (mem_subgroupOf.1 hk))
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hKL.trans hLN)).toEquiv]
    exact hcard

theorem isSporadic_subgroupOf {N L : Subgroup H} (hLN : L ≤ N) {s : TauCeti.SporadicName}
    (hL : IsSporadic ↥L s) : IsSporadic ↥(L.subgroupOf N) s := by
  obtain ⟨e⟩ := hL
  exact ⟨(Subgroup.subgroupOfEquivOfLe hLN).trans e⟩

theorem centralizer_eq_sup_subgroupOf {N L : Subgroup H} {t : H} (hLN : L ≤ N) (htN : t ∈ N)
    (hbal : centralizer ({t} : Set H) = L ⊔ zpowers t) :
    centralizer ({(⟨t, htN⟩ : ↥N)} : Set ↥N) = L.subgroupOf N ⊔ zpowers (⟨t, htN⟩ : ↥N) := by
  have hz : (zpowers t).subgroupOf N = zpowers (⟨t, htN⟩ : ↥N) := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (mem_subgroupOf.1 hx)
      exact mem_zpowers_iff.2 ⟨k, Subtype.ext (by simpa using hk)⟩
    · intro hx
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hx
      refine mem_subgroupOf.2 (mem_zpowers_iff.2 ⟨k, ?_⟩)
      have := congrArg Subtype.val hk
      simpa using this
  rw [← hz, ← Subgroup.subgroupOf_sup hLN (zpowers_le.2 htN)]
  ext x
  rw [mem_subgroupOf, ← hbal, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro hx
    exact congrArg Subtype.val hx
  · intro hx
    exact Subtype.ext hx

theorem ru_false_of_fStar (hf : RuLocalFacts) {N L K : Subgroup H} {t u : H}
    (hsimple : IsSimpleGroup ↥N) (hna : ∃ a b : ↥N, a * b ≠ b * a) (hLN : L ≤ N) (htN : t ∈ N)
    (hL : IsSporadic ↥L .Ru) (hQ : RuPair H L K u) (ht2 : orderOf t = 2)
    (htL : t ∈ centralizer (L : Set H)) (hbal : centralizer ({t} : Set H) = L ⊔ zpowers t)
    (hK : ∀ d ∈ centralizer ({u} : Set H), ∀ k ∈ K, d * k * d⁻¹ ∈ K) : False := by
  refine ru_false_of_simple (H := ↥N) (L := L.subgroupOf N) (K := K.subgroupOf N)
    (t := ⟨t, htN⟩) (u := ⟨u, hLN hQ.1⟩) hf hsimple hna (isSporadic_subgroupOf hLN hL)
    (ruPair_subgroupOf hLN hQ) ?_ ?_ (centralizer_eq_sup_subgroupOf hLN htN hbal) ?_
  · rw [Subgroup.orderOf_mk]; exact ht2
  · exact mem_centralizer_iff.2 fun l hl =>
      Subtype.ext (mem_centralizer_iff.1 htL l (mem_subgroupOf.1 hl))
  · intro d hd k hk
    rw [mem_subgroupOf] at hk ⊢
    have hd' : (d : H) ∈ centralizer ({u} : Set H) :=
      mem_centralizer_singleton_iff.2 (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hd))
    exact hK (d : H) hd' k hk

end Reduction

end CFSG.EvenSporadicStandard.Induction
