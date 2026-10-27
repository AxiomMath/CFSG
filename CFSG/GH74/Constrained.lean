module

public import CFSG.GH74.Defs
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.LocalCores.Layer
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
import CFSG.LocalAnalysis.ComponentInitial.ParabolicLocalCharacteristicTransfer

public section

namespace CFSG.GH74

open Subgroup

theorem pPrimeCore_quotient_pPrimeCore_eq_bot (Y : Type*) [Group Y] [Finite Y] (p : ℕ)
    [Fact p.Prime] : pPrimeCore p (Y ⧸ pPrimeCore p Y) = ⊥ :=
  _root_.CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot p

theorem isTwoConstrained_of_layer_eq_bot {Y : Type*} [Group Y] [Finite Y]
    (h : layer (Y ⧸ pPrimeCore 2 Y) = ⊥) : IsTwoConstrained Y :=
  isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot _ 2
    (pPrimeCore_quotient_pPrimeCore_eq_bot Y 2) h

theorem layer_eq_bot_of_isTwoConstrained {Y : Type*} [Group Y] [Finite Y]
    (h : IsTwoConstrained Y) : layer (Y ⧸ pPrimeCore 2 Y) = ⊥ :=
  layer_eq_bot_of_isCharacteristicP _ 2 h

theorem isTwoConstrained_iff_layer_eq_bot {Y : Type*} [Group Y] [Finite Y] :
    IsTwoConstrained Y ↔ layer (Y ⧸ pPrimeCore 2 Y) = ⊥ :=
  ⟨layer_eq_bot_of_isTwoConstrained, isTwoConstrained_of_layer_eq_bot⟩

theorem isTwoConstrained_of_layerBar_eq_bot {G : Type*} [Group G] [Finite G] (x : G)
    (h : layerBar x = ⊥) : IsTwoConstrained (centralizer ({x} : Set G)) :=
  isTwoConstrained_of_layer_eq_bot h

theorem isTwoConstrained_centralizer_iff_layerBar_eq_bot {G : Type*} [Group G] [Finite G]
    (x : G) : IsTwoConstrained (centralizer ({x} : Set G)) ↔ layerBar x = ⊥ :=
  isTwoConstrained_iff_layer_eq_bot

theorem layer_eq_bot_of_isSolvable_layer {X : Type*} [Group X]
    (h : Group.IsSolvable (layer X)) : layer X = ⊥ := by
  by_contra hne
  have : Nontrivial (layer X) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  have : Group.IsPerfect (layer X) := LocalCores.layer_isPerfect
  exact Group.IsPerfect.not_isSolvable (layer X) h

theorem isTwoConstrained_of_isSolvable {Y : Type*} [Group Y] [Finite Y] [Group.IsSolvable Y] :
    IsTwoConstrained Y :=
  isTwoConstrained_of_layer_eq_bot (layer_eq_bot_of_isSolvable_layer inferInstance)

theorem isTwoConstrained_of_mulEquiv {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsTwoConstrained Y) : IsTwoConstrained Y' :=
  LocalAnalysis.ComponentInitial.isCharacteristicP_of_mulEquiv
    (QuotientGroup.congr (pPrimeCore 2 Y) (pPrimeCore 2 Y') e (pPrimeCore_map_iso 2 e)) h

theorem centralizer_singleton_quotient_eq_map {N : Type*} [Group N] [Finite N] (p : ℕ)
    [Fact p.Prime] (M : Subgroup N) [M.Normal] (hM : Nat.Coprime p (Nat.card M)) {t : N}
    (ht : ∃ k : ℕ, orderOf t = p ^ k) :
    centralizer ({QuotientGroup.mk' M t} : Set (N ⧸ M)) =
      (centralizer ({t} : Set N)).map (QuotientGroup.mk' M) := by
  obtain ⟨k, hk⟩ := ht
  have : Fact (IsPGroup p (zpowers t)) :=
    ⟨IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])⟩
  have h := _root_.CFSG.centralizer_map_quotient_eq_map_centralizer p (zpowers t) M inferInstance hM
  simp only at h
  rwa [MonoidHom.map_zpowers, zpowers_eq_closure, zpowers_eq_closure, centralizer_closure,
    centralizer_closure] at h

theorem centralizer_singleton_pPrimeCore_quotient_eq_map {N : Type*} [Group N] [Finite N]
    (p : ℕ) [Fact p.Prime] {t : N} (ht : ∃ k : ℕ, orderOf t = p ^ k) :
    centralizer ({QuotientGroup.mk' (pPrimeCore p N) t} : Set (N ⧸ pPrimeCore p N)) =
      (centralizer ({t} : Set N)).map (QuotientGroup.mk' (pPrimeCore p N)) :=
  centralizer_singleton_quotient_eq_map p (pPrimeCore p N) pPrimeCore_coprime_card ht

theorem centralizer_involution_pPrimeCore_quotient_eq_map {N : Type*} [Group N] [Finite N] {t : N}
    (ht : orderOf t = 2) :
    centralizer ({QuotientGroup.mk' (pPrimeCore 2 N) t} : Set (N ⧸ pPrimeCore 2 N)) =
      (centralizer ({t} : Set N)).map (QuotientGroup.mk' (pPrimeCore 2 N)) :=
  centralizer_singleton_pPrimeCore_quotient_eq_map 2 ⟨1, by rw [ht, pow_one]⟩

theorem layer_quotient_le_centralizer_map {N : Type*} [Group N] [Finite N] (T : Subgroup N)
    [T.Normal] (hT : IsPGroup 2 T) :
    layer (N ⧸ pPrimeCore 2 N) ≤
      centralizer ((T.map (QuotientGroup.mk' (pPrimeCore 2 N)) : Subgroup (N ⧸ pPrimeCore 2 N)) :
        Set (N ⧸ pPrimeCore 2 N)) := by
  have hn : (T.map (QuotientGroup.mk' (pPrimeCore 2 N))).Normal :=
    Subgroup.Normal.map ‹T.Normal› _ (QuotientGroup.mk'_surjective _)
  have hp : IsPGroup 2 (T.map (QuotientGroup.mk' (pPrimeCore 2 N))) := hT.map _
  have : Group.IsNilpotent (T.map (QuotientGroup.mk' (pPrimeCore 2 N))) := hp.isNilpotent
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (LocalCores.component_solvable_centralizer inferInstance hn.isSubnormal).2

theorem layer_quotient_eq_bot_of_isSolvable_centralizer {N : Type*} [Group N] [Finite N]
    (T : Subgroup N) [T.Normal] (hT : IsPGroup 2 T) {t : N} (htT : t ∈ T)
    (hsolv : Group.IsSolvable (centralizer ({t} : Set N))) :
    layer (N ⧸ pPrimeCore 2 N) = ⊥ := by
  set π := QuotientGroup.mk' (pPrimeCore 2 N) with hπ
  have hle₁ : layer (N ⧸ pPrimeCore 2 N) ≤ centralizer ({π t} : Set (N ⧸ pPrimeCore 2 N)) :=
    (layer_quotient_le_centralizer_map T hT).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_map_of_mem π htT)))
  have hord : ∃ k : ℕ, orderOf t = 2 ^ k := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hT ⟨t, htT⟩
    exact ⟨k, by simpa using hk⟩
  have hle₂ : layer (N ⧸ pPrimeCore 2 N) ≤ (centralizer ({t} : Set N)).map π := by
    rw [← centralizer_singleton_pPrimeCore_quotient_eq_map 2 hord]
    exact hle₁
  have : Group.IsSolvable ((centralizer ({t} : Set N)).map π) :=
    Group.isSolvable_of_surjective (π.subgroupMap_surjective _)
  exact layer_eq_bot_of_isSolvable_layer
    (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle₂))

theorem isTwoConstrained_of_normal_pGroup_of_isSolvable_centralizer {N : Type*} [Group N]
    [Finite N] (T : Subgroup N) [T.Normal] (hT : IsPGroup 2 T) {t : N} (htT : t ∈ T)
    (hsolv : Group.IsSolvable (centralizer ({t} : Set N))) : IsTwoConstrained N :=
  isTwoConstrained_of_layer_eq_bot
    (layer_quotient_eq_bot_of_isSolvable_centralizer T hT htT hsolv)

theorem exists_orderOf_eq_two_of_isPGroup {G : Type*} [Group G] [Finite G] (T : Subgroup G)
    (hT : IsPGroup 2 T) (hne : T ≠ ⊥) : ∃ t ∈ T, orderOf t = 2 := by
  have h2 : 2 ∣ Nat.card T := by
    rcases hT.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hne
    · exact h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := T) 2 h2
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

theorem isSolvable_centralizer_of_isSolvable_centralizer_coe {G : Type*} [Group G]
    (H : Subgroup G) (t : H) (h : Group.IsSolvable (centralizer ({(t : G)} : Set G))) :
    Group.IsSolvable (centralizer ({t} : Set H)) := by
  let f : centralizer ({t} : Set H) →* centralizer ({(t : G)} : Set G) :=
    ((H.subtype.comp (centralizer ({t} : Set H)).subtype)).codRestrict
      (centralizer ({(t : G)} : Set G)) (by
        intro x
        rw [mem_centralizer_singleton_iff]
        have := mem_centralizer_singleton_iff.mp x.2
        exact congrArg Subtype.val this)
  refine Group.isSolvable_of_isSolvable_injective (f := f) ?_
  intro x y hxy
  have h1 : (f x).1 = (f y).1 := congrArg Subtype.val hxy
  exact Subtype.ext (Subtype.ext h1)

theorem isTwoConstrained_of_isPLocal {G : Type*} [Group G] [Finite G]
    (hsolv : ∀ x : G, orderOf x = 2 → Group.IsSolvable (centralizer ({x} : Set G)))
    (H : Subgroup G) (hH : IsPLocal 2 H) : IsTwoConstrained H := by
  obtain ⟨T, hT0, hT2, hHT⟩ := hH
  have hTH : T ≤ H := hHT ▸ le_normalizer
  obtain ⟨t, htT, ht2⟩ := exists_orderOf_eq_two_of_isPGroup T hT2 hT0
  have : (T.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hTH).mpr hHT.le
  exact isTwoConstrained_of_normal_pGroup_of_isSolvable_centralizer (T.subgroupOf H)
    (hT2.of_equiv (subgroupOfEquivOfLe hTH).symm) (t := (⟨t, hTH htT⟩ : H))
    (mem_subgroupOf.mpr htT)
    (isSolvable_centralizer_of_isSolvable_centralizer_coe H ⟨t, hTH htT⟩ (hsolv t ht2))

end CFSG.GH74
