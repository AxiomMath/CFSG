module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallL34Out
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3FourE16Check
public import CFSG.LocalAnalysis.OddStandard.Seitz77L34Sylow

public section

namespace CFSG.OddStandard.Seitz77.L34

open Subgroup CFSG.ComponentClassification CFSG.Open
open scoped commutatorElement

theorem isSylowOf_map {G H : Type*} [Group G] [Finite G] [Group H] {P K : Subgroup G}
    (h : CFSG.ABGLocalTools.IsSylowOf 2 P K) (f : G →* H) :
    CFSG.ABGLocalTools.IsSylowOf 2 (P.map f) (K.map f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (f.subgroupMap_surjective K), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

section Action

open RankTwoSporadic

variable {G : Type*} [Group G] {B : Subgroup G}
  {ψ : normalizer (B : Set G) →* ↥PSL3Four.R}

theorem mem_sup_centralizer_iff (hψ : IsActionHom B (PSL3Four.S.subgroupOf PSL3Four.R) ψ)
    {x : G} (hx : x ∈ normalizer (B : Set G)) :
    x ∈ B ⊔ centralizer (B : Set G) ↔ ψ ⟨x, hx⟩ ∈ PSL3Four.S.subgroupOf PSL3Four.R := by
  constructor
  · intro hmem
    let L : Subgroup G :=
      ((PSL3Four.S.subgroupOf PSL3Four.R).comap ψ).map (normalizer (B : Set G)).subtype
    have hBL : B ≤ L := fun a ha => ⟨⟨a, le_normalizer ha⟩, hψ.map_mem a ha, rfl⟩
    have hCL : centralizer (B : Set G) ≤ L := fun c hc =>
      ⟨⟨c, Subgroup.centralizer_le_normalizer _ hc⟩, Subgroup.mem_comap.2 (by
        rw [(hψ.eq_one_iff ⟨c, Subgroup.centralizer_le_normalizer _ hc⟩).2 hc]
        exact one_mem _), rfl⟩
    obtain ⟨n, hn, hnx⟩ := sup_le hBL hCL hmem
    have : n = ⟨x, hx⟩ := Subtype.ext hnx
    rw [← this]
    exact hn
  · intro hS
    obtain ⟨a, ha, hax⟩ := hψ.exists_eq _ hS
    have h1 : ψ (⟨a, le_normalizer ha⟩⁻¹ * ⟨x, hx⟩) = 1 := by
      rw [map_mul, map_inv, hax, inv_mul_cancel]
    have h2 := (hψ.eq_one_iff _).1 h1
    have h3 : a⁻¹ * x ∈ centralizer (B : Set G) := h2
    have : x = a * (a⁻¹ * x) := by group
    rw [this]
    exact mul_mem_sup ha h3

end Action

end CFSG.OddStandard.Seitz77.L34

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.ComponentClassification CFSG.Open
open scoped commutatorElement

theorem le_sup_centralizer_of_sixteen_le_inf
    {G : Type*} [Group G] [Finite G] {B E : Subgroup G}
    (hB : commutator ↥B = ⊤) (e : ↥B ⧸ center ↥B ≃* ↥PSL3Four.S)
    (hEN : E ≤ normalizer (B : Set G)) (hE : IsElemAbelian 2 E)
    (hcard : 16 * Nat.card ↥(E ⊓ centralizer (B : Set G)) ≤ Nat.card E) :
    E ≤ B ⊔ centralizer (B : Set G) := by
  obtain ⟨ψ, hψ⟩ := RankTwoSporadic.exists_isActionHom RankTwoL3Four.HypII.l34AutModel hB e
  let f : ↥E →* ↥PSL3Four.R := ψ.comp (Subgroup.inclusion hEN)
  have hker : Nat.card f.ker ≤ Nat.card ↥(E ⊓ centralizer (B : Set G)) := by
    rw [← Subgroup.card_map_of_injective E.subtype_injective]
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z.2, (hψ.eq_one_iff _).1 (MonoidHom.mem_ker.1 hz)⟩
  have h1 := Subgroup.card_ker_mul_card_range f
  have hpos : 0 < Nat.card ↥(E ⊓ centralizer (B : Set G)) := Nat.card_pos
  have hV16 : 16 ≤ Nat.card f.range := by
    by_contra hlt
    push Not at hlt
    have h3 : Nat.card f.ker * Nat.card f.range ≤
        Nat.card ↥(E ⊓ centralizer (B : Set G)) * Nat.card f.range := Nat.mul_le_mul_right _ hker
    have h4 : Nat.card ↥(E ⊓ centralizer (B : Set G)) * Nat.card f.range <
        Nat.card ↥(E ⊓ centralizer (B : Set G)) * 16 := Nat.mul_lt_mul_of_pos_left hlt hpos
    omega
  have hVab : IsElemAbelian 2 f.range := by
    refine L34.isElemAbelian_of_forall ?_ ?_
    · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg f (Subtype.ext (L34.comm_of_isElemAbelian hE x.2 y.2))
    · rintro _ ⟨x, rfl⟩
      have hx2 : x ^ 2 = 1 := Subtype.ext (by simpa using hE.2 x x.2)
      rw [← map_pow, hx2, map_one]
  have hVS := RankTwoL3Four.HypII.l34_le_of_sixteen_le' hVab hV16
  intro x hx
  have hxN : x ∈ normalizer (B : Set G) := hEN hx
  exact (L34.mem_sup_centralizer_iff hψ hxN).2 (hVS ⟨⟨x, hx⟩, rfl⟩)

theorem two_part_outer_le {G : Type*} [Group G] [Finite G]
    {A : Subgroup G} (hA : commutator ↥A = ⊤) (e : ↥A ⧸ center ↥A ≃* ↥PSL3Four.S)
    {P : Subgroup G} (hP : IsPGroup 2 P) (hPN : P ≤ normalizer (A : Set G)) :
    (P ⊓ (A ⊔ centralizer (A : Set G))).relIndex P ≤ 4 ∧
      ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ A ⊔ centralizer (A : Set G) := by
  obtain ⟨ψ, hψ⟩ := RankTwoSporadic.exists_isActionHom RankTwoL3Four.HypII.l34AutModel hA e
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup ↥PSL3Four.R := PSL3Four.S.subgroupOf PSL3Four.R
  have : N.Normal := PSL3Four.S_normal
  have hN : Nat.card N = 20160 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe PSL3Four.S_le_R).toEquiv, PSL3Four.card_S]
  have hQ : Nat.card (PSL3Four.R ⧸ N) = 12 := by
    have h := card_eq_card_quotient_mul_card_subgroup N
    rw [PSL3Four.card_R, hN] at h
    omega
  let f : ↥P →* ↥PSL3Four.R ⧸ N :=
    (QuotientGroup.mk' N).comp (ψ.comp (Subgroup.inclusion hPN))
  have hfker : ∀ x : ↥P, f x = 1 ↔ (x : G) ∈ A ⊔ centralizer (A : Set G) := fun x => by
    rw [L34.mem_sup_centralizer_iff hψ (hPN x.2)]
    exact QuotientGroup.eq_one_iff _
  have hrange : IsPGroup 2 f.range := hP.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hcard2 : ∀ k : ℕ, Nat.card f.range = 2 ^ k → k ≤ 2 := fun k hk => by
    have hdvd : 2 ^ k ∣ 12 := hk ▸ hQ ▸ card_subgroup_dvd_card f.range
    by_contra hlt
    have h8 : 2 ^ 3 ∣ 12 := (pow_dvd_pow 2 (by omega)).trans hdvd
    norm_num at h8
  refine ⟨?_, fun x hx y hy => ?_⟩
  · rw [Subgroup.inf_relIndex_left]
    have hidx : ((A ⊔ centralizer (A : Set G)).subgroupOf P) = f.ker := by
      ext x
      rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, hfker]
    rw [Subgroup.relIndex, hidx, Subgroup.index_ker]
    obtain ⟨k, hk⟩ := hrange.exists_card_eq
    rw [hk]
    calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (hcard2 k hk)
      _ = 4 := by norm_num
  · have hcomm := CatFactsSmall.comm_of_isPGroup_two_of_card_twelve hQ f.range hrange
      (f ⟨x, hx⟩) ⟨_, rfl⟩ (f ⟨y, hy⟩) ⟨_, rfl⟩
    have h1 : f ⁅(⟨x, hx⟩ : ↥P), ⟨y, hy⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm
    exact (hfker _).1 h1

end CFSG.OddStandard.Seitz77
