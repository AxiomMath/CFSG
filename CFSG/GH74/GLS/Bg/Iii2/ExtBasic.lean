module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Pattern
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Core
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Bg.Iii2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.ABGLocalTools

section Counting

variable {G : Type} [Group G]

@[expose] noncomputable def rrNum (x : G) : ℕ := Set.ncard {K : Subgroup G | IsRigidRankOneComp x K}

@[expose] noncomputable def cLog (x : G) : ℕ :=
  (Nat.card ↥(centralizer ({x} : Set G))).factorization 2

open scoped Classical in
@[expose] noncomputable def rrMem (x : G) : ℕ := if x ∈ rigidProduct x then 1 else 0

theorem rrMem_eq_one_iff {x : G} : rrMem x = 1 ↔ x ∈ rigidProduct x := by
  unfold rrMem
  by_cases h : x ∈ rigidProduct x <;> simp [h]

theorem rrMem_le_one (x : G) : rrMem x ≤ 1 := by
  unfold rrMem
  split_ifs <;> simp

theorem pow_le_cLog [Finite G] {y : G} {S : Subgroup G} (hS : S ≤ centralizer ({y} : Set G)) {k : ℕ}
    (hk : Nat.card ↥S = 2 ^ k) : k ≤ cLog y := by
  have hdvd : 2 ^ k ∣ Nat.card ↥(centralizer ({y} : Set G)) := hk ▸ Subgroup.card_dvd_of_le hS
  exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hdvd

theorem exists_lex_max {α : Type*} [Finite α] {S : Set α} (hS : S.Nonempty) (f g h : α → ℕ) :
    ∃ a ∈ S, ∀ b ∈ S, f b ≤ f a ∧ (f b = f a → g b ≤ g a ∧ (g b = g a → h b ≤ h a)) := by
  obtain ⟨a, haS, hmax⟩ := Set.exists_max_image S
    (fun a => toLex (f a, toLex (g a, h a))) S.toFinite hS
  refine ⟨a, haS, fun b hb => ?_⟩
  have hb' := hmax b hb
  simp only [Prod.Lex.toLex_le_toLex] at hb'
  omega

end Counting

section TwoGroups

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_centralizer_self (x : G) : x ∈ centralizer ({x} : Set G) :=
  Subgroup.mem_centralizer_iff.2 fun h hh => by rw [Set.mem_singleton_iff.1 hh]

omit [Finite G] in
theorem exists_sylow_mem {x : G} (hx : orderOf x = 2) :
    ∃ T : Subgroup G, IsSylowOf 2 T (centralizer ({x} : Set G)) ∧ x ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxC : x ∈ centralizer ({x} : Set G) := mem_centralizer_self x
  have hA : IsPGroup 2 ↥(Subgroup.zpowers (⟨x, hxC⟩ : ↥(centralizer ({x} : Set G)))) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hx]
    norm_num
  obtain ⟨Q, hQ⟩ := hA.exists_le_sylow
  exact ⟨(Q : Subgroup ↥(centralizer ({x} : Set G))).map (centralizer ({x} : Set G)).subtype,
    ⟨Q, rfl⟩, ⟨⟨x, hxC⟩, hQ (Subgroup.mem_zpowers _), rfl⟩⟩

theorem exists_involution_of_isPGroup {A : Subgroup G} (hA : IsPGroup 2 ↥A) (hne : A ≠ ⊥) :
    ∃ a ∈ A, orderOf a = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hA
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hne ((Subgroup.eq_bot_iff_card A).2 (by simpa using hn))
  have hdvd : 2 ∣ Nat.card ↥A := by
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) 2 hdvd
  exact ⟨a, a.2, by rw [← ha, Subgroup.orderOf_coe]⟩

theorem exists_involution_normal {S P : Subgroup G} (hS : IsPGroup 2 ↥S) (hPS : P ≤ S)
    (hP : ∀ s ∈ S, ∀ p ∈ P, s * p * s⁻¹ ∈ P) (hne : P ≠ ⊥) :
    ∃ y ∈ P, orderOf y = 2 ∧ ∀ s ∈ S, s * y = y * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥S := hS.isNilpotent
  have hnorm : (P.subgroupOf S).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hPS]
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro p
    refine ⟨fun hp => hP s hs p hp, fun hp => ?_⟩
    have h := hP s⁻¹ (S.inv_mem hs) _ hp
    simpa [mul_assoc] using h
  have hne' : P.subgroupOf S ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro p hp
    have h1 : (⟨p, hPS hp⟩ : ↥S) ∈ P.subgroupOf S := hp
    rw [h, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.2 (congrArg Subtype.val h1)
  have hZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hne'
  have hA2 : IsPGroup 2 ↥((P.subgroupOf S ⊓ center ↥S).map S.subtype) :=
    hS.to_le (Subgroup.map_subtype_le _)
  have hAne : (P.subgroupOf S ⊓ center ↥S).map S.subtype ≠ ⊥ := by
    intro h
    apply hZ
    rw [eq_bot_iff]
    intro g hg
    have h1 : (g : G) ∈ (P.subgroupOf S ⊓ center ↥S).map S.subtype := ⟨g, hg, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.2 (Subtype.ext h1)
  obtain ⟨y, hyA, hy2⟩ := exists_involution_of_isPGroup hA2 hAne
  obtain ⟨g, ⟨hgP, hgZ⟩, rfl⟩ := hyA
  refine ⟨(g : G), hgP, hy2, fun s hs => ?_⟩
  exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hgZ ⟨s, hs⟩)

end TwoGroups

end CFSG.GH74.GLS.Bg.Iii2
