module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76Hall32Exit

public section

namespace CFSG.ComponentClassification.Asc76X.Hall32

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76
open CFSG.ComponentClassification.Asc76X

variable {G : Type} [Group G]

structure Setup (S T : Subgroup G) (z : G) : Prop where
  sylow : IsSylowOf 2 S ⊤
  le : T ≤ S
  card : Nat.card T = 4
  sq : ∀ x ∈ T, x ^ 2 = 1
  comm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a
  wc : ∀ g : G, rightConjugate T g ≤ S → rightConjugate T g = T
  mem : z ∈ T
  ne_one : z ≠ 1
  central : ∀ s ∈ S, s * z = z * s

namespace Setup

variable {S T : Subgroup G} {z : G}

theorem le_normalizer (h : Setup S T z) : S ≤ normalizer (T : Set G) :=
  le_normalizer_of_weaklyClosed h.le h.wc

theorem inv_eq (h : Setup S T z) {x : G} (hx : x ∈ T) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_left ((pow_two x).symm.trans (h.sq x hx))

theorem z_mul_z (h : Setup S T z) : z * z = 1 := (pow_two z).symm.trans (h.sq z h.mem)

variable [Finite G]

theorem conj (h : Setup S T z) (k : G) :
    Setup (rightConjugate S k) (rightConjugate T k) (k⁻¹ * z * k) where
  sylow := by
    have htop : rightConjugate (⊤ : Subgroup G) k = ⊤ := by
      rw [rightConjugate_eq_self_iff, normalizer_eq_top_iff.mpr inferInstance]
      exact mem_top k
    have h1 := isSylowOf_rightConjugate h.sylow k
    rwa [htop] at h1
  le := fun x hx => by
    rw [mem_rightConjugate_iff] at hx ⊢
    exact h.le hx
  card := by rw [rightConjugate_card, h.card]
  sq := fun x hx => by
    rw [mem_rightConjugate_iff] at hx
    have e : x ^ 2 = k⁻¹ * (k * x * k⁻¹) ^ 2 * k := by
      rw [pow_two, pow_two]; group
    rw [e, h.sq _ hx, mul_one, inv_mul_cancel]
  comm := fun a ha b hb => by
    rw [mem_rightConjugate_iff] at ha hb
    have h1 := h.comm _ ha _ hb
    calc a * b = k⁻¹ * ((k * a * k⁻¹) * (k * b * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * b * k⁻¹) * (k * a * k⁻¹)) * k := by rw [h1]
      _ = b * a := by group
  wc := fun g hg => by
    rw [rightConjugate_mul] at hg ⊢
    have h1 : rightConjugate T (k * g * k⁻¹) ≤ S := by
      intro x hx
      rw [mem_rightConjugate_iff] at hx
      have h2 : k⁻¹ * x * k ∈ rightConjugate T (k * g) := by
        rw [mem_rightConjugate_iff]
        have e : k * g * (k⁻¹ * x * k) * (k * g)⁻¹ = k * g * k⁻¹ * x * (k * g * k⁻¹)⁻¹ := by
          group
        rw [e]
        exact hx
      have h3 := hg h2
      rw [mem_rightConjugate_iff] at h3
      have e : k * (k⁻¹ * x * k) * k⁻¹ = x := by group
      rwa [e] at h3
    have h4 := h.wc _ h1
    have h5 := congrArg (rightConjugate · k) h4
    simp only [rightConjugate_mul] at h5
    rw [show k * g * k⁻¹ * k = k * g by group] at h5
    exact h5
  mem := by
    rw [mem_rightConjugate_iff]
    have e : k * (k⁻¹ * z * k) * k⁻¹ = z := by group
    rw [e]
    exact h.mem
  ne_one := fun h1 => h.ne_one (by
    have e : z = k * (k⁻¹ * z * k) * k⁻¹ := by group
    rw [e, h1, mul_one, mul_inv_cancel])
  central := fun s hs => by
    rw [mem_rightConjugate_iff] at hs
    have h1 := h.central _ hs
    calc s * (k⁻¹ * z * k) = k⁻¹ * ((k * s * k⁻¹) * z) * k := by group
      _ = k⁻¹ * (z * (k * s * k⁻¹)) * k := by rw [h1]
      _ = k⁻¹ * z * k * s := by group

omit [Finite G] in
theorem le_centralizer (h : Setup S T z) : S ≤ centralizer ({z} : Set G) := fun s hs => by
  rw [mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  exact (h.central s hs).symm

theorem stronglyClosed (h : Setup S T z) :
    ∀ τ ∈ T, ∀ g ∈ centralizer ({z} : Set G), g⁻¹ * τ * g ∈ S → g⁻¹ * τ * g ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({z} : Set G) with hCdef
  have hSC : S ≤ C := h.le_centralizer
  have hTC : T ≤ C := h.le.trans hSC
  have hzC : z ∈ C := hTC h.mem
  have hSX : IsSylowOf 2 (S.subgroupOf C) ⊤ := by
    have h1 := (isSylowOf_iff_card.mp (isSylowOf_of_le hSC le_top h.sylow)).2
    refine isSylowOf_iff_card.mpr ⟨le_top, ?_⟩
    rw [Nat.card_congr (subgroupOfEquivOfLe hSC).toEquiv, card_top, h1]
  have hTSX : T.subgroupOf C ≤ S.subgroupOf C := fun x hx => h.le hx
  have hT4X : Nat.card (T.subgroupOf C) = 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hTC).toEquiv, h.card]
  have hTsqX : ∀ x ∈ T.subgroupOf C, x ^ 2 = 1 := fun x hx => Subtype.ext (by
    simpa using h.sq _ hx)
  have hconj : ∀ g : C, rightConjugate (T.subgroupOf C) g = (rightConjugate T g).subgroupOf C := by
    intro g
    ext x
    simp only [mem_rightConjugate_iff, mem_subgroupOf, coe_mul, coe_inv]
  have hwcX : ∀ g : C, rightConjugate (T.subgroupOf C) g ≤ S.subgroupOf C →
      rightConjugate (T.subgroupOf C) g = T.subgroupOf C := by
    intro g hg
    rw [hconj] at hg ⊢
    have hle : rightConjugate T g ≤ S := by
      intro x hx
      have hxC : x ∈ C := by
        rw [mem_rightConjugate_iff] at hx
        have e : x = (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) * g := by group
        rw [e]
        exact mul_mem (mul_mem (inv_mem g.2) (hTC hx)) g.2
      exact hg (show (⟨x, hxC⟩ : C) ∈ (rightConjugate T g).subgroupOf C from hx)
    rw [h.wc _ hle]
  have hzcX : ∀ g : C, g * ⟨z, hzC⟩ = ⟨z, hzC⟩ * g := fun g => Subtype.ext (by
    have h1 := mem_centralizer_iff.mp g.2 z (Set.mem_singleton z)
    simpa using h1.symm)
  have hz1X : (⟨z, hzC⟩ : C) ≠ 1 := fun h1 => h.ne_one (congrArg Subtype.val h1)
  have key := stronglyClosed_of_central hSX hTSX hT4X hTsqX hwcX
    (show (⟨z, hzC⟩ : C) ∈ T.subgroupOf C from h.mem) hz1X hzcX
  intro τ hτ g hg hgS
  have h1 := key ⟨τ, hTC hτ⟩ hτ ⟨g, hg⟩ (show _ ∈ S from hgS)
  exact h1

theorem mem_of_conj_mem_centralizer (h : Setup S T z) {τ g : G} (hτ : τ ∈ T)
    (hg : g⁻¹ * τ * g ∈ centralizer (T : Set G)) : g⁻¹ * τ * g ∈ T :=
  conj_mem_of_mem_centralizer h.sylow h.le h.comm h.wc hτ hg

omit [Finite G] in
theorem conj_eq_mul (h : Setup S T z) {s a : G} (hs : s ∈ S) (ha : a ∈ T) (has : a * s ≠ s * a) :
    s * a * s⁻¹ = a * z := by
  have ha1 : a ≠ 1 := fun h1 => has (by rw [h1, one_mul, mul_one])
  have haz : a ≠ z := fun h1 => has (by rw [h1]; exact (h.central s hs).symm)
  have hbT : s * a * s⁻¹ ∈ T := (mem_normalizer_iff.mp (h.le_normalizer hs) a).mp ha
  rcases eq_or_of_card_four h.card h.sq h.mem ha h.ne_one ha1 haz hbT with e | e | e | e
  · exact absurd (conj_eq_one_iff.mp e) ha1
  · refine absurd ?_ haz
    calc a = s⁻¹ * (s * a * s⁻¹) * s := by group
      _ = s⁻¹ * (s * z) := by rw [e, h.central s hs, mul_assoc]
      _ = z := by group
  · refine absurd ?_ has
    calc a * s = s * a * s⁻¹ * s := by rw [e]
      _ = s * a := by group
  · exact e

omit [Finite G] in
theorem eq_of_comm (h : Setup S T z) {s a : G} (hs : s ∈ S) (hsC : s ∉ centralizer (T : Set G))
    (ha : a ∈ T) (has : a * s = s * a) : a = 1 ∨ a = z := by
  by_contra hne
  push Not at hne
  exact hsC (mem_centralizer_of_comm h.card h.sq h.mem ha h.ne_one hne.1 hne.2
    (h.central s hs).symm has)

theorem exists_partner (h : Setup S T z) {n : G} (hvS : n⁻¹ * z * n ∈ S)
    (hvC : n⁻¹ * z * n ∉ centralizer (T : Set G)) :
    ∃ k : G, k⁻¹ * z * k = n⁻¹ * z * n ∧
      S ⊓ centralizer ({n⁻¹ * z * n} : Set G) ≤ rightConjugate S k ∧
      z ∈ rightConjugate S k ∧ z ∉ centralizer (rightConjugate T k : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set v := n⁻¹ * z * n with hvdef
  obtain ⟨k, hk, hle⟩ := exists_conj_centralizer_le h.sylow h.central (g := n)
  have hzk : z ∈ rightConjugate S k := by
    refine hle (Subgroup.mem_inf.mpr ⟨h.le h.mem, ?_⟩)
    rw [mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact h.central v hvS
  refine ⟨k, hk, hle, hzk, fun hzC => ?_⟩
  set H := centralizer ({z} : Set G) with hHdef
  have hTkH : rightConjugate T k ≤ H := fun x hx => by
    rw [hHdef, mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact (mem_centralizer_iff.mp hzC x hx).symm
  have hS2 : IsPGroup 2 S := IsPGroup.of_card (isSylowOf_iff_card.mp h.sylow).2
  have hSH : IsSylowOf 2 S H := isSylowOf_of_le h.le_centralizer le_top h.sylow
  obtain ⟨Q, hQ, hTQ⟩ := exists_isSylowOf_le hTkH (isPGroup_rightConjugate (hS2.to_le h.le) k)
  obtain ⟨c, hc, hQc⟩ := exists_conj_of_isSylowOf hSH hQ
  have hTc : rightConjugate T (k * c⁻¹) = T := by
    refine h.wc _ fun x hx => ?_
    rw [mem_rightConjugate_iff] at hx
    have h1 : c⁻¹ * x * c ∈ rightConjugate T k := by
      rw [mem_rightConjugate_iff]
      have e : k * (c⁻¹ * x * c) * k⁻¹ = k * c⁻¹ * x * (k * c⁻¹)⁻¹ := by group
      rw [e]
      exact hx
    have h2 := hTQ h1
    rw [hQc, mem_rightConjugate_iff] at h2
    have e : c * (c⁻¹ * x * c) * c⁻¹ = x := by group
    rwa [e] at h2
  have hTkc : rightConjugate T k = rightConjugate T c := by
    have h1 := congrArg (rightConjugate · c) hTc
    simp only [rightConjugate_mul, inv_mul_cancel_right] at h1
    exact h1
  have hvTk : v ∈ rightConjugate T k := by
    rw [mem_rightConjugate_iff, hvdef, ← hk]
    have e : k * (k⁻¹ * z * k) * k⁻¹ = z := by group
    rw [e]
    exact h.mem
  rw [hTkc, mem_rightConjugate_iff] at hvTk
  have h1 := h.stronglyClosed _ hvTk c hc (by
    have e : c⁻¹ * (c * v * c⁻¹) * c = v := by group
    rw [e]
    exact hvS)
  have e : c⁻¹ * (c * v * c⁻¹) * c = v := by group
  rw [e] at h1
  exact hvC (mem_centralizer_iff.mpr fun y hy => h.comm y hy v h1)

end Setup

end CFSG.ComponentClassification.Asc76X.Hall32
