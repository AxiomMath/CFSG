module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011CFX
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Leaves

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.CFT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2

section Basic

theorem center_trivial_of_simple {K : Type} [Group K] (hs : IsSimpleGroup K)
    (hnab : ∃ a b : K, a * b ≠ b * a) : ∀ k : K, (∀ g : K, g * k = k * g) → k = 1 := by
  intro k hk
  by_contra hk1
  have := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
  · have hmem : k ∈ Subgroup.center K := Subgroup.mem_center_iff.2 hk
    rw [h, Subgroup.mem_bot] at hmem
    exact hk1 hmem
  · obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center K := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.1 ha b).symm

theorem isG2Sp4L4U4_of_concl {J : Type} [Group J] {q : ℕ} (h : Ivk93Concl J q) :
    IsG2Sp4L4U4_fixed J q := by
  rcases h with hPsp | ⟨p, f, hp, hp2, hf, hpf, h8, hm⟩ | ⟨p, f, hp, hp2, hf, hpf, h8, hm⟩ |
    ⟨p, f, hp, hp2, hf, hpf, hm⟩
  · exact Or.inr (Or.inl hPsp)
  · refine Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩))
    · intro hq
      apply h8
      unfold Int.ModEq at hq
      omega
    · have := CFSG.GH74.GLS.Stage2.Final.isLnEps_psl_of_lieModel hm
      rwa [hpf] at this
  · refine Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))
    · intro hq
      apply h8
      unfold Int.ModEq at hq
      omega
    · have := CFSG.GH74.GLS.Stage2.Final.isLnEps_psu_of_lieModel hm
      rwa [hpf] at this
  · exact Or.inl ⟨p, f, hp, hpf.symm, hm⟩

theorem layer_map_mulEquiv' {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (CFSG.layer A).map e.toMonoidHom = CFSG.layer B := by
  have hbij := (CFSG.LocalCores.component_isomorphism e).2
  change MulEquiv.mapSubgroup e (sSup {K : Subgroup A | CFSG.IsComponent K}) = CFSG.layer B
  rw [OrderIso.map_sSup, ← sSup_image]
  exact congrArg sSup hbij.image_eq

end Basic

section Transport

variable {K : Type} [Group K] (X : Subgroup (MulAut K)) (hX : ∀ k : K, MulAut.conj k ∈ X)
  (hZ : ∀ k : K, (∀ g : K, g * k = k * g) → k = 1)

include hZ in
theorem map_innIn_le (x : K) {L : Subgroup K} (hL : L ≤ centralizer ({x} : Set K)) :
    L.map (innIn X hX) ≤ centralizer ({innIn X hX x} : Set ↥X) ⊓ innRange X hX := by
  rintro _ ⟨l, hl, rfl⟩
  refine ⟨?_, innIn_mem_innRange X hX l⟩
  show innIn X hX l ∈ centralizer ({innIn X hX x} : Set ↥X)
  rw [mem_centralizer_innIn X hX hZ]
  have := Subgroup.mem_centralizer_singleton_iff.1 (hL hl)
  show MulAut.conj l x = x
  rw [MulAut.conj_apply]
  calc l * x * l⁻¹ = (x * l) * l⁻¹ := by rw [this]
    _ = x := by group

include hZ in
theorem map_subgroupOf_centEquiv (x : K) {L : Subgroup K} (hL : L ≤ centralizer ({x} : Set K)) :
    (L.subgroupOf (centralizer ({x} : Set K))).map (centEquiv X hX hZ x).toMonoidHom =
      (L.map (innIn X hX)).subgroupOf (centralizer ({innIn X hX x} : Set ↥X) ⊓ innRange X hX) := by
  ext y
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact ⟨(c : K), hc, rfl⟩
  · intro hy
    rw [Subgroup.mem_subgroupOf] at hy
    obtain ⟨l, hl, hly⟩ := hy
    refine ⟨⟨l, hL hl⟩, ?_, ?_⟩
    · exact hl
    · apply Subtype.ext
      exact hly

include hZ in
theorem isComponent_map_innIn (x : K) {L : Subgroup K} (hL : L ≤ centralizer ({x} : Set K))
    (hc : CFSG.IsComponent (L.subgroupOf (centralizer ({x} : Set K)))) :
    CFSG.IsComponent ((L.map (innIn X hX)).subgroupOf
      (centralizer ({innIn X hX x} : Set ↥X) ⊓ innRange X hX)) := by
  rw [← map_subgroupOf_centEquiv X hX hZ x hL]
  exact CFSG.LocalCores.isComponent_map_mulEquiv _ hc

theorem innIn_mem_normalizer_map {L : Subgroup K} {k : K} (hk : k ∈ normalizer (L : Set K)) :
    innIn X hX k ∈ normalizer (((L.map (innIn X hX) : Subgroup ↥X)) : Set ↥X) := by
  rw [Subgroup.mem_normalizer_iff] at hk ⊢
  intro y
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨k * l * k⁻¹, (hk l).1 hl, ?_⟩
    simp
  · rintro ⟨l, hl, hly⟩
    refine ⟨k⁻¹ * l * k, ?_, ?_⟩
    · have := (hk (k⁻¹ * l * k)).2
      rw [show k * (k⁻¹ * l * k) * k⁻¹ = l by group] at this
      exact this hl
    · rw [map_mul, map_mul, map_inv, hly]
      group

include hZ in
theorem val2_transport (x : K)
    (h : (Nat.card ↥(centralizer ({innIn X hX x} : Set ↥X) ⊓ innRange X hX) /
        Nat.card ↥((layer ↥(centralizer ({innIn X hX x} : Set ↥X) ⊓ innRange X hX)).map
          (centralizer ({innIn X hX x} : Set ↥X) ⊓ innRange X hX).subtype)).factorization 2 = 2) :
    (Nat.card ↥(centralizer ({x} : Set K)) / Nat.card ↥(Ez x)).factorization 2 = 2 := by
  set D := centralizer ({innIn X hX x} : Set ↥X) ⊓ innRange X hX with hD
  set C := centralizer ({x} : Set K) with hC
  set e := centEquiv X hX hZ x with he
  have h1 : Nat.card ↥D = Nat.card ↥C := (Nat.card_congr e.toEquiv).symm
  have h2 : Nat.card ↥((layer ↥D).map D.subtype) = Nat.card ↥(layer ↥C) := by
    rw [Subgroup.card_map_of_injective D.subtype_injective,
      ← layer_map_mulEquiv' e, Subgroup.card_map_of_injective e.injective]
  have h3 : Nat.card ↥(Ez x) = Nat.card ↥(layer ↥C) := by
    unfold Ez
    exact Subgroup.card_map_of_injective C.subtype_injective
  rw [h1, h2] at h
  rw [h3]
  exact h

end Transport

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.CFT
