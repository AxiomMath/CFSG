module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerConj

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.B6
open scoped commutatorElement

universe v

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

theorem iSup_comm_of_pairwise {X : Type*} [Group X] {ι : Type*} (L : ι → Subgroup X)
    (hii : ∀ i, ∀ x ∈ L i, ∀ y ∈ L i, x * y = y * x)
    (hij : ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ y ∈ L j, x * y = y * x) :
    ∀ x ∈ (⨆ i, L i : Subgroup X), ∀ y ∈ (⨆ i, L i : Subgroup X), x * y = y * x := by
  have step : ∀ i, ∀ x ∈ L i, ∀ y ∈ (⨆ i, L i : Subgroup X), x * y = y * x := by
    intro i x hx y hy
    refine Subgroup.iSup_induction L hy (C := fun y => x * y = y * x) ?_ ?_ ?_
    · intro j y' hy'
      by_cases hij' : i = j
      · subst hij'
        exact hii i x hx y' hy'
      · exact hij i j hij' x hx y' hy'
    · simp
    · intro y y' hy hy'
      rw [← mul_assoc, hy, mul_assoc, hy', mul_assoc]
  intro x hx y hy
  refine Subgroup.iSup_induction L hx (C := fun x => x * y = y * x) ?_ ?_ ?_
  · intro i x' hx'
    exact step i x' hx' y hy
  · simp
  · intro x x' hx hx'
    rw [mul_assoc, hx', ← mul_assoc, hx, mul_assoc]

theorem exists_conj_natL {G L : Subgroup (V ≃ₗ[k] V)} {ι : Type*} {g : ι → V ≃ₗ[k] V}
    (hg : ∀ i, g i ∈ G) (hall : ∀ x ∈ G, ∃ i, conjR x L = conjR (g i) L)
    {y : V ≃ₗ[k] V} (hy : y ∈ G) (i : ι) :
    ∃ j, conjSub y (conjR (g i) L) = conjR (g j) L := by
  obtain ⟨j, hj⟩ := hall (g i * y⁻¹) (G.mul_mem (hg i) (G.inv_mem hy))
  exact ⟨j, by rw [conjSub_conjR, hj]⟩

theorem exists_threeGroup [Finite V] {G L : Subgroup (V ≃ₗ[k] V)} (hLG : L ≤ G)
    (hL3 : Nat.card L = 3) (hLsub : (L.subgroupOf G).IsSubnormal) :
    ∃ P : Subgroup (V ≃ₗ[k] V), P ≤ G ∧ IsPGroup 3 P ∧ (∀ x ∈ G, conjSub x P ≤ P) ∧ L ≤ P := by
  have : Finite (V ≃ₗ[k] V) := finite_linearEquiv
  let π : Set Nat.Primes := {⟨3, Nat.prime_three⟩}
  have hNcard : Nat.card (L.subgroupOf G) = 3 := by
    rw [show Nat.card (L.subgroupOf G) = Nat.card L from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLG).toEquiv, hL3]
  have hNπ : CFSG.IsPiSubgroup π (⊤ : Subgroup ↥(L.subgroupOf G)) := by
    intro p hp
    rw [Subgroup.card_top, hNcard] at hp
    have : p.val = 3 := (Nat.prime_dvd_prime_iff_eq p.2 Nat.prime_three).1 hp
    exact Set.mem_singleton_iff.2 (Subtype.ext this)
  have hcoreN : CFSG.piCore π ↥(L.subgroupOf G) = ⊤ :=
    top_le_iff.1 (CFSG.LocalCores.le_piCore_of_normal Subgroup.normal_top hNπ)
  have hint := CFSG.LocalCores.prime_set_core_subnormal_intersection π hLsub
  rw [hcoreN, Subgroup.map_top, Subgroup.range_subtype] at hint
  have hNle : L.subgroupOf G ≤ CFSG.piCore π ↥G := inf_eq_left.1 hint.symm
  refine ⟨(CFSG.piCore π ↥G).map G.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · have hπG := CFSG.LocalCores.piCore_isPiSubgroup (G := ↥G) π
    have hpos : Nat.card (CFSG.piCore π ↥G) ≠ 0 := Nat.card_pos.ne'
    have h1 : ∃ n, Nat.card (CFSG.piCore π ↥G) = 3 ^ n :=
      ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (p := 3) hpos fun {d} hd hdd => by
        have := hπG ⟨d, hd⟩ hdd
        have h' : (⟨d, hd⟩ : Nat.Primes) = ⟨3, Nat.prime_three⟩ := Set.mem_singleton_iff.1 this
        exact congrArg Subtype.val h'⟩
    obtain ⟨n, hn⟩ := h1
    have h2 : IsPGroup 3 (CFSG.piCore π ↥G) := IsPGroup.of_card hn
    have e := (CFSG.piCore π ↥G).equivMapOfInjective G.subtype G.subtype_injective
    exact h2.of_surjective e.toMonoidHom e.surjective
  · intro x hx y hy
    rw [mem_conjSub] at hy
    obtain ⟨p, hp, hpy⟩ := hy
    have hn : (CFSG.piCore π ↥G).Normal := inferInstance
    refine ⟨⟨x, hx⟩ * p * ⟨x, hx⟩⁻¹, hn.conj_mem p hp ⟨x, hx⟩, ?_⟩
    have hpy' : (p : V ≃ₗ[k] V) = x⁻¹ * y * x := hpy
    show x * (p : V ≃ₗ[k] V) * x⁻¹ = y
    rw [hpy']
    group
  · intro l hl
    exact ⟨⟨l, hLG hl⟩, hNle hl, rfl⟩

end CFSG.QuasithinUnique.Setup.Layer
