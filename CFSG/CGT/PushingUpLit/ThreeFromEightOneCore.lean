module

public import CFSG.CGT.PushingUpLit.Transport
import CFSG.GroupTheory.ConjugatePairSubnormality
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp
open CFSG.GroupTheory (conjugate_conjugate conjugate_le_of_mem isSubnormal_subgroupOf_conjugate)
open scoped commutatorElement

namespace ThreeFromEight

section Conjugate

variable {G : Type} [Group G]

theorem mem_conjugate_iff {H : Subgroup G} {g x : G} :
    x ∈ conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    change g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ ∈ H
    rwa [show g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y by group]
  · intro hx
    refine ⟨g * x * g⁻¹, hx, ?_⟩
    change g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x
    group

theorem conjugate_one (H : Subgroup G) : conjugate H 1 = H := by
  ext x
  rw [mem_conjugate_iff, one_mul, inv_one, mul_one]

theorem conjugate_eq_self_of_mem_normalizer {H : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (H : Set G)) : conjugate H a = H := by
  ext x
  rw [mem_conjugate_iff]
  exact (Subgroup.mem_normalizer_iff.1 ha x).symm

theorem conjugate_inv_eq_map (H : Subgroup G) (g : G) :
    conjugate H g⁻¹ = H.map (MulAut.conj g).toMonoidHom := by
  unfold conjugate
  rw [inv_inv]

end Conjugate

section SetNormalizer

variable {G : Type} [Group G]

@[expose] def setNormalizer (Γ : Set (Subgroup G)) : Subgroup G where
  carrier := {g | ∀ Z : Subgroup G, Z ∈ Γ ↔ conjugate Z g ∈ Γ}
  one_mem' := by
    intro Z
    rw [conjugate_one]
  mul_mem' := by
    intro a b ha hb Z
    refine (ha Z).trans ((hb (conjugate Z a)).trans ?_)
    rw [conjugate_conjugate]
  inv_mem' := by
    intro a ha Z
    have h := ha (conjugate Z a⁻¹)
    rw [conjugate_conjugate, inv_mul_cancel, conjugate_one] at h
    exact h.symm

theorem mem_setNormalizer_iff {Γ : Set (Subgroup G)} {g : G} :
    g ∈ setNormalizer Γ ↔ ∀ Z : Subgroup G, Z ∈ Γ ↔ conjugate Z g ∈ Γ :=
  Iff.rfl

@[expose] def memberSet (𝔛 : Set (Subgroup G)) (K : Subgroup G) : Set (Subgroup G) :=
  {Z | Z ∈ 𝔛 ∧ Z ≤ K}

theorem le_setNormalizer_memberSet {𝔛 : Set (Subgroup G)}
    (hconj : ∀ Z ∈ 𝔛, ∀ g : G, conjugate Z g ∈ 𝔛) (K : Subgroup G) :
    K ≤ setNormalizer (memberSet 𝔛 K) := by
  intro n hn Z
  have hfwd : ∀ n ∈ K, ∀ Z ∈ memberSet 𝔛 K, conjugate Z n ∈ memberSet 𝔛 K :=
    fun n hn Z hZ => ⟨hconj Z hZ.1 n, conjugate_le_of_mem hZ.2 hn⟩
  refine ⟨fun hZ => hfwd n hn Z hZ, fun hZ => ?_⟩
  have h := hfwd n⁻¹ (inv_mem hn) _ hZ
  rwa [conjugate_conjugate, mul_inv_cancel, conjugate_one] at h

end SetNormalizer

section OTwo

variable {G : Type} [Group G]

theorem isPGroup_oTwoIn (X : Subgroup G) : IsPGroup 2 (oTwoIn X) :=
  IsPGroup.map pCore_isPGroup X.subtype

theorem normalizer_le_normalizer_oTwoIn (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (oTwoIn X : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨fun hc => conj_mem_oTwoIn hg hc, fun hc => ?_⟩
  have h := conj_mem_oTwoIn (inv_mem hg) hc
  simpa [mul_assoc] using h

theorem oTwoIn_eq_map (X : Subgroup G) : oTwoIn X = (pCore 2 ↥X).map X.subtype := rfl

theorem oTwoIn_map_conj (Z : Subgroup G) (a : G) :
    oTwoIn (Z.map (MulAut.conj a).toMonoidHom) = (oTwoIn Z).map (MulAut.conj a).toMonoidHom := by
  have hp := pCore_map_iso 2 ((MulAut.conj a).subgroupMap Z)
  have h : oTwoIn (Z.map (MulAut.conj a : G →* G)) = (oTwoIn Z).map (MulAut.conj a : G →* G) := by
    rw [oTwoIn_eq_map, oTwoIn_eq_map, ← hp, Subgroup.map_map, Subgroup.map_map]
    rfl
  exact h

theorem oTwoIn_ne_bot_of_isShortGroup {X : Subgroup G} [Finite G] (hX : IsShortGroup ↥X) :
    oTwoIn X ≠ ⊥ := by
  intro h
  have h1 : pCore 2 ↥X = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp h
  have h2 : shortU ↥X = ⊥ := by
    unfold shortU
    rw [h1, Subgroup.commutator_bot_left]
  have h3 := hX.nonzero
  rw [h2] at h3
  exact not_lt_bot h3

theorem oTwoIn_le_pCore_of_isSubnormal {K : Type} [Group K] [Finite K] {X : Subgroup K}
    (hX : X.IsSubnormal) : oTwoIn X ≤ pCore 2 K := by
  have h := CFSG.LocalCores.prime_set_core_subnormal_intersection {q : Nat.Primes | q.val = 2} hX
  rw [← pCore_eq_piCore ↥X 2, ← pCore_eq_piCore K 2] at h
  change Subgroup.map X.subtype (pCore 2 ↥X) ≤ pCore 2 K
  exact h.le.trans inf_le_right

theorem oTwoIn_le_oTwoIn_of_isSubnormal [Finite G] {Z N : Subgroup G} (hZN : Z ≤ N)
    (hs : (Z.subgroupOf N).IsSubnormal) : oTwoIn Z ≤ oTwoIn N := by
  have h := Subgroup.map_mono (f := N.subtype) (oTwoIn_le_pCore_of_isSubnormal hs)
  rw [map_oTwoIn_subgroupOf hZN] at h
  exact h

@[expose] def oTwoJoin (Δ : Set (Subgroup G)) : Subgroup G :=
  ⨆ Z : Δ, oTwoIn (Z : Subgroup G)

theorem oTwoIn_le_oTwoJoin {Δ : Set (Subgroup G)} {Z : Subgroup G} (hZ : Z ∈ Δ) :
    oTwoIn Z ≤ oTwoJoin Δ :=
  le_iSup (fun Z : Δ => oTwoIn (Z : Subgroup G)) ⟨Z, hZ⟩

theorem oTwoJoin_le {Δ : Set (Subgroup G)} {K : Subgroup G} (h : ∀ Z ∈ Δ, oTwoIn Z ≤ K) :
    oTwoJoin Δ ≤ K :=
  iSup_le fun Z => h Z Z.2

theorem setNormalizer_le_normalizer_oTwoJoin (Δ : Set (Subgroup G)) :
    setNormalizer Δ ≤ Subgroup.normalizer (oTwoJoin Δ : Set G) := by
  have key : ∀ g ∈ setNormalizer Δ, ∀ h ∈ oTwoJoin Δ, g * h * g⁻¹ ∈ oTwoJoin Δ := by
    intro g hg h hh
    have hle : (oTwoJoin Δ).map (MulAut.conj g).toMonoidHom ≤ oTwoJoin Δ := by
      unfold oTwoJoin
      rw [Subgroup.map_iSup]
      refine iSup_le fun Z => ?_
      have hZ' : conjugate (Z : Subgroup G) g⁻¹ ∈ Δ :=
        ((mem_setNormalizer_iff.1 (inv_mem hg)) Z).1 Z.2
      rw [← oTwoIn_map_conj, ← conjugate_inv_eq_map]
      exact oTwoIn_le_oTwoJoin hZ'
    exact hle ⟨h, hh, rfl⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key g hg h hh, fun hh => ?_⟩
  have h' := key g⁻¹ (inv_mem hg) _ hh
  simpa [mul_assoc] using h'

theorem setNormalizer_eq_of_isMaximalTwoLocal [Finite G] {Δ : Set (Subgroup G)}
    {N : Subgroup G} (hN : IsMaximalTwoLocal N) (hle : N ≤ setNormalizer Δ)
    (hOle : ∀ Z ∈ Δ, oTwoIn Z ≤ oTwoIn N) (hne : ∃ Z ∈ Δ, oTwoIn Z ≠ ⊥) :
    setNormalizer Δ = N := by
  obtain ⟨Z₀, hZ₀, hZ₀ne⟩ := hne
  have hW : oTwoJoin Δ ≤ oTwoIn N := oTwoJoin_le hOle
  have hW2 : IsPGroup 2 (oTwoJoin Δ) := (isPGroup_oTwoIn N).to_le hW
  have hWne : oTwoJoin Δ ≠ ⊥ := by
    intro h
    have h' := oTwoIn_le_oTwoJoin hZ₀
    rw [h] at h'
    exact hZ₀ne (le_bot_iff.1 h')
  have hnorm := setNormalizer_le_normalizer_oTwoJoin Δ
  have hNW : Subgroup.normalizer (oTwoJoin Δ : Set G) = N := by
    by_contra hne'
    exact hN.2 _ (lt_of_le_of_ne (hle.trans hnorm) (Ne.symm hne'))
      (isPLocal_normalizer_of_isPGroup hW2 hWne)
  exact le_antisymm (hnorm.trans hNW.le) hle

end OTwo

end ThreeFromEight

@[expose] def RelativeBlocksCommute (G : Type) [Group G] [Finite G] : Prop :=
  ∀ K : Subgroup G, IsCharacteristicP 2 ↥K → ∀ Y Z : Subgroup G,
    IsBlockOfInX K Y → IsBlockOfInX K Z → Y ≠ Z → ⁅Y, Z⁆ = ⊥

open ThreeFromEight

section Abstract

variable {G : Type} [Group G] [Finite G]

theorem exists_unique_maximalTwoLocal_of_blocksCommute (hcomm : RelativeBlocksCommute G)
    (hchar : IsCharacteristicPType G 2) (𝔛 : Set (Subgroup G))
    (hconj : ∀ Z ∈ 𝔛, ∀ g : G, conjugate Z g ∈ 𝔛) (hX : ∀ Z ∈ 𝔛, InClassX ↥Z)
    (h81 : ∀ Z ∈ 𝔛, ∀ N : Subgroup G, N ∈ maximalTwoLocalsContaining (Z : Set G) →
      (Z.subgroupOf N).IsSubnormal)
    {X : Subgroup G} (hXm : X ∈ 𝔛) :
    ∃ M : Subgroup G, maximalTwoLocalsContaining (X : Set G) = {M} ∧
      (X.subgroupOf M).IsSubnormal := by
  have hOne : oTwoIn X ≠ ⊥ := oTwoIn_ne_bot_of_isShortGroup (hX X hXm).1
  obtain ⟨N₀, hN₀, hN₀max⟩ := exists_isMaximalTwoLocal_ge
    (isPLocal_normalizer_of_isPGroup (isPGroup_oTwoIn X) hOne)
  have hNX₀ : Subgroup.normalizer (X : Set G) ≤ N₀ :=
    (normalizer_le_normalizer_oTwoIn X).trans hN₀
  have hXN₀ : N₀ ∈ maximalTwoLocalsContaining (X : Set G) :=
    ⟨hN₀max, fun x hx => hNX₀ (Subgroup.le_normalizer hx)⟩
  have comm : ∀ N : Subgroup G, IsMaximalTwoLocal N → ∀ Y ∈ 𝔛, ∀ Z ∈ 𝔛, Y ≤ N → Z ≤ N →
      Y ≠ Z → ⁅Y, Z⁆ = ⊥ := fun N hN Y hY Z hZ hYN hZN hne =>
    hcomm N (hchar N hN.1) Y Z ⟨hYN, h81 Y hY N ⟨hN, fun x hx => hYN hx⟩, hX Y hY⟩
      ⟨hZN, h81 Z hZ N ⟨hN, fun x hx => hZN hx⟩, hX Z hZ⟩ hne
  have key : ∀ N ∈ maximalTwoLocalsContaining (X : Set G),
      N = setNormalizer (memberSet 𝔛 (Subgroup.normalizer (X : Set G))) := by
    rintro N ⟨hNmax, hXN'⟩
    have hXN : X ≤ N := fun x hx => hXN' hx
    have hsub : ∀ Z ∈ memberSet 𝔛 N, (Z.subgroupOf N).IsSubnormal :=
      fun Z hZ => h81 Z hZ.1 N ⟨hNmax, fun x hx => hZ.2 hx⟩
    have hOle : ∀ Z ∈ memberSet 𝔛 N, oTwoIn Z ≤ oTwoIn N :=
      fun Z hZ => oTwoIn_le_oTwoIn_of_isSubnormal hZ.2 (hsub Z hZ)
    have hΔΓ : memberSet 𝔛 N ⊆ memberSet 𝔛 (Subgroup.normalizer (X : Set G)) := by
      intro Z hZ
      refine ⟨hZ.1, ?_⟩
      by_cases hZX : Z = X
      · rw [hZX]
        exact Subgroup.le_normalizer
      · have hc : ⁅Z, X⁆ = ⊥ := comm N hNmax Z hZ.1 X hXm hZ.2 hXN hZX
        exact (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc).trans
          (Subgroup.centralizer_le_normalizer _)
    have hd : setNormalizer (memberSet 𝔛 N) = N :=
      setNormalizer_eq_of_isMaximalTwoLocal hNmax (le_setNormalizer_memberSet hconj N) hOle
        ⟨X, ⟨hXm, hXN⟩, hOne⟩
    have hΓΔ : memberSet 𝔛 (Subgroup.normalizer (X : Set G)) ⊆ memberSet 𝔛 N := by
      intro Z hZ
      refine ⟨hZ.1, ?_⟩
      have hnz : ∀ Z₁ ∈ memberSet 𝔛 N, Z ≤ Subgroup.normalizer (Z₁ : Set G) := by
        intro Z₁ hZ₁
        by_cases hZZ : Z = Z₁
        · rw [← hZZ]
          exact Subgroup.le_normalizer
        · have hc : ⁅Z, Z₁⁆ = ⊥ := comm N₀ hN₀max Z hZ.1 Z₁ hZ₁.1 (hZ.2.trans hNX₀)
            ((hΔΓ hZ₁).2.trans hNX₀) hZZ
          exact (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc).trans
            (Subgroup.centralizer_le_normalizer _)
      have hZs : Z ≤ setNormalizer (memberSet 𝔛 N) := by
        intro z hz Z₂
        refine ⟨fun hZ₂ => ?_, fun hZ₂ => ?_⟩
        · rwa [conjugate_eq_self_of_mem_normalizer (hnz Z₂ hZ₂ hz)]
        · have h1 := conjugate_eq_self_of_mem_normalizer (hnz _ hZ₂ (inv_mem hz))
          rw [conjugate_conjugate, mul_inv_cancel, conjugate_one] at h1
          rw [h1]
          exact hZ₂
      rw [hd] at hZs
      exact hZs
    rw [Set.Subset.antisymm hΓΔ hΔΓ, hd]
  refine ⟨N₀, Set.eq_singleton_iff_unique_mem.2 ⟨hXN₀, fun N hN => ?_⟩,
    h81 X hXm N₀ hXN₀⟩
  exact (key N hN).trans (key N₀ hXN₀).symm

end Abstract

end CFSG.CGT.PushingUpLit
