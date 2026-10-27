module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.GroupAction.Blocks
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.AltSevenA1Sylow
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.A7Index15

public section

namespace CFSG.AGLEmbeddingD2.GN

open MulAction

local notation "A₇" => alternatingGroup (Fin 7)

theorem seven_le_index_of_ne_top {H : Subgroup (alternatingGroup (Fin 7))} (hH : H ≠ ⊤) :
    7 ≤ H.index := by
  have hs : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
  by_contra hlt
  push Not at hlt
  let φ : alternatingGroup (Fin 7) →* Equiv.Perm (alternatingGroup (Fin 7) ⧸ H) :=
    MulAction.toPermHom _ _
  have hker : φ.ker = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exact h
    · exfalso
      apply hH
      rw [eq_top_iff]
      intro g _
      have h1 : φ g = 1 := MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top g)
      have h2 : g • ((1 : alternatingGroup (Fin 7)) : alternatingGroup (Fin 7) ⧸ H) =
          ((1 : alternatingGroup (Fin 7)) : alternatingGroup (Fin 7) ⧸ H) := by
        have := congrArg (fun p : Equiv.Perm (alternatingGroup (Fin 7) ⧸ H) =>
          p ((1 : alternatingGroup (Fin 7)) : alternatingGroup (Fin 7) ⧸ H)) h1
        simpa [φ] using this
      have h3 : ((g : alternatingGroup (Fin 7)) : alternatingGroup (Fin 7) ⧸ H) =
          ((1 : alternatingGroup (Fin 7)) : alternatingGroup (Fin 7) ⧸ H) := by
        simpa using h2
      have h4 := QuotientGroup.eq.1 h3
      simpa using H.inv_mem h4
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hker
  have hdvd := Subgroup.card_dvd_of_injective φ hinj
  rw [CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.card_alternatingGroup_seven,
    Nat.card_perm, show Nat.card (alternatingGroup (Fin 7) ⧸ H) = H.index from rfl] at hdvd
  have hfac : Nat.factorial H.index ≤ 720 := by
    have := Nat.factorial_le (show H.index ≤ 6 by omega)
    simpa [Nat.factorial] using this
  have := Nat.le_of_dvd (Nat.factorial_pos _) hdvd
  omega

section Orbits

variable {X : Type*} [MulAction (alternatingGroup (Fin 7)) X]

theorem seven_le_ncard_orbit (x : X) (hx : ¬ ∀ g : alternatingGroup (Fin 7), g • x = x) :
    7 ≤ (orbit (alternatingGroup (Fin 7)) x).ncard := by
  rw [← index_stabilizer]
  apply seven_le_index_of_ne_top
  intro h
  apply hx
  intro g
  have : g ∈ stabilizer (alternatingGroup (Fin 7)) x := by rw [h]; trivial
  exact this

theorem not_two_dvd_ncard_orbit {S : Subgroup (alternatingGroup (Fin 7))} (hodd : ¬ 2 ∣ S.index)
    {x : X} (hx : ∀ s ∈ S, s • x = x) :
    ¬ 2 ∣ (orbit (alternatingGroup (Fin 7)) x).ncard := by
  rw [← index_stabilizer]
  intro h
  exact hodd (h.trans (Subgroup.index_dvd_of_le (fun s hs => hx s hs)))

theorem eq_of_mem_orbit_of_fixed {S : Subgroup (alternatingGroup (Fin 7))} (hS : IsPGroup 2 S)
    (hodd : ¬ 2 ∣ S.index) {u₁ u₂ : X} (h1 : ∀ s ∈ S, s • u₁ = u₁) (h2 : ∀ s ∈ S, s • u₂ = u₂)
    (h : u₂ ∈ orbit (alternatingGroup (Fin 7)) u₁) : u₂ = u₁ := by
  obtain ⟨g, hg⟩ := h
  have hg : g • u₁ = u₂ := hg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 (alternatingGroup (Fin 7)) := hS.toSylow hodd
  have hPH : (P : Subgroup (alternatingGroup (Fin 7))) ≤
      stabilizer (alternatingGroup (Fin 7)) u₁ := by
    intro s hs
    rw [mem_stabilizer_iff]
    exact h1 s (by simpa [P] using hs)
  have hN : ∀ n ∈ Subgroup.normalizer ((P : Subgroup (alternatingGroup (Fin 7))) :
      Set (alternatingGroup (Fin 7))), n ∈ stabilizer (alternatingGroup (Fin 7)) u₁ := by
    intro n hn
    rw [mem_stabilizer_iff]
    exact h1 n (mem_of_mem_normalizer_of_sylow hS hodd (by simpa [P] using hn))
  have hg' : ((g⁻¹ • P : Sylow 2 (alternatingGroup (Fin 7))) : Subgroup (alternatingGroup (Fin 7)))
      ≤ stabilizer (alternatingGroup (Fin 7)) u₁ := by
    intro x hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
    have hx' : g * x * g⁻¹ ∈ S := by simpa [P, MulAut.conj_inv_apply] using hx
    rw [mem_stabilizer_iff]
    have h3 := h2 _ hx'
    rw [← hg, mul_smul, mul_smul, smul_left_cancel_iff, inv_smul_smul] at h3
    exact h3
  have hgmem := mem_of_smul_sylow_le P hPH hN hg'
  rw [mem_stabilizer_iff] at hgmem
  rw [← hg, hgmem]

variable [Finite X]

theorem eq_of_fixed_of_card_sixteen (hX : Nat.card X = 16) (x₀ : X)
    (h0 : ∀ g : alternatingGroup (Fin 7), g • x₀ = x₀)
    (huniq : ∀ x : X, (∀ g : alternatingGroup (Fin 7), g • x = x) → x = x₀)
    {S : Subgroup (alternatingGroup (Fin 7))} (hS : IsPGroup 2 S) (hodd : ¬ 2 ∣ S.index)
    {u₁ u₂ : X} (hu₁ : u₁ ≠ x₀) (hu₂ : u₂ ≠ x₀) (h1 : ∀ s ∈ S, s • u₁ = u₁)
    (h2 : ∀ s ∈ S, s • u₂ = u₂) : u₁ = u₂ := by
  by_cases h : u₂ ∈ orbit (alternatingGroup (Fin 7)) u₁
  · exact (eq_of_mem_orbit_of_fixed hS hodd h1 h2 h).symm
  exfalso
  classical
  have hn1 : 7 ≤ (orbit A₇ u₁).ncard := seven_le_ncard_orbit u₁ fun hf => hu₁ (huniq u₁ hf)
  have hn2 : 7 ≤ (orbit A₇ u₂).ncard := seven_le_ncard_orbit u₂ fun hf => hu₂ (huniq u₂ hf)
  have ho1 := not_two_dvd_ncard_orbit hodd h1
  have ho2 := not_two_dvd_ncard_orbit hodd h2
  have hO0 : orbit A₇ x₀ = {x₀} := by
    ext y
    simp only [mem_orbit_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨g, rfl⟩
      exact h0 g
    · rintro rfl
      exact ⟨1, one_smul _ _⟩
  have hd12 : Disjoint (orbit A₇ u₁) (orbit A₇ u₂) := by
    rcases orbit.eq_or_disjoint (G := A₇) u₁ u₂ with he | hd
    · exact absurd (he ▸ mem_orbit_self u₂) h
    · exact hd
  have hnot0 : ∀ u : X, u ≠ x₀ → Disjoint (orbit A₇ x₀) (orbit A₇ u) := by
    intro u hu
    rcases orbit.eq_or_disjoint (G := A₇) x₀ u with he | hd
    · exfalso
      have : u ∈ orbit A₇ x₀ := he ▸ mem_orbit_self u
      rw [hO0] at this
      exact hu this
    · exact hd
  have hT : ((orbit A₇ x₀ ∪ orbit A₇ u₁) ∪ orbit A₇ u₂).ncard = 1 + (orbit A₇ u₁).ncard +
      (orbit A₇ u₂).ncard := by
    rw [Set.ncard_union_eq, Set.ncard_union_eq (hnot0 u₁ hu₁), hO0, Set.ncard_singleton]
    rw [Set.disjoint_union_left]
    exact ⟨hnot0 u₂ hu₂, hd12⟩
  by_cases hTu : ((orbit A₇ x₀ ∪ orbit A₇ u₁) ∪ orbit A₇ u₂) = Set.univ
  · have := congrArg Set.ncard hTu
    rw [hT, Set.ncard_univ, hX] at this
    omega
  · obtain ⟨w, hw⟩ : ∃ w, w ∉ ((orbit A₇ x₀ ∪ orbit A₇ u₁) ∪ orbit A₇ u₂) := by
      by_contra hcon
      push Not at hcon
      exact hTu (Set.eq_univ_of_forall hcon)
    have hwx : w ≠ x₀ := fun h' => hw (Or.inl (Or.inl (by rw [h']; exact mem_orbit_self _)))
    have hnw : 7 ≤ (orbit A₇ w).ncard := seven_le_ncard_orbit w fun hf => hwx (huniq w hf)
    have hdw : Disjoint ((orbit A₇ x₀ ∪ orbit A₇ u₁) ∪ orbit A₇ u₂) (orbit A₇ w) := by
      rw [Set.disjoint_left]
      intro y hy hyw
      apply hw
      have hyw' : orbit A₇ y = orbit A₇ w := orbit_eq_iff.2 hyw
      have hw' : w ∈ orbit A₇ y := hyw' ▸ mem_orbit_self w
      rcases hy with (hy | hy) | hy
      · exact Or.inl (Or.inl (by
          have : orbit A₇ y = orbit A₇ x₀ := orbit_eq_iff.2 hy
          rw [← this]; exact hw'))
      · exact Or.inl (Or.inr (by
          have : orbit A₇ y = orbit A₇ u₁ := orbit_eq_iff.2 hy
          rw [← this]; exact hw'))
      · exact Or.inr (by
          have : orbit A₇ y = orbit A₇ u₂ := orbit_eq_iff.2 hy
          rw [← this]; exact hw')
    have hcard := Set.ncard_union_eq hdw
    have hle : (((orbit A₇ x₀ ∪ orbit A₇ u₁) ∪ orbit A₇ u₂) ∪ orbit A₇ w).ncard ≤ 16 := by
      rw [← hX]
      exact Set.ncard_le_card _
    rw [hcard, hT] at hle
    omega

theorem three_dvd_card_stabilizer_of_card_sixteen (hX : Nat.card X = 16) (x₀ : X)
    (h0 : ∀ g : alternatingGroup (Fin 7), g • x₀ = x₀) {u : X} (hu : u ≠ x₀) :
    3 ∣ Nat.card (stabilizer (alternatingGroup (Fin 7)) u) := by
  apply CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.a7_three_dvd_card_of_index_le_fifteen
  rw [index_stabilizer]
  have hsub : orbit (alternatingGroup (Fin 7)) u ⊂ Set.univ := by
    rw [Set.ssubset_univ_iff]
    intro hall
    have : x₀ ∈ orbit (alternatingGroup (Fin 7)) u := by rw [hall]; trivial
    obtain ⟨g, hg⟩ := this
    apply hu
    have h1 : u = g⁻¹ • x₀ := by rw [← hg, inv_smul_smul]
    rw [h1, h0]
  have := Set.ncard_lt_ncard hsub
  rw [Set.ncard_univ, hX] at this
  omega

end Orbits

end CFSG.AGLEmbeddingD2.GN
