module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Claim1Assembly
import Mathlib.Tactic.Group
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts Subgroup
open scoped commutatorElement

section Generic

variable {G : Type} [Group G]

theorem zpow_eq_one_or_self {u : G} (hu : u * u = 1) (k : ℤ) : u ^ k = 1 ∨ u ^ k = u := by
  have h2 : u ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hu
  rcases Int.even_or_odd' k with ⟨n, rfl | rfl⟩
  · left
    rw [zpow_mul, h2, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, h2, one_zpow, one_mul]

theorem mem_zpowers_sup_zpowers {z₁ z₂ : G} (hz₁ : z₁ * z₁ = 1) (hz₂ : z₂ * z₂ = 1)
    (hc : z₁ * z₂ = z₂ * z₁) {w : G} (hw : w ∈ Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂) :
    w = 1 ∨ w = z₁ ∨ w = z₂ ∨ w = z₁ * z₂ := by
  have hc' : ∀ a ∈ Subgroup.zpowers z₁, ∀ b ∈ Subgroup.zpowers z₂, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (((show Commute z₁ z₂ from hc).zpow_zpow i j).eq)
  obtain ⟨a, ha, b, hb, rfl⟩ := (BenderBranch.mem_sup_iff_of_commute hc').mp hw
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  rcases zpow_eq_one_or_self hz₁ i with h1 | h1 <;> rcases zpow_eq_one_or_self hz₂ j with h2 | h2 <;>
    simp [h1, h2]

end Generic

section Config

variable {G : Type} [Group G] [Finite G] {T M H S L K : Subgroup G} {s x z₁ z₂ : G}

theorem A3A3K.conj_baum_cases
    (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3) (h34 : Lemma2_4_34_used)
    (hK : A3A3K T M H S L s x z₁ z₂ K) {r ρ : G} (hrR : r ∈ baum S)
    (hrC : r ∈ Subgroup.centralizer (K : Set G)) (hρ : ρ ∈ baum S) :
    ρ * r * ρ⁻¹ = r ∨ ρ * r * ρ⁻¹ = r * z₂ := by
  have hcs := hK.cs
  obtain ⟨e₀⟩ := hK.nonempty_alt6 h34
  have hfr := hK.toA3A3x.frattini_eq hD h27_1
  have hcomm := commutator_le_frattiniOf (isPGroup_baum hcs)
  have hz₁2 : z₁ * z₁ = 1 := by simpa [pow_two] using hK.toA3A3x.sq₁
  have hz₂2 : z₂ * z₂ = 1 := by simpa [pow_two] using hK.toA3A3x.sq₂
  have hz₁z₂ : z₁ * z₂ = z₂ * z₁ := hK.toA3A3x.comm₁₂
  have hz₁K : z₁ ∈ K := hK.z₁_mem_K
  have hz₂C : z₂ ∈ Subgroup.centralizer (K : Set G) := hK.z₂_mem_centralizer
  have hw : ⁅r⁻¹, ρ⁆ ∈ Subgroup.zpowers z₁ ⊔ Subgroup.zpowers z₂ := by
    rw [← hfr]
    exact hcomm (Subgroup.commutator_mem_commutator ((baum S).inv_mem hrR) hρ)
  have hρN : ρ ∈ normalizer (K : Set G) := hK.K_norm (hK.toA3A3x.baum_le_cent₂ hρ)
  have hwC : ⁅r⁻¹, ρ⁆ ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro κ hκ
    have hκ' : ρ⁻¹ * κ * ρ ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp ((normalizer (K : Set G)).inv_mem hρN) κ).mp hκ
      simpa using this
    have h1 : (ρ⁻¹ * κ * ρ) * r = r * (ρ⁻¹ * κ * ρ) :=
      Subgroup.mem_centralizer_iff.mp hrC _ hκ'
    have h2 : κ * r = r * κ := Subgroup.mem_centralizer_iff.mp hrC κ hκ
    have h3 : κ * (ρ * r * ρ⁻¹) = (ρ * r * ρ⁻¹) * κ := by
      calc κ * (ρ * r * ρ⁻¹) = ρ * ((ρ⁻¹ * κ * ρ) * r) * ρ⁻¹ := by group
        _ = ρ * (r * (ρ⁻¹ * κ * ρ)) * ρ⁻¹ := by rw [h1]
        _ = (ρ * r * ρ⁻¹) * κ := by group
    have h4 : κ * r⁻¹ = r⁻¹ * κ := by
      calc κ * r⁻¹ = r⁻¹ * (r * κ) * r⁻¹ := by group
        _ = r⁻¹ * (κ * r) * r⁻¹ := by rw [h2]
        _ = r⁻¹ * κ := by group
    calc κ * ⁅r⁻¹, ρ⁆ = κ * (r⁻¹ * (ρ * r * ρ⁻¹)) := by
          rw [commutatorElement_def]; group
      _ = (κ * r⁻¹) * (ρ * r * ρ⁻¹) := by group
      _ = (r⁻¹ * κ) * (ρ * r * ρ⁻¹) := by rw [h4]
      _ = r⁻¹ * (κ * (ρ * r * ρ⁻¹)) := by group
      _ = r⁻¹ * ((ρ * r * ρ⁻¹) * κ) := by rw [h3]
      _ = (r⁻¹ * (ρ * r * ρ⁻¹)) * κ := by group
      _ = ⁅r⁻¹, ρ⁆ * κ := by rw [commutatorElement_def]; group
  have hz₁C : z₁ ∉ Subgroup.centralizer (K : Set G) := by
    intro h
    apply hK.z₁_ne
    refine eq_one_of_mem_centralizer (A := K) e₀ hz₁K (fun a ha => ?_)
    exact (Subgroup.mem_centralizer_iff.mp h a ha)
  have hwcases : ⁅r⁻¹, ρ⁆ = 1 ∨ ⁅r⁻¹, ρ⁆ = z₂ := by
    rcases mem_zpowers_sup_zpowers hz₁2 hz₂2 hz₁z₂ hw with h | h | h | h
    · exact Or.inl h
    · have h' := hwC
      rw [h] at h'
      exact absurd h' hz₁C
    · exact Or.inr h
    · exfalso
      apply hz₁C
      have : z₁ = (z₁ * z₂) * z₂ := by
        calc z₁ = z₁ * (z₂ * z₂) := by rw [hz₂2, mul_one]
          _ = (z₁ * z₂) * z₂ := by group
      rw [this]
      have h' := hwC
      rw [h] at h'
      exact Subgroup.mul_mem _ h' hz₂C
  have hconj : ρ * r * ρ⁻¹ = r * ⁅r⁻¹, ρ⁆ := by
    rw [commutatorElement_def]; group
  rcases hwcases with h | h
  · left; rw [hconj, h, mul_one]
  · right; rw [hconj, h]

theorem A3A3K.relIndex_centralizerElem_baum_le_two
    (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3)
    (h34 : Lemma2_4_34_used) (hK : A3A3K T M H S L s x z₁ z₂ K) {r : G} (hrR : r ∈ baum S)
    (hrC : r ∈ Subgroup.centralizer (K : Set G)) :
    (centralizerElem r).relIndex (baum S) ≤ 2 := by
  set r' : ↥(baum S) := ⟨r, hrR⟩ with hr'
  set z' : ↥(baum S) := ⟨z₂, hK.z₂_mem_baum⟩ with hz'
  have hcentr : (centralizerElem r).subgroupOf (baum S) = Subgroup.centralizer ({r'} : Set ↥(baum S)) := by
    ext g
    simp only [Subgroup.mem_subgroupOf, centralizerElem, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact Subtype.ext (by simpa using h)
    · intro h
      simpa using congrArg Subtype.val h
  have hsub : conjugatesOf r' ⊆ {r', r' * z'} := by
    intro c hc
    have hc' : IsConj r' c := hc
    obtain ⟨ρ, hρ⟩ := isConj_iff.mp hc'
    have := hK.conj_baum_cases hD h27_1 h34 hrR hrC ρ.2
    have hρ' : ((ρ * r' * ρ⁻¹ : ↥(baum S)) : G) = (ρ : G) * r * (ρ : G)⁻¹ := rfl
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases this with h | h
    · left
      rw [← hρ]
      exact Subtype.ext (hρ'.trans h)
    · right
      rw [← hρ]
      exact Subtype.ext (hρ'.trans h)
  have hcard : (conjugatesOf r').ncard ≤ 2 := by
    calc (conjugatesOf r').ncard ≤ ({r', r' * z'} : Set ↥(baum S)).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := by
          have h2 := Set.ncard_insert_le r' ({r' * z'} : Set ↥(baum S))
          rw [Set.ncard_singleton] at h2
          omega
  rw [Subgroup.relIndex, hcentr, Subgroup.index_centralizer_eq_ncard]
  exact hcard

end Config

end CFSG.QuasithinUnique.DoubleA3
