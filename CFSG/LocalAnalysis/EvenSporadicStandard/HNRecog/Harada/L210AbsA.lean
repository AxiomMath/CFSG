module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L28Rep
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210WrBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.Open

variable {X : Type} [Group X] [Finite X] {A : Subgroup X} {w : X}
  {ψ : ↥(normalizer (A : Set X)) →* A5WrTwo}

private lemma normal_subgroupOf_of_invariant {B : Subgroup X}
    (hBN : B ≤ normalizer (A : Set X))
    (hinv : ∀ n ∈ normalizer (A : Set X), ∀ b ∈ B, n * b * n⁻¹ ∈ B) :
    (B.subgroupOf (normalizer (A : Set X))).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (H := B)
      (K := normalizer (A : Set X)) hBN).mpr
    ((Subgroup.le_normalizer_iff (H := normalizer (A : Set X)) (K := B)).mpr hinv)

private lemma map_normal_subgroupOf_of_invariant {B : Subgroup X}
    (hψ : Function.Surjective ψ) (hBN : B ≤ normalizer (A : Set X))
    (hinv : ∀ n ∈ normalizer (A : Set X), ∀ b ∈ B, n * b * n⁻¹ ∈ B) :
    ((B.subgroupOf (normalizer (A : Set X))).map ψ).Normal :=
  Subgroup.Normal.map (normal_subgroupOf_of_invariant hBN hinv) ψ hψ

theorem Abs210.hirr (h : Abs210 A w ψ) : ∀ B : Subgroup X, B ≤ A →
    (∀ n ∈ normalizer (A : Set X), ∀ b ∈ B, n * b * n⁻¹ ∈ B) → B = ⊥ ∨ B = A := by
  intro B hBA hinv
  exact L28_irreducible h.toL28Hyp hBA (fun n _ b hb => hinv (n : X) n.2 b hb)

theorem Abs210.hO2 (h : Abs210 A w ψ) : ∀ P : Subgroup X, A ≤ P → P ≤ normalizer (A : Set X) →
    (∀ n ∈ normalizer (A : Set X), ∀ p ∈ P, n * p * n⁻¹ ∈ P) → IsPGroup 2 P → P = A := by
  intro P hAP hPN hinv hP
  haveI : ((P.subgroupOf (normalizer (A : Set X))).map ψ).Normal :=
    map_normal_subgroupOf_of_invariant h.surj hPN hinv
  have hPg : IsPGroup 2 (P.subgroupOf (normalizer (A : Set X))) :=
    IsPGroup.comap_subtype (K := normalizer (A : Set X)) hP
  have hbot : (P.subgroupOf (normalizer (A : Set X))).map ψ = ⊥ :=
    L210_eq_bot_of_normal_isPGroup (hPg.map ψ)
  have hle : P.subgroupOf (normalizer (A : Set X)) ≤ ψ.ker :=
    (Subgroup.map_eq_bot_iff (H := P.subgroupOf (normalizer (A : Set X)))
      (f := ψ)).mp hbot
  rw [h.ker] at hle
  apply le_antisymm _ hAP
  intro p hp
  have hpN : p ∈ normalizer (A : Set X) := hPN hp
  have hmem : (⟨p, hpN⟩ : ↥(normalizer (A : Set X))) ∈
      A.subgroupOf (normalizer (A : Set X)) :=
    hle (by rw [Subgroup.mem_subgroupOf]; exact hp)
  rwa [Subgroup.mem_subgroupOf] at hmem

theorem Abs210.hinv (h : Abs210 A w ψ) : ∀ B : Subgroup X, A ≤ B → B ≤ normalizer (A : Set X) →
    (∀ n ∈ normalizer (A : Set X), ∀ b ∈ B, n * b * n⁻¹ ∈ B) → B ≠ A →
      ∃ q ∈ B, q ∉ A ∧ q * q = 1 := by
  intro B hAB hBN hinv hBAne
  haveI : ((B.subgroupOf (normalizer (A : Set X))).map ψ).Normal :=
    map_normal_subgroupOf_of_invariant h.surj hBN hinv
  have hne : (B.subgroupOf (normalizer (A : Set X))).map ψ ≠ ⊥ := by
    intro hbot
    apply hBAne
    apply le_antisymm _ hAB
    intro b hb
    have hle : B.subgroupOf (normalizer (A : Set X)) ≤ ψ.ker :=
      (Subgroup.map_eq_bot_iff (H := B.subgroupOf (normalizer (A : Set X)))
        (f := ψ)).mp hbot
    rw [h.ker] at hle
    have hbN : b ∈ normalizer (A : Set X) := hBN hb
    have hmem : (⟨b, hbN⟩ : ↥(normalizer (A : Set X))) ∈
        A.subgroupOf (normalizer (A : Set X)) :=
      hle (by rw [Subgroup.mem_subgroupOf]; exact hb)
    rwa [Subgroup.mem_subgroupOf] at hmem
  have hcomm : commutator A5WrTwo ≤ (B.subgroupOf (normalizer (A : Set X))).map ψ :=
    L210_base_le_of_normal hne
  obtain ⟨q₀, hq₀A, hq₀sq, hq₀ψ⟩ := h.invol
  obtain ⟨b, hbB', hbψ⟩ := Subgroup.mem_map.mp (hcomm hq₀ψ)
  have hker : b⁻¹ * q₀ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hbψ]
    simp
  rw [h.ker] at hker
  have hcA : ((b⁻¹ * q₀ : ↥(normalizer (A : Set X))) : X) ∈ A := by
    rwa [Subgroup.mem_subgroupOf] at hker
  have hbB : (b : X) ∈ B := by
    rwa [Subgroup.mem_subgroupOf] at hbB'
  have hcB : ((b⁻¹ * q₀ : ↥(normalizer (A : Set X))) : X) ∈ B := hAB hcA
  have hprod : (b : X) * ((b⁻¹ * q₀ : ↥(normalizer (A : Set X))) : X) ∈ B :=
    B.mul_mem hbB hcB
  have heq : (b : X) * ((b⁻¹ * q₀ : ↥(normalizer (A : Set X))) : X) = (q₀ : X) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  exact ⟨(q₀ : X), by rwa [heq] at hprod, hq₀A, hq₀sq⟩

end CFSG.EvenSporadicStandard.HNRecog.Harada
