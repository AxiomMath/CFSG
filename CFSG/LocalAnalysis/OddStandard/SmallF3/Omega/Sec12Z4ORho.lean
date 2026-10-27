module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L12EDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L123aVec
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L123aX

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem z4o_secActs_inv {φ : (Fin 5 → ZMod 2) → G} {h : G} {σ : Equiv.Perm (Fin 5)}
    (hσ : SecActs φ h σ) : SecActs φ h⁻¹ σ⁻¹ := by
  intro v hv
  have h1 := hσ _ (isEvenVec_permVec σ⁻¹ hv)
  rw [← permVec_mul, show σ * σ⁻¹ = 1 from mul_inv_cancel σ, permVec_one] at h1
  rw [← h1]
  group

theorem z4o_mem_K_of_even [Finite G] {t : G} {L S : Subgroup G} (F : Sec12Frame t L S)
    {φ : (Fin 5 → ZMod 2) → G}
    (hperm : IsPermModuleVia IsEvenVec φ (secB S L) (secM t S L ⊓ L)
      (alternatingGroup (Fin 5)))
    {g : G} (hgN : g ∈ normalizer (L : Set G)) {σ : Equiv.Perm (Fin 5)} (hσ : SecActs φ g σ)
    (hσA : σ ∈ alternatingGroup (Fin 5)) : g ∈ L ⊔ centralizer (L : Set G) := by
  obtain ⟨m, hm, hmσ⟩ := hperm.2.2.2.2 σ hσA
  have hmL : m ∈ L := hm.2
  have hgm : g * m⁻¹ ∈ secB S L ⊔ centralizer (L : Set G) := by
    refine F.centB (g * m⁻¹) (mul_mem hgN (inv_mem (Subgroup.le_normalizer hmL))) ?_
    intro b hb
    obtain ⟨v, hv, rfl⟩ := (hperm.2.2.1 b).mp hb
    have h2 := (hσ.mul (z4o_secActs_inv hmσ)) v hv
    rw [show σ * σ⁻¹ = 1 from mul_inv_cancel σ, permVec_one] at h2
    calc g * m⁻¹ * φ v = (g * m⁻¹ * φ v * (g * m⁻¹)⁻¹) * (g * m⁻¹) := by group
      _ = φ v * (g * m⁻¹) := by rw [h2]
  have e : g = (g * m⁻¹) * m := by group
  rw [e]
  exact mul_mem (sup_le_sup_right F.bdata.1 _ hgm) (Subgroup.mem_sup_left hmL)

theorem z4o_exists_swap [Finite G] {t : G} {L S : Subgroup G} (F : Sec12Frame t L S)
    (hS : IsSylow2Of S (centralizer ({t} : Set G))) {φ : (Fin 5 → ZMod 2) → G}
    (hperm : IsPermModuleVia IsEvenVec φ (secB S L) (secM t S L ⊓ L)
      (alternatingGroup (Fin 5)))
    (hS5 : ∀ g ∈ normalizer (L : Set G) ⊓ normalizer (secB S L : Set G),
      ∃ σ, SecActs φ g σ)
    {g : G} (hgS : g ∈ S) (hgK : g ∉ L ⊔ centralizer (L : Set G)) :
    ∃ y ∈ (secM t S L ⊓ L) ⊔ S, SecActs φ y (Equiv.swap 0 1) := by
  have hgY : g ∈ (secM t S L ⊓ L) ⊔ S := Subgroup.mem_sup_right hgS
  have hgNN := (sec123_Y_le F hS hgY).1
  obtain ⟨σ, hσ⟩ := hS5 g hgNN
  have hodd : Equiv.Perm.sign σ = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · exact absurd (z4o_mem_K_of_even F hperm hgNN.1 hσ
        (Equiv.Perm.mem_alternatingGroup.mpr h)) hgK
    · exact h
  have hτ : σ⁻¹ * Equiv.swap 0 1 ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hodd,
      Equiv.Perm.sign_swap (by decide : (0 : Fin 5) ≠ 1)]
    decide
  obtain ⟨m, hm, hmτ⟩ := hperm.2.2.2.2 _ hτ
  refine ⟨g * m, mul_mem hgY (Subgroup.mem_sup_left hm), ?_⟩
  have h := hσ.mul hmτ
  rwa [mul_inv_cancel_left] at h

end CFSG.OddStandard.SmallF3.Omega
