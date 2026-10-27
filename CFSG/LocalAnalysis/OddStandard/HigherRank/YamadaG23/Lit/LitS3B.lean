module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitQuot2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitE16

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {X : Type*} [Group X] [Finite X] {Z A : Subgroup X} [Z.Normal]
variable {G : Type*} [Group G] [Finite G] {π : X →* G}

theorem lit_s3b (h : LitCtx Z A) (hπ : Function.Surjective π) (hk : π.ker = litP Z)
    (φ : ↥(normalizer (A : Set X)) →* Equiv.Perm (Fin 6)) (hφs : Function.Surjective φ)
    (hφk : ∀ g : ↥(normalizer (A : Set X)), φ g = 1 ↔ ∀ a ∈ A, ⁅a, (g : X)⁆ ∈ Z)
    {b : X} (hbA : b ∈ A) (hbZ : b ∉ Z) (hb : ∀ x ∈ CFSG.oddCore X, x * b = b * x) :
    ∀ a ∈ A, ∀ x ∈ CFSG.oddCore X, x * a = a * x := by
  classical
  let C : Subgroup X := Subgroup.centralizer (CFSG.oddCore X : Set X)
  have hCnormal : C.Normal := Subgroup.normal_centralizer (H := CFSG.oddCore X)
  haveI : C.Normal := hCnormal
  obtain ⟨φ', hbar, _⟩ := lit_bar h hπ hk φ hφs hφk
  have hNAW : normalizer (A : Set X) ≤ normalizer ((A ⊓ C : Subgroup X) : Set X) := by
    have htop : normalizer (C : Set X) = ⊤ := Subgroup.normalizer_eq_top (H := C)
    refine (le_inf le_rfl ?_).trans Subgroup.inf_normalizer_le_normalizer_inf
    rw [htop]; exact le_top
  have hWnorm : normalizer ((A.map π : Subgroup G) : Set G) ≤
      normalizer (((A ⊓ C : Subgroup X).map π : Subgroup G) : Set G) := by
    rw [lit_map_normalizer h hπ hk]
    exact (Subgroup.map_mono hNAW).trans (Subgroup.le_normalizer_map (H := A ⊓ C) π)
  have hWA : ((A ⊓ C : Subgroup X).map π) ≤ A.map π := Subgroup.map_mono inf_le_left
  have hbW : b ∈ A ⊓ C :=
    ⟨hbA, Subgroup.mem_centralizer_iff.mpr hb⟩
  have hπb_ne : π b ≠ 1 := by
    intro h1
    have hbP : b ∈ litP Z := hk ▸ (MonoidHom.mem_ker (f := π)).mpr h1
    have hbAZ : b ∈ A ⊓ litP Z := ⟨hbA, hbP⟩
    exact hbZ ((lit_A_inf_litP h) ▸ hbAZ)
  have hWne : ((A ⊓ C : Subgroup X).map π) ≠ ⊥ := by
    intro hbot
    have : π b ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact Subgroup.mem_map_of_mem π hbW
    exact hπb_ne (Subgroup.mem_bot.mp this)
  rcases lit_irreducible (X := G) (A := A.map π)
      (N := normalizer ((A.map π : Subgroup G) : Set G)) le_rfl hbar.card φ'
      hbar.surj hbar.ker hWA hWnorm with hbot | htop
  · exact absurd hbot hWne
  ·
    intro a ha x hx
    have hπa : π a ∈ (A ⊓ C : Subgroup X).map π := by
      rw [htop]; exact Subgroup.mem_map_of_mem π ha
    obtain ⟨w, hwW, hπw⟩ := Subgroup.mem_map.mp hπa
    have hwA : w ∈ A := (Subgroup.mem_inf.mp hwW).1
    have hwC : w ∈ Subgroup.centralizer (CFSG.oddCore X : Set X) := (Subgroup.mem_inf.mp hwW).2
    have hw_comm : x * w = w * x := (Subgroup.mem_centralizer_iff.mp hwC) x hx
    set z : X := w⁻¹ * a with hz
    have hzA : z ∈ A := by rw [hz]; exact A.mul_mem (A.inv_mem hwA) ha
    have hzP : z ∈ litP Z := by
      rw [← hk, MonoidHom.mem_ker, hz, map_mul, map_inv, hπw]
      simp
    have hzZ : z ∈ Z := by
      have hzAZ : z ∈ A ⊓ litP Z := ⟨hzA, hzP⟩
      rwa [lit_A_inf_litP h] at hzAZ
    have hz_comm : x * z = z * x := (h.central z hzZ x).symm
    have ha_eq : a = w * z := by rw [hz]; group
    calc x * a = x * (w * z) := by rw [ha_eq]
      _ = (x * w) * z := by group
      _ = (w * x) * z := by rw [hw_comm]
      _ = w * (x * z) := by group
      _ = w * (z * x) := by rw [hz_comm]
      _ = (w * z) * x := by group
      _ = a * x := by rw [← ha_eq]

end CFSG.OddStandard.HigherRank.YamadaG23
