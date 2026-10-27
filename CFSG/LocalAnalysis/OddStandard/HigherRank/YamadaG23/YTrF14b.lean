module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrMap
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrVocA
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrVocB
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrVocC

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {Γ₁ Γ₂ : Type} [Group Γ₁] [Group Γ₂] [Finite Γ₁] [Finite Γ₂] {f : Γ₁ →* Γ₂}

private lemma map_closure_pair (x y : Γ₁) :
    closure ({f x, f y} : Set Γ₂) = (closure ({x, y} : Set Γ₁)).map f := by
  rw [MonoidHom.map_closure]
  simp

theorem f14b_map_iff (hf : Function.Injective f) (gf : GFrame Γ₁) :
    (gf.map f).F14b ↔ gf.F14b := by
  have hS : (gf.map f).S = gf.S.map f := GFrame.map_S f gf
  have hB : (gf.map f).B = gf.B.map f := GFrame.map_B f gf hf
  have h1 : cen (gf.map f).B = closure {(gf.map f).b₁ * (gf.map f).b₂, (gf.map f).z} ↔
      cen gf.B = closure {gf.b₁ * gf.b₂, gf.z} := by
    have e1 : (gf.map f).b₁ * (gf.map f).b₂ = f (gf.b₁ * gf.b₂) :=
      (map_mul f gf.b₁ gf.b₂).symm
    have e2 : (gf.map f).z = f gf.z := GFrame.map_z f gf
    simp only [hB, cen_map hf, e1, e2, map_closure_pair]
    exact (Subgroup.map_injective hf).eq_iff
  have h2 : cen (gf.map f).B = omega1 (zSeries 2 (gf.map f).S) ↔
      cen gf.B = omega1 (zSeries 2 gf.S) := by
    simp only [hB, hS, cen_map hf, zSeries_map hf, omega1_map hf]
    exact (Subgroup.map_injective hf).eq_iff
  have h3 : IsMaximalIn (gf.map f).S (gf.map f).B ↔ IsMaximalIn gf.S gf.B := by
    simp only [hS, hB]
    exact isMaximalIn_map hf (gf.S) (gf.B)
  have h4 : ¬ IsCyclic ↥(cen (gf.map f).B) ↔ ¬ IsCyclic ↥(cen gf.B) := by
    rw [hB, cen_map hf]
    exact (isCyclic_map hf (cen gf.B)).not
  have h5 : (∀ M : Subgroup Γ₂, IsMaximalIn (gf.map f).S M →
        ¬ IsCyclic ↥(cen M) → M = (gf.map f).B) ↔
      (∀ M : Subgroup Γ₁, IsMaximalIn gf.S M → ¬ IsCyclic ↥(cen M) → M = gf.B) := by
    constructor
    · intro h M hmax hcyc
      have hmax' : IsMaximalIn (gf.map f).S (M.map f) := by
        rw [hS]
        exact (isMaximalIn_map hf (gf.S) M).mpr hmax
      have hcyc' : ¬ IsCyclic ↥(cen (M.map f)) := by
        rw [cen_map hf]
        exact (isCyclic_map hf (cen M)).not.mpr hcyc
      have hMeq : M.map f = (gf.map f).B := h (M.map f) hmax' hcyc'
      rw [hB] at hMeq
      exact (Subgroup.map_injective hf).eq_iff.mp hMeq
    · intro h M hmax hcyc
      have hle : M ≤ (gf.map f).S := le_of_lt hmax.1
      rw [hS] at hle
      obtain ⟨M₁, _hM₁le, hM₁eq⟩ := exists_eq_map_of_le hf (V := gf.S) hle
      have hmax₁ : IsMaximalIn gf.S M₁ := by
        have hmax' : IsMaximalIn (gf.S.map f) (M₁.map f) := by
          rw [← hS, hM₁eq]
          exact hmax
        exact (isMaximalIn_map hf (gf.S) M₁).mp hmax'
      have hcyc₁ : ¬ IsCyclic ↥(cen M₁) := by
        rw [← hM₁eq, cen_map hf] at hcyc
        exact (isCyclic_map hf (cen M₁)).not.mp hcyc
      have hM₁ : M₁ = gf.B := h M₁ hmax₁ hcyc₁
      rw [hM₁, ← hB] at hM₁eq
      exact hM₁eq.symm
  have h6 : thompsonSubgroup (gf.map f).S = thompsonSubgroup (gf.map f).B ↔
      thompsonSubgroup gf.S = thompsonSubgroup gf.B := by
    simp only [hS, hB, thompsonSubgroup_map hf]
    exact (Subgroup.map_injective hf).eq_iff
  have hstep : (gf.map f).a₁ * (gf.map f).a₂ * (gf.map f).h₀
      = f (gf.a₁ * gf.a₂ * gf.h₀) := by
    rw [show (gf.map f).a₁ = f gf.a₁ from rfl,
      show (gf.map f).a₂ = f gf.a₂ from rfl,
      show (gf.map f).h₀ = f gf.h₀ from rfl, ← map_mul, ← map_mul]
  have hcl : closure ({(gf.map f).b₁,
      (gf.map f).a₁ * (gf.map f).a₂ * (gf.map f).h₀} : Set Γ₂) =
      (closure {gf.b₁, gf.a₁ * gf.a₂ * gf.h₀} : Subgroup Γ₁).map f := by
    rw [show (gf.map f).b₁ = f gf.b₁ from rfl, hstep, map_closure_pair]
  have h7 : thompsonSubgroup (gf.map f).B =
        closure {(gf.map f).b₁, (gf.map f).a₁ * (gf.map f).a₂ * (gf.map f).h₀} ↔
      thompsonSubgroup gf.B = closure {gf.b₁, gf.a₁ * gf.a₂ * gf.h₀} := by
    simp only [hB, thompsonSubgroup_map hf, hcl]
    exact (Subgroup.map_injective hf).eq_iff
  have h8 : Nonempty (↥(closure {(gf.map f).b₁,
        (gf.map f).a₁ * (gf.map f).a₂ * (gf.map f).h₀} : Subgroup Γ₂) ≃*
        Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) ↔
      Nonempty (↥(closure {gf.b₁, gf.a₁ * gf.a₂ * gf.h₀} : Subgroup Γ₁) ≃*
        Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) := by
    rw [hcl]
    exact nonempty_equiv_map hf (closure {gf.b₁, gf.a₁ * gf.a₂ * gf.h₀})
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))
  have h9 : cen (gf.map f).B = omega1 (thompsonSubgroup (gf.map f).B) ↔
      cen gf.B = omega1 (thompsonSubgroup gf.B) := by
    simp only [hB, cen_map hf, thompsonSubgroup_map hf, omega1_map hf]
    exact (Subgroup.map_injective hf).eq_iff
  have h10 : (∀ y ∈ thompsonSubgroup (gf.map f).B,
        (gf.map f).h₀ * y * (gf.map f).h₀⁻¹ = y⁻¹) ↔
      (∀ y ∈ thompsonSubgroup gf.B, gf.h₀ * y * gf.h₀⁻¹ = y⁻¹) := by
    simp only [hB, thompsonSubgroup_map hf]
    constructor
    · intro h y hy
      have hy' : f y ∈ (thompsonSubgroup gf.B).map f := Subgroup.mem_map_of_mem f hy
      have h2 : f (gf.h₀ * y * gf.h₀⁻¹) = f y⁻¹ := by
        simpa only [map_mul, map_inv, GFrame.map] using h (f y) hy'
      exact hf h2
    · intro h y hy
      obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.mp hy
      have h2 : (gf.map f).h₀ * f y₀ * ((gf.map f).h₀)⁻¹ = (f y₀)⁻¹ := by
        simpa only [map_mul, map_inv, GFrame.map] using congrArg f (h y₀ hy₀)
      exact h2
  simp only [GFrame.F14b]
  exact and_congr h1 (and_congr h2 (and_congr h3 (and_congr h4 (and_congr h5
    (and_congr h6 (and_congr h7 (and_congr h8 (and_congr h9 h10))))))))

end CFSG.OddStandard.HigherRank.YamadaG23
