module

public import CFSG.Monster.B.Final.SeedUnit
public import CFSG.Monster.Existence.BabyTableIVOf
public import CFSG.Monster.Existence.BabyTableIIIOf
public import CFSG.Monster.Existence.BabyW2Classes
public import CFSG.Permutation.SymmetricCoxeter
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Certificates.Certificate17706

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.BMRows

open Equiv CFSG.Monster.B CFSG.Blueprint CFSG.Permutation.SymmetricCoxeter

theorem eq_one_of_commute_sym5 : ∀ σ : Perm (Fin 5), σ * swap 0 1 = swap 0 1 * σ →
    σ * finRotate 5 = finRotate 5 * σ → σ = 1 := by decide +kernel

theorem injective_of_map_ne_one {H : Type*} [Group H] (ψ : Perm (Fin 5) →* H)
    (h : ψ (swap 0 1 * swap 2 3) ≠ 1) : Function.Injective ψ := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hA : ∀ τ ∈ alternatingGroup (Fin 5), ψ τ = 1 → τ = 1 := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ψ.ker.subgroupOf (alternatingGroup (Fin 5)))
      with hb | ht
    · intro τ hτ h1
      have hmem : (⟨τ, hτ⟩ : alternatingGroup (Fin 5)) ∈
          ψ.ker.subgroupOf (alternatingGroup (Fin 5)) := Subgroup.mem_subgroupOf.2 h1
      rw [hb, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem
    · exfalso
      have hd : swap (0 : Fin 5) 1 * swap 2 3 ∈ alternatingGroup (Fin 5) := by
        rw [Equiv.Perm.mem_alternatingGroup]; decide
      have hmem : (⟨_, hd⟩ : alternatingGroup (Fin 5)) ∈
          ψ.ker.subgroupOf (alternatingGroup (Fin 5)) := by rw [ht]; exact Subgroup.mem_top _
      exact h (Subgroup.mem_subgroupOf.1 hmem)
  rw [injective_iff_map_eq_one]
  intro σ hσ
  have hcomm : ∀ τ : Perm (Fin 5), σ * τ = τ * σ := by
    intro τ
    have hc : σ * τ * σ⁻¹ * τ⁻¹ = 1 := by
      refine hA _ ?_ ?_
      · rw [Equiv.Perm.mem_alternatingGroup]
        simp only [map_mul, map_inv, mul_inv_cancel_comm, mul_inv_cancel]
      · rw [map_mul, map_mul, map_mul, map_inv, map_inv, hσ]
        group
    calc σ * τ = σ * τ * σ⁻¹ * τ⁻¹ * (τ * σ) := by group
      _ = τ * σ := by rw [hc, one_mul]
  exact eq_one_of_commute_sym5 σ (hcomm _) (hcomm _)

structure ElevenSymParts (y x₀ x₁ x₂ x₃ : NativeSporadic.B) : Prop where
  y_pow : y ^ 11 = 1
  y_ne : y ≠ 1
  sq₀ : x₀ * x₀ = 1
  sq₁ : x₁ * x₁ = 1
  sq₂ : x₂ * x₂ = 1
  sq₃ : x₃ * x₃ = 1
  br₀ : x₀ * x₁ * x₀ = x₁ * x₀ * x₁
  br₁ : x₁ * x₂ * x₁ = x₂ * x₁ * x₂
  br₂ : x₂ * x₃ * x₂ = x₃ * x₂ * x₃
  c₀₂ : x₀ * x₂ = x₂ * x₀
  c₀₃ : x₀ * x₃ = x₃ * x₀
  c₁₃ : x₁ * x₃ = x₃ * x₁
  y₀ : x₀ * y = y * x₀
  y₁ : x₁ * y = y * x₁
  y₂ : x₂ * y = y * x₂
  y₃ : x₃ * y = y * x₃
  ne₀₂ : x₀ * x₂ ≠ 1
  rank₀ : Matrix.rank (x₀.val.val - 1) = 1860
  rank₀₂ : Matrix.rank ((x₀ * x₂).val.val - 1) = 2048

theorem exists_elevenSym_parts :
    ∃ v : Fin 5 → NativeSporadic.B, ElevenSymParts (v 0) (v 1) (v 2) (v 3) (v 4) := by
  obtain ⟨Y, X0, X1, X2, X3, mY, m0, m1, m2, m3, h⟩ := Certificates.certificate17706
  obtain ⟨hy11, hy1, h0, h1, h2, h3, b0, b1, b2, c02, c03, c13, y0, y1, y2, y3, ne02, r0, r02⟩ := h
  set y := seedUnit mY (by norm_num) hy11
  set x0 := seedUnit m0 two_ne_zero (by rw [sq]; exact h0)
  set x1 := seedUnit m1 two_ne_zero (by rw [sq]; exact h1)
  set x2 := seedUnit m2 two_ne_zero (by rw [sq]; exact h2)
  set x3 := seedUnit m3 two_ne_zero (by rw [sq]; exact h3)
  have vy : bMat y = Y := bMat_seedUnit _ _ _
  have v0 : bMat x0 = X0 := bMat_seedUnit _ _ _
  have v1 : bMat x1 = X1 := bMat_seedUnit _ _ _
  have v2 : bMat x2 = X2 := bMat_seedUnit _ _ _
  have v3 : bMat x3 = X3 := bMat_seedUnit _ _ _
  have P : ElevenSymParts y x0 x1 x2 x3 :=
    { y_pow := pow_of_bMat (by rw [vy]; exact hy11)
      y_ne := ne_one_of_bMat (by rw [vy]; exact hy1)
      sq₀ := mul_self_of_bMat (by rw [v0]; exact h0)
      sq₁ := mul_self_of_bMat (by rw [v1]; exact h1)
      sq₂ := mul_self_of_bMat (by rw [v2]; exact h2)
      sq₃ := mul_self_of_bMat (by rw [v3]; exact h3)
      br₀ := bMat_injective (by simp only [map_mul, v0, v1]; exact b0)
      br₁ := bMat_injective (by simp only [map_mul, v1, v2]; exact b1)
      br₂ := bMat_injective (by simp only [map_mul, v2, v3]; exact b2)
      c₀₂ := comm_of_bMat (by rw [v0, v2]; exact c02)
      c₀₃ := comm_of_bMat (by rw [v0, v3]; exact c03)
      c₁₃ := comm_of_bMat (by rw [v1, v3]; exact c13)
      y₀ := comm_of_bMat (by rw [v0, vy]; exact y0)
      y₁ := comm_of_bMat (by rw [v1, vy]; exact y1)
      y₂ := comm_of_bMat (by rw [v2, vy]; exact y2)
      y₃ := comm_of_bMat (by rw [v3, vy]; exact y3)
      ne₀₂ := ne_one_of_bMat (by rw [map_mul, v0, v2]; exact ne02)
      rank₀ := by
        change Matrix.rank (bMat x0 - 1) = 1860
        rw [v0]
        exact r0
      rank₀₂ := by
        change Matrix.rank (bMat (x0 * x2) - 1) = 2048
        rw [map_mul, v0, v2]
        exact r02 }
  exact ⟨![y, x0, x1, x2, x3], P⟩

section Registers

@[expose] noncomputable def b11Vec : Fin 5 → NativeSporadic.B :=
  Classical.choose exists_elevenSym_parts

@[expose] noncomputable def b11Reg (i : ℕ) : NativeSporadic.B :=
  if i = 3 then b11Vec 0 else if i = 1 then b11Vec 1 else if i = 5 then b11Vec 2
  else if i = 6 then b11Vec 3 else if i = 2 then b11Vec 4 else 1

@[expose] noncomputable def yEleven : NativeSporadic.B := b11Reg 3

end Registers

theorem b11_parts :
    ElevenSymParts yEleven (b11Reg 1) (b11Reg 5) (b11Reg 6) (b11Reg 2) :=
  Classical.choose_spec exists_elevenSym_parts

theorem exists_sym5_of_parts {y x₀ x₁ x₂ x₃ : NativeSporadic.B}
    (P : ElevenSymParts y x₀ x₁ x₂ x₃) :
    ∃ ψ : Perm (Fin 5) →* NativeSporadic.B, Function.Injective ψ ∧
      (∀ σ, ψ σ * y = y * ψ σ) ∧ ψ (swap 0 1) = x₀ ∧ ψ (swap 0 1 * swap 2 3) = x₀ * x₂ := by
  let x : ℕ → NativeSporadic.B := fun i =>
    if i = 0 then x₀ else if i = 1 then x₁ else if i = 2 then x₂ else if i = 3 then x₃ else 1
  have hx : IsCoxeterA 4 x := by
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i j hij hj => ?_⟩
    · interval_cases i
      · exact P.sq₀
      · exact P.sq₁
      · exact P.sq₂
      · exact P.sq₃
    · have hi3 : i < 3 := by omega
      interval_cases i
      · exact P.br₀
      · exact P.br₁
      · exact P.br₂
    · have hi2 : i < 2 := by omega
      interval_cases i
      · have hj2 : 2 ≤ j := by omega
        interval_cases j
        · exact P.c₀₂
        · exact P.c₀₃
      · obtain rfl : j = 3 := by omega
        exact P.c₁₃
  have hxy : ∀ i < 4, x i * y = y * x i := by
    intro i hi
    interval_cases i
    · exact P.y₀
    · exact P.y₁
    · exact P.y₂
    · exact P.y₃
  obtain ⟨ψ, hψ⟩ := exists_hom_perm 4 x hx
  have h0 : ψ (swap 0 1) = x₀ := by
    have := hψ 0 (by norm_num)
    rwa [adjSwap_of_lt (by norm_num : 0 < 4)] at this
  have h2 : ψ (swap 2 3) = x₂ := by
    have := hψ 2 (by norm_num)
    rwa [adjSwap_of_lt (by norm_num : 2 < 4)] at this
  have h02 : ψ (swap 0 1 * swap 2 3) = x₀ * x₂ := by rw [map_mul, h0, h2]
  have hle : Subgroup.closure (adjSwap 4 '' Set.Iio 4) ≤
      (Subgroup.centralizer ({y} : Set NativeSporadic.B)).comap ψ := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, hψ i hi]
    exact hxy i hi
  have hgen : ∀ σ, ψ σ * y = y * ψ σ := by
    intro σ
    have hσ : σ ∈ (Subgroup.centralizer ({y} : Set NativeSporadic.B)).comap ψ := by
      apply hle
      rw [closure_adjSwap]
      exact Subgroup.mem_top σ
    have h1 : ψ σ ∈ Subgroup.centralizer ({y} : Set NativeSporadic.B) := Subgroup.mem_comap.1 hσ
    exact (Subgroup.mem_centralizer_singleton_iff (G := NativeSporadic.B)).1 h1
  refine ⟨ψ, injective_of_map_ne_one ψ ?_, hgen, h0, h02⟩
  rw [h02]
  exact P.ne₀₂

end CFSG.HardMathSupport.Dickson.BMRows
