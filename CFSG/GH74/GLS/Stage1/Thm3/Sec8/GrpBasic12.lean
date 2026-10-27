module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic

open Subgroup

section ConjMulAut

variable {G : Type*} [Group G]

@[expose] def conjMulAut {Nn M : Subgroup G} (hM : ∀ n ∈ Nn, ∀ m ∈ M, n * m * n⁻¹ ∈ M)
    (n : G) (hn : n ∈ Nn) : MulAut ↥M where
  toFun m := ⟨n * m * n⁻¹, hM n hn m m.2⟩
  invFun m := ⟨n⁻¹ * m * n, by simpa using hM n⁻¹ (inv_mem hn) m m.2⟩
  left_inv m := Subtype.ext (by simp [mul_assoc])
  right_inv m := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem conjMulAut_apply {Nn M : Subgroup G} (hM : ∀ n ∈ Nn, ∀ m ∈ M, n * m * n⁻¹ ∈ M)
    (n : G) (hn : n ∈ Nn) (m : ↥M) :
    ((conjMulAut hM n hn m : ↥M) : G) = n * m * n⁻¹ := rfl

end ConjMulAut

theorem exists_mul_mem_normalizer {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Nn M P : Subgroup G} (hMN : M ≤ Nn) (hM : ∀ n ∈ Nn, ∀ m ∈ M, n * m * n⁻¹ ∈ M)
    (hPM : P ≤ M) (hP : IsPGroup p ↥P) (hind : ¬ p ∣ P.relIndex M) :
    ∀ n ∈ Nn, ∃ m ∈ M, ∃ x ∈ normalizer (P : Set G), n = m * x := by
  intro n hn
  let P₀ : Sylow p ↥M := (hP.comap_subtype (K := M)).toSylow hind
  have hP₀ : ∀ y : ↥M, y ∈ (P₀ : Subgroup ↥M) ↔ (y : G) ∈ P := fun y => Iff.rfl
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq ↥M (conjMulAut hM n hn • P₀) P₀
  have h1 := congrArg (fun Q : Sylow p ↥M => (Q : Subgroup ↥M)) hm
  simp only [Sylow.coe_subgroup_smul, Sylow.pointwise_smul_def] at h1
  have key : ∀ y : ↥M, y ∈ (P₀ : Subgroup ↥M) ↔ ∃ s ∈ (P₀ : Subgroup ↥M),
      ((m : G) * n) * (s : G) * ((m : G) * n)⁻¹ = (y : G) := by
    intro y
    rw [← SetLike.ext_iff.1 h1 y, Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨s', hs', rfl⟩
      rw [Subgroup.mem_smul_pointwise_iff_exists] at hs'
      obtain ⟨s, hs, rfl⟩ := hs'
      refine ⟨s, hs, ?_⟩
      show _ = (m : G) * (n * (s : G) * n⁻¹) * (m : G)⁻¹
      group
    · rintro ⟨s, hs, hsy⟩
      refine ⟨conjMulAut hM n hn s, ?_, ?_⟩
      · exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).2 ⟨s, hs, rfl⟩
      · apply Subtype.ext
        show (m : G) * (n * (s : G) * n⁻¹) * (m : G)⁻¹ = y
        rw [← hsy]
        group
  have hxM : ∀ z ∈ M, ((m : G) * n) * z * ((m : G) * n)⁻¹ ∈ M :=
    hM _ (Nn.mul_mem (hMN m.2) hn)
  refine ⟨(m : G)⁻¹, M.inv_mem m.2, (m : G) * n, ?_, by group⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hhM : h ∈ M := hPM hh
    exact (hP₀ ⟨_, hxM h hhM⟩).1 ((key ⟨_, hxM h hhM⟩).2 ⟨⟨h, hhM⟩, (hP₀ _).2 hh, rfl⟩)
  · intro hh
    have hhM : ((m : G) * n) * h * ((m : G) * n)⁻¹ ∈ M := hPM hh
    obtain ⟨s, hs, hsy⟩ := (key ⟨_, hhM⟩).1 ((hP₀ ⟨_, hhM⟩).2 hh)
    have hsh : (s : G) = h := by
      have h3 := hsy
      simpa using h3
    rw [← hsh]
    exact (hP₀ s).1 hs

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic
