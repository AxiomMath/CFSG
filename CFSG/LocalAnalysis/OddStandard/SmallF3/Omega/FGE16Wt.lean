module

public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Polynomial
open Set DirectSum

variable {V : Type*} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (T : ι → Module.End (ZMod 3) V)

@[expose] def fgWt (χ : ι → ZMod 3) : Submodule (ZMod 3) V :=
  ⨅ i, Module.End.eigenspace (T i) (χ i)

private lemma isFinitelySemisimple_of_mul_self_eq_one
    (f : Module.End (ZMod 3) V) (hf : f * f = 1) : f.IsFinitelySemisimple := by
  have hsep : (X ^ 2 - 1 : (ZMod 3)[X]).Separable := by
    rw [X_pow_sub_one_separable_iff]
    decide
  refine (Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree
    ?_).isFinitelySemisimple
  simp only [map_sub, map_pow, aeval_X, map_one, sub_eq_zero]
  simpa [pow_two] using hf

private lemma iSup_eigenspace_eq_top_of_mul_self_eq_one
    (f : Module.End (ZMod 3) V) (hf : f * f = 1) :
    ⨆ μ : ZMod 3, f.eigenspace μ = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hff : ∀ w, f (f w) = w := by
    intro w
    rw [← Module.End.mul_apply, hf, Module.End.one_apply]
  have ha : v + f v ∈ f.eigenspace 1 := by
    rw [Module.End.mem_eigenspace_iff, map_add, hff v, one_smul]
    abel
  have hb : v - f v ∈ f.eigenspace (-1) := by
    rw [Module.End.mem_eigenspace_iff, map_sub, hff v, neg_smul, one_smul]
    abel
  have hsum : (v + f v) + (v - f v) = (2 : ZMod 3) • v := by
    rw [two_smul]
    abel
  have hmem : v ∈ f.eigenspace 1 ⊔ f.eigenspace (-1) := by
    have h2v : (2 : ZMod 3) • v ∈ f.eigenspace 1 ⊔ f.eigenspace (-1) := by
      rw [← hsum]
      exact Submodule.add_mem _ (Submodule.mem_sup_left ha) (Submodule.mem_sup_right hb)
    rw [show v = (2 : ZMod 3) • ((2 : ZMod 3) • v) by
      rw [smul_smul, show (2 : ZMod 3) * 2 = 1 by decide, one_smul]]
    exact Submodule.smul_mem _ _ h2v
  exact (sup_le (le_iSup (fun μ : ZMod 3 => f.eigenspace μ) 1)
    (le_iSup (fun μ : ZMod 3 => f.eigenspace μ) (-1))) hmem

theorem mem_fgWt {χ : ι → ZMod 3} {v : V} : v ∈ fgWt T χ ↔ ∀ i, T i v = χ i • v := by
  simp [fgWt, Module.End.mem_eigenspace_iff]

theorem fgWt_iSup_eq_top (hT : ∀ i, T i * T i = 1) (hc : ∀ i j, Commute (T i) (T j)) :
    ⨆ χ, fgWt T χ = ⊤ := by
  have hmax : ∀ i (μ : ZMod 3), (T i).maxGenEigenspace μ = (T i).eigenspace μ :=
    fun i μ =>
      (isFinitelySemisimple_of_mul_self_eq_one (T i) (hT i)).maxGenEigenspace_eq_eigenspace μ
  have hdiag : ∀ i, ⨆ μ : ZMod 3, (T i).maxGenEigenspace μ = ⊤ := by
    intro i
    rw [iSup_congr fun μ => hmax i μ]
    exact iSup_eigenspace_eq_top_of_mul_self_eq_one (T i) (hT i)
  have htop :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      T (fun i j _ => hc i j) hdiag
  have hfg : ∀ χ : ι → ZMod 3, fgWt T χ = ⨅ i, (T i).maxGenEigenspace (χ i) := by
    intro χ
    rw [fgWt]
    exact iInf_congr fun i => (hmax i (χ i)).symm
  rw [iSup_congr hfg]
  exact htop

theorem fgWt_iSupIndep (hc : ∀ i j, Commute (T i) (T j)) : iSupIndep (fgWt T) := by
  have hmap : ∀ i j φ, MapsTo (T i) ((T j).maxGenEigenspace φ) ((T j).maxGenEigenspace φ) :=
    fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) φ
  refine (Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo T hmap).mono fun χ => ?_
  rw [fgWt]
  exact le_iInf fun i => (iInf_le _ i).trans Module.End.eigenspace_le_maxGenEigenspace

theorem fgWt_finrank_sum (hT : ∀ i, T i * T i = 1) (hc : ∀ i j, Commute (T i) (T j)) :
    ∑ χ : ι → ZMod 3, Module.finrank (ZMod 3) (fgWt T χ) = Module.finrank (ZMod 3) V := by
  have hint : DirectSum.IsInternal (fgWt T) :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top (fgWt T)).mpr
      ⟨fgWt_iSupIndep T hc, fgWt_iSup_eq_top T hT hc⟩
  have hle : Module.finrank (ZMod 3) (⨁ χ : ι → ZMod 3, fgWt T χ) = Module.finrank (ZMod 3) V :=
    LinearEquiv.finrank_eq (LinearEquiv.ofBijective (DirectSum.coeLinearMap (fgWt T)) hint)
  rw [← hle, Module.finrank_directSum]

theorem fgWt_sq (hT : ∀ i, T i * T i = 1) {χ : ι → ZMod 3} (h : fgWt T χ ≠ ⊥) (i : ι) :
    χ i * χ i = 1 := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff (fgWt T χ)).mp h
  rw [mem_fgWt] at hv
  have h1 := hv i
  have h2 : v = (χ i * χ i) • v := by
    calc v = (T i * T i) v := by rw [hT i, Module.End.one_apply]
      _ = T i (T i v) := by rw [Module.End.mul_apply]
      _ = T i (χ i • v) := by rw [h1]
      _ = χ i • T i v := by rw [map_smul]
      _ = χ i • (χ i • v) := by rw [h1]
      _ = (χ i * χ i) • v := by rw [smul_smul]
  have h3 : (χ i * χ i - 1) • v = 0 := by
    rw [sub_smul, one_smul, ← h2, sub_self]
  rcases smul_eq_zero.mp h3 with h4 | h4
  · exact sub_eq_zero.mp h4
  · exact absurd h4 hv0

theorem fgWt_mul {χ : ι → ZMod 3} (h : fgWt T χ ≠ ⊥) {i j k : ι} (hk : T k = T i * T j) :
    χ k = χ i * χ j := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff (fgWt T χ)).mp h
  rw [mem_fgWt] at hv
  have hk' : (T i * T j) v = χ k • v := by
    rw [← hk]
    exact hv k
  have hij : (T i * T j) v = (χ j * χ i) • v := by
    rw [Module.End.mul_apply, hv j, map_smul, hv i, smul_smul]
  have h2 : χ k • v = (χ i * χ j) • v := by
    rw [← hk', hij, mul_comm (χ j) (χ i)]
  have h3 : (χ k - χ i * χ j) • v = 0 := by
    rw [sub_smul, h2, sub_self]
  rcases smul_eq_zero.mp h3 with h4 | h4
  · exact sub_eq_zero.mp h4
  · exact absurd h4 hv0

theorem fgWt_one {χ : ι → ZMod 3} (h : fgWt T χ ≠ ⊥) {i : ι} (hi : T i = 1) : χ i = 1 := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff (fgWt T χ)).mp h
  rw [mem_fgWt] at hv
  have h1 := hv i
  rw [hi, Module.End.one_apply] at h1
  have h3 : (χ i - 1) • v = 0 := by
    rw [sub_smul, one_smul, ← h1, sub_self]
  rcases smul_eq_zero.mp h3 with h4 | h4
  · exact sub_eq_zero.mp h4
  · exact absurd h4 hv0

end CFSG.OddStandard.SmallF3.Omega
