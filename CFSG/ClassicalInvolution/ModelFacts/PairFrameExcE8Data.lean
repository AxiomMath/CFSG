module

public import CFSG.LieType.Chevalley.LangWeylInvolutionReflections
public import CFSG.LieType.Steinberg.Adjoint.Presentation

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem RootSpace

def thetaE8 : Fin (Tag.rank .E8) → ℤ := ![2, 3, 4, 6, 5, 4, 3, 2]

theorem mem_rootFinset_thetaE8 : thetaE8 ∈ rootFinset .E8 := by decide +kernel

theorem isRoot_thetaE8 : IsRoot .E8 thetaE8 := mem_rootFinset.1 mem_rootFinset_thetaE8

theorem iform_thetaE8_single (i : Fin (Tag.rank .E8)) :
    iform thetaE8 (Pi.single i 1) = if i.val = 7 then 1 else 0 := by
  revert i; decide +kernel

theorem abs_iform_thetaE8_le : ∀ σ ∈ rootFinset .E8, |iform thetaE8 σ| ≤ 2 := by
  decide +kernel

theorem iform_thetaE8_eq_zero_iff : ∀ σ ∈ rootFinset .E8,
    (iform thetaE8 σ = 0 ↔ σ ⟨7, by decide⟩ = 0) := by
  decide +kernel

section Generic

variable {τ : Tag}

theorem iform_smul_smul (w : WeylGroup τ) (x y : Fin τ.rank → ℤ) :
    iform (w • x) (w • y) = iform x y := by
  obtain ⟨c, hc, h⟩ := exists_inner_ofLattice_eq_iform τ
  have h1 : inner ℝ (ofLattice (w • x)) (ofLattice (w • y)) =
      inner ℝ (ofLattice x) (ofLattice y) := by
    rw [← weylAct_ofLattice, ← weylAct_ofLattice, LinearIsometryEquiv.inner_map_map]
  rw [h, h] at h1
  have : (iform (w • x) (w • y) : ℝ) = iform x y := mul_left_cancel₀ hc.ne' h1
  exact_mod_cast this

theorem iform_self_nonneg (x : Fin τ.rank → ℤ) : 0 ≤ iform x x := by
  by_cases hx : x = 0
  · subst hx
    simp [iform]
  · exact (iform_self_pos hx).le

theorem iform_sq_le (x y : Fin τ.rank → ℤ) : iform x y ^ 2 ≤ iform x x * iform y y := by
  by_cases hy : y = 0
  · subst hy
    simp [iform]
  have hyy := iform_self_pos hy
  set a := iform y y with ha
  set b := iform x y with hb
  have h := iform_self_nonneg (a • x - b • y)
  simp only [iform_sub_left, iform_sub_right, iform_smul_left, iform_smul_right] at h
  rw [iform_comm y x, ← hb, ← ha] at h
  have h2 : a * (a * iform x x - b ^ 2) ≥ 0 := by nlinarith
  have := nonneg_of_mul_nonneg_right (by linarith : 0 ≤ a * (a * iform x x - b ^ 2)) hyy
  nlinarith


end Generic

theorem iform_self_isRoot_E8 {σ : Fin (Tag.rank .E8) → ℤ} (hσ : IsRoot .E8 σ) : iform σ σ = 2 := by
  have h : ∀ σ ∈ rootFinset .E8, iform σ σ = 2 := by decide +kernel
  exact h σ (mem_rootFinset.2 hσ)

theorem abs_iform_le_two_E8 {ρ σ : Fin (Tag.rank .E8) → ℤ} (hρ : IsRoot .E8 ρ)
    (hσ : IsRoot .E8 σ) : |iform ρ σ| ≤ 2 := by
  have h := iform_sq_le ρ σ
  rw [iform_self_isRoot_E8 hρ, iform_self_isRoot_E8 hσ] at h
  rw [abs_le]
  constructor <;> nlinarith

theorem even_iform_self_E8 (y : Fin (Tag.rank .E8) → ℤ) : Even (iform y y) := by
  have h : ∀ z : Fin (Tag.rank .E8) → ZMod 2,
      ∑ i, ∑ j, z i * ((Tag.symmetrizedCartan .E8 i j : ℤ) : ZMod 2) * z j = 0 := by
    decide +kernel
  have h2 := h fun i => (y i : ZMod 2)
  rw [even_iff_two_dvd]
  have h3 : ((iform y y : ℤ) : ZMod 2) = 0 := by
    simp only [iform]
    push_cast
    exact h2
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (iform y y) 2).1 h3


open Matrix in
theorem exists_eq_two_smul_of_even_iform_single_E8 (x : Fin (Tag.rank .E8) → ℤ)
    (hx : ∀ j, Even (iform x (Pi.single j 1))) : ∃ y : Fin (Tag.rank .E8) → ℤ, x = 2 • y := by
  have hCx : ∀ j, ((Tag.cartan .E8).mulVec x) j = iform x (Pi.single j 1) := by
    intro j
    rw [iform_single_right]
    simp [Tag.symmetrizer, Matrix.mulVec, dotProduct]
  have hinv : cartanInvE8 * Tag.cartan .E8 = 1 := mul_eq_one_comm.1 cartan_mul_cartanInvE8
  have hx' : x = cartanInvE8.mulVec ((Tag.cartan .E8).mulVec x) := by
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  choose z hz using fun j => hx j
  refine ⟨fun i => ∑ j, cartanInvE8 i j * z j, funext fun i => ?_⟩
  have h1 : x i = ∑ j, cartanInvE8 i j * (iform x (Pi.single j 1)) := by
    conv_lhs => rw [hx']
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hCx j]
    rfl
  rw [h1]
  simp only [Pi.smul_apply, hz]
  rw [two_nsmul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring


end CFSG.ClassicalInvolution.ModelFacts.Levi
