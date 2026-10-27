module

public import CFSG.LieType.Chevalley.LangWeylInvolutionReflections
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExcLayerTwistShape
public import CFSG.LieType.Chevalley.ParabolicRootFactorData
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ClassicalInvolution.ModelFacts.LeviE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem RootSpace CFSG.ClassicalInvolution.RouteD.Exotic

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

section E6

@[expose] def thetaE6 : Fin (Tag.rank .E6) → ℤ := (![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ)

theorem thetaE6_eq_e6Theta : thetaE6 = e6Theta := rfl

theorem isRoot_thetaE6 : IsRoot .E6 thetaE6 := isRoot_e6Theta

@[expose] def JE6 : Set (Fin (Tag.rank .E6)) := {j | j.val ≠ 1}

theorem iform_eq_sum_single' (θ v : Fin (Tag.rank .E6) → ℤ) :
    iform θ v = ∑ j, v j * iform θ (Pi.single j 1) := by
  simp only [iform, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem iform_thetaE6_single_eq (j : Fin (Tag.rank .E6)) :
    iform thetaE6 (Pi.single j 1) = if j.val = 1 then 1 else 0 := by
  fin_cases j <;> decide

theorem iform_thetaE6_eq (v : Fin (Tag.rank .E6) → ℤ) :
    iform thetaE6 v = v ⟨1, by decide⟩ := by
  rw [iform_eq_sum_single']
  simp only [iform_thetaE6_single_eq]
  rw [Finset.sum_eq_single (⟨1, by decide⟩ : Fin (Tag.rank .E6))]
  · simp
  · intro b _ hb
    have : b.val ≠ 1 := fun h => hb (Fin.ext h)
    simp [this]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem coeff_two_le_E6 {σ : Fin (Tag.rank .E6) → ℤ} (hσ : IsRoot .E6 σ) :
    |σ ⟨1, by decide⟩| ≤ 2 := by
  have h : ∀ σ ∈ rootFinset .E6, |σ ⟨1, by decide⟩| ≤ 2 := by decide +kernel
  exact h σ (mem_rootFinset.2 hσ)

theorem abs_iform_thetaE6_le {σ : Fin (Tag.rank .E6) → ℤ} (hσ : IsRoot .E6 σ) :
    |iform thetaE6 σ| ≤ 2 := by
  rw [iform_thetaE6_eq]
  exact coeff_two_le_E6 hσ

theorem mem_parabolicRoots_E6 {σ : Fin (Tag.rank .E6) → ℤ} (hσ : IsRoot .E6 σ)
    (h : iform thetaE6 σ = 0) : σ ∈ parabolicRoots .E6 JE6 := by
  refine ⟨hσ, fun i hi => ?_⟩
  have hi1 : i.val = 1 := by
    by_contra h1
    exact hi h1
  have : i = ⟨1, by decide⟩ := Fin.ext hi1
  rw [this]
  rw [iform_thetaE6_eq] at h
  exact h

theorem iform_self_isRoot_E6 {σ : Fin (Tag.rank .E6) → ℤ} (hσ : IsRoot .E6 σ) :
    iform σ σ = 2 := by
  have h : ∀ σ ∈ rootFinset .E6, iform σ σ = 2 := by decide +kernel
  exact h σ (mem_rootFinset.2 hσ)

theorem abs_iform_le_two_E6 {ρ σ : Fin (Tag.rank .E6) → ℤ} (hρ : IsRoot .E6 ρ)
    (hσ : IsRoot .E6 σ) : |iform ρ σ| ≤ 2 := by
  have h := iform_sq_le ρ σ
  rw [iform_self_isRoot_E6 hρ, iform_self_isRoot_E6 hσ] at h
  rw [abs_le]
  constructor <;> nlinarith

theorem even_iform_self_E6 (y : Fin (Tag.rank .E6) → ℤ) : Even (iform y y) := by
  have h : ∀ z : Fin (Tag.rank .E6) → ZMod 2,
      ∑ i, ∑ j, z i * ((TwistTag.E6.tag.symmetrizedCartan i j : ℤ) : ZMod 2) * z j = 0 := by
    decide +kernel
  have h2 := h fun i => (y i : ZMod 2)
  rw [even_iff_two_dvd]
  have h3 : ((iform y y : ℤ) : ZMod 2) = 0 := by
    simp only [iform]
    push_cast
    exact h2
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (iform y y) 2).1 h3

@[expose] def cartanAdjE6 : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  !![4, 3, 5, 6, 4, 2; 3, 6, 6, 9, 6, 3; 5, 6, 10, 12, 8, 4; 6, 9, 12, 18, 12, 6;
    4, 6, 8, 12, 10, 5; 2, 3, 4, 6, 5, 4]

theorem cartanAdjE6_mul : cartanAdjE6 * Tag.cartan .E6 =
    (3 : ℤ) • (1 : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) := by
  decide +kernel

open Matrix in
theorem exists_eq_two_smul_of_even_iform_single_E6_aux (x : Fin Tag.E6.rank → ℤ)
    (hx : ∀ j, Even (iform x (Pi.single j 1))) : ∃ y : Fin Tag.E6.rank → ℤ, x = 2 • y := by
  have hCx : ∀ j, ((Tag.cartan .E6).mulVec x) j = iform x (Pi.single j 1) := by
    intro j
    rw [iform_single_right]
    simp [Tag.symmetrizer, Matrix.mulVec, dotProduct]
  have h3 : ∀ i, 3 * x i = ∑ j, cartanAdjE6 i j * iform x (Pi.single j 1) := by
    intro i
    have h2 : (cartanAdjE6.mulVec ((Tag.cartan .E6).mulVec x)) i = 3 * x i := by
      rw [Matrix.mulVec_mulVec, cartanAdjE6_mul]
      simp
    calc 3 * x i = (cartanAdjE6.mulVec ((Tag.cartan .E6).mulVec x)) i := h2.symm
      _ = ∑ j, cartanAdjE6 i j * ((Tag.cartan .E6).mulVec x) j := rfl
      _ = ∑ j, cartanAdjE6 i j * iform x (Pi.single j 1) := by simp only [hCx]
  choose z hz using fun j => hx j
  have h4 : ∀ i, 3 * x i = 2 * ∑ j, cartanAdjE6 i j * z j := by
    intro i
    rw [h3 i, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hz j]
    ring
  refine ⟨fun i => ∑ j, cartanAdjE6 i j * z j - x i, funext fun i => ?_⟩
  simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat]
  have := h4 i
  linarith

theorem exists_eq_two_smul_of_even_iform_single_E6 (x : Fin (Tag.rank .E6) → ℤ)
    (hx : ∀ j, Even (iform x (Pi.single j 1))) :
    ∃ y : Fin (Tag.rank .E6) → ℤ, x = 2 • y :=
  exists_eq_two_smul_of_even_iform_single_E6_aux x hx

end E6

end CFSG.ClassicalInvolution.ModelFacts.LeviE6
