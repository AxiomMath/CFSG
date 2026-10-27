module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFGForm
public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFSpStd

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.SpL

open Matrix CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3.Q3NM
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Q3.TL4.Gauss
open CFSG.LocalAnalysis.ComponentInitial (SymplecticTorusWeyl.mem_statedSp_iff)
open scoped MatrixGroups

section Plane

variable {K W : Type} [Field K] [AddCommGroup W] [Module K W]

@[expose] noncomputable def phiLin (e f : W) : (Fin 2 → K) →ₗ[K] W :=
  (LinearMap.proj 0).smulRight e + (LinearMap.proj 1).smulRight f

theorem phiLin_apply (e f : W) (x : Fin 2 → K) : phiLin e f x = x 0 • e + x 1 • f := rfl

theorem beta_phiLin {β : LinearMap.BilinForm K W} (hskew : ∀ u v, β u v = -β v u)
    (hself : ∀ v, β v v = 0) {e f : W} (hef : β e f = 1) (x y : Fin 2 → K) :
    β (phiLin e f x) (phiLin e f y) = x 0 * y 1 - x 1 * y 0 := by
  have hfe : β f e = -1 := by rw [hskew, hef]
  simp only [phiLin_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, hself, hef, hfe]
  ring

theorem phiLin_injective {β : LinearMap.BilinForm K W} (hskew : ∀ u v, β u v = -β v u)
    (hself : ∀ v, β v v = 0) {e f : W} (hef : β e f = 1) :
    Function.Injective (phiLin (K := K) e f) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have h1 := beta_phiLin hskew hself hef ![1, 0] x
  have h2 := beta_phiLin hskew hself hef x ![0, 1]
  rw [hx, map_zero] at h1
  rw [hx, map_zero, LinearMap.zero_apply] at h2
  funext i
  fin_cases i
  · simpa using h2.symm
  · simpa using h1.symm

theorem det_mul_std (X : Matrix (Fin 2) (Fin 2) K) (x y : Fin 2 → K) :
    (X *ᵥ x) 0 * (X *ᵥ y) 1 - (X *ᵥ x) 1 * (X *ᵥ y) 0 = X.det * (x 0 * y 1 - x 1 * y 0) := by
  simp only [mulVec, dotProduct, Fin.sum_univ_two, det_fin_two]
  ring

end Plane

section SpMat

variable {F : Type} [Field F] {n : ℕ}

theorem omega_mulVec_eq (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    (u v : Fin n ⊕ Fin n → F) :
    omega F n (M *ᵥ u) (M *ᵥ v) = u ⬝ᵥ ((Mᵀ * formJ n F * M) *ᵥ v) := by
  rw [omega_apply]
  have e1 : ∀ w, (M *ᵥ u) ⬝ᵥ w = u ⬝ᵥ (Mᵀ *ᵥ w) := fun w => by
    rw [dotProduct_comm, dotProduct_mulVec, mulVec_transpose, dotProduct_comm]
  rw [e1, mulVec_mulVec, mulVec_mulVec]

theorem mem_statedSp_of_omega {g : GL (Fin n ⊕ Fin n) F}
    (h : ∀ u v, omega F n ((g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ u)
      ((g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ v) = omega F n u v) :
    g ∈ StatedSp n F := by
  classical
  rw [SymplecticTorusWeyl.mem_statedSp_iff]
  ext i j
  have h1 := h (Pi.single i 1) (Pi.single j 1)
  rw [omega_mulVec_eq, omega_apply] at h1
  have e : ∀ N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F,
      Pi.single i (1 : F) ⬝ᵥ (N *ᵥ Pi.single j 1) = N i j := fun N => by
    rw [single_dotProduct, one_mul, mulVec_single_one]
    rfl
  rw [e, e] at h1
  exact h1

theorem omega_of_mem_statedSp {g : GL (Fin n ⊕ Fin n) F} (hg : g ∈ StatedSp n F)
    (u v : Fin n ⊕ Fin n → F) :
    omega F n ((g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ u)
      ((g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ v) = omega F n u v := by
  rw [omega_mulVec_eq, SymplecticTorusWeyl.mem_statedSp_iff.mp hg, omega_apply]

end SpMat

end CFSG.ClassicalInvolution.Q3.TL4.SpL
