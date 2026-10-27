module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOrthSplitCJ

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.RankTwoStandard
open scoped Matrix

variable {G : Type} [Group G] {A : Subgroup G} {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  {H : Subgroup (GL ι K)} {e : rankTwoQuot A ≃* StatedProj H}

theorem unipGL_inv {E : Matrix ι ι K} (hE : E * E = 0) (s : K) :
    (unipGL E hE s)⁻¹ = unipGL E hE (-s) := by
  rw [inv_eq_iff_mul_eq_one, unipGL_mul, add_neg_cancel, unipGL_zero]

theorem commute_of_conj_eq_smul [CharP K 2] (hZ : Odd (Nat.card (center ↥A))) {p : G}
    (hp2 : p ^ 2 = 1) {M : GL ι K} (hpM : Represents e p M) {u : G}
    (hu : ⁅A ⊓ centralizer ({p} : Set G), A ⊓ centralizer ({p} : Set G)⁆ ≤
      centralizer ({u} : Set G))
    {U : GL ι K} (hU : Represents e u U) {d : GL ι K} (hd : d ∈ H) (hdM : d * M = M * d)
    {E : Matrix ι ι K} (hE : E * E = 0) (hEM : E * M = M * E) (hEH : ∀ t : K, unipGL E hE t ∈ H)
    {ρ : K} (hρ : ρ ≠ 1)
    (hdE : (d : Matrix ι ι K) * E * ((d⁻¹ : GL ι K) : Matrix ι ι K) = ρ • E) :
    (U : Matrix ι ι K) * E = E * U := by
  set s₀ := (ρ - 1)⁻¹ with hs₀
  have hρ1 : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ
  obtain ⟨h, hh⟩ := exists_represents_of_mem (e := e) hd
  obtain ⟨s, hs2, hs⟩ := exists_represents_sq_eq_one hZ (hEH s₀) (unipGL_sq hE s₀)
  have hcM : ∀ t : K, unipGL E hE t * M = M * unipGL E hE t := fun t => Units.ext (by
    rw [Units.val_mul, Units.val_mul, coe_unipGL, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hEM])
  have hhp : h * p = p * h := commute_of_represents hZ hh hpM hp2 hdM
  have hsp : s * p = p * s := commute_of_represents hZ hs hpM hp2 (hcM s₀)
  have hhC : h ∈ A ⊓ centralizer ({p} : Set G) :=
    mem_inf.mpr ⟨hh.1, mem_centralizer_singleton_iff.mpr hhp⟩
  have hsC : s ∈ A ⊓ centralizer ({p} : Set G) :=
    mem_inf.mpr ⟨hs.1, mem_centralizer_singleton_iff.mpr hsp⟩
  have hcu := mem_centralizer_singleton_iff.mp (hu (commutator_mem_commutator hhC hsC))
  rw [commutatorElement_def] at hcu
  have hconj : d * unipGL E hE s₀ * d⁻¹ = unipGL E hE (ρ * s₀) := Units.ext (by
    rw [Units.val_mul, Units.val_mul, coe_unipGL, coe_unipGL, Matrix.mul_add, Matrix.mul_one,
      Matrix.add_mul, Units.mul_inv, Matrix.mul_smul, Matrix.smul_mul, hdE, smul_smul,
      mul_comm s₀])
  have hrep : Represents e (h * s * h⁻¹ * s⁻¹) (unipGL E hE 1) := by
    have h1 := ((hh.mul hs).mul hh.inv).mul hs.inv
    rwa [hconj, unipGL_inv, unipGL_mul, show ρ * s₀ + -s₀ = 1 by
      rw [hs₀]; field_simp; ring] at h1
  have h1 := hU.mul_comm_of_commute hrep (unipGL_sq hE 1) hcu.symm
  rw [coe_unipGL, one_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h1
  exact add_left_cancel h1

theorem central_of_commute_all [CharP K 2] (hZ : Odd (Nat.card (center ↥A))) {p : G}
    {M : GL ι K} (hpM : Represents e p M) (hM2 : M ^ 2 = 1) {u : G} (hu2 : u ^ 2 = 1)
    {U : GL ι K} (hU : Represents e u U)
    (hcent : ∀ X ∈ H, X * M = M * X → X * U = U * X) :
    ∀ a ∈ A ⊓ centralizer ({p} : Set G), a * u * a⁻¹ = u := by
  intro a ha
  obtain ⟨haA, hap⟩ := mem_inf.mp ha
  obtain ⟨X, hX⟩ := exists_represents e haA
  have hXM : X * M = M * X := Units.ext (by
    rw [Units.val_mul, Units.val_mul]
    exact hX.mul_comm_of_commute hpM hM2 (mem_centralizer_singleton_iff.mp hap))
  have hXU := hcent X hX.2.1 hXM
  have h1 := (hX.mul hU).mul hX.inv
  rw [hXU, mul_inv_cancel_right] at h1
  have h2 : (a * u * a⁻¹) ^ 2 ^ 1 = 1 := by rw [pow_one, conj_pow, hu2, mul_one, mul_inv_cancel]
  exact eq_of_represents hZ h1 hU h2 (k' := 1) (by rw [pow_one]; exact hu2)

end CFSG.ComponentClassification.RankTwoClassical
