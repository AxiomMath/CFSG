module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222Pair
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOrthSplitCJ

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] {A : Subgroup G} {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  {H : Subgroup (GL ι K)} {e : rankTwoQuot A ≃* StatedProj H}

theorem commute_of_pairOrbit [CharP K 2] (hZ : Odd (Nat.card (center ↥A))) {μ : K} (hμ0 : μ ≠ 0)
    (hμ1 : μ ≠ 1) {p : G} (hp2 : p ^ 2 = 1) {M : GL ι K} (hpM : Represents e p M) {u : G}
    (horb : ∀ a ∈ A ⊓ centralizer ({p} : Set G), a * u * a⁻¹ = u ∨ a * u * a⁻¹ = u * p)
    {U : GL ι K} (hU : Represents e u U) {E : Matrix ι ι K} (hE : E * E = 0)
    (hEM : E * M = M * E) (hEH : ∀ t : K, unipGL E hE t ∈ H) :
    (U : Matrix ι ι K) * E = E * U := by
  have hpp : p * p = 1 := by rw [← pow_two]; exact hp2
  have hcM : ∀ t : K, unipGL E hE t * M = M * unipGL E hE t := fun t => Units.ext (by
    rw [Units.val_mul, Units.val_mul, coe_unipGL, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hEM])
  have hfix : ∀ (t : K) (r : G), t ≠ 0 → Represents e r (unipGL E hE t) → r * u * r⁻¹ = u →
      (U : Matrix ι ι K) * E = E * U := by
    intro t r ht hr hru
    have hur : u * r = r * u :=
      calc u * r = r * u * r⁻¹ * r := by rw [hru]
        _ = r * u := by group
    have h1 := hU.mul_comm_of_commute hr (unipGL_sq hE t) hur
    rw [coe_unipGL, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_smul, Matrix.smul_mul] at h1
    exact smul_right_injective _ ht (add_left_cancel h1)
  have hlift : ∀ t : K, ∃ r ∈ A ⊓ centralizer ({p} : Set G), Represents e r (unipGL E hE t) :=
    fun t => by
      obtain ⟨r, -, hr⟩ := exists_represents_sq_eq_one (e := e) hZ (hEH t) (unipGL_sq hE t)
      exact ⟨r, mem_inf.mpr ⟨hr.1, mem_centralizer_singleton_iff.mpr
        (commute_of_represents hZ hr hpM hp2 (hcM t))⟩, hr⟩
  obtain ⟨r₁, hr₁C, hr₁⟩ := hlift 1
  obtain ⟨r₂, hr₂C, hr₂⟩ := hlift μ
  rcases pairOrbit_conj hpp (mem_centralizer_singleton_iff.mp (mem_inf.mp hr₁C).2)
    (horb r₁ hr₁C) with ⟨h1, -⟩ | ⟨-, -, h1, -⟩
  · exact hfix 1 r₁ one_ne_zero hr₁ h1
  rcases pairOrbit_conj hpp (mem_centralizer_singleton_iff.mp (mem_inf.mp hr₂C).2)
    (horb r₂ hr₂C) with ⟨h2, -⟩ | ⟨h2, -⟩
  · exact hfix μ r₂ hμ0 hr₂ h2
  refine hfix (1 + μ) (r₁ * r₂) (fun h => hμ1 ?_) (by rw [← unipGL_mul]; exact hr₁.mul hr₂) ?_
  · linear_combination h - CharTwo.two_eq_zero (R := K)
  · calc r₁ * r₂ * u * (r₁ * r₂)⁻¹ = r₁ * (r₂ * u * r₂⁻¹) * r₁⁻¹ := by group
      _ = u := by rw [h2, h1]

end CFSG.ComponentClassification.RankTwoClassical
