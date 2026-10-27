module

public import CFSG.ClassicalInvolution.SmallCases.EndpointsOrthPatternSpLift
public import CFSG.ClassicalInvolution.RouteD.GapsPerfect
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Basic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance.Sp

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation
  (odd_symplectic_automorphism_semilinear_representation)
open CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)

variable {F : Type} [Field F]

theorem exists_semilinear_lift_conj [Finite F] (hodd : ringChar F ≠ 2) (h4 : 4 ≤ Nat.card F)
    {X : Type} [Group X] (ψ : StatedSp 2 F →* X) (hker : ψ.ker ≤ Subgroup.center (StatedSp 2 F))
    (hnorm : ψ.range.Normal) (d : X) :
    ∃ (A : gsp 2 F) (σ : F ≃+* F), ∀ x : StatedSp 2 F,
      d * ψ x * d⁻¹ = ψ (conjSp 2 F A (fieldSp 2 F σ x)) := by
  classical
  have hperf : Group.IsPerfect (StatedSp 2 F) :=
    (CFSG.LieType.Universal.Symplectic.isQuasisimple 2 F (by norm_num)
      (Or.inl (Or.inr h4))).1
  have := hnorm
  obtain ⟨β, hβ, -⟩ := exists_mulEquiv_of_central_cover (π := proj 2 F) (proj_surjective)
    (CFSG.ClassicalInvolution.RouteD.ker_proj_eq_center 2) (θ := ψ.rangeRestrict)
    ψ.rangeRestrict_surjective (by rwa [MonoidHom.ker_rangeRestrict]) (MulAut.conjNormal d)
  obtain ⟨hall, -, -⟩ := odd_symplectic_automorphism_semilinear_representation (r := 2) hodd le_rfl
  obtain ⟨A, σ, hAσ⟩ := hall β
  refine ⟨A, σ, ?_⟩
  let α : StatedSp 2 F →* StatedSp 2 F :=
    (conjSp 2 F A).toMonoidHom.comp (fieldSp 2 F σ).toMonoidHom
  have hα : ∀ x, proj 2 F (α x) = β (proj 2 F x) := fun x => by
    rw [hAσ, MulAut.mul_apply, fieldAut_proj, conjAut_proj]
    rfl
  intro x
  have h := congrArg Subtype.val (hβ α hα x)
  have h' : d * ψ x * d⁻¹ = ψ (α x) := by simpa [MulAut.conjNormal_apply] using h.symm
  exact h'

theorem hom_eq_of_central_ker {G X L : Type*} [Group G] [Group X] [Group L] [Group.IsPerfect L]
    (θ : G →* X) (hker : θ.ker ≤ Subgroup.center G) (f h : L →* G)
    (hfh : ∀ l, θ (f l) = θ (h l)) : f = h := by
  have hmem : ∀ l, (h l)⁻¹ * f l ∈ Subgroup.center G := fun l => by
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hfh l, inv_mul_cancel]
  let z : L →* Subgroup.center G :=
    { toFun := fun l => ⟨(h l)⁻¹ * f l, hmem l⟩
      map_one' := by simp
      map_mul' := fun l₁ l₂ => by
        apply Subtype.ext
        have hc := Subgroup.mem_center_iff.mp (hmem l₁)
        simp only [map_mul, mul_inv_rev, Subgroup.coe_mul]
        calc (h l₂)⁻¹ * (h l₁)⁻¹ * (f l₁ * f l₂)
            = (h l₂)⁻¹ * ((h l₁)⁻¹ * f l₁) * f l₂ := by group
          _ = ((h l₁)⁻¹ * f l₁) * (h l₂)⁻¹ * f l₂ := by rw [hc ((h l₂)⁻¹)]
          _ = ((h l₁)⁻¹ * f l₁) * ((h l₂)⁻¹ * f l₂) := by group }
  have hz : z = 1 := CFSG.ClassicalInvolution.RouteD.Gaps.hom_eq_one_of_perfect_of_solvable z
  refine MonoidHom.ext fun l => ?_
  have := congrArg (fun w : Subgroup.center G => (w : G)) (DFunLike.congr_fun hz l)
  simp only [MonoidHom.one_apply, z, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_one] at this
  exact inv_mul_eq_one.mp this |>.symm

section Center

variable {n : ℕ}

@[expose] noncomputable def negOne : StatedSp n F :=
  ofSymplecticMat (-1) (by simp)

theorem mat_negOne : mat n F negOne = -1 := rfl

theorem negOne_mul_self : (negOne : StatedSp n F) * negOne = 1 :=
  mat_injective (by rw [map_mul, mat_negOne, map_one]; simp)

theorem negOne_ne_one [NeZero n] (h2 : (2 : F) ≠ 0) : (negOne : StatedSp n F) ≠ 1 := by
  intro h
  have := congrFun (congrFun (congrArg (mat n F) h) (Sum.inl (0 : Fin n))) (Sum.inl 0)
  rw [mat_negOne, map_one] at this
  simp at this
  apply h2
  linear_combination (-1 : F) * this

theorem mem_center_iff [NeZero n] {x : StatedSp n F} :
    x ∈ Subgroup.center (StatedSp n F) ↔ x = 1 ∨ x = negOne := by
  constructor
  · intro hx
    rw [CFSG.LieType.Universal.Symplectic.center_eq, Subgroup.mem_subgroupOf] at hx
    obtain ⟨c, hc⟩ := hx
    have hm : mat n F x = Matrix.scalar _ (c : F) := by
      rw [mat_apply, ← hc]
      rfl
    have key := congrFun (congrFun (mat_transpose_mul_gram_mul x) (Sum.inl (0 : Fin n))) (Sum.inr 0)
    rw [transpose_mul_gram_mul_apply, hm, Finset.sum_eq_single (Sum.inl (0 : Fin n))] at key
    · have hc2 : (c : F) * c = 1 := by
        simpa [Matrix.scalar_apply, gram_apply, sgn, par] using key
      rcases mul_self_eq_one_iff.mp hc2 with h | h
      · left
        refine mat_injective ?_
        rw [hm, h, map_one]
        simp
      · right
        refine mat_injective ?_
        rw [hm, h, mat_negOne]
        ext i j
        by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
    · intro b _ hb
      simp [Matrix.scalar_apply, Matrix.diagonal_apply, hb]
    · simp
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · refine Subgroup.mem_center_iff.mpr fun g => mat_injective ?_
      rw [map_mul, map_mul, mat_negOne]
      simp

end Center

end CFSG.ClassicalInvolution.Balance.StrongBalance.Sp
