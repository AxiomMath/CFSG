module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearHigherBModel
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherLinearAutNormal

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.CatalogueBLinearSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearAction
  CFSG.ComponentClassification.CatalogueBHigherLinearField

variable {n : ℕ} {K : Type} [Field K]

theorem exists_semilinear_of_odd [Finite K] (hn : 3 ≤ n)
    {α : MulAut (ProjectiveSpecialLinearGroup (Fin n) K)} (hα : Odd (orderOf α)) :
    ∃ (A : GL (Fin n) K) (σ : K ≃+* K), α = semilinearAction n K A σ := by
  set e := CatalogueBLinearHigherB.nativeEquiv n K with he
  set β : MulAut (LinearFlag.projectiveSL n K) := MulAut.congr e.symm α with hβ
  have hβo : Odd (orderOf β) := by
    rwa [hβ, MulEquiv.orderOf_eq]
  obtain ⟨A, σ, hAσ⟩ := LinearFlag.mem_semilinearAutGroup_iff.mp
    (LinearFlag.mem_semilinearAutGroup_of_pow_odd hn hβo (pow_orderOf_eq_one β))
  have hAσ' : β = LinearFlag.conjAut n K A * LinearFlag.fieldAut n K σ := hAσ
  refine ⟨A, σ, ?_⟩
  have h1 : α = MulAut.congr e β := by
    rw [hβ]
    ext x
    simp
  rw [h1, hAσ', CatalogueBLinearHigherB.congr_semilinear]

theorem eq_of_fix_perfect {A : GL (Fin n) K} {σ : K ≃+* K}
    {X : Subgroup (SpecialLinearGroup (Fin n) K)} (hX : commutator X = ⊤)
    (hfix : ∀ x ∈ X, semilinearAction n K A σ
      (QuotientGroup.mk' (center (SpecialLinearGroup (Fin n) K)) x) =
        QuotientGroup.mk' (center (SpecialLinearGroup (Fin n) K)) x)
    {x : SpecialLinearGroup (Fin n) K} (hx : x ∈ X) : slSemilinearAction n K A σ x = x := by
  set Z := center (SpecialLinearGroup (Fin n) K) with hZ
  set ρ := slSemilinearAction n K A σ with hρ
  have hζ : ∀ y ∈ X, (ρ y)⁻¹ * y ∈ Z := by
    intro y hy
    have h := hfix y hy
    rw [semilinearAction_mk] at h
    exact QuotientGroup.eq.mp h
  have hcomm : ∀ (z : SpecialLinearGroup (Fin n) K), z ∈ Z → ∀ w, z * w = w * z := fun z hz w =>
    (mem_center_iff.mp hz w).symm
  let ζ : X →* Z :=
    { toFun := fun y => ⟨(ρ y)⁻¹ * y, hζ y y.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        change (ρ ((a : SpecialLinearGroup (Fin n) K) * b))⁻¹ * (a * b) =
          ((ρ a)⁻¹ * a) * ((ρ b)⁻¹ * b)
        rw [map_mul]
        have h1 := hcomm _ (hζ a a.2) ((ρ b)⁻¹)
        calc (ρ a * ρ b)⁻¹ * (↑a * ↑b) = (ρ b)⁻¹ * ((ρ a)⁻¹ * ↑a) * ↑b := by group
          _ = ((ρ a)⁻¹ * ↑a) * (ρ b)⁻¹ * ↑b := by rw [h1]
          _ = ((ρ a)⁻¹ * ↑a) * ((ρ b)⁻¹ * ↑b) := by group }
  have hab : ∀ a b : Z, a * b = b * a := fun a b =>
    Subtype.ext (hcomm _ a.2 _)
  have hker : commutator X ≤ ζ.ker := by
    rw [commutator_def, commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hab _ _
  rw [hX] at hker
  have h := hker (mem_top ⟨x, hx⟩)
  rw [MonoidHom.mem_ker] at h
  have h' : (ρ x)⁻¹ * x = 1 := congrArg Subtype.val h
  rw [inv_mul_eq_one] at h'
  exact h'

theorem commute_of_mem {A B : GL (Fin n) K} (h : A * B = B * A) :
    innerDiagonalAction n K A * innerDiagonalAction n K B =
      innerDiagonalAction n K B * innerDiagonalAction n K A := by
  rw [← map_mul, ← map_mul, h]

end CFSG.ComponentClassification.Foote5.OddLieCore
