module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpOuter
public import CFSG.LocalAnalysis.ComponentInitial.InvolutionFixedFourGroupTransport

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

open Matrix CFSG.Assembly.LowTwoRank SymplecticFlag
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.LocalAnalysis.ComponentInitial.FixedFourGroup
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {r : ℕ} {K : Type} [Field K]

theorem mul_conj_mul_inv {G : Type*} [Group G] (η : MulAut G) (x : G) :
    η * MulAut.conj x * η⁻¹ = MulAut.conj (η x) := by
  refine MulEquiv.ext fun y => ?_
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, MulAut.inv_apply,
    map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem exists_conj_eq_minorAut_pow {m : ℕ} [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (hZ : Subgroup.center (antiSp K) = ⊥) (g : antiSp K)
    (hB : (MulAut.conj g * minorAut K ^ (2 * m + 1)) ^ 2 = 1) :
    ∃ h : antiSp K, MulAut.conj h * (MulAut.conj g * minorAut K ^ (2 * m + 1)) *
      (MulAut.conj h)⁻¹ = minorAut K ^ (2 * m + 1) := by
  set η := minorAut K ^ (2 * m + 1) with hηdef
  obtain ⟨hord, hdesc, -⟩ := even_symplectic_two_nonsquare_outer_involution_descent m hK
  have hη2 : η ^ 2 = 1 := by rw [← hord, pow_orderOf_eq_one]
  have hgg : g * η g = 1 := by
    have h1 : MulAut.conj (g * η g) = 1 := by
      calc MulAut.conj (g * η g) = MulAut.conj g * (η * MulAut.conj g * η⁻¹) := by
            rw [map_mul, mul_conj_mul_inv]
        _ = (MulAut.conj g * η) * (MulAut.conj g * η) * (η * η)⁻¹ := by group
        _ = 1 := by rw [← pow_two, ← pow_two, hB, hη2, inv_one, one_mul]
    have hc : g * η g ∈ Subgroup.center (antiSp K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h2 := congrArg (fun φ : MulAut (antiSp K) => φ y) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      calc y * (g * η g) = g * η g * y * (g * η g)⁻¹ * (g * η g) := by rw [h2]
        _ = g * η g * y := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact hc
  let x : antiSp K ⋊[(Subgroup.zpowers η).subtype] Subgroup.zpowers η :=
    ⟨g, ⟨η, Subgroup.mem_zpowers η⟩⟩
  have hx2 : x ^ 2 = 1 := by
    refine SemidirectProduct.ext ?_ ?_
    · rw [pow_two, SemidirectProduct.mul_left, SemidirectProduct.one_left]
      exact hgg
    · rw [pow_two, SemidirectProduct.mul_right, SemidirectProduct.one_right]
      refine Subtype.ext ?_
      rw [Subgroup.coe_mul, Subgroup.coe_one, ← pow_two]
      exact hη2
  obtain ⟨h, hh⟩ := hdesc x rfl hx2
  have hleft := congrArg SemidirectProduct.left hh
  rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.inv_left,
    SemidirectProduct.left_inl, SemidirectProduct.right_inl, SemidirectProduct.left_inr,
    SemidirectProduct.mul_right, SemidirectProduct.right_inl, one_mul, inv_one, map_one,
    MulAut.one_apply, MulAut.one_apply] at hleft
  refine ⟨h, ?_⟩
  calc MulAut.conj h * (MulAut.conj g * η) * (MulAut.conj h)⁻¹ =
      MulAut.conj (h * g) * (η * MulAut.conj h⁻¹ * η⁻¹) * η := by
        rw [map_mul, map_inv]
        group
    _ = MulAut.conj (h * g * η h⁻¹) * η := by rw [mul_conj_mul_inv, ← map_mul]
    _ = η := by
        rw [show h * g * η h⁻¹ = 1 from hleft, map_one, one_mul]

end CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
