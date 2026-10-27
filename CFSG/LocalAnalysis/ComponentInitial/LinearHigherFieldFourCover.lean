module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFixedLift
public import CFSG.LocalAnalysis.ComponentInitial.LinearFieldFourKernelBound

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFlag

open Subgroup CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def autTransfer {Q P : Type*} [Group Q] [Group P] (e : Q ≃* P) :
    MulAut Q →* MulAut P where
  toFun φ := (e.symm.trans φ).trans e
  map_one' := by
    ext x
    simp
  map_mul' φ ψ := by
    ext x
    simp

theorem autTransfer_apply {Q P : Type*} [Group Q] [Group P] (e : Q ≃* P) (φ : MulAut Q)
    (x : P) : autTransfer e φ x = e (φ (e.symm x)) :=
  rfl

theorem autTransfer_injective {Q P : Type*} [Group Q] [Group P] (e : Q ≃* P) :
    Function.Injective (autTransfer e) := fun φ ψ h => by
  ext x
  have := congrArg (fun χ : MulAut P => χ (e x)) h
  simp only [autTransfer_apply, MulEquiv.symm_apply_apply] at this
  exact e.injective this

theorem card_center_sq_eq_one_le_four (A : Type) [Group A] [Finite A] [Group.IsPerfect A]
    (hQ : CFSG.Blueprint.LieModel (A ⧸ center A) .PSL 3 2 2) :
    Nat.card {z : (QuotientGroup.mk' (center A)).ker // z ^ 2 = 1} ≤ 4 := by
  classical
  set π := QuotientGroup.mk' (center A) with hπ
  have hK : π.ker ≤ center A := by rw [hπ, QuotientGroup.ker_mk']
  have hsurj : Function.Surjective (quotientLift hK) :=
    quotientLift_surjective hK (QuotientGroup.mk'_surjective _)
  obtain ⟨-, -, -, ⟨f, hf⟩, -⟩ :=
    LinearFieldFourKernel.field_four_linear_three_central_two_kernel_rank_and_exponent_bound
      (quotientLift hK) hsurj (ker_quotientLift_le_center hK) (isPGroup_ker_quotientLift hK) hQ
  have h1 := FixedLift.card_sq_eq_one_le_of_surjective (fun x y => mul_comm x y) f.rangeRestrict
    f.rangeRestrict_surjective
  have h4 : Nat.card {x : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) // x ^ 2 = 1} = 4 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hmem : ∀ z : π.ker, ((z : A) : A ⧸ oddPart π.ker hK) ∈ f.range := fun z => by
    rw [hf, MonoidHom.mem_ker, quotientLift_mk]
    exact z.2
  have hsq : ∀ z : {z : π.ker // z ^ 2 = 1}, ((z.1 : A)) ^ 2 = 1 := fun z => by
    have := congrArg Subtype.val z.2
    simpa using this
  let g : {z : π.ker // z ^ 2 = 1} → {w : f.range // w ^ 2 = 1} := fun z =>
    ⟨⟨((z.1 : A) : A ⧸ oddPart π.ker hK), hmem z.1⟩, Subtype.ext (by
      change (((z.1 : A) : A ⧸ oddPart π.ker hK)) ^ 2 = 1
      rw [← QuotientGroup.mk_pow, hsq z, QuotientGroup.mk_one])⟩
  have hginj : Function.Injective g := by
    intro z₁ z₂ h
    have h' : ((z₁.1 : A) : A ⧸ oddPart π.ker hK) = ((z₂.1 : A) : A ⧸ oddPart π.ker hK) :=
      congrArg (fun w : {w : f.range // w ^ 2 = 1} => ((w.1 : f.range) : A ⧸ oddPart π.ker hK)) h
    have hodd := (mem_oddPart.mp (QuotientGroup.eq.mp h')).2
    have hc : Commute ((z₁.1 : A)⁻¹) (z₂.1 : A) := mem_center_iff.mp (hK z₂.1.2) _
    have hsq' : ((z₁.1 : A)⁻¹ * z₂.1) ^ 2 = 1 := by
      rw [hc.mul_pow, inv_pow, hsq z₁, hsq z₂, inv_one, one_mul]
    have hord : orderOf ((z₁.1 : A)⁻¹ * z₂.1) = 1 := by
      have hdvd := orderOf_dvd_of_pow_eq_one hsq'
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exact h1
      · rw [h2] at hodd
        exact absurd hodd (by decide)
    rw [orderOf_eq_one_iff, inv_mul_eq_one] at hord
    exact Subtype.ext (Subtype.ext hord)
  calc Nat.card {z : π.ker // z ^ 2 = 1} ≤ Nat.card {w : f.range // w ^ 2 = 1} :=
        Nat.card_le_card_of_injective g hginj
    _ ≤ _ := h1
    _ = 4 := h4

end LinearFlag

end CFSG.LocalAnalysis.ComponentInitial
