module

public import CFSG.ClassicalInvolution.Phan.PhanB20Cent
public import CFSG.ClassicalInvolution.Phan.PhanB16Bij
public import CFSG.ClassicalInvolution.Phan.PhanB1Coord
public import CFSG.ClassicalInvolution.Phan.PhanD1Family
public import CFSG.ClassicalInvolution.Phan.PhanD5Mat

public section

namespace CFSG.ClassicalInvolution.PhanB3

open Matrix
open CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock mat_longBlock longBlock_injective)
open CFSG.ClassicalInvolution.Asc77.B3C (twShort)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ClassicalInvolution.PhanD4 (negOne coe_negOne)
open scoped MatrixGroups

section Data

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {hK : Nat.card K = (p ^ f) ^ 2} {F : Type} [Field F] [Algebra F K]
  (Q : QData F K (unitaryInvolution K p f)) (c d : F) (hcd : c * c + d * d = -1)
  (h2 : (2 : F) ≠ 0)

theorem twShort_injective : Function.Injective (twShort h2) := by
  have ht : 2 * (2 : F)⁻¹ = 1 := mul_inv_cancel₀ h2
  intro A B h
  have h' := congrArg (mat 2 F) h
  rw [mat_twShort h2, mat_twShort h2] at h'
  have e00 := congrFun (congrFun h' (Sum.inl 0)) (Sum.inl 0)
  have e01 := congrFun (congrFun h' (Sum.inl 0)) (Sum.inl 1)
  have e20 := congrFun (congrFun h' (Sum.inr 0)) (Sum.inl 0)
  have e21 := congrFun (congrFun h' (Sum.inr 0)) (Sum.inl 1)
  simp [twMat, Matrix.fromBlocks] at e00 e01 e20 e21
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp <;> grind

theorem sHom_injective : Function.Injective (sHom Q c d hcd h2) :=
  (twShort_injective h2).comp (nuQ_injective Q c d hcd h2)

theorem lHom_injective : Function.Injective (lHom Q c d hcd h2) := by
  have ht : 2 * (2 : F)⁻¹ = 1 := mul_inv_cancel₀ h2
  exact (longBlock_injective (1 : Fin 2)).comp
    ((conjD_injective (2⁻¹ : F) ht).comp (nuQ_injective Q c (-d) (hcd_neg hcd) h2))

theorem sHom_range (hK : Nat.card K = (p ^ f) ^ 2) :
    (sHom Q c d hcd h2).range = (twShort h2).range := by
  have hs : (nuQ Q c d hcd).range = ⊤ :=
    MonoidHom.range_eq_top.mpr (nuQ_surjective Q c d hK hcd h2)
  show ((twShort h2).comp (nuQ Q c d hcd)).range = _
  rw [MonoidHom.range_comp, hs, ← MonoidHom.range_eq_map]

theorem lHom_range (hK : Nat.card K = (p ^ f) ^ 2) :
    (lHom Q c d hcd h2).range = (longBlock F 2 1).range := by
  have ht : 2 * (2 : F)⁻¹ = 1 := mul_inv_cancel₀ h2
  have hs : ((conjD (2⁻¹ : F) ht).comp (nuQ Q c (-d) (hcd_neg hcd))).range = ⊤ :=
    MonoidHom.range_eq_top.mpr ((conjD_surjective (2⁻¹ : F) ht).comp
      (nuQ_surjective Q c (-d) hK (hcd_neg hcd) h2))
  show ((longBlock F 2 1).comp
    ((conjD (2⁻¹ : F) ht).comp (nuQ Q c (-d) (hcd_neg hcd)))).range = _
  rw [MonoidHom.range_comp, hs, ← MonoidHom.range_eq_map]

theorem center_le_rel (z : StatedSp 2 F) (hz : z ∈ Subgroup.center (StatedSp 2 F)) :
    z ∈ (sHom Q c d hcd h2).range := by
  have ht : 2 * (2 : F)⁻¹ = 1 := mul_inv_cancel₀ h2
  obtain ⟨u, hu2, hmat⟩ := CFSG.ClassicalInvolution.WeakCT.center_sp_scalar hz
  have hu : (u : F) = 1 ∨ (u : F) = -1 := by
    have : (u : F) * (u : F) = 1 := by rw [← pow_two]; exact hu2
    exact mul_self_eq_one_iff.mp this
  rcases hu with hu | hu
  · have : z = 1 := by
      apply mat_injective
      rw [mat_apply, hmat, hu]
      simp
    rw [this]
    exact (sHom Q c d hcd h2).range.one_mem
  · refine ⟨torusTwo (unitaryInvolution K p f) (negOne (unitaryInvolution K p f)), ?_⟩
    apply mat_injective
    rw [mat_sHom, nuOf_torus, mat_apply, hmat, hu]
    have hre : Q.re ((((negOne (unitaryInvolution K p f)) : Kˣ)) : K) = -1 := by
      rw [coe_negOne, Q.re_neg, Q.re_one]
    have him : Q.im ((((negOne (unitaryInvolution K p f)) : Kˣ)) : K) = 0 := by
      rw [coe_negOne, Q.im_neg, Q.im_one, neg_zero]
    rw [hre, him]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [twMat, nuMat, Matrix.fromBlocks, Matrix.scalar_apply] <;> grind

@[expose] noncomputable def b2CoordOfData (hK : Nat.card K = (p ^ f) ^ 2) :
    B2Coord hK F h2 where
  ℓ := lHom Q c d hcd h2
  s := sHom Q c d hcd h2
  ℓ_inj := lHom_injective Q c d hcd h2
  s_inj := sHom_injective Q c d hcd h2
  ℓ_range := lHom_range Q c d hcd h2 hK
  s_range := sHom_range Q c d hcd h2 hK
  comm_tor := comm_tor_rel Q c d hcd h2
  conj_ℓ_s := conj_ℓ_s_rel Q c d hcd h2
  conj_s_ℓ := conj_s_ℓ_rel Q c d hcd h2
  cent := fun x₀ hx₀ g h1 h3 => cent_rel Q c d hcd h2 x₀ hx₀ g h1 h3
  center_le := fun z hz => center_le_rel Q c d hcd h2 z hz

end Data

theorem b2Coord_exists (p f : ℕ) [Fact p.Prime] (hmod : p ^ f % 4 = 3)
    (hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2)
    (h2 : (2 : GaloisField p f) ≠ 0) (hf : 1 ≤ f) : Nonempty (B2Coord hK (GaloisField p f) h2) := by
  have hF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  let _ : Algebra (GaloisField p f) (GaloisField p (2 * f)) :=
    Classical.choice (CFSG.ClassicalInvolution.Models.OrthogonalPairs.Aniso.nonempty_algebra hF hK)
  obtain ⟨Q⟩ := QData.exists_of_card hF hK hmod
  obtain ⟨a, b, hab⟩ := CharP.sq_add_sq (GaloisField p f) p (-1)
  refine ⟨b2CoordOfData Q (a : GaloisField p f) (b : GaloisField p f) ?_ h2 hK⟩
  push_cast at hab
  linear_combination hab

end CFSG.ClassicalInvolution.PhanB3
