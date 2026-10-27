module

public import CFSG.LargeExtraspecial.S4Basic
public import CFSG.LargeExtraspecial.S4Weak
public import CFSG.LargeExtraspecial.S5Comp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S5

open Subgroup Module CFSG.LargeExtraspecial.S4 CFSG.Open CFSG.ComponentClassification

variable {G : Type*} [Group G] [Finite G]

structure SwapData (S : Setting G) (g : G) where
  Z : Subgroup S.O
  t : S.O
  isComponentOf : IsComponentOf Z S.Mbar
  mem_Lbar : t ∈ S.Lbar g
  ne : Z.map (MulAut.conj t).toMonoidHom ≠ Z

namespace SwapData

variable {S : Setting G} {g : G} (D : SwapData S g)

@[expose] noncomputable def W : Subgroup S.O := D.Z.map (MulAut.conj D.t).toMonoidHom

theorem t_mem_Mbar : D.t ∈ S.Mbar := S.Lbar_le_Mbar g D.mem_Lbar

theorem isComponentOf_W : IsComponentOf D.W S.Mbar :=
  isComponentOf_map_conj D.isComponentOf D.t_mem_Mbar

theorem commutator_eq_bot : ⁅D.Z, D.W⁆ = ⊥ :=
  commute_of_isComponentOf_ne D.isComponentOf D.isComponentOf_W D.ne.symm

theorem mul_comm_of_mem {z w : S.O} (hz : z ∈ D.Z) (hw : w ∈ D.W) : z * w = w * z :=
  mul_comm_of_isComponentOf_ne D.isComponentOf D.isComponentOf_W D.ne.symm hz hw

theorem conj_mem_W {z : S.O} (hz : z ∈ D.Z) : D.t * z * D.t⁻¹ ∈ D.W :=
  ⟨z, hz, rfl⟩

theorem t_mul_t (H : Hyp4 S g) : D.t * D.t = 1 := S4.mul_self_of_mem_Lbar S H.conj_mem D.mem_Lbar

theorem t_inv (H : Hyp4 S g) : D.t⁻¹ = D.t := inv_eq_of_mul_eq_one_right (D.t_mul_t H)

theorem mul_comm_of_mem_W {z : S.O} (hzW : z ∈ D.W) {y : S.O} (hy : y ∈ D.Z) : z * y = y * z :=
  (D.mul_comm_of_mem hy hzW).symm

theorem mul_self_eq_one (H : Hyp4 S g) {x : S.O} (hxZ : x ∈ D.Z)
    (hxN : x ∈ normalizer (S.Lbar g : Set S.O)) {k : ℕ} (hk : x ^ (2 ^ k) = 1) : x * x = 1 := by
  have hy : x⁻¹ * (D.t * x * D.t⁻¹) ∈ S.Lbar g := by
    have h1 : x⁻¹ * D.t * x⁻¹⁻¹ ∈ S.Lbar g :=
      (mem_normalizer_iff.mp (inv_mem hxN) D.t).mp D.mem_Lbar
    have := mul_mem h1 (inv_mem D.mem_Lbar)
    simpa [mul_assoc] using this
  have hyy := S4.mul_self_of_mem_Lbar S H.conj_mem hy
  have hc : x⁻¹ * (D.t * x * D.t⁻¹) = (D.t * x * D.t⁻¹) * x⁻¹ :=
    D.mul_comm_of_mem (inv_mem hxZ) (D.conj_mem_W hxZ)
  have hx2 : D.t * (x * x) * D.t⁻¹ = x * x := by
    have e : (x⁻¹ * (D.t * x * D.t⁻¹)) * (x⁻¹ * (D.t * x * D.t⁻¹)) =
        (x⁻¹ * x⁻¹) * (D.t * (x * x) * D.t⁻¹) := by
      calc (x⁻¹ * (D.t * x * D.t⁻¹)) * (x⁻¹ * (D.t * x * D.t⁻¹))
          = x⁻¹ * ((D.t * x * D.t⁻¹) * x⁻¹) * (D.t * x * D.t⁻¹) := by group
        _ = x⁻¹ * (x⁻¹ * (D.t * x * D.t⁻¹)) * (D.t * x * D.t⁻¹) := by rw [← hc]
        _ = (x⁻¹ * x⁻¹) * (D.t * (x * x) * D.t⁻¹) := by group
    rw [e] at hyy
    calc D.t * (x * x) * D.t⁻¹ = (x * x) * ((x⁻¹ * x⁻¹) * (D.t * (x * x) * D.t⁻¹)) := by group
      _ = x * x := by rw [hyy, mul_one]
  have hxxW : x * x ∈ D.W := by
    rw [← hx2]
    exact D.conj_mem_W (mul_mem hxZ hxZ)
  have hsub := D.isComponentOf.2.1
  refine eq_one_of_mem_center_of_pow S hsub (mul_mem hxZ hxZ)
    (fun y hy => D.mul_comm_of_mem_W hxxW hy) (k := k) ?_
  rw [← pow_two, ← pow_mul, mul_comm, pow_mul, hk, one_pow]

theorem inv_mul_conj_mem_Lbar {x : S.O} (hxN : x ∈ normalizer (S.Lbar g : Set S.O)) :
    x⁻¹ * (D.t * x * D.t⁻¹) ∈ S.Lbar g := by
  have h1 : x⁻¹ * D.t * x⁻¹⁻¹ ∈ S.Lbar g :=
    (mem_normalizer_iff.mp (inv_mem hxN) D.t).mp D.mem_Lbar
  have := mul_mem h1 (inv_mem D.mem_Lbar)
  simpa [mul_assoc] using this

@[expose] noncomputable def chi : D.Z →* S.O :=
  InvolutionDiagonal.homomorphism D.Z (MulAut.conj D.t) D.commutator_eq_bot

theorem chi_apply (z : D.Z) : D.chi z = (z : S.O) * (D.t * z * D.t⁻¹) := rfl

theorem chi_mem_Lbar (H : Hyp4 S g) (x : D.Z) (hxN : (x : S.O) ∈ normalizer (S.Lbar g : Set S.O))
    {k : ℕ} (hk : (x : S.O) ^ (2 ^ k) = 1) : D.chi x ∈ S.Lbar g := by
  have hxx := D.mul_self_eq_one H x.2 hxN hk
  have h := D.inv_mul_conj_mem_Lbar hxN
  rwa [inv_eq_of_mul_eq_one_right hxx, ← chi_apply] at h

end SwapData

end CFSG.LargeExtraspecial.S5
