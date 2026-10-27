module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8I13Ctx

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OI13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B S : Subgroup G} {α σ : G}
  (c : OI13Ctx L z t T E B β S α σ)

@[expose] noncomputable def thetaHom : ↥c.W1 →* ↥E where
  toFun w := ⟨(w : G) * (z * (w : G) * z⁻¹), c.theta_mem w.2⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' w w' := Subtype.ext (c.h.theta_mul c.hα c.hF c.hM c.hp w.2 w'.2)

@[simp] theorem thetaHom_coe (w : ↥c.W1) :
    ((c.thetaHom w : ↥E) : G) = (w : G) * (z * (w : G) * z⁻¹) := rfl

theorem thetaHom_surjective : Function.Surjective c.thetaHom := by
  intro e
  obtain ⟨w, hw, h⟩ := c.theta_surj e.2
  exact ⟨⟨w, hw⟩, Subtype.ext h.symm⟩

theorem thetaHom_eq_one {w : ↥c.W1} : c.thetaHom w = 1 ↔ (w : G) = 1 ∨ (w : G) = t := by
  rw [← Subtype.coe_inj]
  exact c.h.theta_eq_one_iff c.hα w.2

theorem thetaHom_eq_iff {w w' : ↥c.W1} :
    c.thetaHom w = c.thetaHom w' ↔ (w' : G) = w ∨ (w' : G) = w * t := by
  rw [← Subtype.coe_inj]
  exact c.h.theta_eq_iff c.hα c.hF c.hM c.hp w.2 w'.2

@[expose] noncomputable def conjW1 (n : ↥c.N1) : ↥c.W1 →* ↥c.W1 where
  toFun w := ⟨(n : G) * w * (n : G)⁻¹, c.N1_W1 n.2 w.2⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' w w' := by
    apply Subtype.ext
    show (n : G) * ((w : G) * w') * (n : G)⁻¹ =
      (n : G) * w * (n : G)⁻¹ * ((n : G) * w' * (n : G)⁻¹)
    group

@[simp] theorem conjW1_coe (n : ↥c.N1) (w : ↥c.W1) :
    ((c.conjW1 n w : ↥c.W1) : G) = (n : G) * w * (n : G)⁻¹ := rfl

theorem conjW1_mul (n n' : ↥c.N1) (w : ↥c.W1) :
    c.conjW1 (n * n') w = c.conjW1 n (c.conjW1 n' w) := by
  apply Subtype.ext
  show ((n * n' : ↥c.N1) : G) * w * ((n * n' : ↥c.N1) : G)⁻¹ =
    (n : G) * ((n' : G) * w * (n' : G)⁻¹) * (n : G)⁻¹
  simp only [Subgroup.coe_mul]
  group

theorem conjW1_one (w : ↥c.W1) : c.conjW1 1 w = w := by
  apply Subtype.ext
  simp

theorem ker_theta_le (n : ↥c.N1) : c.thetaHom.ker ≤ (c.thetaHom.comp (c.conjW1 n)).ker := by
  intro w hw
  rw [MonoidHom.mem_ker] at hw ⊢
  rw [MonoidHom.comp_apply, c.thetaHom_eq_one]
  rcases c.thetaHom_eq_one.1 hw with h1 | h1
  · left; rw [conjW1_coe, h1]; group
  · right; rw [conjW1_coe, h1]; exact c.Nc_t (c.N1_le_Nc n.2)

@[expose] noncomputable def actHom (n : ↥c.N1) : ↥E →* ↥E :=
  c.thetaHom.liftOfRightInverse (Function.surjInv c.thetaHom_surjective)
    (Function.rightInverse_surjInv c.thetaHom_surjective)
    ⟨c.thetaHom.comp (c.conjW1 n), c.ker_theta_le n⟩

theorem actHom_theta (n : ↥c.N1) (w : ↥c.W1) :
    c.actHom n (c.thetaHom w) = c.thetaHom (c.conjW1 n w) :=
  c.thetaHom.liftOfRightInverse_comp_apply (Function.surjInv c.thetaHom_surjective)
    (Function.rightInverse_surjInv c.thetaHom_surjective)
    ⟨c.thetaHom.comp (c.conjW1 n), c.ker_theta_le n⟩ w

theorem actHom_mul (n n' : ↥c.N1) (e : ↥E) :
    c.actHom (n * n') e = c.actHom n (c.actHom n' e) := by
  obtain ⟨w, rfl⟩ := c.thetaHom_surjective e
  rw [actHom_theta, actHom_theta, actHom_theta, conjW1_mul]

theorem actHom_one (e : ↥E) : c.actHom 1 e = e := by
  obtain ⟨w, rfl⟩ := c.thetaHom_surjective e
  rw [actHom_theta, conjW1_one]

@[expose] noncomputable def rho1Aux (n : ↥c.N1) : MulAut ↥E where
  toFun := c.actHom n
  invFun := c.actHom n⁻¹
  left_inv := fun e => by rw [← actHom_mul, inv_mul_cancel, actHom_one]
  right_inv := fun e => by rw [← actHom_mul, mul_inv_cancel, actHom_one]
  map_mul' := (c.actHom n).map_mul

@[expose] noncomputable def rho1 : ↥c.N1 →* MulAut ↥E where
  toFun := c.rho1Aux
  map_one' := MulEquiv.ext fun e => c.actHom_one e
  map_mul' n n' := MulEquiv.ext fun e => c.actHom_mul n n' e

theorem rho1_theta (n : ↥c.N1) (w : ↥c.W1) :
    c.rho1 n (c.thetaHom w) = c.thetaHom (c.conjW1 n w) := c.actHom_theta n w

@[expose] noncomputable def zconjN1 : ↥c.N1 →* ↥c.N1 where
  toFun n := ⟨z * (n : G) * z⁻¹, c.z_conj_N1 n.2⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' n n' := by
    apply Subtype.ext
    show z * ((n : G) * n') * z⁻¹ = z * n * z⁻¹ * (z * n' * z⁻¹)
    group

@[simp] theorem zconjN1_coe (n : ↥c.N1) : ((c.zconjN1 n : ↥c.N1) : G) = z * (n : G) * z⁻¹ := rfl

theorem zconjN1_zconjN1 (n : ↥c.N1) : c.zconjN1 (c.zconjN1 n) = n := by
  apply Subtype.ext
  simp only [zconjN1_coe]
  exact c.z_conj_conj _

@[expose] noncomputable def rho : ↥c.N1 →* MulAut ↥E × MulAut ↥E :=
  c.rho1.prod (c.rho1.comp c.zconjN1)

theorem rho_fst (n : ↥c.N1) : (c.rho n).1 = c.rho1 n := rfl

theorem rho_snd (n : ↥c.N1) : (c.rho n).2 = c.rho1 (c.zconjN1 n) := rfl

theorem rho_zconj (n : ↥c.N1) : c.rho (c.zconjN1 n) = ((c.rho n).2, (c.rho n).1) := by
  ext1
  · rfl
  · show c.rho1 (c.zconjN1 (c.zconjN1 n)) = c.rho1 n
    rw [zconjN1_zconjN1]

end OI13Ctx

end CFSG.EvenSporadicStandard.Fin76b
