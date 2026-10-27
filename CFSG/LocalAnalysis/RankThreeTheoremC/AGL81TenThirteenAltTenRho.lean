module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.AltTen

open Equiv Equiv.Perm

noncomputable def permEquivAut : Perm (Fin 10) ≃* MulAut (alternatingGroup (Fin 10)) :=
  MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 10)))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 10 (by norm_num)
      (by norm_num))

theorem coe_permEquivAut_apply (σ : Perm (Fin 10)) (a : alternatingGroup (Fin 10)) :
    ((permEquivAut σ a : alternatingGroup (Fin 10)) : Perm (Fin 10)) = σ * a * σ⁻¹ :=
  MulAut.conjNormal_apply σ a

variable {Y : Type*} [Group Y] {K : Subgroup Y} [K.Normal]

noncomputable def rho (eK : ↥K ≃* alternatingGroup (Fin 10)) : Y →* Perm (Fin 10) :=
  permEquivAut.symm.toMonoidHom.comp ((MulAut.congr eK).toMonoidHom.comp MulAut.conjNormal)

theorem permEquivAut_rho (eK : ↥K ≃* alternatingGroup (Fin 10)) (y : Y) :
    permEquivAut (rho eK y) = MulAut.congr eK (MulAut.conjNormal y) := by
  simp [rho]

theorem rho_conj (eK : ↥K ≃* alternatingGroup (Fin 10)) (y : Y) (k : ↥K) :
    rho eK y * (eK k : Perm (Fin 10)) * (rho eK y)⁻¹ =
      (eK (MulAut.conjNormal y k) : Perm (Fin 10)) := by
  have h := congrArg (fun φ : MulAut (alternatingGroup (Fin 10)) =>
    ((φ (eK k) : alternatingGroup (Fin 10)) : Perm (Fin 10))) (permEquivAut_rho eK y)
  simp only [coe_permEquivAut_apply] at h
  rw [h, MulAut.congr_apply]
  simp

theorem rho_coe (eK : ↥K ≃* alternatingGroup (Fin 10)) (k : ↥K) :
    rho eK (k : Y) = (eK k : Perm (Fin 10)) := by
  apply permEquivAut.injective
  ext a
  rw [permEquivAut_rho, coe_permEquivAut_apply, MulAut.congr_apply]
  have h1 : (MulAut.conjNormal (k : Y)) (eK.symm a) = k * eK.symm a * k⁻¹ := by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    simp
  simp only [MulEquiv.trans_apply, h1, map_mul, map_inv, MulEquiv.apply_symm_apply,
    Subgroup.coe_mul, Subgroup.coe_inv]

theorem rho_eq_one_iff (eK : ↥K ≃* alternatingGroup (Fin 10)) (y : Y) :
    rho eK y = 1 ↔ y ∈ Subgroup.centralizer (K : Set Y) := by
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h1 := rho_conj eK y ⟨k, hk⟩
    rw [h, one_mul, inv_one, mul_one] at h1
    have h2 : MulAut.conjNormal y ⟨k, hk⟩ = ⟨k, hk⟩ := by
      apply eK.injective
      exact Subtype.ext h1.symm
    have h3 := congrArg Subtype.val h2
    rw [MulAut.conjNormal_apply] at h3
    calc k * y = (y * k * y⁻¹) * y := by rw [h3]
      _ = y * k := by group
  · intro h
    apply permEquivAut.injective
    rw [map_one, permEquivAut_rho]
    have h1 : MulAut.conjNormal y = (1 : MulAut ↥K) := by
      ext k
      rw [MulAut.conjNormal_apply, MulAut.one_apply]
      have := Subgroup.mem_centralizer_iff.1 h (k : Y) k.2
      calc y * (k : Y) * y⁻¹ = ((k : Y) * y) * y⁻¹ := by rw [this]
        _ = k := by group
    rw [h1, map_one]

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.AltTen
