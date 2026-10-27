module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128CentMat

@[expose] public section

namespace CFSG.OddStandard.SmallF3.Omega

abbrev S8P : Type := Multiplicative (EvW × EvW)

abbrev S8A : Type := MulAut S8P

def s8dAp (f : S8A) (p : EvW × EvW) : EvW × EvW :=
  Multiplicative.toAdd (f (Multiplicative.ofAdd p))

theorem s8dAp_mul (f g : S8A) (p : EvW × EvW) : s8dAp (f * g) p = s8dAp f (s8dAp g p) := rfl

theorem s8dAp_one (p : EvW × EvW) : s8dAp 1 p = p := rfl

theorem s8dAp_add (f : S8A) (p q : EvW × EvW) : s8dAp f (p + q) = s8dAp f p + s8dAp f q :=
  map_mul f (Multiplicative.ofAdd p) (Multiplicative.ofAdd q)

theorem s8dAp_zero (f : S8A) : s8dAp f 0 = 0 := map_one f

theorem s8dAp_inv_ap (f : S8A) (p : EvW × EvW) : s8dAp f⁻¹ (s8dAp f p) = p :=
  f.symm_apply_apply (Multiplicative.ofAdd p)

theorem s8dAp_ap_inv (f : S8A) (p : EvW × EvW) : s8dAp f (s8dAp f⁻¹ p) = p :=
  f.apply_symm_apply (Multiplicative.ofAdd p)

theorem s8d_ext {f g : S8A} (h : ∀ p, s8dAp f p = s8dAp g p) : f = g :=
  MulEquiv.ext fun x => h (Multiplicative.toAdd x)

def s8dOfAdd (e : (EvW × EvW) ≃+ (EvW × EvW)) : S8A := AddEquiv.toMultiplicative e

theorem s8dAp_ofAdd (e : (EvW × EvW) ≃+ (EvW × EvW)) (p : EvW × EvW) :
    s8dAp (s8dOfAdd e) p = e p := rfl

def s8dPermE (σ : Equiv.Perm (Fin 5)) : EvW ≃+ EvW where
  toFun := permW σ
  invFun := permW σ⁻¹
  left_inv a := Subtype.ext (by
    show permVec σ⁻¹ (permVec σ a.1) = a.1
    rw [← permVec_mul, inv_mul_cancel, permVec_one])
  right_inv a := Subtype.ext (by
    show permVec σ (permVec σ⁻¹ a.1) = a.1
    rw [← permVec_mul, mul_inv_cancel, permVec_one])
  map_add' := (permW σ).map_add

def s8dProd : Equiv.Perm (Fin 5) × Equiv.Perm (Fin 5) →* S8A where
  toFun st := s8dOfAdd ((s8dPermE st.1).prodCongr (s8dPermE st.2))
  map_one' := s8d_ext fun _ => rfl
  map_mul' _ _ := s8d_ext fun _ => rfl

def s8dDiag : Equiv.Perm (Fin 5) →* S8A :=
  s8dProd.comp ((MonoidHom.id (Equiv.Perm (Fin 5))).prod (MonoidHom.id (Equiv.Perm (Fin 5))))

theorem s8dDiag_eq (σ : Equiv.Perm (Fin 5)) : s8dDiag σ = s8dProd (σ, σ) := rfl

theorem s8dAp_diag (σ : Equiv.Perm (Fin 5)) (p : EvW × EvW) :
    s8dAp (s8dDiag σ) p = (permW σ p.1, permW σ p.2) := rfl

def s8dProdA : ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5)) →* S8A :=
  s8dProd.comp ((alternatingGroup (Fin 5)).subtype.prodMap (alternatingGroup (Fin 5)).subtype)

theorem s8dProdA_eq (x : ↥(alternatingGroup (Fin 5)) × ↥(alternatingGroup (Fin 5))) :
    s8dProdA x = s8dProd ((x.1 : Equiv.Perm (Fin 5)), (x.2 : Equiv.Perm (Fin 5))) := rfl

def s8dThetaE (T : (Matrix (Fin 2) (Fin 2) (ZMod 2))ˣ) : (EvW × EvW) ≃+ (EvW × EvW) where
  toFun := thetaW (T : Matrix (Fin 2) (Fin 2) (ZMod 2))
  invFun := thetaW (↑T⁻¹ : Matrix (Fin 2) (Fin 2) (ZMod 2))
  left_inv p := by
    have h := congrArg (fun φ : (EvW × EvW) →+ (EvW × EvW) => φ p)
      (sec128_thetaW_mul (↑T⁻¹ : Matrix (Fin 2) (Fin 2) (ZMod 2)) T)
    simp only [Units.inv_mul, sec128_thetaW_one, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply] at h
    exact h.symm
  right_inv p := by
    have h := congrArg (fun φ : (EvW × EvW) →+ (EvW × EvW) => φ p)
      (sec128_thetaW_mul (T : Matrix (Fin 2) (Fin 2) (ZMod 2)) ↑T⁻¹)
    simp only [Units.mul_inv, sec128_thetaW_one, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply] at h
    exact h.symm
  map_add' := map_add _

def s8dTheta : (Matrix (Fin 2) (Fin 2) (ZMod 2))ˣ →* S8A where
  toFun T := s8dOfAdd (s8dThetaE T)
  map_one' := s8d_ext fun p => by
    show thetaW (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) p = p
    rw [sec128_thetaW_one]
    rfl
  map_mul' T T' := s8d_ext fun p => by
    show thetaW ((T : Matrix (Fin 2) (Fin 2) (ZMod 2)) * T') p = thetaW T (thetaW T' p)
    rw [sec128_thetaW_mul]
    rfl

theorem s8dAp_theta (T : (Matrix (Fin 2) (Fin 2) (ZMod 2))ˣ) (p : EvW × EvW) :
    s8dAp (s8dTheta T) p = thetaW (T : Matrix (Fin 2) (Fin 2) (ZMod 2)) p := rfl

def s8dG : ↥(alternatingGroup (Fin 5)) :=
  ⟨finRotate 5, by rw [Equiv.Perm.mem_alternatingGroup, sign_finRotate]; decide⟩

def s8dSplit (T : (Matrix (Fin 2) (Fin 2) (ZMod 2))ˣ) : S8A :=
  s8dTheta T * s8dProd (finRotate 5, 1) * (s8dTheta T)⁻¹

theorem s8d_permW_smul (σ : Equiv.Perm (Fin 5)) (c : ZMod 2) (a : EvW) :
    permW σ (c • a) = c • permW σ a :=
  rfl

theorem s8dTheta_comm_diag (T : (Matrix (Fin 2) (Fin 2) (ZMod 2))ˣ) (σ : Equiv.Perm (Fin 5)) :
    s8dTheta T * s8dDiag σ = s8dDiag σ * s8dTheta T := by
  refine s8d_ext fun p => ?_
  rw [s8dAp_mul, s8dAp_mul, s8dAp_theta, s8dAp_diag, s8dAp_diag, s8dAp_theta,
    sec128_thetaW_apply, sec128_thetaW_apply]
  simp only [map_add, s8d_permW_smul]

end CFSG.OddStandard.SmallF3.Omega
