module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoFixedField
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear

public section

namespace CFSG.ComponentClassification.CatalogueBLinearTwoFixed

noncomputable section

open Matrix CFSG.GorensteinWalter

universe u

theorem subfield_GL_map_injective (K : Type u) [Field K] (S : Subfield K) :
    Function.Injective (Matrix.GeneralLinearGroup.map (n := Fin 2) S.subtype) := by
  intro A B h
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  apply S.subtype.injective
  exact congrArg (fun C : GL (Fin 2) K => C i j) h

@[expose] def subfieldPGLMap (K : Type u) [Field K] (S : Subfield K) :
    PGL2 S →* PGL2 K := Matrix.ProjGenLinGroup.map S.subtype

theorem subfield_GL_scalar_reflect (K : Type u) [Field K] (S : Subfield K)
    (A : GL (Fin 2) S) (c : Kˣ)
    (hA : Matrix.GeneralLinearGroup.map S.subtype A =
      Matrix.GeneralLinearGroup.scalar (Fin 2) c) :
    ∃ b : Sˣ, A = Matrix.GeneralLinearGroup.scalar (Fin 2) b := by
  have h00 : ((A 0 0 : S) : K) = (c : K) := by
    have h := congrArg (fun B : GL (Fin 2) K => B 0 0) hA
    simpa only [Matrix.GeneralLinearGroup.map_apply, Subfield.subtype_apply,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq] using h
  have hne : A 0 0 ≠ 0 := by
    intro hz
    apply c.ne_zero
    rw [← h00, hz]
    rfl
  let b : Sˣ := Units.mk0 (A 0 0) hne
  have hb : Units.map S.subtype b = c := by
    apply Units.ext
    exact h00
  refine ⟨b, subfield_GL_map_injective K S ?_⟩
  rw [Matrix.GeneralLinearGroup.map_scalar, hb]
  exact hA

theorem subfieldPGLMap_injective (K : Type u) [Field K] (S : Subfield K) :
    Function.Injective (subfieldPGLMap K S) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map S.subtype A) = 1 at hg
  rw [Matrix.ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.center_eq_range_scalar] at hg
  obtain ⟨c, hc⟩ := hg
  obtain ⟨b, hb⟩ := subfield_GL_scalar_reflect K S A c hc.symm
  rw [hb]
  exact Matrix.ProjGenLinGroup.mk_scalar b

theorem pglFieldAut_mk (K : Type u) [Field K] (sigma : K ≃+* K)
    (A : GL (Fin 2) K) :
    pgl2FieldAut K sigma (Matrix.ProjGenLinGroup.mk A) =
      Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map sigma.toRingHom A) := by
  exact pgl2RingEquiv_mk sigma A

theorem fixed_projective_scalar_norm (K : Type u) [Field K] (sigma : K ≃+* K)
    (hsigma : orderOf sigma = 2) (A : GL (Fin 2) K)
    (c : Kˣ) (hA : Matrix.GeneralLinearGroup.map sigma.toRingHom A =
      A * Matrix.GeneralLinearGroup.scalar (Fin 2) c) :
    c * Units.map sigma.toMonoidHom c = 1 := by
  have hmap2 : Matrix.GeneralLinearGroup.map sigma.toRingHom
      (Matrix.GeneralLinearGroup.map sigma.toRingHom A) = A := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    exact involution_apply_apply K sigma hsigma (A i j)
  have h := congrArg (Matrix.GeneralLinearGroup.map sigma.toRingHom) hA
  rw [hmap2, map_mul, Matrix.GeneralLinearGroup.map_scalar, hA,
    mul_assoc, ← map_mul] at h
  have hs : Matrix.GeneralLinearGroup.scalar (Fin 2)
      (c * Units.map sigma.toMonoidHom c) = 1 := by
    apply mul_left_cancel (a := A)
    simpa using h.symm
  apply Units.ext
  have h00 := congrArg (fun B : GL (Fin 2) K => B 0 0) hs
  simpa using h00

theorem fixed_projective_exists_subfield_matrix (K : Type u) [Field K]
    (sigma : K ≃+* K) (hsigma : orderOf sigma = 2) (A : GL (Fin 2) K)
    (hfixed : pgl2FieldAut K sigma (Matrix.ProjGenLinGroup.mk A) =
      Matrix.ProjGenLinGroup.mk A) :
    ∃ B : GL (Fin 2) (fixedField K sigma),
      Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map (fixedField K sigma).subtype B) =
        Matrix.ProjGenLinGroup.mk A := by
  rw [pglFieldAut_mk] at hfixed
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hfixed
  let c := u⁻¹
  have hA : Matrix.GeneralLinearGroup.map sigma.toRingHom A =
      A * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
    apply mul_right_cancel (b := Matrix.GeneralLinearGroup.scalar (Fin 2) u)
    simpa [c, mul_assoc] using hu
  have hn := fixed_projective_scalar_norm K sigma hsigma A c hA
  obtain ⟨b, hb⟩ := exists_unit_hilbert90 K sigma hsigma c hn
  let T := A * Matrix.GeneralLinearGroup.scalar (Fin 2) b
  have hT : Matrix.GeneralLinearGroup.map sigma.toRingHom T = T := by
    change Matrix.GeneralLinearGroup.map sigma.toRingHom
      (A * Matrix.GeneralLinearGroup.scalar (Fin 2) b) =
        A * Matrix.GeneralLinearGroup.scalar (Fin 2) b
    rw [Matrix.GeneralLinearGroup.map_mul]
    change Matrix.GeneralLinearGroup.map sigma.toRingHom A *
      Matrix.GeneralLinearGroup.map sigma.toRingHom
        (Matrix.GeneralLinearGroup.scalar (Fin 2) b) =
          A * Matrix.GeneralLinearGroup.scalar (Fin 2) b
    rw [hA, Matrix.GeneralLinearGroup.map_scalar]
    change A * Matrix.GeneralLinearGroup.scalar (Fin 2) c *
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map sigma.toMonoidHom b) =
        A * Matrix.GeneralLinearGroup.scalar (Fin 2) b
    rw [hb,
      mul_assoc, ← map_mul]
    simp
  obtain ⟨B, hB⟩ := exists_fixedField_GL K sigma T (fun i j =>
    congrArg (fun C : GL (Fin 2) K => C i j) hT)
  refine ⟨B, ?_⟩
  rw [hB]
  dsimp [T]
  rw [map_mul, Matrix.ProjGenLinGroup.mk_scalar, mul_one]

theorem pgl_fixed_iff_mem_subfield_range (K : Type u) [Field K]
    (sigma : K ≃+* K) (hsigma : orderOf sigma = 2) (g : PGL2 K) :
    pgl2FieldAut K sigma g = g ↔ g ∈ (subfieldPGLMap K (fixedField K sigma)).range := by
  constructor
  · intro h
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
    obtain ⟨B, hB⟩ := fixed_projective_exists_subfield_matrix K sigma hsigma A h
    exact ⟨Matrix.ProjGenLinGroup.mk B, hB⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
    change pgl2FieldAut K sigma
        (Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map (fixedField K sigma).subtype A)) =
      Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map (fixedField K sigma).subtype A)
    rw [pglFieldAut_mk]
    congr 1
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    exact fixedField_coe K sigma (A i j)

end

end CFSG.ComponentClassification.CatalogueBLinearTwoFixed
