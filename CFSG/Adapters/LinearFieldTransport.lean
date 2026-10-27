module

public import CFSG.Adapters.ProjectiveSpecialLinear

public section

noncomputable section

namespace CFSG.ClassicalModels

open Matrix

@[expose] def specialLinearFieldEquiv
    {K L : Type*} [Field K] [Field L] (e : K ≃+* L)
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    SpecialLinearGroup ι K ≃* SpecialLinearGroup ι L where
  toFun := SpecialLinearGroup.map e.toRingHom
  invFun := SpecialLinearGroup.map e.symm.toRingHom
  left_inv A := by
    apply Subtype.ext
    ext i j
    exact e.symm_apply_apply (A i j)
  right_inv A := by
    apply Subtype.ext
    ext i j
    exact e.apply_symm_apply (A i j)
  map_mul' := map_mul _

theorem specialLinearFieldEquiv_map_center
    {K L : Type*} [Field K] [Field L] (e : K ≃+* L)
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (Subgroup.center (SpecialLinearGroup ι K)).map
      (specialLinearFieldEquiv e ι).toMonoidHom = Subgroup.center (SpecialLinearGroup ι L) :=
  Subgroup.map_center_eq (specialLinearFieldEquiv e ι)

@[expose] def projectiveSpecialLinearFieldEquiv
    {K L : Type*} [Field K] [Field L] (e : K ≃+* L)
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    ProjectiveSpecialLinearGroup ι K ≃* ProjectiveSpecialLinearGroup ι L :=
  QuotientGroup.congr _ _ (specialLinearFieldEquiv e ι)
    (specialLinearFieldEquiv_map_center e ι)

@[expose] def finiteFieldEquivGaloisField
    (K : Type*) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime]
    (hf : 0 < f) (hK : Nat.card K = p ^ f) : K ≃+* GaloisField p f := by
  let _ := Fintype.ofFinite K
  let _ := Fintype.ofFinite (GaloisField p f)
  apply FiniteField.ringEquivOfCardEq
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
    GaloisField.card p f hf.ne']

@[expose] def statedLinearModelEquivGaloisPSL
    (K : Type) [Field K] [Finite K] (n p f : ℕ) [Fact p.Prime]
    (hf : 0 < f) (hK : Nat.card K = p ^ f) :
    CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL n K) ≃*
      ProjectiveSpecialLinearGroup (Fin n) (GaloisField p f) :=
  (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
    (projectiveSpecialLinearFieldEquiv (finiteFieldEquivGaloisField K p f hf hK) (Fin n))

end CFSG.ClassicalModels
