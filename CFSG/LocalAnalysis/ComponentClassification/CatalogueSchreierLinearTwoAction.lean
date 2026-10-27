module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoSemilinear

public section

namespace CFSG.ComponentClassification.CatalogueSchreierLinearTwo

noncomputable section

open CFSG.GorensteinWalter
open scoped Pointwise

universe u

@[expose] def pslRangeEquiv (K : Type u) [Field K] :
    PSL2 K ≃* (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range :=
  MulEquiv.ofBijective Matrix.ProjectiveSpecialLinearGroup.toPGL.rangeRestrict
    ⟨fun _ _ h => Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
      (congrArg Subtype.val h), Matrix.ProjectiveSpecialLinearGroup.toPGL.rangeRestrict_surjective⟩

theorem pslRangeEquiv_coe (K : Type u) [Field K] (x : PSL2 K) :
    ((pslRangeEquiv K x : Matrix.ProjectiveSpecialLinearGroup.toPGL.range) : PGL2 K) =
      Matrix.ProjectiveSpecialLinearGroup.toPGL x := rfl

@[expose] def pglAction (K : Type u) [Field K] : PGL2 K →* MulAut (PSL2 K) := by
  let H := (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range
  let : H.Normal := pglPSLRange_normal K
  exact (MulAut.congr (pslRangeEquiv K).symm).toMonoidHom.comp
    (MulAut.conjNormal (H := H))

theorem toPGL_pglAction (K : Type u) [Field K] (g : PGL2 K) (x : PSL2 K) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL (pglAction K g x) =
      g * Matrix.ProjectiveSpecialLinearGroup.toPGL x * g⁻¹ := by
  let H := (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range
  let : H.Normal := pglPSLRange_normal K
  let e : PSL2 K ≃* H := pslRangeEquiv K
  change ((e (pglAction K g x) : H) : PGL2 K) = _
  have he : e (pglAction K g x) = (MulAut.conjNormal (H := H) g) (e x) := by
    change e (e.symm ((MulAut.conjNormal (H := H) g) (e x))) = _
    exact e.apply_symm_apply _
  rw [he, MulAut.conjNormal_apply]
  rfl

theorem pglAction_toPGL (K : Type u) [Field K] (x : PSL2 K) :
    pglAction K (Matrix.ProjectiveSpecialLinearGroup.toPGL x) = MulAut.conj x := by
  ext y
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  rw [toPGL_pglAction]
  simp [MulAut.conj_apply]

theorem pglAction_fieldAut (K : Type u) [Field K] (sigma : K ≃+* K) :
    (pglAction K).comp (((pgl2FieldAut K) sigma).toMonoidHom) =
      (MulAut.conj (psl2FieldAut K sigma)).toMonoidHom.comp (pglAction K) := by
  ext g x
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  change Matrix.ProjectiveSpecialLinearGroup.toPGL
      (pglAction K ((pgl2FieldAut K) sigma g) x) =
    Matrix.ProjectiveSpecialLinearGroup.toPGL
      (MulAut.conj ((psl2FieldAut K) sigma) (pglAction K g) x)
  rw [toPGL_pglAction, MulAut.conj_apply]
  rw [← map_inv (psl2FieldAut K) sigma, MulAut.mul_apply, MulAut.mul_apply]
  symm
  change Matrix.ProjectiveSpecialLinearGroup.toPGL
      ((psl2FieldAut K) sigma (pglAction K g ((psl2FieldAut K) sigma⁻¹ x))) = _
  rw [psl2FieldAut_toPGL, toPGL_pglAction, psl2FieldAut_toPGL]
  simp

@[expose] def semilinearAction (K : Type u) [Field K] :
    PGammaL2 K →* MulAut (PSL2 K) :=
  SemidirectProduct.lift (pglAction K) (psl2FieldAut K) (pglAction_fieldAut K)

@[simp]
theorem semilinearAction_inl (K : Type u) [Field K] (g : PGL2 K) :
    semilinearAction K (SemidirectProduct.inl g) = pglAction K g := by
  simp [semilinearAction]

@[simp]
theorem semilinearAction_inr (K : Type u) [Field K] (sigma : K ≃+* K) :
    semilinearAction K (SemidirectProduct.inr sigma) = psl2FieldAut K sigma := by
  simp [semilinearAction]

theorem pglAction_eq_native (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) :
    pglAction K = pgl2InnerAutPSL2 K hK hcard := by
  ext g x
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  rw [toPGL_pglAction, toPGL_pgl2InnerAutPSL2_apply]

theorem semilinearAction_eq_native (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) :
    semilinearAction K = pGammaL2ToMulAutPSL2 K hK hcard := by
  apply SemidirectProduct.hom_ext
  · ext g
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, semilinearAction_inl,
      pGammaL2ToMulAutPSL2_inl, pglAction_eq_native K hK hcard]
  · ext sigma
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, semilinearAction_inr,
      pGammaL2ToMulAutPSL2_inr]

theorem pglAction_projectiveLine
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime] (hKcard : Nat.card K = p ^ f)
    (g : PGL2 K) (x : PSL2ProjectiveLine K) :
    psl2MulAutProjectiveLine K hKcard (pglAction K g) x = g • x := by
  let e := psl2ProjectiveLineEquivSylow K hKcard
  let beta := pglAction K g
  let P : Sylow p (PSL2 K) := e x
  let P' : Sylow p (PSL2 K) := beta • P
  let Q : Sylow p (PSL2 K) := e (g • x)
  let B : Subgroup (PSL2 K) := MulAction.stabilizer (PSL2 K) (g • x)
  have hPfix {h : PSL2 K} (hh : h ∈ (P : Subgroup (PSL2 K))) : h • x = x := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [psl2ProjectiveLineEquivSylow_stabilizer K hKcard]
    exact Subgroup.le_normalizer hh
  have hP'leB : (P' : Subgroup (PSL2 K)) ≤ B := by
    intro y hy
    rw [MulAction.mem_stabilizer_iff]
    change y ∈ (P : Subgroup (PSL2 K)).map beta.toMonoidHom at hy
    obtain ⟨h, hh, rfl⟩ := hy
    calc
      beta h • (g • x) =
          Matrix.ProjectiveSpecialLinearGroup.toPGL (beta h) • (g • x) :=
        (psl2ToPGL_smul (beta h) (g • x)).symm
      _ = (g * Matrix.ProjectiveSpecialLinearGroup.toPGL h * g⁻¹) • (g • x) := by
        rw [toPGL_pglAction]
      _ = g • (h • x) := by
        simp only [mul_smul, inv_smul_smul, psl2ToPGL_smul]
      _ = g • x := by rw [hPfix hh]
  have hBQ : B = Subgroup.normalizer (Q : Subgroup (PSL2 K)) :=
    psl2ProjectiveLineEquivSylow_stabilizer K hKcard (g • x)
  have hQleB : (Q : Subgroup (PSL2 K)) ≤ B := by
    rw [hBQ]
    exact Subgroup.le_normalizer
  have hQnormal : ((Q : Subgroup (PSL2 K)).subgroupOf B).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hQleB).2
    rw [hBQ]
  let QSyl : Sylow p B := Q.subtype hQleB
  let PSyl : Sylow p B := P'.subtype hP'leB
  have hQSylNormal : (QSyl : Subgroup B).Normal := hQnormal
  let : Unique (Sylow p B) := Sylow.unique_of_normal QSyl hQSylNormal
  have hP'eqQ : P' = Q := Sylow.subtype_injective (Subsingleton.elim PSyl QSyl)
  apply e.injective
  rw [psl2MulAutProjectiveLine_apply, Equiv.apply_symm_apply]
  exact hP'eqQ

end

end CFSG.ComponentClassification.CatalogueSchreierLinearTwo
