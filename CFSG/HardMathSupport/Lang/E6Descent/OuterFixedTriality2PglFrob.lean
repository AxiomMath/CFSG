module

public import CFSG.RankThree.PartTwo.Sec21.LangTwisted2ProofD4Frob

public noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace CFSG.HardMathSupport.Lang.E6Descent.Tri2Pgl

open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec8
open CFSG.RankThree.PartTwo.Sec8.LangTwisted2Proof

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley LangTwistedProof Matrix
open scoped MatrixGroups


variable {L : Type} [Field L] [CharP L 2]

theorem twistHom_triple (Fr : L →+* L) (j : Fin 3) (a b c : L) :
    twistHom TwistTag.D4 L Fr (pinnedX TwistTag.D4.tag L (secVec j 0) a *
        pinnedX TwistTag.D4.tag L (secVec j 1) b * pinnedX TwistTag.D4.tag L (secVec j 2) c) =
      pinnedX TwistTag.D4.tag L (secVec j 0) (Fr c) *
        pinnedX TwistTag.D4.tag L (secVec j 1) (Fr a) *
          pinnedX TwistTag.D4.tag L (secVec j 2) (Fr b) := by
  obtain ⟨e0, e1, e2⟩ := permLattice_secVec j
  rw [map_mul, map_mul, twistHom_pinnedX_of_two Fr (isRoot_secVec j 0) a,
    twistHom_pinnedX_of_two Fr (isRoot_secVec j 1) b,
    twistHom_pinnedX_of_two Fr (isRoot_secVec j 2) c, e0, e1, e2]
  have c10 := commute_secVec_pp (L := L) j (i := 1) (k := 0) (Fr a) (Fr c)
  have c20 := commute_secVec_pp (L := L) j (i := 2) (k := 0) (Fr b) (Fr c)
  rw [mul_assoc, c20.eq, ← mul_assoc, c10.eq]

theorem twistHom_neg_triple (Fr : L →+* L) (j : Fin 3) (a b c : L) :
    twistHom TwistTag.D4 L Fr (pinnedX TwistTag.D4.tag L (-secVec j 0) a *
        pinnedX TwistTag.D4.tag L (-secVec j 1) b * pinnedX TwistTag.D4.tag L (-secVec j 2) c) =
      pinnedX TwistTag.D4.tag L (-secVec j 0) (Fr c) *
        pinnedX TwistTag.D4.tag L (-secVec j 1) (Fr a) *
          pinnedX TwistTag.D4.tag L (-secVec j 2) (Fr b) := by
  obtain ⟨e0, e1, e2⟩ := permLattice_secVec j
  rw [map_mul, map_mul, twistHom_pinnedX_of_two Fr (IsRoot.neg (isRoot_secVec j 0)) a,
    twistHom_pinnedX_of_two Fr (IsRoot.neg (isRoot_secVec j 1)) b,
    twistHom_pinnedX_of_two Fr (IsRoot.neg (isRoot_secVec j 2)) c, permLattice_neg,
    permLattice_neg, permLattice_neg, e0, e1, e2]
  have c10 := commute_secVec_nn (L := L) j (i := 1) (k := 0) (Fr a) (Fr c)
  have c20 := commute_secVec_nn (L := L) j (i := 2) (k := 0) (Fr b) (Fr c)
  rw [mul_assoc, c20.eq, ← mul_assoc, c10.eq]

theorem fin3_cases (j : Fin 3) : j = 0 ∨ j = 1 ∨ j = 2 := by
  revert j
  decide

section Orbits

variable {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0) (Fr : L →+* L) (hFr : Fr (μ : L) = (μ : L))

include hμ hFr

theorem fr_secKappa (j : Fin 3) : Fr (secKappa μ j) = secKappa μ j := by
  have hμ3 := pow_three_of_sq_add hμ
  rcases fin3_cases j with rfl | rfl | rfl
  · rw [secKappa_zero, hFr]
  · rw [secKappa_one, map_pow, hFr]
  · rw [secKappa_two hμ3, map_one]

theorem twistHom_secOrbitX (j : Fin 3) (a : L) :
    twistHom TwistTag.D4 L Fr (secOrbitX μ j a) =
      secOrbitX μ j (secKappa μ j ^ 2 * Fr a) := by
  have h3 := secKappa_pow_three (pow_three_of_sq_add hμ) j
  have hk := fr_secKappa hμ Fr hFr j
  rw [secOrbitX, twistHom_triple, secOrbitX]
  have e0 : Fr (secKappa μ j ^ 2 * a) = secKappa μ j ^ 2 * Fr a := by
    rw [map_mul, map_pow, hk]
  have e1 : Fr a = secKappa μ j * (secKappa μ j ^ 2 * Fr a) := by
    linear_combination (-(Fr a)) * h3
  have e2 : Fr (secKappa μ j * a) = secKappa μ j ^ 2 * (secKappa μ j ^ 2 * Fr a) := by
    rw [map_mul, hk]
    linear_combination (-(secKappa μ j * Fr a)) * h3
  rw [e0, e2, ← e1]

theorem twistHom_secOrbitY (j : Fin 3) (a : L) :
    twistHom TwistTag.D4 L Fr (secOrbitY μ j a) =
      secOrbitY μ j (secKappa μ j * Fr a) := by
  have h3 := secKappa_pow_three (pow_three_of_sq_add hμ) j
  have hk := fr_secKappa hμ Fr hFr j
  rw [secOrbitY, twistHom_neg_triple, secOrbitY]
  have e0 : Fr (secKappa μ j * a) = secKappa μ j * Fr a := by
    rw [map_mul, hk]
  have e1 : Fr a = secKappa μ j ^ 2 * (secKappa μ j * Fr a) := by
    linear_combination (-(Fr a)) * h3
  have e2 : Fr (secKappa μ j ^ 2 * a) = secKappa μ j * (secKappa μ j * Fr a) := by
    rw [map_mul, map_pow, hk]
    ring
  rw [e0, e2, ← e1]

end Orbits

@[expose] def frTuple (Fr : L →+* L) (a : Fin TwistTag.D4.tag.rank → Lˣ) :
    Fin TwistTag.D4.tag.rank → Lˣ :=
  ![Units.map Fr.toMonoidHom (a 0), Units.map Fr.toMonoidHom (a 0),
    Units.map Fr.toMonoidHom (a 2), Units.map Fr.toMonoidHom (a 0)]

theorem twistHom_rootDiagUnit_fixed (Fr : L →+* L) {a : Fin TwistTag.D4.tag.rank → Lˣ}
    (ha1 : a 1 = a 0) (ha3 : a 3 = a 0) :
    twistHom TwistTag.D4 L Fr (rootDiagUnit TwistTag.D4.tag a) =
      rootDiagUnit TwistTag.D4.tag (frTuple Fr a) := by
  rw [twistHom_rootDiagUnit_eq]
  congr 1
  funext i
  rcases d4_cases i with rfl | rfl | rfl | rfl
  · rw [show TwistTag.D4.perm.symm 0 = 3 by decide, ha3]
    rfl
  · rw [show TwistTag.D4.perm.symm 1 = 0 by decide]
    rfl
  · rw [show TwistTag.D4.perm.symm 2 = 2 by decide]
    rfl
  · rw [show TwistTag.D4.perm.symm 3 = 1 by decide, ha1]
    rfl

@[expose] def secD (μ : Lˣ) : GL (Fin 3) L where
  val := Matrix.diagonal ![1, (μ : L), 1]
  inv := Matrix.diagonal ![1, (μ : L)⁻¹, 1]
  val_inv := by
    have h0 : (μ : L) ≠ 0 := Units.ne_zero μ
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    fin_cases k <;> simp [h0]
  inv_val := by
    have h0 : (μ : L) ≠ 0 := Units.ne_zero μ
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    fin_cases k <;> simp [h0]

theorem coe_secD_inv (μ : Lˣ) :
    (((secD μ : GL (Fin 3) L)⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      Matrix.diagonal ![1, (μ : L)⁻¹, 1] := rfl

theorem coe_secD (μ : Lˣ) :
    ((secD μ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) = Matrix.diagonal ![1, (μ : L), 1] :=
  rfl

@[expose] def pglRingMap {A B : Type} [Field A] [Field B] (ι : A →+* B) : PGL(3, A) →* PGL(3, B) :=
  QuotientGroup.map _ _ (Matrix.GeneralLinearGroup.map ι) (by
    intro g hg
    rw [Subgroup.mem_comap]
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hg ⊢
    obtain ⟨c, rfl⟩ := hg
    refine ⟨Units.map ι.toMonoidHom c, Units.ext ?_⟩
    rw [Matrix.GeneralLinearGroup.val_map_apply, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.scalar_apply,
      Matrix.diagonal_map (map_zero ι)]
    rfl)

theorem pglRingMap_mk {A B : Type} [Field A] [Field B] (ι : A →+* B) (g : GL (Fin 3) A) :
    pglRingMap ι (ProjGenLinGroup.mk g) =
      ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map ι g) :=
  rfl

@[expose] def secFrE (μ : Lˣ) (Fr : L →+* L) : PGL(3, L) →* PGL(3, L) :=
  (MulAut.conj (ProjGenLinGroup.mk (secD μ : GL (Fin 3) L))).toMonoidHom.comp (pglRingMap Fr)

theorem secFrE_mk (μ : Lˣ) (Fr : L →+* L) (g : GL (Fin 3) L) :
    secFrE μ Fr (ProjGenLinGroup.mk g) =
      ProjGenLinGroup.mk (secD μ * Matrix.GeneralLinearGroup.map Fr g * (secD μ)⁻¹) := by
  simp [secFrE, pglRingMap_mk, MulAut.conj_apply]

section Partners

variable {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0) (Fr : L →+* L)

include hμ

theorem secD_conj_tv01 (c : L) :
    secD μ * Matrix.GeneralLinearGroup.map Fr (tvGL (i := 0) (j := 1) (by decide) c) *
        (secD μ)⁻¹ = tvGL (i := 0) (j := 1) (by decide) ((μ : L) ^ 2 * Fr c) := by
  refine Units.ext ?_
  have hinv := inv_eq_sq_of_sq_add hμ
  have h0 : (μ : L) ≠ 0 := Units.ne_zero μ
  rw [Units.val_mul, Units.val_mul, coe_secD, coe_secD_inv, Matrix.GeneralLinearGroup.val_map_apply,
    coe_tvGL, coe_tvGL]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply,
      Matrix.single_apply, hinv, Matrix.diagonal_apply, Matrix.map_apply] <;>
    grind

theorem secD_conj_tv12 (c : L) :
    secD μ * Matrix.GeneralLinearGroup.map Fr (tvGL (i := 1) (j := 2) (by decide) c) *
        (secD μ)⁻¹ = tvGL (i := 1) (j := 2) (by decide) ((μ : L) * Fr c) := by
  refine Units.ext ?_
  have hinv := inv_eq_sq_of_sq_add hμ
  have h0 : (μ : L) ≠ 0 := Units.ne_zero μ
  rw [Units.val_mul, Units.val_mul, coe_secD, coe_secD_inv, Matrix.GeneralLinearGroup.val_map_apply,
    coe_tvGL, coe_tvGL]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply,
      Matrix.single_apply, hinv, Matrix.diagonal_apply, Matrix.map_apply] <;>
    grind

theorem secD_conj_tv02 (c : L) :
    secD μ * Matrix.GeneralLinearGroup.map Fr (tvGL (i := 0) (j := 2) (by decide) c) *
        (secD μ)⁻¹ = tvGL (i := 0) (j := 2) (by decide) (Fr c) := by
  refine Units.ext ?_
  have hinv := inv_eq_sq_of_sq_add hμ
  have h0 : (μ : L) ≠ 0 := Units.ne_zero μ
  rw [Units.val_mul, Units.val_mul, coe_secD, coe_secD_inv, Matrix.GeneralLinearGroup.val_map_apply,
    coe_tvGL, coe_tvGL]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply,
      Matrix.single_apply, hinv, Matrix.diagonal_apply, Matrix.map_apply] <;>
    grind

theorem secD_conj_tv10 (c : L) :
    secD μ * Matrix.GeneralLinearGroup.map Fr (tvGL (i := 1) (j := 0) (by decide) c) *
        (secD μ)⁻¹ = tvGL (i := 1) (j := 0) (by decide) ((μ : L) * Fr c) := by
  refine Units.ext ?_
  have hinv := inv_eq_sq_of_sq_add hμ
  have h0 : (μ : L) ≠ 0 := Units.ne_zero μ
  rw [Units.val_mul, Units.val_mul, coe_secD, coe_secD_inv, Matrix.GeneralLinearGroup.val_map_apply,
    coe_tvGL, coe_tvGL]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply,
      Matrix.single_apply, hinv, Matrix.diagonal_apply, Matrix.map_apply] <;>
    grind

theorem secD_conj_tv21 (c : L) :
    secD μ * Matrix.GeneralLinearGroup.map Fr (tvGL (i := 2) (j := 1) (by decide) c) *
        (secD μ)⁻¹ = tvGL (i := 2) (j := 1) (by decide) ((μ : L) ^ 2 * Fr c) := by
  refine Units.ext ?_
  have hinv := inv_eq_sq_of_sq_add hμ
  have h0 : (μ : L) ≠ 0 := Units.ne_zero μ
  rw [Units.val_mul, Units.val_mul, coe_secD, coe_secD_inv, Matrix.GeneralLinearGroup.val_map_apply,
    coe_tvGL, coe_tvGL]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply,
      Matrix.single_apply, hinv, Matrix.diagonal_apply, Matrix.map_apply] <;>
    grind

theorem secD_conj_tv20 (c : L) :
    secD μ * Matrix.GeneralLinearGroup.map Fr (tvGL (i := 2) (j := 0) (by decide) c) *
        (secD μ)⁻¹ = tvGL (i := 2) (j := 0) (by decide) (Fr c) := by
  refine Units.ext ?_
  have hinv := inv_eq_sq_of_sq_add hμ
  have h0 : (μ : L) ≠ 0 := Units.ne_zero μ
  rw [Units.val_mul, Units.val_mul, coe_secD, coe_secD_inv, Matrix.GeneralLinearGroup.val_map_apply,
    coe_tvGL, coe_tvGL]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply,
      Matrix.single_apply, hinv, Matrix.diagonal_apply, Matrix.map_apply] <;>
    grind

end Partners

theorem secD_conj_dgGL (μ : Lˣ) (Fr : L →+* L) (a : Fin TwistTag.D4.tag.rank → Lˣ) :
    secD μ * Matrix.GeneralLinearGroup.map Fr (dgGL a) * (secD μ)⁻¹ =
      dgGL (frTuple Fr a) := by
  refine Units.ext ?_
  have hμ0 : (μ : L) ≠ 0 := Units.ne_zero μ
  have hs : (Units.map Fr.toMonoidHom (a 0) : L) = Fr (a 0) := rfl
  have hu : (Units.map Fr.toMonoidHom (a 2) : L) = Fr (a 2) := rfl
  rw [Units.val_mul, Units.val_mul, coe_secD, coe_secD_inv, Matrix.GeneralLinearGroup.val_map_apply]
  change Matrix.diagonal ![1, (μ : L), 1] * (secTorD a).map Fr *
    Matrix.diagonal ![1, (μ : L)⁻¹, 1] = secTorD (frTuple Fr a)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [secTorD, frTuple, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply,
      Matrix.map_apply, hs, hu, hμ0] <;>
    field_simp

theorem secGraph_twistHom [IsAlgClosed L] {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0)
    {Fr : L →+* L} (hFr : Fr (μ : L) = (μ : L)) {m : ModGL TwistTag.D4.tag L}
    (hm : m ∈ secM μ) :
    ∀ P, (m, P) ∈ secGraph μ →
      (twistHom TwistTag.D4 L Fr m, secFrE μ Fr P) ∈ secGraph μ := by
  induction hm using Subgroup.iSup_induction' with
  | hp o x hx =>
    intro P hP
    rcases o with _ | ⟨j, _ | _⟩
    · obtain ⟨htT, htP⟩ := hx
      obtain ⟨a, ha1, ha3, rfl⟩ := exists_rootDiagUnit_of_mem_torus_fixed htT htP
      have hPa := secGraph_snd_eq hP (mem_secGraph (mem_secM_of_mem_torus μ htT htP)
        (adRel_rootDiagUnit μ ha1 ha3))
      subst hPa
      rw [secFrE_mk, secD_conj_dgGL, twistHom_rootDiagUnit_fixed Fr ha1 ha3]
      set a' := frTuple Fr a with ha'
      have ha'1 : a' 1 = a' 0 := rfl
      have ha'3 : a' 3 = a' 0 := rfl
      have hT : rootDiagUnit TwistTag.D4.tag a' ∈ torusGroup TwistTag.D4.tag L :=
        rootDiagUnit_mem_torusGroup a'
      have hP' : rootDiagUnit TwistTag.D4.tag a' ∈
          graphCentralizer TwistTag.D4.tag L (diagramMap TwistTag.D4 L) := by
        have hTG : torusGroup TwistTag.D4.tag L ≤ adjointGroup TwistTag.D4.tag L :=
          (Subgroup.closure_le _).2 fun _ ⟨q, hq⟩ => hq ▸ torusElt_mem_adjointGroup q.1 q.2
        refine Subgroup.mem_inf.2 ⟨hTG hT, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        refine (rootDiagUnit_commute_diagramMap_iff a').2 ?_
        funext i
        rcases d4_cases i with rfl | rfl | rfl | rfl
        · rw [show TwistTag.D4.perm.symm 0 = 3 by decide, ha'3]
        · rw [show TwistTag.D4.perm.symm 1 = 0 by decide, ha'1]
        · rw [show TwistTag.D4.perm.symm 2 = 2 by decide]
        · rw [show TwistTag.D4.perm.symm 3 = 1 by decide, ha'1, ha'3]
      exact mem_secGraph (mem_secM_of_mem_torus μ hT hP') (adRel_rootDiagUnit μ ha'1 ha'3)
    · obtain ⟨c, rfl⟩ := hx
      have hμ3 := pow_three_of_sq_add hμ
      fin_cases j
      · have hPc := secGraph_snd_eq hP (mem_secGraph (secOrbitY_mem_secM μ 0 _)
          (adRel_secOrbitY_zero μ hμ (Multiplicative.toAdd c)))
        subst hPc
        change (twistHom TwistTag.D4 L Fr (secOrbitY μ 0 _), _) ∈ _
        rw [secFrE_mk, secD_conj_tv10 hμ, twistHom_secOrbitY hμ Fr hFr, secKappa_zero]
        exact mem_secGraph (secOrbitY_mem_secM μ 0 _) (adRel_secOrbitY_zero μ hμ _)
      · have hPc := secGraph_snd_eq hP (mem_secGraph (secOrbitY_mem_secM μ 1 _)
          (adRel_secOrbitY_one μ hμ (Multiplicative.toAdd c)))
        subst hPc
        change (twistHom TwistTag.D4 L Fr (secOrbitY μ 1 _), _) ∈ _
        rw [secFrE_mk, secD_conj_tv21 hμ, twistHom_secOrbitY hμ Fr hFr, secKappa_one]
        exact mem_secGraph (secOrbitY_mem_secM μ 1 _) (adRel_secOrbitY_one μ hμ _)
      · have hPc := secGraph_snd_eq hP (mem_secGraph (secOrbitY_mem_secM μ 2 _)
          (adRel_secOrbitY_two μ hμ (Multiplicative.toAdd c)))
        subst hPc
        change (twistHom TwistTag.D4 L Fr (secOrbitY μ 2 _), _) ∈ _
        rw [secFrE_mk, secD_conj_tv20 hμ, twistHom_secOrbitY hμ Fr hFr, secKappa_two hμ3,
          one_mul]
        exact mem_secGraph (secOrbitY_mem_secM μ 2 _) (adRel_secOrbitY_two μ hμ _)
    · obtain ⟨c, rfl⟩ := hx
      have hμ3 := pow_three_of_sq_add hμ
      have h3 : (μ : L) ^ 3 = 1 := by linear_combination ((μ : L) - 1) * hμ
      fin_cases j
      · have hPc := secGraph_snd_eq hP (mem_secGraph (secOrbitX_mem_secM μ 0 _)
          (adRel_secOrbitX_zero μ hμ (Multiplicative.toAdd c)))
        subst hPc
        change (twistHom TwistTag.D4 L Fr (secOrbitX μ 0 _), _) ∈ _
        rw [secFrE_mk, secD_conj_tv01 hμ, twistHom_secOrbitX hμ Fr hFr, secKappa_zero]
        exact mem_secGraph (secOrbitX_mem_secM μ 0 _) (adRel_secOrbitX_zero μ hμ _)
      · have hPc := secGraph_snd_eq hP (mem_secGraph (secOrbitX_mem_secM μ 1 _)
          (adRel_secOrbitX_one μ hμ (Multiplicative.toAdd c)))
        subst hPc
        change (twistHom TwistTag.D4 L Fr (secOrbitX μ 1 _), _) ∈ _
        rw [secFrE_mk, secD_conj_tv12 hμ, twistHom_secOrbitX hμ Fr hFr, secKappa_one]
        have e : (((μ : L) ^ 2) ^ 2) * Fr (Multiplicative.toAdd c) = (μ : L) * Fr (Multiplicative.toAdd c) := by
          linear_combination ((μ : L) * Fr (Multiplicative.toAdd c)) * h3
        rw [e]
        exact mem_secGraph (secOrbitX_mem_secM μ 1 _) (adRel_secOrbitX_one μ hμ _)
      · have hPc := secGraph_snd_eq hP (mem_secGraph (secOrbitX_mem_secM μ 2 _)
          (adRel_secOrbitX_two μ hμ (Multiplicative.toAdd c)))
        subst hPc
        change (twistHom TwistTag.D4 L Fr (secOrbitX μ 2 _), _) ∈ _
        rw [secFrE_mk, secD_conj_tv02 hμ, twistHom_secOrbitX hμ Fr hFr, secKappa_two hμ3,
          one_pow, one_mul]
        exact mem_secGraph (secOrbitX_mem_secM μ 2 _) (adRel_secOrbitX_two μ hμ _)
  | h1 =>
    intro P hP
    have hP1 := secGraph_snd_eq hP (secGraph μ).one_mem
    subst hP1
    rw [map_one, map_one]
    exact (secGraph μ).one_mem
  | hmul x y hx hy ihx ihy =>
    intro P hP
    obtain ⟨Px, hPx⟩ := exists_secGraph_of_mem_secM hμ hx
    obtain ⟨Py, hPy⟩ := exists_secGraph_of_mem_secM hμ hy
    have hxy : (x * y, Px * Py) ∈ secGraph μ := (secGraph μ).mul_mem hPx hPy
    have hP' := secGraph_snd_eq hP hxy
    subst hP'
    have h := (secGraph μ).mul_mem (ihx Px hPx) (ihy Py hPy)
    rw [Prod.mk_mul_mk, ← map_mul, ← map_mul] at h
    exact h

@[expose] def secFixE (μ : Lˣ) (Fr : L →+* L) : Subgroup (ModGL TwistTag.D4.tag L) :=
  secM μ ⊓ (twistHom TwistTag.D4 L Fr).eqLocus (MonoidHom.id _)

@[expose] def pglFixE (μ : Lˣ) (Fr : L →+* L) : Subgroup PGL(3, L) :=
  (secFrE μ Fr).eqLocus (MonoidHom.id _)

theorem secPhi_mem_pglFixE [IsAlgClosed L] {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0)
    {Fr : L →+* L} (hFr : Fr (μ : L) = (μ : L)) {m : ModGL TwistTag.D4.tag L}
    (hm : m ∈ secFixE μ Fr) : secPhi μ hμ ⟨m, hm.1⟩ ∈ pglFixE μ Fr := by
  have h1 := secPhi_mem hμ ⟨m, hm.1⟩
  have h2 := secGraph_twistHom hμ hFr hm.1 _ h1
  have hfix : twistHom TwistTag.D4 L Fr m = m := hm.2
  rw [hfix] at h2
  exact (secGraph_snd_eq h1 h2).symm

@[expose] def secFixEHom [IsAlgClosed L] {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0)
    {Fr : L →+* L} (hFr : Fr (μ : L) = (μ : L)) : secFixE μ Fr →* pglFixE μ Fr where
  toFun m := ⟨secPhi μ hμ ⟨m.1, m.2.1⟩, secPhi_mem_pglFixE hμ hFr m.2⟩
  map_one' := Subtype.ext (map_one (secPhi μ hμ))
  map_mul' m m' := Subtype.ext (map_mul (secPhi μ hμ) ⟨m.1, m.2.1⟩ ⟨m'.1, m'.2.1⟩)

theorem secFixEHom_bijective [IsAlgClosed L] {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0)
    {Fr : L →+* L} (hFr : Fr (μ : L) = (μ : L)) :
    Function.Bijective (secFixEHom hμ hFr) := by
  refine ⟨fun m m' h => ?_, fun P => ?_⟩
  · have h' : secPhi μ hμ ⟨m.1, m.2.1⟩ = secPhi μ hμ ⟨m'.1, m'.2.1⟩ :=
      congrArg Subtype.val h
    have := (secPhi μ hμ).injective h'
    exact Subtype.ext (congrArg (fun x : secM μ => (x : ModGL TwistTag.D4.tag L)) this)
  · set m := (secPhi μ hμ).symm P.1 with hm
    have hmP : ((m : ModGL TwistTag.D4.tag L), P.1) ∈ secGraph μ := by
      have := secPhi_mem hμ m
      rwa [hm, MulEquiv.apply_symm_apply] at this
    have h2 := secGraph_twistHom hμ hFr m.2 _ hmP
    have hPfix : secFrE μ Fr P.1 = P.1 := P.2
    rw [hPfix] at h2
    have h3 := (secGraph μ).mul_mem h2 ((secGraph μ).inv_mem hmP)
    rw [Prod.inv_mk, Prod.mk_mul_mk, mul_inv_cancel] at h3
    have h4 := eq_one_of_mem_secGraph hμ h3
    have hfix : twistHom TwistTag.D4 L Fr (m : ModGL TwistTag.D4.tag L) = m := mul_inv_eq_one.1 h4
    refine ⟨⟨m, m.2, hfix⟩, Subtype.ext ?_⟩
    change secPhi μ hμ ⟨m.1, m.2⟩ = P.1
    rw [hm]
    exact MulEquiv.apply_symm_apply _ _

@[expose] def secFixEEquiv [IsAlgClosed L] {μ : Lˣ} (hμ : (μ : L) ^ 2 + μ + 1 = 0)
    {Fr : L →+* L} (hFr : Fr (μ : L) = (μ : L)) : secFixE μ Fr ≃* pglFixE μ Fr :=
  MulEquiv.ofBijective _ (secFixEHom_bijective hμ hFr)

end CFSG.HardMathSupport.Lang.E6Descent.Tri2Pgl
