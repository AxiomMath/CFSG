module

public import CFSG.LieType.SpecialLinear.ExteriorModel.FixedLine
public import CFSG.LieType.SpecialLinear.TypeLabel.Basic
public import CFSG.LieType.SpecialLinear.EndNode.CoverDatum

public section

namespace CFSG.LieType.SpecialLinear.SLModel

open Matrix CFSG.LieType.SpecialLinear.ExteriorModel CFSG.LieType.SpecialLinear
  CFSG.LieType.Universal.SpecialLinear CFSG.LieType.Universal.Unitary CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
open scoped MatrixGroups

noncomputable section

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {k : Type} [Field k] [CharP k 2]
  [Algebra F k] {m f : ℕ}

@[expose] noncomputable def frobTwist (F k : Type) [Field F] [CharP F 2] [Field k] [Algebra F k]
    (f : ℕ) : Fin f → (F →+* k) :=
  fun r => (algebraMap F k).comp (iterateFrobenius F 2 r)

omit [Fintype F] [CharP k 2] in
theorem frobTwist_apply (r : Fin f) (t : F) :
    frobTwist F k f r t = algebraMap F k (t ^ 2 ^ (r : ℕ)) := by
  simp [frobTwist, iterateFrobenius_def]

omit [Fintype F] [CharP k 2] in
theorem twistHom_apply (g : SpecialLinearGroup (Fin (m + 1)) F) (r : Fin f) :
    (twistHom (frobTwist F k f) g) r = SpecialLinearGroup.map (frobTwist F k f r) g := rfl

@[expose] noncomputable def slModelRep (ε : Fin f → Finset (Fin (m + 1))) :
    Representation k (SpecialLinearGroup (Fin (m + 1)) F) (BModel k ε) :=
  (bRep ε).comp (twistHom (frobTwist F k f))

omit [Fintype F] in
theorem slModelRep_mk (ε : Fin f → Finset (Fin (m + 1)))
    (g : SpecialLinearGroup (Fin (m + 1)) F) (w : bCyc (k := k) ε) :
    slModelRep (F := F) (k := k) ε g (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk ⟨bMat ε (fun r =>
          ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) F).map (frobTwist F k f r))) *ᵥ
          (w : BIdx ε → k),
        by
          simpa only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] using
            bMat_mulVec_mem_bCyc ε
              (fun r => SpecialLinearGroup.map (frobTwist F k f r) g) w.2⟩ := by
  rw [slModelRep]
  change (bRep ε ((twistHom (frobTwist F k f)) g)) (Submodule.Quotient.mk w) = _
  rw [bRep_mk]
  have h : (fun r => (((twistHom (frobTwist F k f)) g r :
      SpecialLinearGroup (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)) = fun r =>
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F).map (frobTwist F k f r) := by
    funext r
    rw [twistHom_apply, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  refine congrArg (Submodule.Quotient.mk (p :=
    (bRad (k := k) ε).comap (bCyc (k := k) ε).subtype)) (Subtype.ext ?_)
  simp only [h]

omit [Fintype F] [CharP F 2] in
theorem prod_btop_pow_eq (ε : Fin f → Finset (Fin (m + 1))) (d : Fin (m + 1) → F) :
    (∏ p : Fin f × Fin (m + 1),
        ∏ a ∈ ((btop ε p : Set.powersetCard (Fin (m + 1)) (bdeg ε p)) : Finset (Fin (m + 1))),
          d a ^ 2 ^ (p.1 : ℕ)) = ∏ a, d a ^ bExp ε a := by
  classical
  have hbtop : ∀ p : Fin f × Fin (m + 1),
      ((btop ε p : Set.powersetCard (Fin (m + 1)) (bdeg ε p)) : Finset (Fin (m + 1))) =
        Finset.univ.filter fun a : Fin (m + 1) => (a : ℕ) < bdeg ε p := by
    intro p
    simp [btop, ktop, initSeg]
  simp only [hbtop]
  rw [Fintype.prod_prod_type]
  simp_rw [Finset.prod_filter]
  calc (∏ r : Fin f, ∏ j : Fin (m + 1), ∏ a : Fin (m + 1),
        if (a : ℕ) < bdeg ε (r, j) then d a ^ 2 ^ (r : ℕ) else 1)
      = ∏ r : Fin f, ∏ a : Fin (m + 1), ∏ j : Fin (m + 1),
          (if (a : ℕ) < bdeg ε (r, j) then d a ^ 2 ^ (r : ℕ) else 1) := by
        refine Finset.prod_congr rfl fun r _ => ?_
        exact Finset.prod_comm
    _ = ∏ a : Fin (m + 1), ∏ r : Fin f, ∏ j : Fin (m + 1),
          (if (a : ℕ) < bdeg ε (r, j) then d a ^ 2 ^ (r : ℕ) else 1) :=
        Finset.prod_comm
    _ = ∏ a : Fin (m + 1), d a ^ bExp ε a := by
        refine Finset.prod_congr rfl fun a _ => ?_
        have hset : ∀ r : Fin f, (Finset.univ.filter fun j : Fin (m + 1) =>
            (a : ℕ) < bdeg ε (r, j)) = (ε r).filter fun j => a < j := by
          intro r
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          unfold bdeg
          by_cases hj : j ∈ ε r
          · rw [if_pos hj]
            simp only [hj, true_and]
            exact Fin.lt_def
          · rw [if_neg hj]
            simp [hj]
        have hinner : ∀ r : Fin f,
            (∏ j : Fin (m + 1),
              (if (a : ℕ) < bdeg ε (r, j) then d a ^ 2 ^ (r : ℕ) else 1)) =
              (d a ^ 2 ^ (r : ℕ)) ^ ((ε r).filter fun j => a < j).card := by
          intro r
          rw [← hset r, ← Finset.prod_filter]
          exact Finset.prod_const _
        simp_rw [hinner]
        rw [bExp]
        simp_rw [← pow_mul]
        rw [Finset.prod_pow_eq_pow_sum]

theorem bTop_mem_fixU (ε : Fin f → Finset (Fin (m + 1))) :
    bTop ε ∈ (coverId m F 2).datum.fixU (slModelRep (F := F) (k := k) ε) := by
  rw [CurtisDatum.mem_fixU]
  intro u hu
  have hu' : u ∈ (curtisDatum m F 2).U := by
    rwa [coverId_datum_U m F 2] at hu
  rw [mem_curtisDatum_U_iff] at hu'
  obtain ⟨hdiag, htri⟩ := hu'
  have hmat : bMat ε (fun r =>
      ((u : Matrix (Fin (m + 1)) (Fin (m + 1)) F).map (frobTwist F k f r))) *ᵥ bvec ε =
      bvec ε := by
    refine bMat_mulVec_bvec_of_unitriangular ε (fun r a b hba => ?_) (fun r a => ?_)
    · rw [Matrix.map_apply, htri a b hba, map_zero]
    · rw [Matrix.map_apply, hdiag a, map_one]
  rw [bTop, slModelRep_mk]
  refine congrArg (Submodule.Quotient.mk (p :=
    (bRad (k := k) ε).comap (bCyc (k := k) ε).subtype)) (Subtype.ext ?_)
  simpa using hmat

theorem slModelRep_torus (ε : Fin f → Finset (Fin (m + 1))) :
    ∀ h ∈ (curtisDatum m F 2).H,
      slModelRep (F := F) (k := k) ε h (bTop ε) = slChiEps m (algebraMap F k) ε h • bTop ε := by
  intro h hh
  have hhH : h ∈ ⨆ s, torus m F s := hh
  have hdiag : (h : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag :=
    (mem_iSup_torus_iff m F).mp hhH
  have hfam : (fun r => (h : Matrix (Fin (m + 1)) (Fin (m + 1)) F).map
      (frobTwist F k f r)) =
      fun r => Matrix.diagonal (fun a =>
        frobTwist F k f r ((h : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a a)) := by
    funext r
    rw [← hdiag.diagonal_diag, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext a
    rw [Matrix.diagonal_apply_eq]
  have hbm : bMat ε (fun r => (h : Matrix (Fin (m + 1)) (Fin (m + 1)) F).map
      (frobTwist F k f r)) *ᵥ bvec ε =
      (∏ p : Fin f × Fin (m + 1), ∏ a ∈ ((btop ε p :
        Set.powersetCard (Fin (m + 1)) (bdeg ε p)) : Finset (Fin (m + 1))),
        frobTwist F k f p.1 (((h : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a a))) • bvec ε := by
    rw [hfam, bMat_diagonal_mulVec_bvec]
  have hscalar : (∏ p : Fin f × Fin (m + 1), ∏ a ∈ ((btop ε p :
      Set.powersetCard (Fin (m + 1)) (bdeg ε p)) : Finset (Fin (m + 1))),
        frobTwist F k f p.1 (((h : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a a))) =
      algebraMap F k (∏ a, (h : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a a ^ bExp ε a) := by
    have h1 : (∏ p : Fin f × Fin (m + 1), ∏ a ∈ ((btop ε p :
        Set.powersetCard (Fin (m + 1)) (bdeg ε p)) : Finset (Fin (m + 1))),
          frobTwist F k f p.1 (((h : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a a))) =
        ∏ p : Fin f × Fin (m + 1), algebraMap F k (∏ a ∈ ((btop ε p :
          Set.powersetCard (Fin (m + 1)) (bdeg ε p)) : Finset (Fin (m + 1))),
            ((h : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a a) ^ 2 ^ (p.1 : ℕ)) := by
      refine Finset.prod_congr rfl fun p _ => ?_
      rw [← map_prod, frobTwist_apply, map_pow, Finset.prod_pow, ← map_pow]
    rw [h1, ← map_prod]
    congr 1
    exact prod_btop_pow_eq ε fun a => (h : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a a
  rw [bTop, slModelRep_mk]
  rw [← Submodule.Quotient.mk_smul]
  refine congrArg (Submodule.Quotient.mk (p :=
    (bRad (k := k) ε).comap (bCyc (k := k) ε).subtype)) (Subtype.ext ?_)
  rw [Submodule.coe_smul]
  change bMat ε (fun r => (h : Matrix (Fin (m + 1)) (Fin (m + 1)) F).map
    (frobTwist F k f r)) *ᵥ bvec ε =
      slChiEps m (algebraMap F k) ε h • bvec ε
  rw [hbm, hscalar]
  rfl

end

end CFSG.LieType.SpecialLinear.SLModel
