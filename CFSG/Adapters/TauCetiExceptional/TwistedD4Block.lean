module

public import CFSG.Adapters.TauCetiExceptional.TwistedD4Match
public import CFSG.Adapters.TauCetiExceptional.TwistedBlock
import all TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.D.TripledWeight

public noncomputable section

namespace CFSG.TauCetiBridge.Twisted

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule TauCeti TauCeti.DynkinType
open CFSG.TauCetiBridge.Minuscule

attribute [local instance 100] LieRing.ofAssociativeRing

@[expose] def d4Blk (a : Fin 24) : Fin 3 := ⟨(a : ℕ) / 8, by omega⟩

@[expose] def d4E (A : Type*) [CommRing A] (i : Fin (Tag.rank .D4)) :
    Matrix (Fin 24) (Fin 24) A :=
  (D4Tripled.raisingMatrix (d4Node.symm i)).map (Int.cast : ℤ → A)

@[expose] def d4F (A : Type*) [CommRing A] (i : Fin (Tag.rank .D4)) :
    Matrix (Fin 24) (Fin 24) A :=
  (D4Tripled.loweringMatrix (d4Node.symm i)).map (Int.cast : ℤ → A)

@[expose] def d4Wt (a : Fin 24) (i : Fin (Tag.rank .D4)) : ℤ :=
  d4TripledWeight a (d4Node.symm i)

theorem d4Wt_mem (a : Fin 24) (i : Fin (Tag.rank .D4)) :
    d4Wt a i = -1 ∨ d4Wt a i = 0 ∨ d4Wt a i = 1 :=
  d4TripledWeight_apply_eq_neg_one_or_eq_zero_or_eq_one a _

theorem d4Wt_injective : Function.Injective d4Wt := fun a b h =>
  d4TripledWeight_injective (funext fun i => by
    have := congrFun h (d4Node i)
    simpa [d4Wt] using this)

theorem raising_isBlockDiag :
    ∀ (i : Fin 4) (a b : Fin 24), d4Blk a ≠ d4Blk b →
      (if d4TripledWeight b i = -1 ∧ a = d4TripledReflection i b then (1 : ℤ) else 0) = 0 := by
  decide +kernel

theorem lowering_isBlockDiag :
    ∀ (i : Fin 4) (a b : Fin 24), d4Blk a ≠ d4Blk b →
      (if d4TripledWeight b i = 1 ∧ a = d4TripledReflection i b then (1 : ℤ) else 0) = 0 := by
  decide +kernel

theorem one_add_smul_isBlockDiag {A : Type*} [CommRing A] (c : A) {E : Matrix (Fin 24) (Fin 24) ℤ}
    (hE : IsBlockDiag d4Blk ℤ E) :
    IsBlockDiag d4Blk A (1 + c • E.map (Int.cast : ℤ → A)) := by
  intro a b hab
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, hE a b hab, Int.cast_zero, smul_zero,
    add_zero]
  exact isBlockDiag_one a b hab

theorem toMat_rootUnit_mem_blockGL
    (K : Type*) [Field K] (i : Fin 4) (c : K) (s : Bool) :
    toMat d4Match.lab K (rootUnit d4tData_valid K
      ((if s then 1 else -1) • Pi.single (d4Match.node i) 1) c) ∈ blockGL d4Blk K := by
  have hinv : ∀ (γ : Fin (Tag.rank .D4) → ℤ) (c : K),
      (toMat d4Match.lab K (rootUnit d4tData_valid K γ c))⁻¹ =
        toMat d4Match.lab K (rootUnit d4tData_valid K γ (-c)) := fun γ c => by
    rw [← map_inv]
    congr 1
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← rootUnit_add, neg_add_cancel, rootUnit_zero]
  cases s
  · simp only [Bool.false_eq_true, ↓reduceIte, neg_smul, one_smul]
    refine mem_blockGL_of ?_ ?_
    · rw [← d4_rootSubgroupPoints_inr, D4Tripled.coe_rootSubgroupPoints_inr, toAdd_ofAdd]
      exact one_add_smul_isBlockDiag c fun a b hab => by
        rw [D4Tripled.loweringMatrix_apply]; exact lowering_isBlockDiag i a b hab
    · rw [hinv, ← d4_rootSubgroupPoints_inr, D4Tripled.coe_rootSubgroupPoints_inr, toAdd_ofAdd]
      exact one_add_smul_isBlockDiag (-c) fun a b hab => by
        rw [D4Tripled.loweringMatrix_apply]; exact lowering_isBlockDiag i a b hab
  · simp only [↓reduceIte, one_smul]
    refine mem_blockGL_of ?_ ?_
    · rw [← d4_rootSubgroupPoints_inl, D4Tripled.coe_rootSubgroupPoints_inl, toAdd_ofAdd]
      exact one_add_smul_isBlockDiag c fun a b hab => by
        rw [D4Tripled.raisingMatrix_apply]; exact raising_isBlockDiag i a b hab
    · rw [hinv, ← d4_rootSubgroupPoints_inl, D4Tripled.coe_rootSubgroupPoints_inl, toAdd_ofAdd]
      exact one_add_smul_isBlockDiag (-c) fun a b hab => by
        rw [D4Tripled.raisingMatrix_apply]; exact raising_isBlockDiag i a b hab

theorem d4_points_isBlockDiag
    (A : Type*) [CommRing A] (g : Matrix.GeneralLinearGroup (Fin 24) A)
    (hg : g ∈ D4Tripled.points A) : IsBlockDiag d4Blk A (g : Matrix (Fin 24) (Fin 24) A) := by
  have hroot : ∀ (j : Fin 4 ⊕ Fin 4) (c : ℚ),
      (D4Tripled.rootSubgroupPoints j ℚ (Multiplicative.ofAdd c) :
        Matrix.GeneralLinearGroup (Fin 24) ℚ) ∈ blockGL d4Blk ℚ := by
    intro j c
    rcases j with i | i
    · refine mem_blockGL_of ?_ ?_
      · rw [D4Tripled.coe_rootSubgroupPoints_inl, toAdd_ofAdd]
        exact one_add_smul_isBlockDiag c fun a b hab => by
          rw [D4Tripled.raisingMatrix_apply]
          exact raising_isBlockDiag i a b hab
      · rw [← Subgroup.coe_inv, ← map_inv, D4Tripled.coe_rootSubgroupPoints_inl,
          show (Multiplicative.ofAdd c)⁻¹ = Multiplicative.ofAdd (-c) from rfl, toAdd_ofAdd]
        exact one_add_smul_isBlockDiag (-c) fun a b hab => by
          rw [D4Tripled.raisingMatrix_apply]
          exact raising_isBlockDiag i a b hab
    · refine mem_blockGL_of ?_ ?_
      · rw [D4Tripled.coe_rootSubgroupPoints_inr, toAdd_ofAdd]
        exact one_add_smul_isBlockDiag c fun a b hab => by
          rw [D4Tripled.loweringMatrix_apply]
          exact lowering_isBlockDiag i a b hab
      · rw [← Subgroup.coe_inv, ← map_inv, D4Tripled.coe_rootSubgroupPoints_inr,
          show (Multiplicative.ofAdd c)⁻¹ = Multiplicative.ofAdd (-c) from rfl, toAdd_ofAdd]
        exact one_add_smul_isBlockDiag (-c) fun a b hab => by
          rw [D4Tripled.loweringMatrix_apply]
          exact lowering_isBlockDiag i a b hab
  intro a b hab
  have h := d4_evalMat_eq_zero_of_root_subgroups (blockGL d4Blk ℚ) hroot
    (MvPolynomial.X (a, b)) (fun g' hg' => by
      rw [BigCell.evalMat_X]
      exact hg'.1 a b hab) A g hg
  rwa [BigCell.evalMat_X] at h

theorem d4E_eq_mapMatrix (L : Type*) [CommRing L] (i : Fin (Tag.rank .D4)) :
    d4E L i = (Int.castRingHom L).mapMatrix (D4Tripled.raisingMatrix (d4Node.symm i)) :=
  rfl

theorem d4F_eq_mapMatrix (L : Type*) [CommRing L] (i : Fin (Tag.rank .D4)) :
    d4F L i = (Int.castRingHom L).mapMatrix (D4Tripled.loweringMatrix (d4Node.symm i)) :=
  rfl

theorem map_cartanGeneratorMatrix (L : Type*) [CommRing L] (i : Fin 4) :
    (Int.castRingHom L).mapMatrix (D4Tripled.cartanGeneratorMatrix i) =
      Matrix.diagonal fun a => (d4TripledWeight a i : L) := by
  ext a b
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, D4Tripled.cartanGeneratorMatrix_apply]
  by_cases hab : a = b
  · subst hab
    simp
  · rw [ite_eq_right hab.elim, Matrix.diagonal_apply_ne _ hab, map_zero]

theorem d4E_comm (L : Type*) [CommRing L] (i : Fin (Tag.rank .D4)) :
    d4E L i * d4F L i - d4F L i * d4E L i = Matrix.diagonal fun a => (d4Wt a i : L) := by
  have h := D4Tripled.isSerreSystem.lie_E_F_self (d4Node.symm i)
  rw [Ring.lie_def] at h
  rw [d4E_eq_mapMatrix, d4F_eq_mapMatrix, ← map_mul, ← map_mul, ← map_sub, h,
    map_cartanGeneratorMatrix]
  rfl

theorem d4E_commH (L : Type*) [CommRing L] (i j : Fin (Tag.rank .D4)) :
    Matrix.diagonal (fun a => (d4Wt a i : L)) * d4E L j -
      d4E L j * Matrix.diagonal (fun a => (d4Wt a i : L)) =
        ((Tag.cartan .D4 i j : ℤ) : L) • d4E L j := by
  have h := D4Tripled.isSerreSystem.lie_H_E (d4Node.symm i) (d4Node.symm j)
  rw [Ring.lie_def] at h
  have hc : CartanMatrix.D 4 (d4Node.symm i) (d4Node.symm j) = Tag.cartan .D4 i j := by
    have := d4_cartan (d4Node.symm i) (d4Node.symm j)
    rwa [D4Tripled.weightTable_cartanMatrix, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply] at this
  have e := congrArg (Int.castRingHom L).mapMatrix h
  rw [map_sub, map_mul, map_mul, map_cartanGeneratorMatrix, hc] at e
  unfold d4Wt
  rw [d4E_eq_mapMatrix, e]
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
    eq_intCast, Int.cast_mul]

theorem d4E_ne_zero (L : Type*) [CommRing L] [Nontrivial L] (j : Fin (Tag.rank .D4)) :
    d4E L j ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_d4TripledWeight_apply_eq_neg_one (d4Node.symm j)
  intro h
  have e := congrArg (fun M : Matrix (Fin 24) (Fin 24) L =>
    M (d4TripledReflection (d4Node.symm j) a) a) h
  simp only [d4E, Matrix.map_apply, D4Tripled.raisingMatrix_apply, ha, and_true, ite_true,
    Int.cast_one, Matrix.zero_apply] at e
  exact one_ne_zero e

theorem cartan_D4_off (i j : Fin (Tag.rank .D4)) (hij : i ≠ j) :
    Tag.cartan .D4 i j = 0 ∨ Tag.cartan .D4 i j = -1 := by
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | (left; rfl) | (right; rfl)

theorem reflection_eq_self_of_wt_eq_zero :
    ∀ (i : Fin 4) (c : Fin 24), d4TripledWeight c i = 0 → d4TripledReflection i c = c := by
  decide +kernel

theorem d4_isDiag_of_commute {L : Type*} [Field L] (h2 : (2 : L) ≠ 0)
    {z : Matrix (Fin 24) (Fin 24) L}
    (hz : ∀ i, z * Matrix.diagonal (fun a => (d4Wt a i : L)) =
      Matrix.diagonal (fun a => (d4Wt a i : L)) * z) {a b : Fin 24} (hab : a ≠ b) : z a b = 0 :=
  isDiag_of_commute_diagonal h2 d4Wt d4Wt_mem d4Wt_injective hz hab

theorem d4_diag_eq_of_commute {L : Type*} [Field L] {z : Matrix (Fin 24) (Fin 24) L}
    (hz : ∀ a b, a ≠ b → z a b = 0) (hE : ∀ i, z * d4E L i = d4E L i * z)
    (hF : ∀ i, z * d4F L i = d4F L i * z) {a b : Fin 24} (hab : d4Blk a = d4Blk b) :
    z a a = z b b := by
  have hstep : ∀ (i : Fin 4) (c : Fin 24),
      z c c = z (d4TripledReflection i c) (d4TripledReflection i c) := by
    intro i c
    rcases d4TripledWeight_apply_eq_neg_one_or_eq_zero_or_eq_one c i with h | h | h
    · refine diag_eq_of_commute hz (hE (d4Node i)) ?_
      simp [d4E, D4Tripled.raisingMatrix_apply, h]
    · rw [reflection_eq_self_of_wt_eq_zero i c h]
    · refine diag_eq_of_commute hz (hF (d4Node i)) ?_
      simp [d4F, D4Tripled.loweringMatrix_apply, h]
  have hpath : ∀ (l : List (Fin 4)) (c : Fin 24),
      z c c = z (l.foldl (fun c i => d4TripledReflection i c) c)
        (l.foldl (fun c i => d4TripledReflection i c) c) := by
    intro l
    induction l with
    | nil => intro c; rfl
    | cons i l ih => intro c; rw [List.foldl_cons, ← ih, ← hstep]
  obtain ⟨l, hl⟩ := (exists_foldl_d4TripledReflection_eq_iff a b).2 (by
    have := congrArg Fin.val hab
    simp only [d4Blk] at this
    simp only [d4TripledSummand, this])
  rw [hpath l a, hl]

theorem d4_excl : ∀ π' : Equiv.Perm (Fin (Tag.rank .D4)),
    (∀ ij : Fin (Tag.rank .D4) × Fin (Tag.rank .D4),
      Tag.cartan .D4 (π' ij.1) (π' ij.2) = Tag.cartan .D4 ij.1 ij.2) →
    (∀ a, ∃ b, d4Blk b = d4Blk a ∧ ∀ j, d4Wt b (π' j) = d4Wt a j) → π' = 1 := by
  decide +kernel

end CFSG.TauCetiBridge.Twisted
