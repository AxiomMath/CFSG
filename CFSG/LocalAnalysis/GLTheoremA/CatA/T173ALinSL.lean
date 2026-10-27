module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ALinDefs
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open scoped MatrixGroups

theorem lin_mem_SL_iff {d : ℕ} {F : Type} [Field F] {A : GL (Fin d) F} :
    A ∈ LinSL d F ↔ (A : Matrix (Fin d) (Fin d) F).det = 1 := by
  show A ∈ LargeEvenSLGroup (Fin d) F ↔ _
  rw [largeEvenSLGroup_eq_statedSL]
  exact StatedAPI.mem_statedSL_iff

theorem lin_conj_mem_SL {d : ℕ} {F : Type} [Field F] (g : GL (Fin d) F) {A : GL (Fin d) F}
    (hA : A ∈ LinSL d F) : g * A * g⁻¹ ∈ LinSL d F := by
  rw [lin_mem_SL_iff] at hA ⊢
  have h1 : (g : Matrix (Fin d) (Fin d) F).det *
      ((g⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hA]
  linear_combination h1

theorem lin_isElemAbelian_map {p : ℕ} {G G' : Type} [Group G] [Group G'] (f : G →* G')
    {E : Subgroup G} (hE : IsElemAbelian p E) : IsElemAbelian p (E.map f) := by
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    apply Subtype.ext
    show f a * f b = f b * f a
    rw [← map_mul, ← map_mul, isElemAbelian_commute hE ha hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE.2 a ha, map_one]

@[expose] def LinBlockGrp (d : ℕ) (F : Type) [Field F] (I : Finset (Fin d)) :
    Subgroup (GL (Fin d) F) where
  carrier := LinBlockSet d F I
  one_mem' := by
    refine ⟨(LinSL d F).one_mem, fun i j _ => ?_⟩
    simp [Matrix.one_apply]
  mul_mem' := by
    rintro g h ⟨hg, hgI⟩ ⟨hh, hhI⟩
    refine ⟨(LinSL d F).mul_mem hg hh, fun i j hij => ?_⟩
    rw [Units.val_mul, Matrix.mul_apply]
    rcases hij with hi | hj
    · simp only [hgI i _ (Or.inl hi), ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
      exact hhI i j (Or.inl hi)
    · simp only [hhI _ j (Or.inr hj), mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      exact hgI i j (Or.inr hj)
  inv_mem' := by
    rintro g ⟨hg, hgI⟩
    refine ⟨(LinSL d F).inv_mem hg, fun i j hij => ?_⟩
    rcases hij with hi | hj
    · have h1 := congrFun (congrFun (Units.mul_inv g) i) j
      rw [Matrix.mul_apply] at h1
      simp only [hgI i _ (Or.inl hi), ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, if_true, Matrix.one_apply] at h1
      exact h1
    · have h1 := congrFun (congrFun (Units.inv_mul g) i) j
      rw [Matrix.mul_apply] at h1
      simp only [hgI _ j (Or.inr hj), mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, Matrix.one_apply] at h1
      exact h1

@[expose] def LinBlockSub (d : ℕ) (F : Type) [Field F] (I : Finset (Fin d)) :
    Subgroup (LinPSL d F) :=
  ((LinBlockGrp d F I).subgroupOf (LinSL d F)).map (LinMk d F)

theorem coe_linBlockSub (d : ℕ) (F : Type) [Field F] (I : Finset (Fin d)) :
    (LinBlockSub d F I : Set (LinPSL d F)) = LinBlockImage d F I := by
  rw [LinBlockSub, Subgroup.coe_map]
  rfl

@[expose] def LinLevelSet {d : ℕ} {F : Type} [Field F] (a : GL (Fin d) F)
    (I : Finset (Fin d)) : Prop :=
  I.Nonempty ∧ ∃ c : F, ∀ i : Fin d, i ∈ I ↔ (a : Matrix (Fin d) (Fin d) F) i i = c

@[expose] def LinDiagImage (d : ℕ) (F : Type) [Field F] : Set (LinPSL d F) :=
  {z | ∃ t : ↥(LinSL d F), (∀ i j : Fin d, i ≠ j →
    ((t : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i j = 0) ∧ LinMk d F t = z}

theorem lin_diagImage_comm {d : ℕ} {F : Type} [Field F] {s t : LinPSL d F}
    (hs : s ∈ LinDiagImage d F) (ht : t ∈ LinDiagImage d F) : s * t = t * s := by
  obtain ⟨u, hu, rfl⟩ := hs
  obtain ⟨v, hv, rfl⟩ := ht
  rw [← map_mul, ← map_mul]
  congr 1
  have hU : ((u : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      Matrix.diagonal fun i => ((u : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.diagonal_apply_ne _ hij, hu i j hij]
  have hV : ((v : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      Matrix.diagonal fun i => ((v : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.diagonal_apply_ne _ hij, hv i j hij]
  apply Subtype.ext
  apply Units.ext
  show ((u : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) * ((v : GL (Fin d) F) : Matrix _ _ F) =
    ((v : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) * ((u : GL (Fin d) F) : Matrix _ _ F)
  rw [hU, hV, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
