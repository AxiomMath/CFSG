module

public import CFSG.Adapters.CatalogueFieldBridges.Unitary
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15NoXBlockBorelAll

public section

namespace CFSG.ClassicalGroups.UnitaryFlag

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem scalar_mul_eq_smul (c : K) (A : Matrix (HypIndex r ε) (HypIndex r ε) K) :
    Matrix.scalar (HypIndex r ε) c * A = c • A := by
  ext i j
  rw [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]

theorem inv_scalar_eq {c : K} (hc : c ≠ 0) :
    (Matrix.scalar (HypIndex r ε) c)⁻¹ = Matrix.scalar (HypIndex r ε) c⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  rw [← map_mul, mul_inv_cancel₀ hc, map_one]

@[simp] theorem torusEntries_inl (h : UnitaryFieldData p f K) (a : Fin r → Kˣ) (d : Fin ε → Kˣ)
    (i : Fin r) : torusEntries h a d (.inl i) = (a i : K) := rfl

@[simp] theorem torusEntries_inr_inl (h : UnitaryFieldData p f K) (a : Fin r → Kˣ)
    (d : Fin ε → Kˣ) (k : Fin ε) : torusEntries h a d (.inr (.inl k)) = (d k : K) := rfl

@[simp] theorem torusEntries_inr_inr (h : UnitaryFieldData p f K) (a : Fin r → Kˣ)
    (d : Fin ε → Kˣ) (i : Fin r) :
    torusEntries h a d (.inr (.inr i)) = (h.bar (a i))⁻¹ := rfl

theorem torusEntries_ne_zero (h : UnitaryFieldData p f K) (a : Fin r → Kˣ) (d : Fin ε → Kˣ)
    (x : HypIndex r ε) : torusEntries h a d x ≠ 0 := by
  rcases x with i | k | i
  · simpa using (a i).ne_zero
  · simpa using (d k).ne_zero
  · simpa using inv_ne_zero (map_ne_zero h.bar (a i).ne_zero)

theorem exists_mem_hypTorus_diag (h : UnitaryFieldData p f K) (hε : ε ≤ 1)
    {a : Fin r → Kˣ} {d : Fin ε → Kˣ} (hd : ∀ k, h.norm (d k : K) = 1)
    (hp : torusRatio h a d = 1) :
    ∃ t : hypSU h r ε, t ∈ hypTorus h r ε ∧
      ((t : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
        Matrix.diagonal (torusEntries h a d) ∧
      ∀ (ht : t ∈ hypTorus h r ε),
        hypDiagHom h r ε hε ⟨t, hypTorus_le_hypBorel h ht⟩ = a := by
  obtain ⟨g, hgt, hgmat⟩ := torusMat_mem_hypSU h a hd hp
  refine ⟨g, hgt, hgmat, fun ht => ?_⟩
  funext i
  refine Units.ext ?_
  rw [coe_hypDiagHom]
  show ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) (.inl i) (.inl i) =
    ((a i : Kˣ) : K)
  rw [hgmat, Matrix.diagonal_apply_eq]
  rfl

theorem exists_hypScalars_mul_of_comm {h : UnitaryFieldData p f K} {g u : hypSU h r ε}
    (hcomm : hypProj h r ε g * hypProj h r ε u = hypProj h r ε u * hypProj h r ε g) :
    ∃ z ∈ hypScalars h r ε, g * u = z * u * g := by
  have h1 : hypProj h r ε (g * u * g⁻¹ * u⁻¹) = 1 := by
    calc hypProj h r ε (g * u * g⁻¹ * u⁻¹)
        = hypProj h r ε g * hypProj h r ε u * (hypProj h r ε g)⁻¹ *
            (hypProj h r ε u)⁻¹ := by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      _ = 1 := by rw [hcomm]; group
  have h2 : g * u * g⁻¹ * u⁻¹ ∈ hypScalars h r ε := by
    rw [← ker_hypProj h r ε]
    simpa using h1
  refine ⟨g * u * g⁻¹ * u⁻¹, h2, ?_⟩
  group

theorem exists_hypScalars_conj_mul_of_comm {h : UnitaryFieldData p f K} {g u : hypSU h r ε}
    (hcomm : hypProj h r ε g * hypProj h r ε u = hypProj h r ε u * hypProj h r ε g) :
    ∃ z ∈ hypScalars h r ε, g⁻¹ * u * g = z * u := by
  have h1 : hypProj h r ε (g⁻¹ * u * g * u⁻¹) = 1 := by
    calc hypProj h r ε (g⁻¹ * u * g * u⁻¹)
        = (hypProj h r ε g)⁻¹ * hypProj h r ε u * hypProj h r ε g *
            (hypProj h r ε u)⁻¹ := by
          simp only [map_mul, map_inv]
      _ = 1 := by
          rw [show (hypProj h r ε g)⁻¹ * hypProj h r ε u * hypProj h r ε g =
            (hypProj h r ε g)⁻¹ * (hypProj h r ε u * hypProj h r ε g) by group,
            ← hcomm]
          group
  have h2 : g⁻¹ * u * g * u⁻¹ ∈ hypScalars h r ε := by
    rw [← ker_hypProj h r ε]
    simpa using h1
  refine ⟨g⁻¹ * u * g * u⁻¹, h2, ?_⟩
  group

theorem mul_N_eq_N_mul_of_conj_scalar {h : UnitaryFieldData p f K} {g u z : hypSU h r ε} {c : K}
    (hzmat : ((z : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      Matrix.scalar (HypIndex r ε) c)
    (hgu : g * u = z * u * g) (huU : u ∈ hypUnitriangular h r ε)
    (hMT : ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).BlockTriangular
      fullPos)
    {N : Matrix (HypIndex r ε) (HypIndex r ε) K}
    (humat : ((u : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = 1 + N)
    {x y : HypIndex r ε} (hxy : x ≠ y)
    (hMx : ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) x x ≠ 0) :
    (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) * N) x y =
      (N * ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)) x y := by
  have hmu := mem_hypUnitriangular.mp huU
  have hm : ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
        ((u : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      ((z : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
        ((u : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
        ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) := by
    simpa only [Subgroup.coe_mul, Units.val_mul] using
      congrArg (fun w : hypSU h r ε => ((w : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K)) hgu
  have hdx : ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) x x =
      c * ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) x x := by
    have h := congrFun (congrFun hm x) x
    rw [hzmat, scalar_mul_eq_smul, Matrix.smul_mul, Matrix.smul_apply] at h
    rw [mul_apply_self_of_blockTriangular fullPos_injective hMT hmu.1, hmu.2] at h
    rw [mul_apply_self_of_blockTriangular fullPos_injective hmu.1 hMT, hmu.2] at h
    simpa using h
  have hc : c = 1 := by
    rw [mul_comm c] at hdx
    exact (mul_left_cancel₀ hMx (by simpa using hdx)).symm
  have hz1 : ((z : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = 1 := by
    rw [hzmat, hc]
    simp
  have h := congrFun (congrFun hm x) y
  rw [humat, hz1] at h
  simp only [Matrix.mul_add, Matrix.mul_one, Matrix.one_mul, Matrix.add_mul,
    Matrix.add_apply] at h
  exact add_left_cancel h



theorem centralizer_hypProjUnitriangular_le (h : UnitaryFieldData p f K) (hr : 1 ≤ r)
    (hε : ε ≤ 1) :
    Subgroup.centralizer (hypProjUnitriangular h r ε : Set (hypPSU h r ε)) ≤
      hypProjUnitriangular h r ε := by
  classical
  intro x hx
  obtain ⟨g, rfl⟩ := hypProj_surjective h r ε x
  have hgB : g ∈ hypBorel h r ε := by
    refine mem_hypBorel_of_conj h hr hε fun u hu i hi => ?_
    obtain ⟨z, hz, hzu⟩ := exists_hypScalars_conj_mul_of_comm (g := g) (u := u)
      (((Subgroup.mem_centralizer_iff.mp hx) (hypProj h r ε u) ⟨u, hu, rfl⟩).symm)
    have hfix : u • hypFlag h r ε i = hypFlag h r ε i := by
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · subst h0
        rw [hypFlag, if_pos (Nat.zero_le r), isoFlag_zero, Subgroup.smul_def, smul_eq_map,
          Submodule.map_bot]
      · exact (mem_hypBorel.mp (hypUnitriangular_le_hypBorel h hu)) i h0 hi
    calc u • g • hypFlag h r ε i = g • (g⁻¹ * u * g) • hypFlag h r ε i := by
          rw [smul_smul, smul_smul]
          group
      _ = g • (z * u) • hypFlag h r ε i := by rw [hzu]
      _ = g • hypFlag h r ε i := by
          rw [mul_smul, hfix, smul_submodule_of_mem_normOneScalars hz]
  set M : Matrix (HypIndex r ε) (HypIndex r ε) K :=
    ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) with hM
  have hMT : M.BlockTriangular fullPos := by
    rw [hM]; exact blockTriangular_of_mem_hypBorel h hε hgB
  have hgram : (M.map h.bar)ᵀ * hypGram r ε K * M = hypGram r ε K := by
    rw [hM]; exact (mem_hypSU.mp g.2).1
  have hdet : M.det = 1 := by rw [hM]; exact (mem_hypSU.mp g.2).2
  obtain ⟨hMblk, hA, hP, hD⟩ := eq_blk3_of_blockTriangular hMT
  rw [hMblk] at hgram
  obtain ⟨h1, h2, h3, h4⟩ := (blk3_gram_iff h _ _ _ _ _ _).mp hgram
  have hAdet : IsUnit (blkA M).det := isUnit_det_of_mul_eq_one h1
  have hDeq : blkD M = barInvT h (blkA M) := eq_barInvT_of_mul_eq_one h1
  have hDii : ∀ i : Fin r, blkD M i i = (h.bar (blkA M i i))⁻¹ := fun i => by
    rw [hDeq]; exact barInvT_apply_self hA hAdet i
  have hAii : ∀ i : Fin r, M (.inl i) (.inl i) = blkA M i i := fun i => by
    rw [hMblk]; rfl
  have hFii : ∀ i : Fin r, M (.inr (.inr i)) (.inr (.inr i)) = (h.bar (blkA M i i))⁻¹ := by
    intro i
    rw [hMblk]
    change blkD M i i = (h.bar (blkA M i i))⁻¹
    exact hDii i
  have hAne : ∀ i : Fin r, blkA M i i ≠ 0 := by
    intro i hi
    have h := diag_ne_zero_of_mem_hypBorel hε hgB (Sum.inr (Sum.inr i))
    rw [← hM, hFii i, hi, map_zero] at h
    simp at h
  have hPkk : ∀ k : Fin ε, h.norm (blkP M k k) = 1 := by
    intro k
    haveI : Subsingleton (Fin ε) :=
      ⟨fun a b => Fin.ext (by have := a.2; have := b.2; omega)⟩
    have hkk := congrFun (congrFun h2 k) k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.one_apply_eq] at hkk
    rw [Finset.sum_eq_single k] at hkk
    · rw [UnitaryFieldData.norm, mul_comm]
      exact hkk
    · intro l _ hlk
      exact absurd (Subsingleton.elim l k) hlk
    · simp
  have hM0 : M (.inl (⟨0, hr⟩ : Fin r)) (.inl (⟨0, hr⟩ : Fin r)) ≠ 0 := by
    rw [hM]; exact diag_ne_zero_of_mem_hypBorel hε hgB _
  set c0 : K := M (.inl (⟨0, hr⟩ : Fin r)) (.inl (⟨0, hr⟩ : Fin r)) with hc0
  have hc0ne : c0 ≠ 0 := hM0
  have hshort : ∀ i : Fin r, i ≠ ⟨0, hr⟩ → c0 = M (.inl i) (.inl i) := by
    intro i hi
    have hne : (Sum.inl (⟨0, hr⟩ : Fin r) : Fin r ⊕ Fin r) ≠ Sum.inl i := by
      simp only [ne_eq, Sum.inl.injEq]
      exact fun hh => hi hh.symm
    have hdom : (1 : K) ∈ uRootDom h (.inl ⟨0, hr⟩) (.inl i) := by
      rw [uRootDom_of_ne h (by simp)]
      trivial
    have hpos : (⟨0, hr⟩ : Fin r) < i := by
      rw [Fin.lt_def]
      show (0 : ℕ) < (i : ℕ)
      exact Nat.pos_of_ne_zero (fun h0 => hi (Fin.ext (by simpa using h0)))
    let u : hypSU h r ε := uRootElt h (a := .inl ⟨0, hr⟩) (b := .inl i) hne ⟨1, hdom⟩
    have huU : u ∈ hypUnitriangular h r ε := uRootElt_short_mem h hpos ⟨1, hdom⟩
    set A : Matrix (HypIndex r ε) (HypIndex r ε) K :=
      Matrix.single (.inl (⟨0, hr⟩ : Fin r)) (.inl i) (1 : K) with hA
    set B : Matrix (HypIndex r ε) (HypIndex r ε) K :=
      Matrix.single (.inr (.inr i)) (.inr (.inr (⟨0, hr⟩ : Fin r))) (h.bar 1) with hB
    let N : Matrix (HypIndex r ε) (HypIndex r ε) K := A - B
    have humat : ((u : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
        1 + N := by
      rw [coe_uRootElt, uRootMat_inl_inl]
      show (1 : Matrix (HypIndex r ε) (HypIndex r ε) K) +
          Matrix.single (Sum.inl (⟨0, hr⟩ : Fin r)) (Sum.inl i) (1 : K) -
          Matrix.single (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr (⟨0, hr⟩ : Fin r))) (h.bar 1) =
        1 + N
      dsimp only [N, A, B]
      abel
    obtain ⟨z, hz, hgu⟩ := exists_hypScalars_mul_of_comm (g := g) (u := u)
      (((Subgroup.mem_centralizer_iff.mp hx) (hypProj h r ε u) ⟨u, huU, rfl⟩).symm)
    obtain ⟨cz, hznorm, hzpow, hzGL⟩ := mem_normOneScalars.mp hz
    have hzmat : ((z : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
        Matrix.scalar (HypIndex r ε) (cz : K) := by
      rw [hzGL, GeneralLinearGroup.coe_scalar]
    have hkey := mul_N_eq_N_mul_of_conj_scalar hzmat hgu huU hMT humat
      (x := .inl (⟨0, hr⟩ : Fin r)) (y := .inl i)
      (by rintro (h : (Sum.inl (⟨0, hr⟩ : Fin r) : HypIndex r ε) = Sum.inl i)
          exact hi (Sum.inl.inj h).symm)
      hM0
    have e1 : (M * A) (.inl (⟨0, hr⟩ : Fin r)) (.inl i) =
        M (.inl (⟨0, hr⟩ : Fin r)) (.inl (⟨0, hr⟩ : Fin r)) * 1 := by
      rw [hA, Matrix.mul_single_apply_same]
    have e2 : (M * B) (.inl (⟨0, hr⟩ : Fin r)) (.inl i) = 0 := by
      rw [hB, Matrix.mul_single_apply_of_ne _ _ _ _ _
        (by simp : (Sum.inl i : HypIndex r ε) ≠ Sum.inr (Sum.inr (⟨0, hr⟩ : Fin r)))]
    have hleft : (M * N) (.inl (⟨0, hr⟩ : Fin r)) (.inl i) =
        M (.inl (⟨0, hr⟩ : Fin r)) (.inl (⟨0, hr⟩ : Fin r)) := by
      rw [show N = A - B from rfl, Matrix.mul_sub, Matrix.sub_apply, e1, e2, sub_zero, mul_one]
    have f1 : (A * M) (.inl (⟨0, hr⟩ : Fin r)) (.inl i) = 1 * M (.inl i) (.inl i) := by
      rw [hA, Matrix.single_mul_apply_same]
    have f2 : (B * M) (.inl (⟨0, hr⟩ : Fin r)) (.inl i) = 0 := by
      rw [hB, Matrix.single_mul_apply_of_ne _ _ _ _ _
        (by simp : (Sum.inl (⟨0, hr⟩ : Fin r) : HypIndex r ε) ≠ Sum.inr (Sum.inr i))]
    have hright : (N * M) (.inl (⟨0, hr⟩ : Fin r)) (.inl i) = M (.inl i) (.inl i) := by
      rw [show N = A - B from rfl, Matrix.sub_mul, Matrix.sub_apply, f1, f2, sub_zero, one_mul]
    rw [hleft, hright] at hkey
    exact hkey
  obtain ⟨cE, hcE, hcE0⟩ := exists_mem_traceZero_ne_zero' h
  have hlong : ∀ i : Fin r, M (.inl i) (.inl i) = M (.inr (.inr i)) (.inr (.inr i)) := by
    intro i
    have hdom : cE ∈ uRootDom h (.inl i) (.inr i) := by
      rw [show (Sum.inr i : Fin r ⊕ Fin r) = (Sum.inl i).swap from rfl, uRootDom_swap]
      exact hcE
    let u : hypSU h r ε := uRootElt h (a := .inl i) (b := .inr i) (inl_ne_inr i) ⟨cE, hdom⟩
    have huU : u ∈ hypUnitriangular h r ε := uRootElt_long_mem h i ⟨cE, hdom⟩
    set A : Matrix (HypIndex r ε) (HypIndex r ε) K :=
      Matrix.single (.inl i) (.inr (.inr i)) cE with hA
    let N : Matrix (HypIndex r ε) (HypIndex r ε) K := A
    have humat : ((u : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
        1 + N := by
      rw [coe_uRootElt, uRootMat_inl_inr_self]
    obtain ⟨z, hz, hgu⟩ := exists_hypScalars_mul_of_comm (g := g) (u := u)
      (((Subgroup.mem_centralizer_iff.mp hx) (hypProj h r ε u) ⟨u, huU, rfl⟩).symm)
    obtain ⟨cz, hznorm, hzpow, hzGL⟩ := mem_normOneScalars.mp hz
    have hzmat : ((z : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
        Matrix.scalar (HypIndex r ε) (cz : K) := by
      rw [hzGL, GeneralLinearGroup.coe_scalar]
    have hMx : M (.inl i) (.inl i) ≠ 0 := by
      rw [hAii i]
      exact hAne i
    have hkey := mul_N_eq_N_mul_of_conj_scalar hzmat hgu huU hMT humat
      (x := .inl i) (y := .inr (.inr i))
      (by rintro (h : (Sum.inl i : HypIndex r ε) = Sum.inr (Sum.inr i)); cases h)
      hMx
    have e1 : (M * A) (.inl i) (.inr (.inr i)) = M (.inl i) (.inl i) * cE := by
      rw [hA, Matrix.mul_single_apply_same]
    have hleft : (M * N) (.inl i) (.inr (.inr i)) = M (.inl i) (.inl i) * cE := by
      rw [show N = A from rfl, e1]
    have f1 : (A * M) (.inl i) (.inr (.inr i)) = cE * M (.inr (.inr i)) (.inr (.inr i)) := by
      rw [hA, Matrix.single_mul_apply_same]
    have hright : (N * M) (.inl i) (.inr (.inr i)) =
        cE * M (.inr (.inr i)) (.inr (.inr i)) := by
      rw [show N = A from rfl, f1]
    rw [hleft, hright] at hkey
    rw [mul_comm cE (M (.inr (.inr i)) (.inr (.inr i)))] at hkey
    exact mul_right_cancel₀ hcE0 hkey
  have hzheis : ∀ k : Fin ε, c0 = M (.inr (.inl k)) (.inr (.inl k)) := by
    intro k
    obtain ⟨b, hb⟩ := exists_add_bar_eq_neg_one h
    let u : hypSU h r ε := zHeisElt h (⟨0, hr⟩ : Fin r) k hb
    have huU : u ∈ hypUnitriangular h r ε := zHeisElt_mem h (⟨0, hr⟩ : Fin r) k hb
    set A : Matrix (HypIndex r ε) (HypIndex r ε) K :=
      Matrix.single (.inr (.inl k)) (.inr (.inr (⟨0, hr⟩ : Fin r))) (1 : K) with hA
    set B : Matrix (HypIndex r ε) (HypIndex r ε) K :=
      Matrix.single (.inl (⟨0, hr⟩ : Fin r)) (.inr (.inl k)) (1 : K) with hB
    set C : Matrix (HypIndex r ε) (HypIndex r ε) K :=
      Matrix.single (.inl (⟨0, hr⟩ : Fin r)) (.inr (.inr (⟨0, hr⟩ : Fin r))) b with hC
    let N : Matrix (HypIndex r ε) (HypIndex r ε) K := A - B + C
    have humat : ((u : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
        1 + N := by
      rw [show ((u : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
        1 + zHeisNil (⟨0, hr⟩ : Fin r) k b from rfl]
      rfl
    obtain ⟨z, hz, hgu⟩ := exists_hypScalars_mul_of_comm (g := g) (u := u)
      (((Subgroup.mem_centralizer_iff.mp hx) (hypProj h r ε u) ⟨u, huU, rfl⟩).symm)
    obtain ⟨cz, hznorm, hzpow, hzGL⟩ := mem_normOneScalars.mp hz
    have hzmat : ((z : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
        Matrix.scalar (HypIndex r ε) (cz : K) := by
      rw [hzGL, GeneralLinearGroup.coe_scalar]
    have hkey := mul_N_eq_N_mul_of_conj_scalar hzmat hgu huU hMT humat
      (x := .inl (⟨0, hr⟩ : Fin r)) (y := .inr (.inl k))
      (by rintro (h : (Sum.inl (⟨0, hr⟩ : Fin r) : HypIndex r ε) = Sum.inr (Sum.inl k)); cases h)
      hM0
    have e1 : (M * A) (.inl (⟨0, hr⟩ : Fin r)) (.inr (.inl k)) = 0 := by
      rw [hA, Matrix.mul_single_apply_of_ne _ _ _ _ _
        (by simp : (Sum.inr (Sum.inl k) : HypIndex r ε) ≠ Sum.inr (Sum.inr (⟨0, hr⟩ : Fin r)))]
    have e2 : (M * B) (.inl (⟨0, hr⟩ : Fin r)) (.inr (.inl k)) =
        M (.inl (⟨0, hr⟩ : Fin r)) (.inl (⟨0, hr⟩ : Fin r)) * 1 := by
      rw [hB, Matrix.mul_single_apply_same]
    have e3 : (M * C) (.inl (⟨0, hr⟩ : Fin r)) (.inr (.inl k)) = 0 := by
      rw [hC, Matrix.mul_single_apply_of_ne _ _ _ _ _
        (by simp : (Sum.inr (Sum.inl k) : HypIndex r ε) ≠ Sum.inr (Sum.inr (⟨0, hr⟩ : Fin r)))]
    have hleft : (M * N) (.inl (⟨0, hr⟩ : Fin r)) (.inr (.inl k)) =
        -M (.inl (⟨0, hr⟩ : Fin r)) (.inl (⟨0, hr⟩ : Fin r)) := by
      rw [show N = A - B + C from rfl, Matrix.mul_add, Matrix.mul_sub, Matrix.add_apply,
        Matrix.sub_apply, e1, e2, e3, zero_sub, mul_one]
      ring
    have hzero : M (.inr (.inr (⟨0, hr⟩ : Fin r))) (.inr (.inl k)) = 0 := by
      rw [hMblk]; rfl
    have f1 : (A * M) (.inl (⟨0, hr⟩ : Fin r)) (.inr (.inl k)) = 0 := by
      rw [hA, Matrix.single_mul_apply_of_ne _ _ _ _ _
        (by simp : (Sum.inl (⟨0, hr⟩ : Fin r) : HypIndex r ε) ≠ Sum.inr (Sum.inl k))]
    have f2 : (B * M) (.inl (⟨0, hr⟩ : Fin r)) (.inr (.inl k)) =
        1 * M (.inr (.inl k)) (.inr (.inl k)) := by
      rw [hB, Matrix.single_mul_apply_same]
    have f3 : (C * M) (.inl (⟨0, hr⟩ : Fin r)) (.inr (.inl k)) =
        b * M (.inr (.inr (⟨0, hr⟩ : Fin r))) (.inr (.inl k)) := by
      rw [hC, Matrix.single_mul_apply_same]
    have hright : (N * M) (.inl (⟨0, hr⟩ : Fin r)) (.inr (.inl k)) =
        -M (.inr (.inl k)) (.inr (.inl k)) := by
      rw [show N = A - B + C from rfl, Matrix.add_mul, Matrix.sub_mul, Matrix.add_apply,
        Matrix.sub_apply, f1, f2, f3, hzero, mul_zero, zero_sub, one_mul]
      ring
    rw [hleft, hright] at hkey
    exact neg_inj.mp hkey
  have he : ∀ i : Fin r, M (.inl i) (.inl i) = c0 := by
    intro i
    by_cases hi : i = (⟨0, hr⟩ : Fin r)
    · rw [hi, hc0]
    · exact (hshort i hi).symm
  have hdiag : ∀ y : HypIndex r ε, M y y = c0 := by
    intro y
    rcases y with i | k | i
    · exact he i
    · exact (hzheis k).symm
    · rw [← hlong i]
      exact he i
  have hnormc : h.norm c0 = 1 := by
    have hAe : M (.inl (⟨0, hr⟩ : Fin r)) (.inl (⟨0, hr⟩ : Fin r)) = blkA M (⟨0, hr⟩ : Fin r) (⟨0, hr⟩ : Fin r) := hAii _
    have hAf : M (.inr (.inr (⟨0, hr⟩ : Fin r))) (.inr (.inr (⟨0, hr⟩ : Fin r))) =
        (h.bar (blkA M (⟨0, hr⟩ : Fin r) (⟨0, hr⟩ : Fin r)))⁻¹ := hFii _
    have hrel : blkA M (⟨0, hr⟩ : Fin r) (⟨0, hr⟩ : Fin r) = (h.bar (blkA M (⟨0, hr⟩ : Fin r) (⟨0, hr⟩ : Fin r)))⁻¹ :=
      hAe.symm.trans ((hlong (⟨0, hr⟩ : Fin r)).trans hAf)
    have hc0A : c0 = blkA M (⟨0, hr⟩ : Fin r) (⟨0, hr⟩ : Fin r) := by rw [hc0]; exact hAe
    have hAA : h.bar (blkA M (⟨0, hr⟩ : Fin r) (⟨0, hr⟩ : Fin r)) = (blkA M (⟨0, hr⟩ : Fin r) (⟨0, hr⟩ : Fin r))⁻¹ := by
      have hb := congrArg h.bar hrel
      rw [map_inv₀, UnitaryFieldData.bar_bar h] at hb
      exact hb
    rw [UnitaryFieldData.norm, hc0A, hAA]
    exact mul_inv_cancel₀ (hAne (⟨0, hr⟩ : Fin r))
  have hpowc : c0 ^ (2 * r + ε) = 1 := by
    have hprodA : (∏ i : Fin r, blkA M i i) = c0 ^ r := by
      rw [Finset.prod_congr rfl (fun i _ => ?_), Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
      rw [← hAii i, hdiag]
    have hprodD : (∏ i : Fin r, blkD M i i) = c0 ^ r := by
      rw [Finset.prod_congr rfl (fun i _ => ?_), Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
      rw [hDii i, ← hFii i]
      exact hdiag _
    have hprodP : (∏ k : Fin ε, blkP M k k) = c0 ^ ε := by
      rw [Finset.prod_congr rfl (fun k _ => ?_), Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
      rw [show blkP M k k = M (.inr (.inl k)) (.inr (.inl k)) from by rw [hMblk]; rfl, hdiag]
    have hd := hdet
    rw [hMblk, det_blk3, det_of_isUpperTriangular hA, det_of_isUpperTriangular hP,
      det_of_isLowerTriangular _ hD, hprodA, hprodP, hprodD] at hd
    rw [← hd, ← pow_add, ← pow_add]
    congr 1
    ring
  set u0 : Kˣ := Units.mk0 c0 hc0ne with hu0
  have hu0val : (u0 : K) = c0 := rfl
  have hu0pow : u0 ^ (2 * r + ε) = 1 := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact hpowc
  have hd0 : ∀ k : Fin ε, h.norm (((fun _ : Fin ε => u0) k : Kˣ) : K) = 1 := fun _ => hnormc
  have hbar : h.bar (u0 : K) = (u0 : K)⁻¹ := by
    have h := hnormc
    rw [UnitaryFieldData.norm, ← hu0val] at h
    exact eq_inv_of_mul_eq_one_right h
  have hp0 : torusRatio h (fun _ : Fin r => u0) (fun _ : Fin ε => u0) = 1 := by
    rw [torusRatio]
    have hdiv : (u0 : K) / h.bar (u0 : K) = (u0 : K) * (u0 : K) := by
      rw [hbar, div_eq_mul_inv, inv_inv]
    rw [Finset.prod_congr rfl (fun i _ => hdiv), Finset.prod_const, Finset.prod_const,
      Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
    have h1 : ((u0 : K) * (u0 : K)) ^ r * (u0 : K) ^ ε = (u0 : K) ^ (2 * r + ε) := by
      conv_lhs => rw [mul_pow, ← pow_add, ← pow_add]
      congr 1
      ring
    rw [h1]
    exact hpowc
  obtain ⟨z0, hz0T, hz0mat, hz0diag⟩ := exists_mem_hypTorus_diag h hε hd0 hp0
  have hz0diagval : ((z0 : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      Matrix.scalar (HypIndex r ε) (u0 : K) := by
    rw [hz0mat, Matrix.scalar_apply]
    congr 1
    funext x
    rcases x with i | k | i
    · rfl
    · rfl
    · show (h.bar ((fun _ : Fin r => u0) i))⁻¹ = (u0 : K)
      rw [hbar, inv_inv]
  have hz0Z : z0 ∈ hypScalars h r ε := by
    refine mem_normOneScalars.mpr ⟨u0, hnormc, hu0pow, ?_⟩
    exact Units.ext hz0diagval
  have hz0inv : ((z0⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K) =
      GeneralLinearGroup.scalar (HypIndex r ε) u0⁻¹ := by
    refine Units.ext ?_
    show (((z0⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) = Matrix.scalar (HypIndex r ε) ((u0⁻¹ : Kˣ) : K)
    rw [Subgroup.coe_inv, Matrix.coe_units_inv, hz0diagval,
      inv_scalar_eq (Units.ne_zero u0), Units.val_inv_eq_inv_val]
  have hmatu' : ((z0⁻¹ * g : hypSU h r ε) : GL (HypIndex r ε) K) =
        Matrix.scalar (HypIndex r ε) ((u0 : K)⁻¹) * M := by
    rw [Subgroup.coe_mul, Units.val_mul, hz0inv, ← hM, GeneralLinearGroup.coe_scalar,
      Units.val_inv_eq_inv_val]
  set N' : Matrix (HypIndex r ε) (HypIndex r ε) K :=
    Matrix.scalar (HypIndex r ε) ((u0 : K)⁻¹) * M - 1 with hN'
  have hN0 : ∀ a, N' a a = 0 := by
    intro a
    rw [hN', Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_mul, hdiag a,
      Matrix.one_apply_eq, ← hu0val, inv_mul_cancel₀ (Units.ne_zero u0), sub_self]
  have hNup : ∀ a b, fullPos b < fullPos a → N' a b = 0 := by
    intro a b hba
    have hab : a ≠ b := fun h => by rw [h] at hba; exact lt_irrefl _ hba
    rw [hN', Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_mul, hMT hba, mul_zero,
      Matrix.one_apply_ne hab, sub_zero]
  have hu'U : z0⁻¹ * g ∈ hypUnitriangular h r ε := by
    refine CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_hypUnitriangular_of_strict
      (N := N') ?_ ?_
    · rw [hmatu', hN']
      abel
    · intro a b hab
      rcases lt_trichotomy (fullPos a) (fullPos b) with h | h | h
      · exact h
      · exact absurd (by rw [fullPos_injective h]; exact hN0 b) hab
      · exact absurd (hNup a b h) hab
  refine ⟨z0⁻¹ * g, hu'U, ?_⟩
  have hz0ker : hypProj h r ε z0 = 1 := by
    have hmem := hz0Z
    rw [← ker_hypProj h r ε] at hmem
    exact MonoidHom.mem_ker.mp hmem
  rw [map_mul, map_inv, hz0ker, inv_one, one_mul]

end CFSG.ClassicalGroups.UnitaryFlag

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.SQTK CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient

theorem odd_centralizer_centralizes_of_component_2A
    {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsQuasisimple L)
    (m : ℕ) (hm : 3 ≤ m) (Q : TauCeti.PrimePower) (hQ : Q.p = 2)
    (hv : (TauCeti.LieTypeIndex.twistedA m Q).Valid)
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.twistedA m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    {U : Subgroup L} (hU2 : IsPGroup 2 U)
    (hUmax : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    ∀ {x : L}, Odd (orderOf x) → x ∈ Subgroup.centralizer (U : Set L) →
      ∀ l : L, x * l = l * x := by
  classical
  set rr : ℕ := (m + 1) / 2 with hrr
  set ee : ℕ := (m + 1) % 2 with hee
  have h2r : 2 * rr + ee = m + 1 := by omega
  have hee1 : ee ≤ 1 := by omega
  have hrr1 : 1 ≤ rr := by omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  let K := GaloisField 2 (2 * Q.exponent)
  have hK : UnitaryFieldData 2 Q.exponent K :=
    { prime := Nat.prime_two
      one_le := Q.exponent_pos
      card := GaloisField.card 2 (2 * Q.exponent) (by have := Q.exponent_pos; omega) }
  have hK' : UnitaryFieldData Q.p Q.exponent K :=
    { prime := Q.prime_p
      one_le := Q.exponent_pos
      card := by
        rw [hQ]
        exact GaloisField.card 2 (2 * Q.exponent) (by have := Q.exponent_pos; omega) }
  haveI : Finite K := hK.finite
  haveI : Finite (hypPSU hK rr ee) :=
    Finite.of_surjective (hypProj hK rr ee) (hypProj_surjective hK rr ee)
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := rr) (ε := ee) hK
  let e1 : (TauCeti.CFSGIndex.lie
      (⟨TauCeti.LieTypeIndex.twistedA m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group ≃*
      StatedProj (StatedSU (m + 1) (2 ^ Q.exponent) K) := by
    have h := (CFSG.Adapters.CatalogueFieldBridges.primeFormP_one_mulEquiv_twistedA hK'
        (N := m + 1) (by omega) hv).some.symm.trans
      (((CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.nonempty_primeFormP_mulEquiv hK'
        (show CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.IsPrimeFormGram
          (1 : GL (Fin (m + 1)) K) from
          ⟨by simp, fun i j => by
            rw [Units.val_one, Matrix.one_apply]
            split_ifs
            · exact Subfield.one_mem ⊥
            · exact Subfield.zero_mem ⊥⟩)).some).trans
        (unitaryPSUEquiv hK' (by omega)))
    rwa [show Q.p ^ Q.exponent = 2 ^ Q.exponent from by rw [hQ]] at h
  let e2 : hypPSU hK rr ee ≃*
      StatedProj (StatedSU (2 * rr + ee) (2 ^ Q.exponent) K) :=
    hypPSUEquivStatedProj hK hR (by omega)
  let eIdx : StatedProj (StatedSU (m + 1) (2 ^ Q.exponent) K) ≃*
      StatedProj (StatedSU (2 * rr + ee) (2 ^ Q.exponent) K) :=
    h2r.symm ▸ MulEquiv.refl (StatedProj (StatedSU (m + 1) (2 ^ Q.exponent) K))
  let Φ : L ⧸ Subgroup.center L ≃* hypPSU hK rr ee :=
    e.trans (e1.trans (eIdx.trans e2.symm))
  intro x hxodd hxcent l
  let πL : L →* L ⧸ Subgroup.center L := QuotientGroup.mk' (Subgroup.center L)
  have hUindex : ¬ 2 ∣ U.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hUmax.2.2
  let S : Sylow 2 L := hU2.toSylow hUindex
  have hScoe : (S : Subgroup L) = U := IsPGroup.toSylow_coe hU2 hUindex
  let W : Sylow 2 (L ⧸ Subgroup.center L) :=
    Sylow.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center L)) S
  have hWcoe : (W : Subgroup (L ⧸ Subgroup.center L)) = U.map πL := by
    rw [Sylow.coe_mapSurjective, hScoe]
  let V : Sylow 2 (hypPSU hK rr ee) := Sylow.mapSurjective (f := Φ.toMonoidHom) Φ.surjective W
  have hVcoe : (V : Subgroup (hypPSU hK rr ee)) = W.map Φ := rfl
  let y : hypPSU hK rr ee := Φ (πL x)
  have hyodd : Odd (orderOf y) := by
    rw [MulEquiv.orderOf_eq]
    exact Odd.of_dvd_nat hxodd (orderOf_map_dvd πL x)
  have hycent : y ∈ Subgroup.centralizer ((V : Subgroup (hypPSU hK rr ee)) :
      Set (hypPSU hK rr ee)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    rw [hVcoe, hWcoe] at hu
    obtain ⟨w, hw, rfl⟩ := hu
    obtain ⟨u0, hu0, rfl⟩ := hw
    show Φ (πL u0) * Φ (πL x) = Φ (πL x) * Φ (πL u0)
    calc Φ (πL u0) * Φ (πL x) = Φ (πL u0 * πL x) := (map_mul Φ _ _).symm
      _ = Φ (πL (u0 * x)) := by rw [← map_mul]
      _ = Φ (πL (x * u0)) := by rw [(Subgroup.mem_centralizer_iff.mp hxcent) u0 hu0]
      _ = Φ (πL x * πL u0) := by rw [← map_mul]
      _ = Φ (πL x) * Φ (πL u0) := map_mul Φ _ _
  obtain ⟨P₀, hP₀coe⟩ := (unitary_order_and_Sylow hK hrr1 hee1).2.2.2.2.1
  have hQ2 : Q.p = 2 := hQ
  have hŪ2 : IsPGroup 2 ↥(hypProjUnitriangular hK rr ee) := by
    have h := P₀.isPGroup'
    rw [hP₀coe] at h
    refine isPGroup_iff_orderOf_dvd_pow.mpr fun g => ?_
    obtain ⟨k, hk⟩ := isPGroup_iff_orderOf_dvd_pow.mp h g
    exact ⟨k, by simpa only [hQ2] using hk⟩
  have hŪindex : ¬ 2 ∣ (hypProjUnitriangular hK rr ee).index := by
    have h := P₀.not_dvd_index
    rw [hP₀coe] at h
    intro h2
    exact h (by simpa only [hQ2.symm] using h2)
  let P : Sylow 2 (hypPSU hK rr ee) := hŪ2.toSylow hŪindex
  have hPcoe : (P : Subgroup (hypPSU hK rr ee)) = hypProjUnitriangular hK rr ee :=
    IsPGroup.toSylow_coe hŪ2 hŪindex
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (hypPSU hK rr ee) V P
  have hPsmul : (P : Subgroup (hypPSU hK rr ee)) =
      MulAut.conj k • (V : Subgroup (hypPSU hK rr ee)) := by
    rw [← hk, Sylow.coe_subgroup_smul]
  have hmem_iff : ∀ x : hypPSU hK rr ee,
      x ∈ (P : Subgroup (hypPSU hK rr ee)) ↔
        k⁻¹ * x * k ∈ (V : Subgroup (hypPSU hK rr ee)) := by
    intro x
    rw [hPsmul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      MulAut.conj_inv_apply]
  have hconj : k * y * k⁻¹ ∈ Subgroup.centralizer
      ((P : Subgroup (hypPSU hK rr ee)) : Set (hypPSU hK rr ee)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hv : k⁻¹ * u * k ∈ (V : Subgroup (hypPSU hK rr ee)) := (hmem_iff u).mp hu
    have hu' : u = k * (k⁻¹ * u * k) * k⁻¹ := by group
    rw [hu']
    calc (k * (k⁻¹ * u * k) * k⁻¹) * (k * y * k⁻¹)
        = k * ((k⁻¹ * u * k) * y) * k⁻¹ := by group
      _ = k * (y * (k⁻¹ * u * k)) * k⁻¹ := by
          rw [(Subgroup.mem_centralizer_iff.mp hycent) (k⁻¹ * u * k) hv]
      _ = (k * y * k⁻¹) * (k * (k⁻¹ * u * k) * k⁻¹) := by group
  have hmemP : k * y * k⁻¹ ∈ (P : Subgroup (hypPSU hK rr ee)) := by
    have hc := hconj
    rw [hPcoe] at hc
    rw [hPcoe]
    exact centralizer_hypProjUnitriangular_le hK hrr1 hee1 hc
  have hmemV : y ∈ V := by
    have h2 := (hmem_iff _).mp hmemP
    have h3 : k⁻¹ * (k * y * k⁻¹) * k = y := by group
    rwa [h3] at h2
  have hyone : y = 1 := by
    by_contra hne
    have hne' : (⟨y, hmemV⟩ : (V : Subgroup (hypPSU hK rr ee))) ≠ 1 := by
      intro h
      exact hne (congrArg Subtype.val h)
    have h2 : 2 ∣ orderOf (⟨y, hmemV⟩ : (V : Subgroup (hypPSU hK rr ee))) :=
      V.isPGroup'.dvd_orderOf hne'
    have hyV : orderOf (⟨y, hmemV⟩ : (V : Subgroup (hypPSU hK rr ee))) = orderOf y :=
      (Subgroup.orderOf_coe _).symm
    rw [hyV] at h2
    exact hyodd.not_two_dvd_nat h2
  have hxZ : x ∈ Subgroup.center L := by
    have h1 : Φ (πL x) = 1 := hyone
    have h2 : πL x = 1 := Φ.injective (by rw [h1, map_one])
    exact (QuotientGroup.eq_one_iff x).mp h2
  exact (Subgroup.mem_center_iff.mp hxZ l).symm

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem noXBlock_borelPre_done_2A
    (hX : GNSetting X T) {Ls : Subgroup (X ⧸ gnC T)}
    (hLs : CFSG.Open.IsComponentOf Ls ⊤)
    (hinv : gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)))
    (m : ℕ) (hm : 3 ≤ m) (Q : TauCeti.PrimePower) (hQ : Q.p = 2)
    (hv : (TauCeti.LieTypeIndex.twistedA m Q).Valid)
    (e : ↥Ls ⧸ Subgroup.center ↥Ls ≃* (TauCeti.CFSGIndex.lie
      (⟨TauCeti.LieTypeIndex.twistedA m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    (Y : Subgroup X) (hY : Y ≤ borelPre T Ls)
    (hsub : CFSG.Open.IsSubnormal Y (borelPre T Ls))
    (hblock : CFSG.AGLEmbedding.InClassXBlock Y) : False := by
  classical
  haveI : Finite (X ⧸ gnC T) :=
    Finite.of_surjective (QuotientGroup.mk' (gnC T)) (QuotientGroup.mk'_surjective (gnC T))
  refine noXBlock_borelPre_done hX hLs hinv ?_ Y hY hsub hblock
  refine hLI_of_component_li hX hLs ?_
  intro U hU2 hUmax x hxodd hxc
  exact odd_centralizer_centralizes_of_component_2A hLs.2.2 m hm Q hQ hv e hU2 hUmax hxodd hxc

end CFSG.LocalAnalysis.RankThreeUC.S15

end
