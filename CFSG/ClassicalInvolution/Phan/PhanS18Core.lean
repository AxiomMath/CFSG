module

public import CFSG.ClassicalInvolution.Phan.PhanS17Mu

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q7

open SimpleGraph CFSG.ClassicalInvolution.PhanB3.S.Std CFSG.ClassicalInvolution.PhanB3.S.Std.Q

variable {K K' : Type} [Field K] [Field K']

@[expose] def MuConnectedAt (M : Model K) (A C : FFPt M) : Prop :=
  ∀ B D : FFPt M, (ffGraph M).Adj A B → (ffGraph M).Adj C B → (ffGraph M).Adj A D →
    (ffGraph M).Adj C D → Relation.ReflTransGen (MuAdj M A C) B D

theorem muConnected_iff_at (M : Model K) :
    MuConnected M ↔ ∀ A C : FFPt M, bf M A.1.rep C.1.rep ≠ 0 → MuConnectedAt M A C :=
  Iff.rfl

theorem ffPt_eq_iff {M : Model K} (A B : FFPt M) :
    A = B ↔ ∃ c : K, c ≠ 0 ∧ A.1.rep = c • B.1.rep := by
  constructor
  · rintro rfl
    exact ⟨1, one_ne_zero, by simp⟩
  · rintro ⟨c, _, h⟩
    apply Subtype.ext
    exact (Projectivization.mk_rep A.1).symm.trans
      (((Projectivization.mk_eq_mk_iff' K _ _ A.1.rep_nonzero B.1.rep_nonzero).2
        ⟨c, h.symm⟩).trans (Projectivization.mk_rep B.1))

structure Simil (M : Model K) (M' : Model K') where
  φ : K ≃+* K'
  T : Vec K ≃ Vec K'
  n : K'
  n_ne : n ≠ 0
  smul : ∀ (c : K) (x : Vec K), T (c • x) = φ c • T x
  bf_eq : ∀ x y : Vec K, bf M' (T x) (T y) = n * φ (bf M x y)
  comm : ∀ x : Vec K, T (tauV M x) = tauV M' (T x)

namespace Simil

variable {M : Model K} {M' : Model K'} (S : Simil M M')

theorem her_eq (x y : Vec K) : her M' (S.T x) (S.T y) = S.n * S.φ (her M x y) := by
  unfold her
  rw [← S.comm, S.bf_eq]

theorem gram_eq (x y : Vec K) : gram M' (S.T x) (S.T y) = S.n ^ 2 * S.φ (gram M x y) := by
  simp only [gram, S.her_eq, map_sub, map_mul]
  ring

theorem isFF_iff (x : Vec K) : IsFF M' (S.T x) ↔ IsFF M x := by
  unfold IsFF
  rw [S.bf_eq, S.her_eq]
  simp [S.n_ne]

theorem col_iff (x y : Vec K) : Col M' (S.T x) (S.T y) ↔ Col M x y := by
  unfold Col
  rw [S.bf_eq, S.gram_eq]
  simp [S.n_ne]

def symm : Simil M' M where
  φ := S.φ.symm
  T := S.T.symm
  n := S.φ.symm S.n⁻¹
  n_ne := by simpa using S.n_ne
  smul c x := by
    apply S.T.injective
    rw [S.smul]
    simp
  bf_eq x y := by
    have h := S.bf_eq (S.T.symm x) (S.T.symm y)
    simp only [Equiv.apply_symm_apply] at h
    have h2 : S.φ (bf M (S.T.symm x) (S.T.symm y)) = S.n⁻¹ * bf M' x y := by
      rw [h, ← mul_assoc, inv_mul_cancel₀ S.n_ne, one_mul]
    have h3 := congrArg S.φ.symm h2
    rw [RingEquiv.symm_apply_apply, map_mul] at h3
    exact h3
  comm x := by
    apply S.T.injective
    rw [S.comm]
    simp

theorem isFF_T {x : Vec K} (hx : IsFF M x) : IsFF M' (S.T x) := (S.isFF_iff x).2 hx

noncomputable def ptMap (A : FFPt M) : FFPt M' := FFPt.mk M' (S.isFF_T A.2)

theorem ptMap_rep (A : FFPt M) : ∃ c : K', c ≠ 0 ∧ (S.ptMap A).1.rep = c • S.T A.1.rep :=
  FFPt.mk_rep M' (S.isFF_T A.2)

theorem ptMap_eq_of_rep {A : FFPt M} {B : FFPt M'} {d : K'} (hd : d ≠ 0)
    (h : B.1.rep = d • S.T A.1.rep) : S.ptMap A = B := by
  obtain ⟨c, hc, hA⟩ := S.ptMap_rep A
  rw [ffPt_eq_iff]
  refine ⟨c * d⁻¹, mul_ne_zero hc (inv_ne_zero hd), ?_⟩
  rw [hA, h, smul_smul, mul_assoc, inv_mul_cancel₀ hd, mul_one]

theorem adj_ptMap (A B : FFPt M) :
    (ffGraph M').Adj (S.ptMap A) (S.ptMap B) ↔ (ffGraph M).Adj A B := by
  obtain ⟨c, hc, hA⟩ := S.ptMap_rep A
  obtain ⟨d, hd, hB⟩ := S.ptMap_rep B
  show Col M' (S.ptMap A).1.rep (S.ptMap B).1.rep ↔ Col M A.1.rep B.1.rep
  rw [hA, hB, col_smul M' hc hd, S.col_iff]

theorem symm_ptMap_ptMap (A : FFPt M) : S.symm.ptMap (S.ptMap A) = A := by
  obtain ⟨c, hc, hA⟩ := S.ptMap_rep A
  refine S.symm.ptMap_eq_of_rep (d := (S.φ.symm c)⁻¹) (inv_ne_zero (by simpa using hc)) ?_
  have : S.symm.T (S.ptMap A).1.rep = S.φ.symm c • A.1.rep := by
    rw [hA]
    change S.T.symm (c • S.T A.1.rep) = _
    apply S.T.injective
    rw [S.smul]
    simp
  rw [this, smul_smul, inv_mul_cancel₀ (by simpa using hc), one_smul]

theorem ptMap_symm_ptMap (B : FFPt M') : S.ptMap (S.symm.ptMap B) = B := by
  obtain ⟨c, hc, hB⟩ := S.symm.ptMap_rep B
  refine S.ptMap_eq_of_rep (d := (S.φ c)⁻¹) (inv_ne_zero (by simpa using hc)) ?_
  have : S.T (S.symm.ptMap B).1.rep = S.φ c • B.1.rep := by
    rw [hB, S.smul]
    change S.φ c • S.T (S.T.symm B.1.rep) = _
    simp
  rw [this, smul_smul, inv_mul_cancel₀ (by simpa using hc), one_smul]

noncomputable def ptEquiv : FFPt M ≃ FFPt M' where
  toFun := S.ptMap
  invFun := S.symm.ptMap
  left_inv := S.symm_ptMap_ptMap
  right_inv := S.ptMap_symm_ptMap

noncomputable def graphIso : ffGraph M ≃g ffGraph M' where
  toEquiv := S.ptEquiv
  map_rel_iff' := fun {A B} => S.adj_ptMap A B

theorem bf_ptMap_ne_iff (A C : FFPt M) :
    bf M' (S.ptMap A).1.rep (S.ptMap C).1.rep ≠ 0 ↔ bf M A.1.rep C.1.rep ≠ 0 := by
  obtain ⟨c, hc, hA⟩ := S.ptMap_rep A
  obtain ⟨d, hd, hC⟩ := S.ptMap_rep C
  rw [hA, hC, bf_smul_left, bf_smul_right, S.bf_eq]
  have h1 : c * (d * (S.n * S.φ (bf M A.1.rep C.1.rep))) =
      (c * d * S.n) * S.φ (bf M A.1.rep C.1.rep) := by ring
  rw [h1]
  simp [hc, hd, S.n_ne]

theorem muConnectedAt_of_simil {A C : FFPt M}
    (h : MuConnectedAt M' (S.ptMap A) (S.ptMap C)) : MuConnectedAt M A C := by
  intro B D hAB hCB hAD hCD
  have h1 := h (S.ptMap B) (S.ptMap D) ((S.adj_ptMap A B).2 hAB) ((S.adj_ptMap C B).2 hCB)
    ((S.adj_ptMap A D).2 hAD) ((S.adj_ptMap C D).2 hCD)
  have hstep : ∀ x y, MuAdj M' (S.ptMap A) (S.ptMap C) x y →
      MuAdj M A C (S.symm.ptMap x) (S.symm.ptMap y) := by
    rintro x y ⟨hxy, hAx, hAy, hCx, hCy⟩
    refine ⟨(S.symm.adj_ptMap x y).2 hxy, ?_, ?_, ?_, ?_⟩
    · have := (S.symm.adj_ptMap (S.ptMap A) x).2 hAx
      rwa [S.symm_ptMap_ptMap] at this
    · have := (S.symm.adj_ptMap (S.ptMap A) y).2 hAy
      rwa [S.symm_ptMap_ptMap] at this
    · have := (S.symm.adj_ptMap (S.ptMap C) x).2 hCx
      rwa [S.symm_ptMap_ptMap] at this
    · have := (S.symm.adj_ptMap (S.ptMap C) y).2 hCy
      rwa [S.symm_ptMap_ptMap] at this
  have h2 := Relation.ReflTransGen.lift S.symm.ptMap hstep _ _ h1
  simpa only [Function.onFun, S.symm_ptMap_ptMap] using h2

end Simil

structure SigmaIso (M : Model K) where
  toLinearEquiv : Vec K ≃ₗ[K] Vec K
  bf_eq : ∀ x y : Vec K, bf M (toLinearEquiv x) (toLinearEquiv y) = bf M x y
  comm : ∀ x : Vec K, toLinearEquiv (tauV M x) = tauV M (toLinearEquiv x)

@[expose] def SigmaIso.toSimil {M : Model K} (g : SigmaIso M) : Simil M M where
  φ := RingEquiv.refl K
  T := g.toLinearEquiv.toEquiv
  n := 1
  n_ne := one_ne_zero
  smul c x := by simp
  bf_eq x y := by simp [g.bf_eq]
  comm := g.comm

theorem SigmaIso.toSimil_T {M : Model K} (g : SigmaIso M) (x : Vec K) :
    g.toSimil.T x = g.toLinearEquiv x := rfl

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q7
