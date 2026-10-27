module

public import CFSG.LargeExtraspecial.AS35WL43Q
public import CFSG.LargeExtraspecial.AS35WL43N
public import CFSG.LargeExtraspecial.AS35WL4

public section

namespace CFSG.LargeExtraspecial

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartTwo.Census
  CFSG.ComponentClassification.CatFactsL4U4

namespace AS35W

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] noncomputable def f3 : ZMod 3 ≃+* nineBase :=
  letI := Fintype.ofFinite nineBase
  ZMod.ringEquiv nineBase fintype_card_nineBase

@[expose] def e4 : Fin 4 ≃ Fin 2 × Fin 2 := (finProdFinEquiv (m := 2) (n := 2)).symm

@[expose] noncomputable def pslCongr' {m n : Type} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] {R S : Type} [CommRing R] [CommRing S]
    (φ : SpecialLinearGroup m R ≃* SpecialLinearGroup n S) :
    ProjectiveSpecialLinearGroup m R ≃* ProjectiveSpecialLinearGroup n S :=
  QuotientGroup.congr _ _ φ (by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_center_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩ g
      obtain ⟨g', rfl⟩ := φ.surjective g
      change φ g' * φ y = φ y * φ g'
      rw [← map_mul, ← map_mul, hy]
    · intro hx
      refine ⟨φ.symm x, fun g => φ.injective ?_, by simp⟩
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hx])

@[expose] noncomputable def slReindex' {m n : Type} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] {R : Type} [CommRing R] (e : m ≃ n) :
    SpecialLinearGroup m R ≃* SpecialLinearGroup n R where
  toFun A := ⟨reindex e e (A : Matrix m m R), by rw [det_reindex_self]; exact A.2⟩
  invFun A := ⟨reindex e.symm e.symm (A : Matrix n n R), by rw [det_reindex_self]; exact A.2⟩
  left_inv A := Subtype.ext (by simp)
  right_inv A := Subtype.ext (by simp)
  map_mul' A B := Subtype.ext (by
    change reindex e e ((A : Matrix m m R) * (B : Matrix m m R)) =
      reindex e e (A : Matrix m m R) * reindex e e (B : Matrix m m R)
    rw [reindex_apply, reindex_apply, reindex_apply, submatrix_mul_equiv])

@[expose] noncomputable def slRing' {m : Type} [Fintype m] [DecidableEq m] {R S : Type}
    [CommRing R] [CommRing S] (f : R ≃+* S) :
    SpecialLinearGroup m R ≃* SpecialLinearGroup m S where
  toFun := SpecialLinearGroup.map f.toRingHom
  invFun := SpecialLinearGroup.map f.symm.toRingHom
  left_inv A := Subtype.ext (by ext i j; simp)
  right_inv A := Subtype.ext (by ext i j; simp)
  map_mul' := map_mul _

@[expose] noncomputable def phi43 :
    projectiveSL 4 (ZMod 3) ≃* ProjectiveSpecialLinearGroup (Fin 2 × Fin 2) nineBase :=
  (LinearCover.projectiveSpecialLinearEquivProjectiveSL 4 (ZMod 3)).symm.trans
    (pslCongr' ((slRing' f3).trans (slReindex' e4)))

theorem phi43_proj (g : SpecialLinearGroup (Fin 4) (ZMod 3)) :
    phi43 (proj 4 (ZMod 3) g) = QuotientGroup.mk' _ (slReindex' e4 (slRing' f3 g)) :=
  rfl

@[expose] def nSL : SpecialLinearGroup (Fin 4) (ZMod 3) :=
  ⟨InvClassL.stdN 2, by rw [InvClassL.det_stdN]; decide⟩

theorem f3_two : f3 2 = -1 := by
  rw [map_ofNat]
  have h3 : ((3 : ℕ) : nineBase) = 0 := CharP.cast_eq_zero nineBase 3
  push_cast at h3
  linear_combination h3

theorem phi43_nSL : slReindex' e4 (slRing' f3 nSL) = nineInvolution := by
  apply Subtype.ext
  refine Matrix.ext fun ⟨a, b⟩ ⟨c, d⟩ => ?_
  change f3 (InvClassL.stdN 2 (e4.symm (a, b)) (e4.symm (c, d))) =
    nineBlock (nineI • (1 : Matrix (Fin 2) (Fin 2) (GaloisField 3 2))) (a, b) (c, d)
  rw [nineBlock_i_smul_one_apply]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [e4, finProdFinEquiv, InvClassL.stdN, nineR, f3_two]

theorem false_of_u2 (hz : W2Data (projectiveSL 4 (ZMod 3)) (proj 4 (ZMod 3) nSL)) : False := by
  have : Finite (ProjectiveSpecialLinearGroup (Fin 2 × Fin 2) nineBase) :=
    Finite.of_equiv _ phi43.toEquiv
  have h := hz.map phi43
  rw [phi43_proj, phi43_nSL] at h
  exact false_of_nineInvolution h

theorem nonzero_three : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = -1 := by decide

theorem pow_four_three : ∀ x : ZMod 3, x ≠ 0 → x ^ 4 = 1 := by decide

theorem eq_two_of_not_isSquare {x : ZMod 3} (h0 : x ≠ 0) (h : ¬ IsSquare x) : x = 2 := by
  fin_cases x
  · exact absurd rfl h0
  · exact absurd ⟨1, rfl⟩ h
  · rfl

theorem w2Good_psl43 : W2Good (projectiveSL 4 (ZMod 3)) := by
  intro z hz
  exfalso
  have hchar : ringChar (ZMod 3) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; norm_num
  obtain ⟨g, rfl⟩ := proj_surjective 4 (ZMod 3) z
  have hpow : proj 4 (ZMod 3) g ^ 2 = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (by rw [hz.orderOf_eq])
  have hg2 : g * g ∈ scalars 4 (ZMod 3) := by
    rw [← proj_eq_one_iff, map_mul, ← sq, hpow]
  obtain ⟨c, -, hc⟩ := mem_scalars.1 hg2
  have hX : (g : Matrix (Fin 4) (Fin 4) (ZMod 3)) * g = (c : ZMod 3) • 1 := by
    have hc' : (g : Matrix (Fin 4) (Fin 4) (ZMod 3)) * g = scalar (Fin 4) (c : ZMod 3) := hc
    rw [hc', scalar_apply, smul_one_eq_diagonal]
  have hns : ∀ a : ZMod 3, (g : Matrix (Fin 4) (Fin 4) (ZMod 3)) ≠ a • 1 := by
    intro a ha
    have hdet : a ^ 4 = 1 := by
      have h1 := g.2
      rw [ha, det_smul, det_one, mul_one, Fintype.card_fin] at h1
      exact h1
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact absurd hdet (by decide)
    have h1 : proj 4 (ZMod 3) g = 1 := proj_eq_one_iff.2 ⟨Units.mk0 a ha0,
      Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hdet, Units.val_one]), by
        rw [ha, Units.val_mk0, scalar_apply, smul_one_eq_diagonal]⟩
    have h2 := hz.orderOf_eq
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have key : ∀ (P : GL (Fin 4) (ZMod 3)) (Y : SpecialLinearGroup (Fin 4) (ZMod 3)) (t : ZMod 3),
      t ≠ 0 → (t • (g : Matrix (Fin 4) (Fin 4) (ZMod 3))) * (P : Matrix (Fin 4) (Fin 4) (ZMod 3)) =
        (P : Matrix (Fin 4) (Fin 4) (ZMod 3)) * (Y : Matrix (Fin 4) (Fin 4) (ZMod 3)) →
      W2Data (projectiveSL 4 (ZMod 3)) (proj 4 (ZMod 3) Y) := by
    intro P Y t ht hP
    set A : GL (Fin 4) (ZMod 3) := P⁻¹
    have hz' := hz.map (conjAut 4 (ZMod 3) A)
    rw [conjAut_proj] at hz'
    set S := ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 (ZMod 3) A g
    have hS : (S : Matrix (Fin 4) (Fin 4) (ZMod 3)) =
        t⁻¹ • (Y : Matrix (Fin 4) (Fin 4) (ZMod 3)) := by
      rw [coe_slConjugation]
      have e1 : ((A : GL (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3)) *
          (P : Matrix (Fin 4) (Fin 4) (ZMod 3)) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      have e2 : ((A⁻¹ : GL (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3)) =
          (P : Matrix (Fin 4) (Fin 4) (ZMod 3)) := by rw [inv_inv]
      rw [e2]
      have e3 : (g : Matrix (Fin 4) (Fin 4) (ZMod 3)) * (P : Matrix (Fin 4) (Fin 4) (ZMod 3)) =
          t⁻¹ • ((P : Matrix (Fin 4) (Fin 4) (ZMod 3)) *
            (Y : Matrix (Fin 4) (Fin 4) (ZMod 3))) := by
        rw [← hP, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [Matrix.mul_assoc, e3, Matrix.mul_smul, ← Matrix.mul_assoc, e1, Matrix.one_mul]
    rcases nonzero_three _ (inv_ne_zero ht) with h1 | h1
    · have hSY : S = Y := Subtype.ext (by rw [hS, h1, one_smul])
      rwa [hSY] at hz'
    · set sc := scalarElement (-1 : (ZMod 3)ˣ) (by decide) (n := 4)
      have hSY : S = sc * Y := Subtype.ext (by
        rw [hS, h1, coe_mul4, coe_scalarElement, scalar_apply, ← smul_one_eq_diagonal,
          Matrix.smul_mul, Matrix.one_mul, Units.val_neg, Units.val_one])
      rw [hSY, map_mul, proj_eq_one_iff.2 (scalarElement_mem_scalars _ _), one_mul] at hz'
      exact hz'
  rcases InvClassL.classify_inv hchar hX c.ne_zero hns with
    ⟨l, hl0, -, -, P, hP⟩ | ⟨l, hl0, -, hdet, -⟩ | ⟨hsq, P, hP⟩
  · exact false_of_u1 (key P dSL l⁻¹ (inv_ne_zero hl0) hP)
  · rw [det_smul, g.2, mul_one, Fintype.card_fin, pow_four_three _ (inv_ne_zero hl0)] at hdet
    exact absurd hdet (by decide)
  · have hc2 := eq_two_of_not_isSquare c.ne_zero hsq
    rw [hc2] at hP
    exact false_of_u2 (key P nSL 1 one_ne_zero (by rw [one_smul]; exact hP))

theorem l43W2Input : L43W2Input := by
  intro K _ _ hK
  have : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP K 3 := charP_of_card_eq_prime hK'
  let f : ZMod 3 ≃+* K := ZMod.ringEquiv K hK'
  let Ψ : projectiveSL 4 K ≃* projectiveSL 4 (ZMod 3) :=
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL 4 K).symm.trans
      ((pslCongr' (slRing' f.symm)).trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL 4 (ZMod 3)))
  exact W2Good.of_mulEquiv Ψ w2Good_psl43

theorem l4W2Input : L4W2Input := l4W2Input_of l43W2Input

end AS35W

end CFSG.LargeExtraspecial
