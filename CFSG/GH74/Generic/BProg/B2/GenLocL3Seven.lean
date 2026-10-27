module

public import CFSG.GH74.Generic.BProg.B2.GenLocL3Good
public import CFSG.GH74.Generic.BProg.B2.GenLocL3Lin

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.CatalogueBHigherLinearAction
open scoped MatrixGroups

namespace GenLocL3Seven

open GenLocL3Good

theorem eq_one_of_card_prime {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p) (σ : K ≃+* K) : σ = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = p := by rw [Fintype.card_eq_nat_card]; exact hK
  let e := ZMod.ringEquivOfPrime K hp hK'
  have h1 : (σ : K →+* K).comp (e : ZMod p →+* K) = (e : ZMod p →+* K) := Subsingleton.elim _ _
  ext x
  obtain ⟨z, rfl⟩ := e.surjective x
  have := congrArg (fun f : ZMod p →+* K => f z) h1
  simpa using this

theorem not_isSquare_neg_one_of_card_seven {K : Type} [Field K] [Finite K] (hK : Nat.card K = 7) :
    ¬ IsSquare (-1 : K) := by
  have : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 7 := by rw [Fintype.card_eq_nat_card]; exact hK
  rw [FiniteField.isSquare_neg_one_iff, hK']
  norm_num

theorem eq_of_sq_eq_of_isSquare {K : Type} [Field K] {a b : K} (hb : b ≠ 0) (h : a * a = b * b)
    (hs : IsSquare (a * b)) (hneg : ¬ IsSquare (-1 : K)) : a = b := by
  have h1 : (a - b) * (a + b) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h1 with h2 | h2
  · linear_combination h2
  · exfalso
    apply hneg
    obtain ⟨r, hr⟩ := hs
    have ha : a = -b := by linear_combination h2
    refine ⟨r / b, ?_⟩
    rw [ha] at hr
    field_simp
    linear_combination hr

theorem det_diag2 {K : Type} [Field K] (a b : Kˣ) :
    ((diag2 a b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = (a : K) * b := by
  rw [coe_diag2, Matrix.det_diagonal, Fin.prod_univ_two]
  simp

theorem slConjugation_diag2_self {K : Type} [Field K] (a : Kˣ) :
    slConjugation 2 K (diag2 a a) = 1 := by
  refine MulEquiv.ext fun g => Subtype.ext ?_
  rw [LinearFlag.coe_slConjugation, coe_diag2, coe_diag2_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply] <;> field_simp

theorem blk_trivial_of_inner {K : Type} [Field K] [Finite K] (hK : Nat.card K = 7) {A : Type} [Group A]
    (hsq : ∀ a : A, a * a = 1)
    (α : A →* MulAut (LinearFlag.projectiveSL 3 K)) (hα : α.range ≤ frameStab 3 K) (i : Fin 2)
    (hin : ((rest i).comp (toFrame α hα)).range ≤
      (MulAut.conj : SL(2, K) →* MulAut SL(2, K)).range) :
    (noDual K).comap α ≤ ((rest i).comp (toFrame α hα)).ker := by
  intro a ha
  obtain ⟨x, σ, hx, hax⟩ := ha
  have hσ : σ = 1 := eq_one_of_card_prime (by norm_num) hK σ
  rw [hσ, map_one, mul_one] at hax
  obtain ⟨u, rfl⟩ := exists_diag3 hx
  have hsq1 : LinearFlag.conjAut 3 K (diag3 u) * LinearFlag.conjAut 3 K (diag3 u) = 1 := by
    rw [← hax, ← map_mul, hsq a, map_one]
  obtain ⟨c, hc0, hc⟩ := GenLocL3NFAux.scalar_of_conjAut_eq (diag3 u * diag3 u) 1
    (by rw [map_mul, map_one, hsq1])
  have hd : ∀ j, c * ((u j : K) * (u j : K)) = 1 := by
    intro j
    have := congrFun (congrFun hc j) j
    simp only [Units.val_one, Matrix.one_apply_eq, Units.val_mul, coe_diag3, Matrix.diagonal_mul_diagonal,
      Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul] at this
    linear_combination -this
  have hmem : (rest i).comp (toFrame α hα) a =
      slConjugation 2 K (diag2 (u (GenLocL3Blk.pos i 0)) (u (GenLocL3Blk.pos i 1))) := by
    rw [MonoidHom.comp_apply, ← rest_conjAut u i]
    congr 1
    exact Subtype.ext hax
  refine MonoidHom.mem_ker.2 ?_
  have hi : (rest i).comp (toFrame α hα) a ∈
      (MulAut.conj : SL(2, K) →* MulAut SL(2, K)).range := hin ⟨a, rfl⟩
  rw [hmem] at hi ⊢
  have hsqr := isSquare_det_of_mem_inn _ hi
  rw [det_diag2] at hsqr
  have hneg := not_isSquare_neg_one_of_card_seven hK
  have heq : ((u (GenLocL3Blk.pos i 0) : Kˣ) : K) = u (GenLocL3Blk.pos i 1) := by
    refine eq_of_sq_eq_of_isSquare (u (GenLocL3Blk.pos i 1)).ne_zero ?_ hsqr hneg
    have h0 := hd (GenLocL3Blk.pos i 0)
    have h1 := hd (GenLocL3Blk.pos i 1)
    have : c * (((u (GenLocL3Blk.pos i 0) : Kˣ) : K) * (u (GenLocL3Blk.pos i 0) : Kˣ)) =
      c * (((u (GenLocL3Blk.pos i 1) : Kˣ) : K) * (u (GenLocL3Blk.pos i 1) : Kˣ)) := by rw [h0, h1]
    exact mul_left_cancel₀ hc0 this
  rw [Units.ext heq]
  exact slConjugation_diag2_self _

section Assembly

variable {K : Type} [Field K] [Finite K]

theorem gammaAct_eq_top_of_le_frameStab_seven
    (hK : Nat.card K = 7)
    {A : Type} [Group A] [Finite A] (α : A →* MulAut (LinearFlag.projectiveSL 3 K)) (hA : IsRank23 A)
    (hα : α.range ≤ frameStab 3 K) : gammaAct α = ⊤ := by
  have hsq : ∀ a : A, a * a = 1 := fun a => WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA.1 a
  refine gammaAct_eq_top_of_blocks α hα fun i => ?_
  by_cases hin : ((rest i).comp (toFrame α hα)).range ≤
      (MulAut.conj : SL(2, K) →* MulAut SL(2, K)).range
  · exact gammaAct_eq_top_of_le_ker _ (adm_comap_noDual hA.1 α hα)
      (blk_trivial_of_inner hK hsq α hα i hin)
  · exact gammaAct_sl2_of_not_inner_odd (p := 7) (f := 1) (by norm_num) (by norm_num)
      (by simpa using hK) (by norm_num) odd_one _ hA hin

theorem genProp_projectiveSL3_seven
    (hK : Nat.card K = 7) : GenProp (LinearFlag.projectiveSL 3 K) := by
  intro A _ _ α hA
  have hD : CFSG.IsElementaryAbelian 2 ↥α.range :=
    GenLocBasic.isEA_of_surjective hA.1 α.rangeRestrict α.rangeRestrict_surjective
  obtain ⟨β, hβ⟩ := exists_conj_le_frameStab (p := 7) (f := 1) (by norm_num) (by norm_num)
    (by simpa using hK) α.range hD
  refine GenLocL3Lin.gammaAct_eq_top_of_conj α β ?_
  refine gammaAct_eq_top_of_le_frameStab_seven hK _ hA ?_
  rintro _ ⟨a, rfl⟩
  exact hβ ⟨α a, ⟨a, rfl⟩, rfl⟩

end Assembly

end GenLocL3Seven

section PSL3

theorem genProp_psl3_seven
    {J : Type} [Group J] {p f : ℕ} (h7 : p ^ f = 7)
    (hJ : LieModel J .PSL 3 p f) : GenProp J := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := GenLocL5Out.stated_PSL hJ
  let ψ : J ≃* LinearFlag.projectiveSL 3 F :=
    e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        3 F))
  exact GenLocL3Lin.genProp_of_mulEquiv ψ.symm
    (GenLocL3Seven.genProp_projectiveSL3_seven (hF.trans h7))

end PSL3

end CFSG.GH74.Generic.BProg.B2
