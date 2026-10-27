module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5Fix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5Four
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatOddLinear
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatOddLinearTwo

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.EvenSporadicStandard.SolomonRed CFSG.LocalAnalysis.EvenBN.GMSK

variable {Y : Type} [Group Y] {τ : Y}

theorem pgl2_five_exists_orderOf_four {F₀ : Type} [Field F₀] [Fintype F₀]
    (hF : Fintype.card F₀ = 5) : ∃ x : Matrix.ProjGenLinGroup (Fin 2) F₀, orderOf x = 4 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : CharP F₀ 5 := charP_of_card_eq_prime hF
  have h5 : (5 : F₀) = 0 := CharP.cast_eq_zero F₀ 5
  have h2ne : (2 : F₀) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (R := F₀) Nat.prime_two (by norm_num)
  have h2pow : (2 : F₀) ^ 4 = 1 := by linear_combination 3 * h5
  have h4ne : (4 : F₀) ≠ 1 := by
    intro h
    have h3 : (3 : F₀) = 0 := by
      have h' : (4 : F₀) - 1 = 0 := by rw [h, sub_self]
      rwa [show (4 : F₀) - 1 = (3 : F₀) by ring] at h'
    have hdvd := (CharP.cast_eq_zero_iff F₀ 5 3).1 h3
    norm_num at hdvd
  set A : Matrix (Fin 2) (Fin 2) F₀ := Matrix.diagonal ![2, 1] with hA
  have hdet : A.det ≠ 0 := by
    rw [hA, Matrix.det_diagonal, Fin.prod_univ_two]
    simpa using h2ne
  let δ : Matrix.GeneralLinearGroup (Fin 2) F₀ := Matrix.GeneralLinearGroup.mkOfDetNeZero A hdet
  have hδval : (δ : Matrix (Fin 2) (Fin 2) F₀) = A :=
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero A hdet
  have hA2 : A ^ 2 = Matrix.diagonal ![4, 1] := by
    rw [hA, Matrix.diagonal_pow]
    congr 1
    funext i
    change (![2, 1] : Fin 2 → F₀) i ^ 2 = ![4, 1] i
    fin_cases i <;> simp <;> norm_num
  have hA4 : A ^ 4 = 1 := by
    rw [hA, Matrix.diagonal_pow]
    have hv : (![2, 1] : Fin 2 → F₀) ^ 4 = 1 := by
      funext i
      change (![2, 1] : Fin 2 → F₀) i ^ 4 = 1
      fin_cases i <;> simp [h2pow]
    simp [hv]
  have hδ4 : δ ^ 4 = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp only [Units.val_pow_eq_pow_val, hδval, hA4, Matrix.GeneralLinearGroup.coe_one]
  have hδ2center : δ ^ 2 ∉ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) F₀) := by
    intro hmem
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, MonoidHom.mem_range] at hmem
    obtain ⟨u, hu⟩ := hmem
    have e00 : (u : F₀) = (4 : F₀) := by
      have h := congrArg
        (fun M : Matrix.GeneralLinearGroup (Fin 2) F₀ => (M : Matrix (Fin 2) (Fin 2) F₀) 0 0) hu
      simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
        Units.val_pow_eq_pow_val, hδval, hA2] using h
    have e11 : (u : F₀) = (1 : F₀) := by
      have h := congrArg
        (fun M : Matrix.GeneralLinearGroup (Fin 2) F₀ => (M : Matrix (Fin 2) (Fin 2) F₀) 1 1) hu
      simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
        Units.val_pow_eq_pow_val, hδval, hA2] using h
    exact h4ne (e00.symm.trans e11)
  have hnot : ¬ (Matrix.ProjGenLinGroup.mk δ) ^ (2 ^ 1) = 1 := by
    rw [show (2 : ℕ) ^ 1 = 2 by norm_num, ← map_pow, Matrix.ProjGenLinGroup.mk_eq_one]
    exact hδ2center
  refine ⟨Matrix.ProjGenLinGroup.mk δ, ?_⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : (Matrix.ProjGenLinGroup.mk δ) ^ (2 ^ (1 + 1)) = 1 := by
    rw [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num, ← map_pow]
    simp [hδ4]
  have hord := orderOf_eq_prime_pow (p := 2) (n := 1)
    (x := Matrix.ProjGenLinGroup.mk δ) hnot hfin
  rw [show (2 : ℕ) ^ (1 + 1) = 4 by norm_num] at hord
  exact hord

theorem z2a5_not_L225 [Finite Y] (h : Z2A5Hyp Y τ) {S : Subgroup Y} (hS : FixedData Y S) :
    ¬ LieModel ↥S .PSL 2 5 2 := by
  intro hL
  haveI := hS.normal
  obtain ⟨k, _, _, d⟩ := z2a5_datum h hS
  have hM := OddClassicalRankOne.statedClassicalModel_of_lieModel (by decide) hL
  obtain ⟨-, -, -, -, F₀, _, _, hF₀, ⟨ψ⟩⟩ :=
    CFSG.LocalAnalysis.EvenBN.GMSK.odd_linear_two_involution_fixed_normal_even_SL2_square_five
      hM (by norm_num) d.two_le k d.card_eq _ d.orderOf_eq _ d.le_fixed d.normal
      d.nonempty_mulEquiv
  obtain ⟨x, hx4⟩ := pgl2_five_exists_orderOf_four hF₀
  apply z2a5_eqLocus_no_four h (ψ.symm x : ↥S) (ψ.symm x).2
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq ψ.symm x, hx4]

end CFSG.OddStandard.SmallF3.Omega
