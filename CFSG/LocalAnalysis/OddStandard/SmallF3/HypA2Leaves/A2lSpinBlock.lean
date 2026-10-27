module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCoverBasic
public import CFSG.ClassicalInvolution.WeakCT.SpinMinus6Generated

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CliffordAlgebra QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.TwistedPairs CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

theorem a2lNegOne_eq_torusHom (E : Type) [Field E] : a2lNegOne E = torusHom E (-1) := by
  apply Subtype.ext
  rw [coe_torusHom]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [a2lNegOne]

theorem a2lNegOne_ne_one_of_two_ne_zero {E : Type} [Field E] (h2 : (2 : E) ≠ 0) :
    a2lNegOne E ≠ 1 := by
  intro h1
  have h := congrArg (fun A : SL(2, E) => (A : Matrix (Fin 2) (Fin 2) E) 0 0) h1
  simp only [a2lNegOne, Matrix.SpecialLinearGroup.coe_one] at h
  apply h2
  have : (-1 : E) = 1 := by simpa using h
  linear_combination -this

theorem a2l_mem_center_of_coe_eq_neg_one {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {x : spinGroup Q} (hx : (x : CliffordAlgebra Q) = -1) :
    x ∈ Subgroup.center (spinGroup Q) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  change (g : CliffordAlgebra Q) * (x : CliffordAlgebra Q) =
    (x : CliffordAlgebra Q) * (g : CliffordAlgebra Q)
  rw [hx, mul_neg_one, neg_one_mul]

section Block

variable {F : Type} [Field F] [Finite F] {b c : F} [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)]

theorem a2l_shortBlock_negOne (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (h2 : (2 : F) ≠ 0)
    (n : ℕ) (k : Fin (n - 1)) :
    ((shortBlock hirr n k (a2lNegOne (ShortField b c)) : spinGroup (quadMinus n F b c)) :
      CliffordAlgebra (quadMinus n F b c)) = -1 := by
  have := finite_shortField (b := b) (c := c)
  set h := shortBlock hirr n k (a2lNegOne (ShortField b c)) with hh
  have hfc : fieldCoord (((-1 : (ShortField b c)ˣ)) : ShortField b c) = -planeOne := by
    ext j
    fin_cases j <;> simp [fieldCoord, planeOne, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  have hker : h ∈ (spinAction (quadMinus n F b c)).ker := by
    rw [MonoidHom.mem_ker, hh, a2lNegOne_eq_torusHom, shortBlock_torus, hfc]
    exact spinAction_shortTorusElt_neg_planeOne hirr n k
  have h2' : (2 : ShortField b c) ≠ 0 := by
    intro h0
    apply h2
    have h3 : algebraMap F (ShortField b c) 2 = algebraMap F (ShortField b c) 0 := by
      rw [map_ofNat, map_zero]
      exact h0
    exact (algebraMap F (ShortField b c)).injective h3
  have hne : h ≠ 1 := by
    intro h1
    exact a2lNegOne_ne_one_of_two_ne_zero h2'
      (shortBlock_injective hirr h2 n k (h1.trans (map_one _).symm))
  have hcent := isCentral_cliffordAlgebra_quadMinus n b c hirr
  exact ((mem_ker_spinAction_iff_of_isCentral _ h).1 hker).resolve_left hne

end Block

theorem a2l_exists_spinMinus_sl2
    {F : Type} [Field F] [Finite F] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (h2 : (2 : F) ≠ 0) (n : ℕ) (k : Fin (n - 1)) :
    ∃ (E : Type) (_ : Field E) (_ : Fintype E) (Θ : SL(2, E) →* spinGroup (quadMinus n F b c)),
      Fintype.card E = Nat.card F ^ 2 ∧ Function.Injective Θ ∧
        ((Θ (a2lNegOne E) : spinGroup (quadMinus n F b c)) :
          CliffordAlgebra (quadMinus n F b c)) = -1 := by
  haveI := fact_shortField hirr
  haveI := finite_shortField (b := b) (c := c)
  haveI := Fintype.ofFinite (ShortField b c)
  refine ⟨ShortField b c, inferInstance, inferInstance, shortBlock hirr n k, ?_,
    shortBlock_injective hirr h2 n k, a2l_shortBlock_negOne hirr h2 n k⟩
  rw [← Nat.card_eq_fintype_card, Nat.card_congr (QuadraticAlgebra.equivProd (-c) b),
    Nat.card_prod, pow_two]

end CFSG.OddStandard.SmallF3.HypA2Leaves
