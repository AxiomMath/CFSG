module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1429SubD4Fix
import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4Field

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.H1429Sub

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Dickson.DefCharOuter.Export
open CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthD4
open scoped commutatorElement

set_option linter.unusedSectionVars false


section Types

open CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent

variable {K : Type} [Field K] [Finite K] [CharP K 3]

theorem noU42At_twisted_D4 {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f)
    (T : K ≃+* K) (hT3 : T ^ 3 = 1) (hT1 : T ≠ 1) (j : ℤ) (hj : j = 1 ∨ j = 2)
    (α : MulAut (adjointGroup Tag.D4 K)) (hα : α = twistedEntrywiseAut TwistTag.D4 j T) :
    NoU42At α := by
  rcases hj with rfl | rfl
  · obtain rfl : α = alphaOne T := hα.trans (twistedEntrywiseAut_one_eq T)
    exact noU42At_alphaOne hf hK T hT3 hT1
  · obtain rfl : α = (alphaOne T⁻¹)⁻¹ := hα.trans (twistedEntrywiseAut_two_eq T)
    refine NoU42At.of_inv ?_
    rw [inv_inv]
    exact noU42At_alphaOne hf hK T⁻¹ (by rw [inv_pow, hT3, inv_one]) (inv_ne_one.2 hT1)

theorem noU42At_fieldType_D4 {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f)
    (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1) (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    (hαeq : α = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K 0)) : NoU42At α := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d, T, hd0, hdf, hT, hT3, hσT⟩ :=
    exists_frobenius_of_cube Nat.prime_three hf K hK σ hσ3 hσ1
  have hT1 : T ≠ 1 := by
    rintro rfl
    rcases hσT with h | h
    · exact hσ1 h
    · exact hσ1 (by rw [h, one_pow])
  rw [d4Graph_zero, mul_one] at hαeq
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 ≤ 3 ^ 2 := by norm_num
      _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hconj : ∀ (β : MulAut (adjointGroup Tag.D4 K)) (g' : adjointGroup Tag.D4 K)
      (a' : Fin Tag.D4.rank → Kˣ), β = MulAut.conj g' * exactNormalAut Tag.D4 K a' T 0 →
      β ^ 3 = 1 → NoU42At β := by
    intro β g' a' hβ hβ3
    obtain ⟨ψ, hψ⟩ := exists_conj_eq_entrywiseAdjointAut_D4 hK hK4 hd0 hdf T hT g' a' β hβ hβ3
    refine NoU42At.of_conj ψ β ?_
    rw [hψ]
    exact noU42At_entrywise_D4 hf hK T hT3 hT1
  rcases hσT with hσ | hσ
  · rw [hσ] at hαeq
    exact hconj α g a hαeq hα3
  · obtain ⟨g', a', hα2⟩ := sq_conj_mul_exactNormalAut g a σ
    have hσ2 : σ ^ 2 = T := by
      rw [hσ, ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hT3, one_mul]
    rw [hσ2, ← hαeq] at hα2
    have hα23 : (α ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hα3, one_pow]
    have hα22 : (α ^ 2) ^ 2 = α := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hα3, one_mul]
    exact NoU42At.of_pow 2 (hconj (α ^ 2) g' a' hα2 hα23) (fixedSubgroup_pow_eq hα22).symm

theorem noU42At_graphFieldType_D4 {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f)
    (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1) (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ) (hε : ε < 3) (hε0 : ε ≠ 0)
    (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    (hαeq : α = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) : NoU42At α := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  obtain ⟨e, T, he, hef, hT, hσT⟩ :=
    exists_frobenius_eq_or_inv_of_orderOf_three Nat.prime_three hf K hK σ hord
  have hT3 : T ^ 3 = 1 := by
    rcases hσT with h | h
    · rwa [h] at hσ3
    · rwa [h, inv_pow, inv_eq_one] at hσ3
  have hT1 : T ≠ 1 := by
    rintro rfl
    rcases hσT with h | h
    · exact hσ1 h
    · exact hσ1 (by rw [h, inv_one])
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 ≤ 3 ^ 2 := by norm_num
      _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hε' : ε = 1 ∨ ε = 2 := by omega
  rcases hσT with hσ | hσ
  · rw [hσ] at hαeq
    obtain ⟨ψ, hψ⟩ :=
      exists_conj_eq_twistedEntrywiseAut_of_normalForm K hK hK4 he hef T hT α hα3 g a ε hαeq
    refine NoU42At.of_conj ψ α ?_
    exact noU42At_twisted_D4 hf hK T hT3 hT1 (ε : ℤ)
      (by rcases hε' with rfl | rfl <;> simp) _ hψ
  · rw [hσ] at hαeq
    obtain ⟨ψ, hψ⟩ := exists_conj_inv_eq_twistedEntrywiseAut_of_normalForm K hK hK4 he hef T T⁻¹
      hT (mul_inv_cancel T) α hα3 g a ε hαeq
    have hshift : twistedEntrywiseAut TwistTag.D4 (-(ε : ℤ)) T =
        twistedEntrywiseAut TwistTag.D4 (3 - (ε : ℤ)) T := by
      have h := twistedEntrywiseAut_add_mul_order TwistTag.D4 (-(ε : ℤ)) 1 T
      rw [show -(ε : ℤ) + 1 * ((TwistTag.D4.order : ℕ) : ℤ) = 3 - (ε : ℤ) by
        change -(ε : ℤ) + 1 * 3 = _
        ring] at h
      exact h.symm
    refine NoU42At.of_inv (NoU42At.of_conj ψ α⁻¹ ?_)
    exact noU42At_twisted_D4 hf hK T hT3 hT1 (3 - (ε : ℤ))
      (by rcases hε' with rfl | rfl <;> simp) _ (hψ.trans hshift)

end Types

end CFSG.LocalAnalysis.GLTheoremA.H1429Sub

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.H1429Sub
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Dickson.DefCharOuter.Export
open CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent


theorem i1429SubD4_holds : I1429SubLieAt SubIsD4 := by
  intro S _ _ hS hnc d hchar ⟨q, hd⟩ ⟨e⟩ β hβ hout I hI hU
  have hord : orderOf β = 3 := orderOf_three_of_not_inner hβ hout
  obtain ⟨d, hv⟩ := d
  cases hd
  have hq3 : q.p = 3 := by simpa using hchar
  exfalso
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card q.p q.exponent (by omega), TauCeti.PrimePower.card_def]
  haveI : CharP (GaloisField q.p q.exponent) 3 := CharP.congr q.p hq3
  have hK3 : Nat.card (GaloisField q.p q.exponent) = 3 ^ q.exponent := by
    rw [hcard, TauCeti.PrimePower.card_def, hq3]
  obtain ⟨br⟩ := CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_adjointQuotient_D4_equiv
    (GaloisField q.p q.exponent) q hv hcard
  let φ : S ≃* adjointGroup Tag.D4 (GaloisField q.p q.exponent) :=
    (e.trans br.symm).trans ((QuotientGroup.quotientMulEquivOfEq
      CFSG.LieType.Chevalley.center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot)
  haveI : Finite (adjointGroup Tag.D4 (GaloisField q.p q.exponent)) :=
    Finite.of_equiv S φ.toEquiv
  have hβ' : MulAut.congr φ β ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  have hout' : MulAut.congr φ β ∉
      CFSG.HardMathSupport.Solomon.LocalBalance.innerAut
        (adjointGroup Tag.D4 (GaloisField q.p q.exponent)) := fun h =>
    hout ((congr_mem_range_conj_iff φ β).1 h)
  have key : NoU42At (MulAut.congr φ β) := by
    obtain ⟨g, a, σ, ε, hε, hαeq, hσ3, hcase⟩ :=
      outer_cube_normal_form_cases (MulAut.congr φ β) hβ' hout'
    rcases hcase with ⟨hε0, hσ1⟩ | ⟨hε0, hσ1⟩ | ⟨hε0, hσ1⟩
    · subst hε0
      exact noU42At_fieldType_D4 hf hK3 _ hβ' g a σ hσ3 hσ1 hαeq
    · exact noU42At_graphFieldType_D4 hf hK3 _ hβ' g a σ ε hε hε0 hσ3 hσ1 hαeq
    · subst hσ1
      exact noU42At_d4_graph g a ε (Nat.pos_of_ne_zero hε0) hε _ hαeq hβ'
  obtain ⟨hI', ⟨eI⟩⟩ := component_transport φ rfl hI
  exact key _ hI' ((Nat.card_congr eI.toEquiv).symm.trans (I1431Z.card_eq_of_u4two hU))

end CFSG.LocalAnalysis.GLTheoremA
