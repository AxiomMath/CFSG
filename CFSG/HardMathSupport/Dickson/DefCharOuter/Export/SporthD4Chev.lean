module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthD4Cent
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.D4ThreeStmt
import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4Field
import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4AmbientForm
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthD4Def
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthGeneric

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.ComponentClassification.OuterAutomorphisms (inner_normal)

namespace SporthD4

section Generic

variable {S : Type} [Group S]

theorem conj_mem_innerAut_iff (ψ β : MulAut S) : ψ * β * ψ⁻¹ ∈ innerAut S ↔ β ∈ innerAut S := by
  constructor
  · intro h
    have h' := (inner_normal S).conj_mem _ h ψ⁻¹
    rwa [show ψ⁻¹ * (ψ * β * ψ⁻¹) * ψ⁻¹⁻¹ = β by group] at h'
  · intro h
    exact (inner_normal S).conj_mem _ h ψ

theorem fixSubgroup_inv_eq (β : MulAut S) : fixSubgroup β⁻¹ = fixSubgroup β := by
  ext x
  show β⁻¹ x = x ↔ β x = x
  constructor
  · intro h
    calc β x = β (β⁻¹ x) := by rw [h]
      _ = x := MulAut.apply_inv_self _ β x
  · intro h
    calc β⁻¹ x = β⁻¹ (β x) := by rw [h]
      _ = x := MulAut.inv_apply_self _ β x

theorem outerCentData_of_inv {p : ℕ} {β : MulAut S} (h : OuterCentData p β⁻¹) :
    OuterCentData p β where
  unique I J hI hJ := h.unique I J (by rwa [fixSubgroup_inv_eq]) (by rwa [fixSubgroup_inv_eq])
  chev I hI := h.chev I (by rwa [fixSubgroup_inv_eq])
  core hexc := by
    have := h.core hexc
    rwa [fixSubgroup_inv_eq] at this
  cent hexc w hw hwβ hfixw :=
    h.cent hexc w hw (Commute.inv_right (show Commute w β from hwβ)).eq
      (by rwa [fixSubgroup_inv_eq])
  noHatSix hp3 I hI := h.noHatSix hp3 I (by rwa [fixSubgroup_inv_eq])
  l227 hp3 I hI hL β' hβ3 hββ' hmap :=
    h.l227 hp3 I (by rwa [fixSubgroup_inv_eq]) hL β' hβ3
      (Commute.inv_right (show Commute β' β from hββ')).eq hmap

end Generic

end SporthD4

set_option linter.unusedSectionVars false

namespace SporthD4

section Types

variable {K : Type} [Field K] [Finite K] [CharP K 3]

theorem twistedEntrywiseAut_two_eq (T : K ≃+* K) :
    twistedEntrywiseAut TwistTag.D4 2 T = (alphaOne T⁻¹)⁻¹ := by
  have h1 : (twistedEntrywiseAut TwistTag.D4 1 T⁻¹)⁻¹ =
      twistedEntrywiseAut TwistTag.D4 (-1) T := by
    have h := twistedEntrywiseAut_inv TwistTag.D4 1 T⁻¹
    rwa [inv_inv] at h
  have h2 := twistedEntrywiseAut_add_mul_order TwistTag.D4 (-1) 1 T
  rw [show (-1 : ℤ) + 1 * ((TwistTag.D4.order : ℕ) : ℤ) = 2 by decide] at h2
  exact h2.trans (h1.symm.trans (congrArg (fun x => x⁻¹) (twistedEntrywiseAut_one_eq T⁻¹)))

theorem outerCentData_twisted_D4 {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f)
    (T : K ≃+* K) (hT3 : T ^ 3 = 1) (hT1 : T ≠ 1) (j : ℤ) (hj : j = 1 ∨ j = 2)
    (α : MulAut (adjointGroup Tag.D4 K)) (hα : α = twistedEntrywiseAut TwistTag.D4 j T)
    (hout : α ∉ innerAut (adjointGroup Tag.D4 K)) : OuterCentData 3 α := by
  rcases hj with rfl | rfl
  · obtain rfl : α = alphaOne T := hα.trans (twistedEntrywiseAut_one_eq T)
    exact outerCentData_alphaOne hf hK T hT3 hT1 hout
  · obtain rfl : α = (alphaOne T⁻¹)⁻¹ := hα.trans (twistedEntrywiseAut_two_eq T)
    refine outerCentData_of_inv ?_
    rw [inv_inv]
    refine outerCentData_alphaOne hf hK T⁻¹ (by rw [inv_pow, hT3, inv_one]) (inv_ne_one.2 hT1) ?_
    intro hin
    exact hout (inv_mem hin)

theorem outerCentData_fieldType_D4 {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f)
    (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1)
    (hout : α ∉ innerAut (adjointGroup Tag.D4 K)) (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    (hαeq : α = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K 0)) :
    OuterCentData 3 α := by
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
      β ^ 3 = 1 → β ∉ innerAut (adjointGroup Tag.D4 K) → OuterCentData 3 β := by
    intro β g' a' hβ hβ3 hβout
    obtain ⟨ψ, hψ⟩ := exists_conj_eq_entrywiseAdjointAut_D4 hK hK4 hd0 hdf T hT g' a' β hβ hβ3
    refine OuterCentData.of_conj Nat.prime_three ψ β ?_
    rw [hψ]
    refine outerCentData_entrywise_D4 hf hK T hT3 hT1 fun hin => hβout ?_
    rw [← hψ] at hin
    exact (conj_mem_innerAut_iff ψ β).1 hin
  rcases hσT with hσ | hσ
  · rw [hσ] at hαeq
    exact hconj α g a hαeq hα3 hout
  · obtain ⟨g', a', hα2⟩ := sq_conj_mul_exactNormalAut g a σ
    have hσ2 : σ ^ 2 = T := by
      rw [hσ, ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hT3, one_mul]
    rw [hσ2, ← hαeq] at hα2
    have hα23 : (α ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hα3, one_pow]
    have hα22 : (α ^ 2) ^ 2 = α := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hα3, one_mul]
    have hout2 : α ^ 2 ∉ innerAut (adjointGroup Tag.D4 K) := fun h =>
      hout (by rw [← hα22]; exact pow_mem h 2)
    exact OuterCentData.of_pow 2 (hconj (α ^ 2) g' a' hα2 hα23 hout2)
      (fixedSubgroup_pow_eq hα22).symm

theorem outerCentData_graphFieldType_D4 {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f)
    (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1)
    (hout : α ∉ innerAut (adjointGroup Tag.D4 K)) (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ) (hε : ε < 3) (hε0 : ε ≠ 0)
    (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    (hαeq : α = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) :
    OuterCentData 3 α := by
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
    refine OuterCentData.of_conj Nat.prime_three ψ α ?_
    refine outerCentData_twisted_D4 hf hK T hT3 hT1 (ε : ℤ)
      (by rcases hε' with rfl | rfl <;> simp) _ hψ fun hin => hout ?_
    exact (conj_mem_innerAut_iff ψ α).1 hin
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
    refine outerCentData_of_inv (OuterCentData.of_conj Nat.prime_three ψ α⁻¹ ?_)
    refine outerCentData_twisted_D4 hf hK T hT3 hT1 (3 - (ε : ℤ))
      (by rcases hε' with rfl | rfl <;> simp) _ (hψ.trans hshift) fun hin => hout ?_
    exact inv_mem_iff.1 ((conj_mem_innerAut_iff ψ α⁻¹).1 hin)

end Types

end SporthD4

open SporthD4 in
theorem d4ThreeOuterCent_of_graphCent (hG : D4ThreeGraphCent) : D4ThreeOuterCent := by
  intro S _ _ q hv hS hq3 β hβ hout
  obtain ⟨e⟩ := hS
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
  have hout' : MulAut.congr φ β ∉ innerAut (adjointGroup Tag.D4 (GaloisField q.p q.exponent)) :=
    fun h => hout ((congr_mem_innerAut_iff φ β).1 h)
  refine OuterCentData.of_congr Nat.prime_three φ ?_
  obtain ⟨g, a, σ, ε, hε, hαeq, hσ3, hcase⟩ :=
    outer_cube_normal_form_cases (MulAut.congr φ β) hβ' hout'
  rcases hcase with ⟨hε0, hσ1⟩ | ⟨hε0, hσ1⟩ | ⟨hε0, hσ1⟩
  · subst hε0
    exact outerCentData_fieldType_D4 hf hK3 _ hβ' hout' g a σ hσ3 hσ1 hαeq
  · exact outerCentData_graphFieldType_D4 hf hK3 _ hβ' hout' g a σ ε hε hε0 hσ3 hσ1 hαeq
  · subst hσ1
    exact hG (GaloisField q.p q.exponent) g a ε (Nat.pos_of_ne_zero hε0) hε _ hαeq hβ'

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export
