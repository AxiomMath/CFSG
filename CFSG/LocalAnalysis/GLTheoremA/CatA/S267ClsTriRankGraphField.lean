module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsTriRankFix
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4AmbientGraphField
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThreeRank
import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTrialityOrient

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)


theorem fixRankTwo_twistedEntrywiseAut_D4 {ℓ e : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3)
    (he : 1 ≤ e) (K : Type) [Field K] [Finite K] [CharP K ℓ] (hK : Nat.card K = (ℓ ^ e) ^ 3)
    (T : K ≃+* K) (hT : ∀ c, T c = c ^ (ℓ ^ e)) (j : ℤ) (hj : j = 1 ∨ j = 2) :
    FixRankTwo (twistedEntrywiseAut TwistTag.D4 j T) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Fintype K := Fintype.ofFinite K
  have hq3 : ∀ c : K, c ^ ((ℓ ^ e) ^ 3) = c := fun c => by
    rw [← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  obtain ⟨σ, r, hr, hσ, hfix⟩ : ∃ (σ : K ≃+* K) (r : ℕ), (r = 1 ∨ r = 2) ∧
      (∀ c, σ c = c ^ ((ℓ ^ e) ^ r)) ∧
      fixedSubgroup (twistedEntrywiseAut TwistTag.D4 j T) =
        fixedSubgroup (twistedEntrywiseAut TwistTag.D4 1 σ) := by
    rcases hj with rfl | rfl
    · exact ⟨T, 1, Or.inl rfl, fun c => by rw [pow_one]; exact hT c, rfl⟩
    · have hT3 : T ^ 3 = 1 := by
        refine RingEquiv.ext fun c => ?_
        change T (T (T c)) = c
        rw [hT, hT, hT, ← pow_mul, ← pow_mul,
          show ℓ ^ e * (ℓ ^ e * ℓ ^ e) = (ℓ ^ e) ^ 3 by ring, hq3]
      have hinv : ∀ c, (T⁻¹) c = c ^ ((ℓ ^ e) ^ 2) := by
        have h1 : T⁻¹ = T ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hT3)
        intro c
        rw [h1, pow_two]
        change T (T c) = _
        rw [hT, hT, ← pow_mul, sq]
      exact ⟨T⁻¹, 2, Or.inr rfl, hinv, fixedSubgroup_twistedEntrywiseAut_D4_two T⟩
  let L := AlgebraicClosure K
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  obtain ⟨-, -, hΓ, -, -⟩ := triality_both_field_orientations_simple_full_ambient_fixed_group
    ℓ e hℓ he K hK L r hr σ.toRingHom (fun c => hσ c) (iterateFrobenius L ℓ e)
    (fun c => iterateFrobenius_def ℓ e c)
  set C₀ := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC₀
  have hC₀X : C₀ ≤ adjointGroup TwistTag.D4.tag K :=
    (graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom).trans
      (twistedFixedGroup_le_adjointGroup TwistTag.D4 K σ.toRingHom)
  have hfixJ : fixSubgroup (twistedEntrywiseAut TwistTag.D4 j T) =
      C₀.subgroupOf (adjointGroup TwistTag.D4.tag K) := by
    change fixedSubgroup _ = _
    rw [hfix, fixedSubgroup_twistedEntrywiseAut_one TwistTag.D4 σ, hΓ]
  have hrank : ∀ F : Subgroup ↥C₀, CFSG.Open.IsElemAbelian 3 F → Nat.card F ≤ 3 ^ 2 := by
    intro F hF
    rcases hr with rfl | rfl
    · exact CFSG.HardMathSupport.Timmesfeld.CrossChar.card_le_nine_of_graphFixedRootGroup_odd hℓ
        hℓ2 hℓ3 he hK (fun c => by rw [pow_one] at hσ; exact hσ c) F hF
    · obtain ⟨φ⟩ := CFSG.HardMathSupport.Dickson.DefCharOuter.Export.exists_mulEquiv_graphFixedRootGroup_frobenius_sq_D4
        K hK σ T hσ hT
      rw [← Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective]
      exact CFSG.HardMathSupport.Timmesfeld.CrossChar.card_le_nine_of_graphFixedRootGroup_odd hℓ
        hℓ2 hℓ3 he hK (σ := T.toRingHom) hT _ (hF.map φ.toMonoidHom)
  exact FixRankTwo.of_mulEquiv
    ((MulEquiv.subgroupCongr hfixJ).trans (Subgroup.subgroupOfEquivOfLe hC₀X)) hrank

theorem fixRankTwo_d4_graphField {ℓ f : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3)
    (K : Type) [Field K] [Finite K] [CharP K ℓ] (hK : Nat.card K = ℓ ^ f)
    (α : MulAut (adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1) (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ) (hε : ε < 3) (hε0 : ε ≠ 0) (hσ : σ ≠ 1)
    (hα : α = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) :
    FixRankTwo α := by
  haveI : Finite (ModGL Tag.D4 K) := finite_modGL
  haveI : Finite (adjointGroup Tag.D4 K) := Subtype.finite
  have hσ3 := sigma_pow_three_eq_one_of_cube α hα3 g a σ ε hα
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ
  have hf : 1 ≤ f := by
    by_contra hf
    have hf0 : f = 0 := by omega
    have := Finite.one_lt_card (α := K)
    rw [hK, hf0, pow_zero] at this
    omega
  obtain ⟨e, T, he, hef, hT, hσT⟩ :=
    exists_frobenius_eq_or_inv_of_orderOf_three (Fact.out : ℓ.Prime) hf K hK σ hord
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ ℓ ^ 2 := Nat.pow_le_pow_left (Fact.out : ℓ.Prime).two_le 2
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right (Fact.out : ℓ.Prime).pos (by omega)
  have hK' : Nat.card K = (ℓ ^ e) ^ 3 := by rw [hK, ← hef, pow_mul]
  rcases hσT with rfl | rfl
  · obtain ⟨ψ, hψ⟩ := exists_conj_eq_twistedEntrywiseAut_of_normalForm K hK hK4 he hef _ hT α hα3
      g a ε hα
    have h1 := fixRankTwo_twistedEntrywiseAut_D4 hℓ2 hℓ3 he K hK' _ hT (ε : ℤ) (by omega)
    rw [← hψ] at h1
    exact FixRankTwo.of_conj ψ h1
  · obtain ⟨ψ, hψ⟩ := exists_conj_inv_eq_twistedEntrywiseAut_of_normalForm K hK hK4 he hef T T⁻¹
      hT (mul_inv_cancel T) α hα3 g a ε hα
    have hshift : twistedEntrywiseAut TwistTag.D4 (-(ε : ℤ)) T =
        twistedEntrywiseAut TwistTag.D4 (3 - (ε : ℤ)) T := by
      have h := twistedEntrywiseAut_add_mul_order TwistTag.D4 (-(ε : ℤ)) 1 T
      rw [show -(ε : ℤ) + 1 * ((TwistTag.D4.order : ℕ) : ℤ) = 3 - (ε : ℤ) by
        change -(ε : ℤ) + 1 * 3 = _
        ring] at h
      exact h.symm
    have h1 := fixRankTwo_twistedEntrywiseAut_D4 hℓ2 hℓ3 he K hK' T hT (3 - (ε : ℤ)) (by omega)
    rw [← hshift, ← hψ] at h1
    exact FixRankTwo.of_inv (FixRankTwo.of_conj ψ h1)

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
