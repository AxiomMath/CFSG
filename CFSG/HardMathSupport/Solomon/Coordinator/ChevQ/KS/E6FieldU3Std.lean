module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6Model8
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6FieldU3Misc

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3 CFSG.RankThree.PartOne.KE

section Std


theorem exists_std8_fieldCompat {K : Type} [Field K] [Finite K] (hK : Nat.card K = 64)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 8) :
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (_ : CharP L 2) (D : Std8 L)
      (e : twistedE6RootGroup K σ ≃* ↥D.S.Γ) (_ : Algebra K L), ∀ η : K ≃+* K,
        ∃ (η' : L ≃+* L) (m : ModGL Tag.E6 L),
          (∀ c : K, η' (algebraMap K L c) = algebraMap K L (η c)) ∧
          ∀ x : twistedE6RootGroup K σ,
            ((e (fieldActor σ η x) : ↥D.S.Γ) : ModGL Tag.E6 L) =
              m * Units.map (entrywiseHom η'.toRingHom) ((e x : ↥D.S.Γ) : ModGL Tag.E6 L) *
                m⁻¹ := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hK2 : Nat.card K = (2 ^ 3) ^ 2 := by rw [hK]; norm_num
  have hσ2 : ∀ c, σ c = c ^ (2 ^ 3) := fun c => by rw [hσ]; norm_num
  haveI hcK : CharP K 2 := charP_of_card_eq_prime_pow (f := 6)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  set L := AlgebraicClosure K with hL
  haveI hcL : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  haveI hL' : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨Fr, hFr, D, hΦ, hDq, hDn⟩ :=
    exists_langDatum_twistedE6 Nat.prime_two (by norm_num : 1 ≤ 3) K hK2 twE6W0
  have hFr8 : ∀ c, Fr c = c ^ 8 := fun c => by rw [hFr c]; norm_num
  have hDq8 : D.q = 8 := by rw [hDq]; norm_num
  have hfin := finite_model_twistedE6 Nat.prime_two (by norm_num : 1 ≤ 3) hK2 hσ2 hFr D hΦ
  have hAlg : (D.toSetup 3 (Equiv.neg _) (frobRootMap_neg8 hFr8 D hΦ hDq8 hDn) Nat.prime_three
      (Or.inr (by rw [hDq8]; norm_num))
      ⟨hDq8 ▸ (Nat.prime_two.isPrimePow.pow (by norm_num : 3 ≠ 0) : IsPrimePow 8),
        by rw [hDq8]; exact_mod_cast (CharP.cast_eq_zero_iff L 2 8).2 (by norm_num)⟩
      (by rw [hDq8]; norm_num) hfin).IsAlgebraic :=
    LangSetup.isAlgebraic_of_isAlgClosure _ K 2
      (by show Nat.card K = D.q ^ 2; rw [hK, hDq8]; norm_num)
  let D8 : Std8 L :=
    ⟨D.toSetup 3 (Equiv.neg _) (frobRootMap_neg8 hFr8 D hΦ hDq8 hDn) Nat.prime_three
      (Or.inr (by rw [hDq8]; norm_num))
      ⟨hDq8 ▸ (Nat.prime_two.isPrimePow.pow (by norm_num : 3 ≠ 0) : IsPrimePow 8),
        by rw [hDq8]; exact_mod_cast (CharP.cast_eq_zero_iff L 2 8).2 (by norm_num)⟩
      (by rw [hDq8]; norm_num) hfin, Fr, hFr8, hDq8, fun γ => rfl, hΦ, hDn, hAlg⟩
  let e : twistedE6RootGroup K σ ≃* ↥D8.S.Γ :=
    twistedE6EquivΓ Nat.prime_two (by norm_num : 1 ≤ 3) hK2 hσ2 hFr D hΦ
  let g0 : ModGL Tag.E6 L := D.g0
  let bc : twistedE6RootGroup K σ → ModGL Tag.E6 L := fun x =>
    baseChangeGL (algebraMap K L) (x : ModGL TwistTag.E6.tag K)
  have hecoe : ∀ x : twistedE6RootGroup K σ, ((e x : ↥D8.S.Γ) : ModGL Tag.E6 L) =
      g0⁻¹ * bc x * g0 :=
    fun x => coe_twistedE6EquivΓ Nat.prime_two (by norm_num : 1 ≤ 3) hK2 hσ2 hFr D hΦ x
  refine ⟨L, inferInstance, hL', hcL, D8, e, inferInstance, fun η => ?_⟩
  let η' : L ≃+* L := IsAlgClosure.equivOfEquiv L L η
  have hη' : ∀ c : K, η' (algebraMap K L c) = algebraMap K L (η c) := fun c =>
    IsAlgClosure.equivOfEquiv_algebraMap L L η c
  refine ⟨η', g0⁻¹ * Units.map (entrywiseHom η'.toRingHom) g0, hη', fun x => ?_⟩
  have h1 : bc x = g0 * ((e x : ↥D8.S.Γ) : ModGL Tag.E6 L) * g0⁻¹ := by
    rw [hecoe x]
    group
  have h2 : bc (fieldActor σ η x) = Units.map (entrywiseHom η'.toRingHom) (bc x) :=
    baseChangeGL_entrywise_comm (algebraMap K L) η.toRingHom η'.toRingHom hη' _
  rw [hecoe, h2, h1]
  simp only [map_mul, map_inv, mul_inv_rev, inv_inv]
  group

end Std

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
