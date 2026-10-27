module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4InnerLarge
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4ToralThree

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem f4_toralCentralizer_component_of_reps
    {K : Type} [Field K] {p : ℕ} (hK2 : ringChar K ≠ 2)
    (hC3 : ∀ N : Subgroup (toralCentralizer .F4 K (bitsTuple f4BitsC3)), IsComponent N →
      OddLieCentralQuotient p N)
    (hB4 : ∀ N : Subgroup (toralCentralizer .F4 K (bitsTuple f4BitsB4)), IsComponent N →
      OddLieCentralQuotient p N)
    {b : Fin Tag.F4.rank → Kˣ} (hb : ∀ i, b i = 1 ∨ b i = -1) (hb1 : b ≠ 1)
    {M : Subgroup (toralCentralizer .F4 K b)} (hM : IsComponent M) :
    OddLieCentralQuotient p M := by
  obtain ⟨ρ, hρ, w, hw, hmap⟩ :=
    exists_conj_toralCentralizer_of_orbitCheck hK2 f4SignOrbitB4_check hb
  have hlen : f4SignRepsB4.length = 3 := rfl
  rw [hlen] at hρ
  have key : ∀ (c : Fin (Tag.rank .F4) → Kˣ),
      (toralCentralizer .F4 K c).map
        (MulAut.conj (canonicalRep (coxeterSystem .F4) K w)).toMonoidHom =
          toralCentralizer .F4 K b →
      (∀ N : Subgroup (toralCentralizer .F4 K c), IsComponent N → OddLieCentralQuotient p N) →
        OddLieCentralQuotient p M := by
    intro c hc hcomp
    let e : toralCentralizer .F4 K c ≃* toralCentralizer .F4 K b :=
      ((toralCentralizer .F4 K c).equivMapOfInjective _ (MulAut.conj _).injective).trans
        (MulEquiv.subgroupCongr hc)
    exact oddLieCentralQuotient_of_mulEquiv (M.equivMapOfInjective e.symm.toMonoidHom
      e.symm.injective) (hcomp _ (LocalCores.isComponent_map_mulEquiv e.symm hM))
  interval_cases ρ
  · exact absurd (eq_one_of_rootChar_smul_eq_one (w := w) (by
      intro v
      rw [hw v]
      congr 1
      funext i
      have h0 : listMask (τ := .F4) (f4SignRepsB4.getD 0 []) i = false := by
        revert i
        decide
      change (if listMask (τ := .F4) (f4SignRepsB4.getD 0 []) i then (-1 : Kˣ) else 1) = 1
      rw [h0]
      rfl)) hb1
  · exact key _ hmap hC3
  · exact key _ hmap hB4

theorem oddExcInnerDiagInput_F4
    : OddExcInnerDiagInput .F4 := by
  intro K _ _ p f hp hp2 hKp α g a hαg hαo L hL
  by_cases h5 : 5 ≤ Nat.card K
  · exact oddExcInnerDiag_F4_of_five_le hp hp2 hKp h5 hαg hαo hL
  ·
    obtain ⟨hf, h3⟩ := one_le_and_three_le_of_card hp hp2 hKp
    have hKodd : Odd (Nat.card K) := by
      rw [hKp]
      exact (hp.eq_two_or_odd'.resolve_left hp2).pow
    have hq3 : Nat.card K = 3 := by
      obtain ⟨k, hk⟩ := hKodd
      omega
    have : CharP K p := finite_field_prime_power_characteristic hp hf hKp
    have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
    have hα : α ^ 2 = 1 := hαo ▸ pow_orderOf_eq_one α
    have hα1 : α ≠ 1 := fun h => by
      rw [h, orderOf_one] at hαo
      exact absurd hαo (by norm_num)
    obtain ⟨b, hb, hb1, ⟨Θ⟩⟩ :=
      exists_toralCentralizer_equiv_of_innerDiag (Or.inr (Or.inl rfl)) hKodd hαg hα
    exact oddLieCentralQuotient_of_mulEquiv (L.equivMapOfInjective Θ.toMonoidHom Θ.injective)
      (f4_toralCentralizer_component_of_reps hK2
        (fun N hN => f4_toral_C3_component_three hp hp2 hKp hq3 hN)
        (fun N hN => f4_toral_B4_component_frame hp hp2 hKp hN) hb (hb1 hα1)
        (LocalCores.isComponent_map_mulEquiv Θ hL))

end CFSG.ComponentClassification.CatLeafProof
