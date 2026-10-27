module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXUntw
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.ExcResOutF4
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OutTriD4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

private theorem ringChar_eq_two_of_card_eq_pow {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) : ringChar K = 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := n) (by rwa [← Nat.card_eq_fintype_card])
  exact ringChar.eq K 2


private theorem mem_range_twistedE6InndiagConj_of_mem_innAutDerived {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {β : MulAut ↥(twistedE6RootGroup K σ)}
    (hβ : β ∈ innAutDerived ↥(twistedE6RootGroup K σ)) :
    β ∈ (twistedE6InndiagConj K σ).range := by
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  have hKf : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hcyc : IsCyclic (RingAut K) :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hℓ K hKf).2
  have hΘ : innAutDerived ↥(twistedE6RootGroup K σ) ≤ Θ.ker := by
    refine sup_le ?_ ?_
    · rw [hker]
      exact le_sup_left
    · exact CFSG.HardMathSupport.Dickson.Sec6.I1431.excres_commutator_le_ker Θ
        fun x y => hcyc.isMulCommutative.is_comm.comm x y
  rw [range_twistedE6InndiagConj, ← hker]
  exact hΘ hβ

theorem exists_comp_of_two_twistedE6 {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (hq4 : 4 ≤ 2 ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ (2 ^ f) ^ 2 - 1)
    (β : MulAut ↥(twistedE6RootGroup K σ)) (hβmem : β ∈ innAutDerived ↥(twistedE6RootGroup K σ))
    (hβp : β ^ p = 1) (hβ1 : β ≠ 1) (P : Subgroup ↥(twistedE6RootGroup K σ))
    (hPβ : P ≤ fixSubgroup β) (hP2 : IsPGroup 2 ↥P) (hP1 : P ≠ ⊥) :
    ∃ J : Subgroup ↥(twistedE6RootGroup K σ), IsComponentOf J (fixSubgroup β) ∧
      p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) ∧ ⁅P, J⁆ ≠ ⊥ ∧
      P ≤ J ⊔ (fixSubgroup β ⊓ Subgroup.centralizer (J : Set ↥(twistedE6RootGroup K σ))) := by
  have hK2 : ringChar K = 2 := ringChar_eq_two_of_card_eq_pow (n := f * 2)
    (by rw [hK, ← pow_mul])
  haveI : Finite ↥(twistedE6RootGroup K σ) := Subtype.finite
  obtain ⟨h, rfl⟩ := mem_range_twistedE6InndiagConj_of_mem_innAutDerived Nat.prime_two hf hK σ hσ
    hβmem
  have hp1 : h ^ p = 1 := twistedE6InndiagConj_injective Nat.prime_two hf hK σ hσ
    (by rw [map_pow, hβp, map_one])
  have hh1 : h ≠ 1 := fun h' => hβ1 (by rw [h', map_one])
  have hmon : MonomialToralAt Tag.E6 p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp) hp hp2
  obtain ⟨S, a, ι, hSq, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inndiag_twE6_of_prime Nat.prime_two hf hK σ hσ hp hp2 hp hp2 (Or.inr hq4)
      hmon (twistedE6InndiagConj K σ h) (h : ModGL TwistTag.E6.tag K) h.2
      (twistedE6InndiagConj_apply h) (by rw [← Subgroup.coe_pow, hp1]; rfl)
      (fun h' => hh1 (Subtype.ext h'))
  exact exists_comp_of_langSetup_two hK2 S (by rw [hSq]; exact hq4) hp hp2
    (by rw [hSq]; exact hpq) hT hap h1 ι hinj hrange _ hconj P hPβ hP2 hP1

theorem exists_comp_of_two_trialityD4 {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (hq4 : 4 ≤ 2 ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ (2 ^ f) ^ 2 - 1)
    (β : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hβmem : β ∈ innAutDerived ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hβp : β ^ p = 1) (hβ1 : β ≠ 1) (P : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hPβ : P ≤ fixSubgroup β) (hP2 : IsPGroup 2 ↥P) (hP1 : P ≠ ⊥) :
    ∃ J : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      IsComponentOf J (fixSubgroup β) ∧ p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) ∧ ⁅P, J⁆ ≠ ⊥ ∧
      P ≤ J ⊔ (fixSubgroup β ⊓
        Subgroup.centralizer (J : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) := by
  have hK2 : ringChar K = 2 := ringChar_eq_two_of_card_eq_pow (n := f * 3)
    (by rw [hK, ← pow_mul])
  haveI : Finite ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  have hβinn : β ∈ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range :=
    sup_le le_rfl (CFSG.HardMathSupport.Dickson.Sec6.I1431.t6outtrid4_commutator_le_range
      Nat.prime_two hf hK σ hσ) hβmem
  obtain ⟨x, rfl⟩ := hβinn
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hxp : x ^ p = 1 :=
    mulAut_conj_injective_of_center_eq_bot hZ (by rw [map_pow, hβp, map_one])
  have hx1 : x ≠ 1 := fun h => hβ1 (by rw [h, map_one])
  have hmon : MonomialToralAt Tag.D4 p :=
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five (by simp) hp hp2
  obtain ⟨S, a, ι, hSq, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
    exists_langSetup_of_inner_triD4_of_prime Nat.prime_two hf hK σ hσ hp hp2 hp hp2 (Or.inr hq4)
      hmon x hxp hx1
  exact exists_comp_of_langSetup_two hK2 S (by rw [hSq]; exact hq4) hp hp2
    (by rw [hSq]; exact hpq) hT hap h1 ι hinj hrange _ hconj P hPβ hP2 hP1

end CFSG.LocalAnalysis.GLTheoremA.T263.DX
