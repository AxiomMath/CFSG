module

public import CFSG.LieType.Chevalley.G2ThreeAutomorphismNormalForm
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abG2
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab CFSG.LocalAnalysis.ComponentInitial CFSG.Open
open CFSG.LieType.Ree (ReeTag)


theorem card_dvd_of_ker_eq_range {G M H : Type} [Group G] [Group M] [Group H] [Finite G]
    [Finite M] [Finite H] (c : G →* M) (Θ : M →* H) (hker : Θ.ker = c.range) :
    Nat.card M ∣ Nat.card G * Nat.card H := by
  have h1 := Subgroup.card_ker_mul_card_range Θ
  have h2 : Nat.card Θ.ker ∣ Nat.card G := by
    rw [hker]
    have := Subgroup.card_ker_mul_card_range c
    exact ⟨Nat.card c.ker, by rw [← this, mul_comm]⟩
  have h3 : Nat.card Θ.range ∣ Nat.card H := Subgroup.card_subgroup_dvd_card _
  rw [← h1]
  exact mul_dvd_mul h2 h3


theorem card_mulAut_G2_dvd {M : Type} [Group M] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hM : LieModel M .G2 0 p 1) : Nat.card (MulAut M) ∣ 2 * ordG2 p := by
  classical
  obtain ⟨K, hK, hKfin, hcard, ⟨φ⟩⟩ := exists_equiv_of_lieModel hM
  rw [pow_one] at hcard
  have hGcard : Nat.card (adjointGroup .G2 K) = ordG2 p := by
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hcard]
  have hMeq : Nat.card (MulAut M) = Nat.card (MulAut (adjointGroup .G2 K)) :=
    Nat.card_congr (MulAut.congr φ).toEquiv
  have hfinG : Finite (adjointGroup .G2 K) := inferInstance
  have hfinAut : Finite (MulAut (adjointGroup .G2 K)) :=
    Finite.of_injective (fun f : MulAut (adjointGroup .G2 K) =>
      (f : adjointGroup .G2 K → adjointGroup .G2 K)) DFunLike.coe_injective
  rw [hMeq]
  by_cases hp3 : p = 3
  · subst hp3
    have : CharP K ReeTag.G2.prime := finite_field_prime_power_characteristic hp le_rfl
      (by rw [pow_one]; exact hcard)
    obtain ⟨-, -, ⟨Θ, -, -, hΘk⟩, -⟩ := G2_three_exact_automorphism_normal_form (f := 1) le_rfl K
      (by rw [pow_one]; exact hcard)
    have h := card_dvd_of_ker_eq_range (MulAut.conj : adjointGroup .G2 K →*
      MulAut (adjointGroup .G2 K)) Θ hΘk
    have h2 : Nat.card (Multiplicative (ZMod (2 * 1))) = 2 := by
      rw [show 2 * 1 = 2 by norm_num]
      exact Nat.card_zmod 2
    rw [h2, hGcard] at h
    rwa [mul_comm] at h
  · obtain ⟨-, Θ, -, -, hΘk, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form hp hp2
      le_rfl K (by rw [pow_one]; exact hcard) .G2 (Or.inr ⟨rfl, hp3⟩)
    have hfinR : Finite (K ≃+* K) :=
      Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective
    have h := card_dvd_of_ker_eq_range (MulAut.conj : adjointGroup .G2 K →*
      MulAut (adjointGroup .G2 K)) Θ hΘk
    have h2 : Nat.card (K ≃+* K) = 1 :=
      (card_ringAut_and_isCyclic hp K (by rw [pow_one]; exact hcard)).1
    rw [h2, hGcard, mul_one] at h
    exact h.trans (dvd_mul_left _ _)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
