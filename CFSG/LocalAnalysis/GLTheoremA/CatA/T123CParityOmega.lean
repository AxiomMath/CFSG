module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CParityCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CParityOrth
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbitModel
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelFamily

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T123C

open CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction (Points)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (stated_pointFamily_fixed)

private theorem two_pow_mod_three {n : ℕ} (hn : Odd n) : 2 ^ n % 3 = 2 := by
  obtain ⟨m, hm⟩ := hn
  rw [hm, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

private theorem card_points_eq {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) : Nat.card (Points Q) = Nat.card (singularLinesIn Q ⊤) :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => ⟨fun h => ⟨le_top, h⟩, fun h => h.2⟩)

private theorem not_dvd_of_split_count {p q n I : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ q + 1) (hn : Odd n) (hq : 1 ≤ q)
    (h : (q - 1) * I = (q ^ n - 1) * (q ^ (n - 1) + 1)) : ¬ p ∣ I := by
  intro hI
  have hq' : (q : ZMod p) = -1 := by
    have h0 : ((q + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpq
    push_cast at h0
    linear_combination h0
  have h' : ((q - 1 : ℕ) : ZMod p) * (I : ZMod p) =
      ((q ^ n - 1 : ℕ) : ZMod p) * ((q ^ (n - 1) + 1 : ℕ) : ZMod p) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, h]
  rw [(ZMod.natCast_eq_zero_iff I p).2 hI, mul_zero, Nat.cast_sub (Nat.one_le_pow n q hq),
    Nat.cast_add, Nat.cast_pow, Nat.cast_pow, Nat.cast_one, hq', hn.neg_one_pow,
    (Nat.Odd.sub_odd hn odd_one).neg_one_pow] at h'
  have h4 : ((2 ^ 2 : ℕ) : ZMod p) = 0 := by
    push_cast
    linear_combination h'
  have h2 := hp.dvd_of_dvd_pow ((ZMod.natCast_eq_zero_iff _ _).1 h4)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)

theorem parityCoreOmMinus_holds : ParityCoreOmMinus := by
  intro n K _ _ b c hn h6 hK hirr
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK1 : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  have : CharP K 2 := ringChar_eq_of_card_eq Nat.prime_two le_rfl hK1 ▸ ringChar.charP K
  obtain ⟨hnd, hT⟩ := regular_quadMinus (K := K) (n := n) (by omega) hirr
  refine parityCoreAt_of_statedPointAction (coe_quadMinus n K b c)
    (commutator_orthogonalGroup_quadMinus (by omega) hirr) hnd hT ?_ Nat.prime_three ?_
  · have hmodel : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadMinus n K b c)))
        .POmegaMinus n 2 1 :=
      ⟨⟨Nat.prime_two, le_rfl, show 4 ≤ n by omega⟩, K, inferInstance, inferInstance, hK1, b, c,
        hirr, ⟨MulEquiv.refl _⟩⟩
    exact (OrthogonalTail.orthogonal_geometry_tail_model_point_family_invariant _ .POmegaMinus
      (Or.inr rfl) n 2 1 hmodel (by omega) K hK1 b c hirr).1
  · set f := (OrthogonalTail.minusTailIsometry n K b c).toLinearEquiv
    have hf : ∀ w, quadMinus n K b c (f w) =
        OrthogonalTail.quadTail (n - 1) (OrthogonalTail.minusTailForm K b c) w :=
      (OrthogonalTail.minusTailIsometry n K b c).map_app
    have h2 := card_singular_vectors (quadMinus n K b c) ⊤
    rw [hK, show (2 : ℕ) - 1 = 1 from rfl, one_mul] at h2
    have h3 : Nat.card {w : (Fin (n - 1) ⊕ Fin (n - 1) → K) × (Fin 2 → K) //
          w ≠ 0 ∧ OrthogonalTail.quadTail (n - 1) (OrthogonalTail.minusTailForm K b c) w = 0} =
        Nat.card {v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K //
          v ∈ (⊤ : Submodule K _) ∧ v ≠ 0 ∧ quadMinus n K b c v = 0} :=
      Nat.card_congr (Equiv.subtypeEquiv f.toEquiv fun w => by
        rw [LinearEquiv.coe_toEquiv, hf, f.map_ne_zero_iff]
        exact ⟨fun h => ⟨Submodule.mem_top, h⟩, fun h => h.2⟩)
    have h4 := OrthogonalTail.card_quadTail_nonzero_singular
      (OrthogonalTail.anisotropic_minusTailForm hirr) (n - 1)
    rw [Module.finrank_fin_fun, hK, show n - 1 + 2 - 1 = n by omega] at h4
    have hpts : Nat.card (Points (quadMinus n K b c)) = (2 ^ (n - 1) - 1) * (2 ^ n + 1) := by
      rw [card_points_eq, ← h4, h3]
      exact h2.symm
    have ha := two_pow_mod_three (Nat.Even.sub_odd (by omega) hn odd_one)
    have hb : 2 ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hpts, hb, Nat.dvd_iff_mod_eq_zero, Nat.mul_mod]
    generalize 2 ^ (n - 1) = a at ha ⊢
    have h5 : (a - 1) % 3 = 1 := by omega
    have h6 : (2 * a + 1) % 3 = 2 := by omega
    rw [h5, h6]
    norm_num

theorem parityCoreOmPlus_holds : ParityCoreOmPlus := by
  intro p n k K _ _ hp hp2 hn h5 hk hpk hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := ringChar_eq_of_card_eq Nat.prime_two hk hK ▸ ringChar.charP K
  obtain ⟨hnd, hT⟩ := regular_quadPlus (K := K) (n := n) (by omega)
  refine parityCoreAt_of_statedPointAction (coe_quadPlus n K)
    (commutator_orthogonalGroup_quadPlus (by omega)) hnd hT ?_ hp ?_
  · rw [eq_top_iff]
    intro α _
    exact stated_pointFamily_fixed h5 α
  · rw [card_points_eq]
    exact not_dvd_of_split_count hp hp2 (by rw [hK]; exact hpk) hn
      (by rw [hK]; exact Nat.one_le_two_pow) (orthogonal_geometry_split_point_count K n).1

end CFSG.LocalAnalysis.GLTheoremA.T123C

end
