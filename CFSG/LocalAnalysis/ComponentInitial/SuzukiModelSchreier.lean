module

public import CFSG.LocalAnalysis.ComponentInitial.SuzukiRootA
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiTwoAAutomorphisms
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelInterface
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingOuterBound

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.Blueprint CFSG.LieType.Ree
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {a : ℕ} {K : Type} [Field K]

theorem Suzuki_root_automorphism_solvable (ha : 1 ≤ a) [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    derivedSeries (MulAut (suzukiU a K)) 3 = ⊥ := by
  obtain ⟨hchar, ⟨φ, hφ⟩, hθθ, -⟩ := suzuki_frobenius_exponents a K hK
  let _ : Module (ZMod 2) K := (ZMod.algebra K 2).toModule
  have hφ4 : φ ^ 4 ≠ 1 := by
    intro h4
    have hψ : ∀ x : K, (φ ^ 2) x = x ^ 2 := fun x => by
      rw [sq, RingAut.mul_apply, hφ, hφ, hθθ]
    have hx : ∀ x : K, x ^ 4 = x := fun x => by
      have h := ringAut_pow_apply_of_sq hψ 2 x
      rw [← pow_mul, h4, RingAut.one_apply] at h
      norm_num at h
      exact h.symm
    have : Fintype K := Fintype.ofFinite K
    have hcard : Fintype.card K = 2 ^ (2 * a + 1) := by rw [← Nat.card_eq_fintype_card, hK]
    have hdeg := FiniteField.X_pow_card_sub_X_natDegree_eq K (by norm_num : 1 < 4)
    have hP := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      (Polynomial.X ^ 4 - Polynomial.X : Polynomial K) (f := id) Function.injective_id
      (fun x => by simp [hx x])
      (by
        rw [hdeg, hcard]
        calc 4 < 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [hP, Polynomial.natDegree_zero] at hdeg
    omega
  obtain ⟨-, -, -, -, -, -, -, h3, -⟩ :=
    suzuki_two_A_automorphism_solvable (K := K) (by omega : 1 ≤ 2 * a + 1) hK φ hφ4
  obtain ⟨ι, -⟩ := Suzuki_root_A_isomorphism hK φ hφ
  rw [← map_derivedSeries_eq (f := (MulAut.congr ι).symm.toMonoidHom)
    (MulAut.congr ι).symm.surjective, h3, Subgroup.map_bot]

theorem Suzuki_model_Schreier (H : Type) [Group H] (p f : ℕ) (h : SuzukiModel H p f) :
    derivedSeries (Outer H) 3 = ⊥ ∧ Group.IsSolvable (Outer H) := by
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := h
  have hG : derivedSeries (Outer (suzukiGroup a K)) 3 = ⊥ := by
    obtain ⟨-, -, -, -, -, hprod, hinj⟩ := Suzuki_model_opposite_root_interface ha hK
    set C := pairAutSubgroup (suzukiU a K)
      ((suzukiU a K).map (MulAut.conj (suzukiWElt a K)).toMonoidHom) with hCdef
    have hC : derivedSeries C 3 = ⊥ := by
      have h1 := map_derivedSeries_le_derivedSeries (pairAutRestrict (suzukiU a K)
        ((suzukiU a K).map (MulAut.conj (suzukiWElt a K)).toMonoidHom)) 3
      rw [Suzuki_root_automorphism_solvable ha hK, le_bot_iff,
        Subgroup.map_eq_bot_iff_of_injective _ hinj] at h1
      exact h1
    let π : C →* Outer (suzukiGroup a K) :=
      (QuotientGroup.mk' (inner (suzukiGroup a K))).comp C.subtype
    have hπ : Function.Surjective π := by
      intro q
      obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective (inner (suzukiGroup a K)) q
      obtain ⟨g, β, hβ, rfl⟩ := hprod α
      refine ⟨⟨β, hβ⟩, ?_⟩
      change ((β : MulAut (suzukiGroup a K)) : Outer (suzukiGroup a K)) =
        ((MulAut.conj g * β : MulAut (suzukiGroup a K)) : Outer (suzukiGroup a K))
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (N := inner (suzukiGroup a K))
        (MulAut.conj g)).2 ⟨g, rfl⟩, one_mul]
    rw [← map_derivedSeries_eq hπ, hC, Subgroup.map_bot]
  obtain ⟨⟨E, -⟩, -⟩ := outer_isomorphism e
  have hH : derivedSeries (Outer H) 3 = ⊥ := by
    rw [← map_derivedSeries_eq (f := E.symm.toMonoidHom) E.symm.surjective, hG, Subgroup.map_bot]
  exact ⟨hH, ⟨⟨3, hH⟩⟩⟩

end CFSG.LocalAnalysis.ComponentInitial
