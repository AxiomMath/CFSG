module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoRankOne

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem diag_rootChar_eq_one_of_a2Shadow (K : Type) [Field K] (σ : K ≃+* K)
    (E₀ : Subgroup (twistedE6RootGroup K σ)) (hE₀ : ∀ a ∈ E₀, ∀ b ∈ E₀, Commute a b)
    (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (hmono : ∀ x ∈ E₀, ∃ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
      ∃ w : WeylGroup TwistTag.E6.tag,
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
            g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w)
    (hnd : ¬ ∀ x ∈ E₀, g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (x : ModGL TwistTag.E6.tag K) * g0 ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K))
    {α β : Fin TwistTag.E6.tag.rank → ℤ} (hαβ : IsA2Pair α β)
    (hW : TwE6WeylPartsIn K σ E₀ g0 (Subgroup.zpowers (rootReflection α * rootReflection β))) :
    ∀ x ∈ E₀, g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (x : ModGL TwistTag.E6.tag K) * g0 ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K) →
      ∃ b : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
            g0 = rootDiagUnit TwistTag.E6.tag b ∧ rootChar b α = 1 ∧ rootChar b β = 1 := by
  intro x hx hxT
  set L := AlgebraicClosure K
  set ι := baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K L) with hι
  obtain ⟨x₀, hx₀'⟩ := not_forall.1 hnd
  obtain ⟨hx₀, hx₀T⟩ := not_imp.1 hx₀'
  obtain ⟨t₀, ht₀, w, hw⟩ := hmono x₀ hx₀
  have hwS := hW x₀ hx₀ t₀ ht₀ w hw
  have hw1 : w ≠ 1 := by
    rintro rfl
    rw [canonicalRep_one, mul_one] at hw
    exact hx₀T (hw ▸ ht₀)
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hxT
  refine ⟨b, hb, ?_⟩
  obtain ⟨b₀, hb₀⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht₀
  set n := canonicalRep (coxeterSystem TwistTag.E6.tag) L w with hn
  have hφ : ∀ y z : twistedE6RootGroup K σ,
      g0⁻¹ * ι ((y * z : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0 =
        (g0⁻¹ * ι (y : ModGL TwistTag.E6.tag K) * g0) *
          (g0⁻¹ * ι (z : ModGL TwistTag.E6.tag K) * g0) := by
    intro y z
    rw [Subgroup.coe_mul, map_mul]
    group
  have hcomm : x * x₀ = x₀ * x := hE₀ x hx x₀ hx₀
  have hc := hφ x x₀
  rw [hcomm, hφ x₀ x, hb, hw, hb₀] at hc
  have hdd : rootDiagUnit TwistTag.E6.tag b * rootDiagUnit TwistTag.E6.tag b₀ =
      rootDiagUnit TwistTag.E6.tag b₀ * rootDiagUnit TwistTag.E6.tag b :=
    Units.ext (by
      change rootDiag b * rootDiag b₀ = rootDiag b₀ * rootDiag b
      rw [rootDiag_mul_rootDiag, rootDiag_mul_rootDiag, mul_comm])
  have h1 : rootDiagUnit TwistTag.E6.tag b₀ * (n * rootDiagUnit TwistTag.E6.tag b) =
      rootDiagUnit TwistTag.E6.tag b₀ * (rootDiagUnit TwistTag.E6.tag b * n) := by
    rw [← mul_assoc, hc, ← mul_assoc, ← mul_assoc, hdd]
  have hdn : rootDiagUnit TwistTag.E6.tag b = n * rootDiagUnit TwistTag.E6.tag b * n⁻¹ := by
    rw [mul_left_cancel h1, mul_inv_cancel_right]
  have hfix : ∀ u, rootChar b (w • u) = rootChar b u :=
    (rootDiagUnit_eq_conj_canonicalRep_iff b b w).1 hdn
  set p := rootReflection α * rootReflection β with hp
  have hp3 : p ^ (3 : ℤ) = 1 := by
    have h := hαβ.pairRefl_pow_three
    exact_mod_cast h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hwS
  have hpk : w = p ^ (k % 3) := by
    have hkk : k = 3 * (k / 3) + k % 3 := by omega
    rw [← hk]
    conv_lhs => rw [hkk]
    rw [zpow_add, zpow_mul, hp3, one_zpow, one_mul]
  have hfixp : ∀ u, rootChar b (p • u) = rootChar b u := by
    have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hk3 with h | h | h
    · exact absurd (by rw [hpk, h, zpow_zero]) hw1
    · have e : p = w := by rw [hpk, h, zpow_one]
      rw [e]
      exact hfix
    · have e : p = w * w := by
        rw [hpk, h, ← zpow_add, show (2 : ℤ) + 2 = 3 + 1 by norm_num, zpow_add, hp3, one_mul,
          zpow_one]
      intro u
      rw [e, mul_smul, hfix, hfix]
  exact rootChar_eq_one_of_pairRefl_fixed_E6 hαβ b hfixp

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end
