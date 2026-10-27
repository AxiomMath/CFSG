module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoCaseDefs
import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeBlock
public import CFSG.Monster.B.E6.StdF4RadicalRoots

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem rk1_rootChar_neg {L : Type} [Field L] (b : Fin Tag.E6.rank → Lˣ)
    (v : Fin Tag.E6.rank → ℤ) : rootChar b (-v) = (rootChar b v)⁻¹ := by
  rw [← zero_sub, rootChar_sub, rootChar_zero, one_mul]

section Lattice


theorem exists_root_iform_a2Pair_E6 {α β : Fin Tag.E6.rank → ℤ} (h : IsA2Pair α β) :
    ∃ δ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 δ ∧ iform δ α = 0 ∧ iform δ β = -1 := by
  obtain ⟨v, hv0, hv2⟩ := exists_weyl_a2Pair_E6 h
  refine ⟨v • (Pi.single 3 1 : Fin Tag.E6.rank → ℤ), IsRoot.smul (IsRoot.basis 3) v, ?_, ?_⟩
  · rw [← hv0, iform_smul]
    decide +kernel
  · rw [← hv2, iform_smul]
    decide +kernel

theorem rootChar_eq_one_of_pairRefl_fixed_E6 {L : Type} [Field L] {α β : Fin Tag.E6.rank → ℤ}
    (h : IsA2Pair α β) (b : Fin Tag.E6.rank → Lˣ)
    (hb : ∀ v, rootChar b ((rootReflection α * rootReflection β) • v) = rootChar b v) :
    rootChar b α = 1 ∧ rootChar b β = 1 := by
  obtain ⟨δ, -, hδα, hδβ⟩ := exists_root_iform_a2Pair_E6 h
  have hrβ : rootReflection β • δ = δ + β := by
    rw [rootReflection_smul h.isRoot_snd, corootPair, iform_comm β δ, hδβ,
      iform_self_E6 h.isRoot_snd]
    norm_num
  have hrα : rootReflection α • δ = δ :=
    rootReflection_smul_of_iform_eq_zero h.isRoot_fst (by rw [iform_comm]; exact hδα)
  have hα' : (rootReflection α * rootReflection β) • α = β := by
    rw [mul_smul, h.rootReflection_snd_smul_fst, smul_add, rootReflection_smul_self h.isRoot_fst,
      h.rootReflection_fst_smul_snd, neg_add_cancel_left]
  have hβ' : (rootReflection α * rootReflection β) • β = -(α + β) := by
    rw [mul_smul, rootReflection_smul_self h.isRoot_snd, smul_neg, h.rootReflection_fst_smul_snd]
  have hδ' : (rootReflection α * rootReflection β) • δ = δ + (α + β) := by
    rw [mul_smul, hrβ, smul_add, hrα, h.rootReflection_fst_smul_snd]
  have e1 := hb α
  have e2 := hb β
  have e3 := hb δ
  rw [hα'] at e1
  rw [hβ', rk1_rootChar_neg, rootChar_add] at e2
  rw [hδ', rootChar_add, rootChar_add] at e3
  have hab : rootChar b α * rootChar b β = 1 := by
    have e3' : rootChar b δ * (rootChar b α * rootChar b β) = rootChar b δ * 1 := by
      rw [mul_one]
      exact e3
    exact mul_left_cancel e3'
  rw [hab, inv_one] at e2
  exact ⟨e1.symm.trans e2.symm, e2.symm⟩

end Lattice

section Kill


theorem twE6CaseIIA2Kill_holds : TwE6CaseIIA2Kill := by
  intro K _ _ σ q _ _ _ _ _ E₀ hE₀ _ _ _ Fr _ v _ g0 _ _ hmono h0 α β hαβ hW x hx hxT
  set L := AlgebraicClosure K
  set ι := baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K L) with hι
  obtain ⟨x₀, hx₀'⟩ := not_forall.1 h0
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
  have hcomm : x * x₀ = x₀ * x := congrArg Subtype.val (hE₀.1.is_comm.comm ⟨x, hx⟩ ⟨x₀, hx₀⟩)
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
  have hnd : rootDiagUnit TwistTag.E6.tag b = n * rootDiagUnit TwistTag.E6.tag b * n⁻¹ := by
    rw [mul_left_cancel h1, mul_inv_cancel_right]
  have hfix : ∀ u, rootChar b (w • u) = rootChar b u :=
    (rootDiagUnit_eq_conj_canonicalRep_iff b b w).1 hnd
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

end Kill

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end
