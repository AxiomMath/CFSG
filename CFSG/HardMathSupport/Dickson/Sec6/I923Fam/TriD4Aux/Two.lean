module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4Aux.G2Class
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4Aux.PGLClass
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TriD4OuterAux.Two

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec8
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi PiField ModThree)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.HardMathSupport.Dickson.Sec6.I923
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross (card_projImage_glPi_three)

set_option linter.unusedSectionVars false


theorem noL2Layer_fieldActor_two_all {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    NoL2Layer (fieldActor (t := TwistTag.D4) σ σ) := by
  rcases Nat.lt_or_ge f 2 with h | h
  · obtain rfl : f = 1 := by omega
    exact noL2Layer_fieldActor_one hK σ hσ
  · exact noL2Layer_fieldActor_two h hK σ hσ

theorem noL2Layer_three_D4_outer_two {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hφ3 : φ ^ 3 = 1)
    (hφ : φ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) :
    NoL2Layer φ := by
  haveI := finite_graphFixedRootGroup_D4 σ
  have hG2 : NoL2Layer (fieldActor (t := TwistTag.D4) σ σ) :=
    noL2Layer_fieldActor_two_all hf hK σ hσ
  rcases Item8KFacts2Proof.isStdGraphFieldConj_or_nonempty_autFix_equiv hf hK hσ hφ3
    (by exact hφ) with ⟨β, hβ | hβ⟩ | he₂
  · rw [hβ]
    exact noL2Layer_conj β hG2
  · rw [hβ]
    exact noL2Layer_conj β ((noL2Layer_inv_iff _).2 hG2)
  · obtain ⟨e₂⟩ := he₂
    have hfix : fixSubgroup φ = Sec4.autFix φ := Subgroup.ext fun _ => Iff.rfl
    let ef : ↥(fixSubgroup φ) ≃* ↥(Sec4.autFix φ) := MulEquiv.subgroupCongr hfix
    rcases Nat.even_or_odd f with hfe | hfo
    · obtain ⟨F, _, _, hF, ⟨e₃⟩⟩ := kF82D4SecondCentY0Even_holds f hfe hf K σ hK hσ
      have hPi : PiField true 2 f F := ⟨Nat.prime_two, hf, hF⟩
      have hf2 : 2 ≤ f := by
        obtain ⟨k, hk⟩ := hfe
        omega
      have hq2 : 2 < 2 ^ f :=
        lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf2)
      exact noL2Layer_of_equiv_projImage hPi hq2 φ (ef.trans (e₂.trans e₃))
        fun r hr => not_typeL2_projImage_slPi_true hPi hq2 hr
    · obtain ⟨F, _, _, hF, ⟨e₃⟩⟩ := kF82D4SecondCentY0_holds f hfo K σ hK hσ
      have hPi : PiField false 2 f F := ⟨Nat.prime_two, hf, hF⟩
      by_cases hf1 : f = 1
      · subst hf1
        refine noL2Layer_of_card_dvd φ (N := 216) (by norm_num) ?_ 8 (by norm_num) ?_
        · have h1 := card_projImage_glPi_three hPi
          rw [Nat.card_congr (ef.trans (e₂.trans e₃)).toEquiv, h1]
          norm_num
        · intro r hr hr8
          omega
      · have hf3 : 3 ≤ f := by
          obtain ⟨k, hk⟩ := hfo
          omega
        have hq2 : 2 < 2 ^ f :=
          lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf3)
        exact noL2Layer_of_equiv_projImage hPi hq2 φ (ef.trans (e₂.trans e₃))
          fun r hr => not_typeL2_projImage_slPi_false hPi hq2 hr

end CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux
