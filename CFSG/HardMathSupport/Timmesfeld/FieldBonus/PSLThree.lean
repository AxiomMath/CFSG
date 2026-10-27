module

public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.Basic
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Models
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Even3
public import CFSG.RankThree.PartOne.KC.LinearSubfieldInclusion
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.SteinbergR3ELinearFieldDescent

public section

namespace CFSG.HardMathSupport.Timmesfeld.FieldBonus

open Subgroup CFSG CFSG.Blueprint CFSG.RankThree.PartOne
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartOne.Sec66T (fixSub fixSubEquiv fixSub_congr)
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.HardMathSupport.Timmesfeld.Tables.Census
open CFSG.Assembly.LowTwoRank (StatedProj StatedSL projectiveSpecialLinearGroupEquivStatedProj)

theorem one_add_one_of_card_two_pow' {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) : (1 : K) + 1 = 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have hc : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK])
  have : ((2 : ℕ) : K) = 0 := CharP.cast_eq_zero K 2
  simpa [one_add_one_eq_two] using this

theorem threeTwoWitness_projectiveSL_three {k : Type} [Field k] [Finite k] {ℓ m : ℕ}
    (hℓ : ℓ.Prime) (hk : Nat.card k = ℓ ^ m) : ThreeTwoWitness (projectiveSL 3 k) := by
  have hW : ThreeTwoWitness (StatedProj (StatedSL 3 k)) := by
    by_cases h2 : ℓ = 2
    · subst h2
      exact threeTwoWitness_statedProj_psl_three_even (one_add_one_of_card_two_pow' hk)
    · exact threeTwoWitness_psl_three_odd (neg_one_ne_one_of_card hℓ h2 hk)
  exact hW.of_mulEquiv ((projectiveSpecialLinearGroupEquivStatedProj 3 k).symm.trans
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 k))

theorem outerFixedWitness_psl_three {X : Type} [Group X] {K : Type} [Field K] [Finite K]
    (hK3 : Nat.card K % 3 = 2) (e : X ≃* projectiveSL 3 K) : OuterFixedWitness X := by
  refine OuterFixedWitness.of_mulEquiv e ?_
  intro α hα3 hαi
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hαord : orderOf α = 3 :=
    orderOf_eq_prime hα3 (fun h1 => hαi (h1 ▸ (CFSG.RankThree.PartOne.Sec66T.innerAut _).one_mem))
  obtain ⟨ℓ, hℓchar⟩ := CharP.exists K
  have hℓ : ℓ.Prime := CharP.char_is_prime K ℓ
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ', hcard⟩ := FiniteField.card K ℓ
  have hK : Nat.card K = ℓ ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hcard
  have hf : 1 ≤ (f : ℕ) := f.pos
  have hn3 : 3 ≤ 3 := le_rfl
  have hpℓ : (3 : ℕ) ≠ ℓ := by
    rintro rfl
    rw [hK] at hK3
    have : 3 ∣ 3 ^ (f : ℕ) := dvd_pow_self 3 (by omega)
    omega
  have hdiagK : ¬ 3 ∣ Nat.gcd 3 (Nat.card K - 1) := by
    intro h
    have := h.trans (Nat.gcd_dvd_right _ _)
    omega
  obtain ⟨hgenTop, -⟩ := automorphism_generation (K := K) hn3
  obtain ⟨-, -, -, -, -, -, -, hidx, -, -⟩ := standard_outer_quotients (n := 3) (K := K)
  have hE : α ∈ semilinearAutGroup 3 K := by
    have hidx' : (semilinearAutGroup 3 K).index ≤ 2 := by
      have h2' : (semilinearAutGroup 3 K).relIndex (standardAutGroup 3 K) ≤ 2 := hidx
      rwa [hgenTop, Subgroup.relIndex_top_right] at h2'
    refine OutStructure.mem_of_pow_mem_of_index_le_two _ hidx' (show Odd 3 by decide) ?_
    rw [hα3]
    exact Subgroup.one_mem _
  have hD : α ∉ linearAutGroup 3 K := by
    intro hD
    exact hαi (OutStructure.linear_D2 Nat.prime_three hn3 hdiagK _ hD 1
      (by rw [pow_one, hα3]; exact Subgroup.one_mem _))
  obtain ⟨-, -, -, -, -, -, -, hdesc⟩ :=
    CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent hℓ hf hn3 hK
  obtain ⟨hpf, σ, hσord, ⟨h, -, hαh⟩, hkcard⟩ := hdesc 3 Nat.prime_three hpℓ α hE hD hαord
  set k := semilinearFixedSubfield σ with hk
  have hσfix : ∀ c ∈ k, σ c = c := fun c hc => hc
  have hinj := linearSubfieldInclusion_injective (by omega : 0 < 3) k
  have hW := threeTwoWitness_projectiveSL_three (k := ↥k) hℓ hkcard
  let ι : projectiveSL 3 ↥k →* ↥(fixSub (fieldAut 3 K σ)) :=
    (linearSubfieldInclusion 3 k).codRestrict _ (fun x => fieldAut_linearSubfieldInclusion hσfix x)
  have hιinj : Function.Injective ι := fun x y hxy => hinj (congrArg Subtype.val hxy)
  have hWf : ThreeTwoWitness ↥(fixSub (fieldAut 3 K σ)) := hW.of_injective ι hιinj
  let φ : projectiveSL 3 K ≃* projectiveSL 3 K := (h⁻¹ : MulAut (projectiveSL 3 K))
  have hφα : MulAut.congr φ α = fieldAut 3 K σ := by
    have : MulAut.congr φ α = h⁻¹ * α * h⁻¹⁻¹ := rfl
    rw [this, hαh]
    group
  have hfix : fixSub (fieldAut 3 K σ) = (fixSub α).map φ.toMonoidHom := by
    rw [← hφα]
    exact fixSub_congr φ α
  let e1 : ↥(fixSub α) ≃* ↥(fixSub (fieldAut 3 K σ)) :=
    (Subgroup.equivMapOfInjective (fixSub α) φ.toMonoidHom φ.injective).trans
      (MulEquiv.subgroupCongr hfix.symm)
  exact hWf.of_mulEquiv e1.symm

end CFSG.HardMathSupport.Timmesfeld.FieldBonus
