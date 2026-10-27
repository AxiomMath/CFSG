module

public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.Basic
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.L2Odd
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.L2Even
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_TablesB
public import CFSG.RankThree.PartOne.FOC.PSLTwoOuter
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Models

public section

namespace CFSG.HardMathSupport.Timmesfeld.FieldBonus

open CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartOne.Sec66T (fixSub)
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo (coordinateG pslEquivCoordinateG)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSL projectiveSpecialLinearGroupEquivStatedProj)
open scoped MatrixGroups

theorem not_threeTwoWitness_psl_two_odd_pow {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : Odd f) {X : Type} [Group X] (e : X ≃* projectiveSL 2 K) :
    ¬ ThreeTwoWitness X := by
  rintro ⟨P, hP, hP2, x, hx, hxN⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have hc : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK])
  have hmod : Nat.card K % 3 = 2 := by
    rw [hK]
    exact ComponentBalance.two_pow_odd_mod_three hf
  let e' : X ≃* SL(2, K) :=
    (e.trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 K).symm).trans
      (ComponentBalance.SL2Char2.mulEquivPSL K).symm
  have h1 := ComponentBalance.SL2Char2.eq_one_of_normalizes_two_group hmod (P.map e'.toMonoidHom)
    (hP2.map _) (by rwa [Ne, Subgroup.map_eq_bot_iff_of_injective P e'.injective]) (e' x)
    (by rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]) (by
      rintro _ ⟨s, hs, rfl⟩
      have := (Subgroup.mem_normalizer_iff.1 hxN s).1 hs
      exact ⟨x * s * x⁻¹, this, by simp⟩)
  have : x = 1 := e'.injective (h1.trans (map_one e').symm)
  rw [this, orderOf_one] at hx
  omega

theorem outerFixedWitness_psl_two {X : Type} [Group X] {K : Type} [Field K] [Finite K]
    (e : X ≃* projectiveSL 2 K) (hw : ThreeTwoWitness X) : OuterFixedWitness X := by
  refine OuterFixedWitness.of_mulEquiv e ?_
  have hw' : ThreeTwoWitness (projectiveSL 2 K) := hw.of_mulEquiv e
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
  let ψ : projectiveSL 2 K ≃* coordinateG K :=
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 K).symm.trans
      (pslEquivCoordinateG K)
  obtain ⟨hpf, k, hkcard, ⟨eX⟩⟩ :=
    CFSG.RankThree.PartOne.FOC.psl_two_fixSub_equiv_gen hℓ Nat.prime_three (by norm_num) hf hK ψ
      hαord hαi
  have hW : ThreeTwoWitness (StatedProj (StatedSL 2 k)) := by
    by_cases h2 : ℓ = 2
    · subst h2
      have hfe : Even (f : ℕ) := by
        by_contra hfo
        exact not_threeTwoWitness_psl_two_odd_pow hK (Nat.not_even_iff_odd.1 hfo)
          (MulEquiv.refl _) hw'
      obtain ⟨m, hm⟩ := hpf
      have hdiv : (f : ℕ) / 3 = m := by omega
      have hme : Even m := by
        rcases hfe with ⟨a, ha⟩
        exact ⟨a - m, by omega⟩
      rw [hdiv] at hkcard
      exact threeTwoWitness_psl_two_pow_even hkcard hme
    · have : Fintype k := Fintype.ofFinite k
      have hodd : Nat.card k % 2 = 1 := by
        rw [hkcard]
        exact Nat.odd_iff.1 ((hℓ.odd_of_ne_two h2).pow)
      have hneg : (-1 : k) ≠ 1 :=
        CFSG.HardMathSupport.Timmesfeld.Tables.Census.neg_one_ne_one_of_card hℓ h2 hkcard
      refine threeTwoWitness_psl_two_odd (fun h0 => hneg ?_) hodd
      have : (1 : k) + 1 = 0 := by simpa [one_add_one_eq_two] using h0
      exact neg_eq_of_add_eq_zero_left this
  exact hW.of_mulEquiv ((eX.trans ((pslEquivCoordinateG k).symm.trans
    (projectiveSpecialLinearGroupEquivStatedProj 2 k))).symm)

end CFSG.HardMathSupport.Timmesfeld.FieldBonus
