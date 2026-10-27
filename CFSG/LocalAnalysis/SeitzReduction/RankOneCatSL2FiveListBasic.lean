module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2TwoOddFive
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2OddFive

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

@[expose] def FiveA5Group (X : Type) [Group X] : Prop :=
  (∃ D : Subgroup X, IsComponent D ∧ LieModel (D ⧸ center D) .PSL 2 2 2) ∧
    ∀ Q : Subgroup X, IsPGroup 2 Q → Nat.card Q ≤ 16

namespace FiveList

theorem lieModel_centerQuotient_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {t : StatedLieTag} {n p f : ℕ} (h : LieModel (A ⧸ center A) t n p f) :
    LieModel (B ⧸ center B) t n p f :=
  LieType.CurtisTits.lieModel_of_mulEquiv (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)) h

theorem lieModel_centerQuotient_of_simple {L Y : Type} [Group L] [Group Y] [IsSimpleGroup Y]
    (hnab : ∃ a b : Y, a * b ≠ b * a) (E : L ≃* Y) {t : StatedLieTag} {n p e : ℕ}
    (hY : LieModel Y t n p e) : LieModel (L ⧸ center L) t n p e := by
  have hZ : center Y = ⊥ := ComponentClassification.ExcSelector.center_eq_bot_of_isSimpleGroup' hnab
  refine lieModel_centerQuotient_of_mulEquiv E.symm ?_
  exact LieType.CurtisTits.lieModel_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm hY

end FiveList

theorem FiveA5Group.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : FiveA5Group X) : FiveA5Group Y := by
  obtain ⟨⟨D, hD, hDm⟩, h2⟩ := h
  refine ⟨⟨D.map e.toMonoidHom, LocalCores.isComponent_map_mulEquiv e hD,
    FiveList.lieModel_centerQuotient_of_mulEquiv
      (D.equivMapOfInjective e.toMonoidHom e.injective) hDm⟩, fun Q hQ => ?_⟩
  have h1 := h2 (Q.map e.symm.toMonoidHom) (hQ.map _)
  rwa [Subgroup.card_map_of_injective e.symm.injective] at h1

theorem fiveA5Group_of_catSL2Hyp {J : Type} [Group J] [Finite J] {τ : MulAut J}
    (h : CatSL2Hyp J τ 2) : FiveA5Group (fixedSubgroup τ) := by
  obtain ⟨-, D, hD, hDm, h2⟩ := h
  refine ⟨⟨D, hD, hDm⟩, fun Q hQ => ?_⟩
  have h1 := card_le_of_isPGroup_fixedSubgroup hD hDm h2 hQ
  have h2' : padicValNat 2 2 = 1 := by simp
  rw [h2'] at h1
  simpa using h1

theorem FiveA5Group.not_dvd {X : Type} [Group X] [Finite X] (h : FiveA5Group X) :
    ¬ 32 ∣ Nat.card X := by
  intro h32
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime (G := X) 2 (n := 5)
    (by norm_num; exact h32)
  have h1 := h.2 Q (IsPGroup.of_card hQ)
  rw [hQ] at h1
  norm_num at h1

theorem FiveA5Group.of_eq {S : Type} [Group S] {γ γ' : MulAut S} (hγ : γ = γ')
    (h : FiveA5Group (fixedSubgroup γ)) : FiveA5Group (fixedSubgroup γ') :=
  h.of_mulEquiv (MulEquiv.subgroupCongr (congrArg fixedSubgroup hγ))

theorem FiveA5Group.congr {J J' : Type} [Group J] [Group J'] (e : J ≃* J') {α : MulAut J}
    (h : FiveA5Group (fixedSubgroup α)) : FiveA5Group (fixedSubgroup (MulAut.congr e α)) :=
  h.of_mulEquiv (ComponentClassification.CatLeafProof.fixedSubgroupCongrEquiv e α)

theorem eq_five_of_lieModel_PSL_two_two
    {X : Type} [Group X] (hX : LieModel X .PSL 2 2 2) {t : StatedLieTag} {n p g : ℕ}
    (hp2 : p ≠ 2) (hadm : StatedLieAdmissible t n p g) (h : LieModel X t n p g) :
    t = .PSL ∧ n = 2 ∧ p ^ g = 5 := by
  have hadm2 := CrossChar.statedLieAdmissible_of_lieModel hX
  have hT : t ≠ .Tits := by
    rintro rfl
    exact hp2 hadm.2.2.2.1
  rcases CrossChar.crossChar_arith hadm2 hadm hp2
      (CrossChar.card_mul_lieOrderDivisor_of_ne_Tits hadm2 hX (by decide))
      (CrossChar.card_mul_lieOrderDivisor_of_ne_Tits hadm h hT) with
    ⟨-, -, -, h1, h2, h5⟩ | ⟨-, h3, -⟩ | ⟨h1, -⟩
  · exact ⟨h1, h2, h5⟩
  · omega
  · exact absurd h1 (by decide)

theorem eq_one_of_five_pow_eq_five {g : ℕ} (h : 5 ^ g = 5) : g = 1 := by
  have h' : 5 ^ g = 5 ^ 1 := by rw [h, pow_one]
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 5) h'

@[expose] def OddFiveSL2BoundFamilyInput (t : StatedLieTag) : Prop :=
  ∀ (J : Type) [Group J] [Finite J], IsSimpleGroup J → (∃ a b : J, a * b ≠ b * a) →
    ∀ (m f : ℕ), StatedLieAdmissible t m 5 f → LieModel J t m 5 f →
      ∀ τ : MulAut J, CatSL2Hyp J τ 2 → AutTwoBound J 2

section Bound

theorem autTwoBound_two_of_fiveList {J : Type} [Group J] [Finite J] (hJ : IsSimpleGroup J)
    (hna : ∃ a b : J, a * b ≠ b * a)
    (h : LieModel J .PSL 2 5 2 ∨ LieModel J .PSL 3 5 1 ∨ LieModel J .PSU 3 5 1 ∨
      LieModel J .PSp 2 5 1) : AutTwoBound J 2 := by
  rcases h with h1 | h1 | h1 | h1
  · exact autTwoBound_two_of_L2_25 hJ hna h1
  · exact autTwoBound_two_of_L3_5 hJ hna h1
  · exact autTwoBound_two_of_U3_5 hJ hna h1
  · exact autTwoBound_two_of_PSp4_5 hJ hna h1

theorem oddFiveSL2BoundFamilyInput_of_list {t : StatedLieTag}
    (h : OddFiveSL2ListFamilyInput t) : OddFiveSL2BoundFamilyInput t :=
  fun J _ _ hJ hna m f hadm hJm τ hτ =>
    autTwoBound_two_of_fiveList hJ hna (h J hJ hna m f hadm hJm τ hτ)

theorem catSL2OddLieBound_two_of_boundFamilies (hGLS : GLS3OddLieAutComponentsInput)
    (h : ∀ t, OddFiveSL2BoundFamilyInput t) : CatSL2OddLieBound 2 := by
  rintro J _ _ hJ hna ⟨t, m, p, f, hp, hp2, hadm, hJm⟩ τ hτ
  obtain rfl := eq_five_of_catSL2Hyp_two hGLS hp hp2 hadm hJm hτ
  exact h t J hJ hna m f hadm hJm τ hτ

end Bound

end CFSG.SeitzReduction.RankOne
