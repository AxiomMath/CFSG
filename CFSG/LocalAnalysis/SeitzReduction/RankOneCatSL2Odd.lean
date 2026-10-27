module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2Small
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenOuterPSL
public import CFSG.LocalAnalysis.SeitzReduction.RankOneU3StarCat

public section

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

@[expose] def SL2NotOddLieInputAt (n : ℕ) : Prop :=
  ∀ (X : Type) [Group X], LieModel X .PSL 2 2 n → ¬ OddLieType X

section G2Three


theorem card_outer_le_two_of_lieModel_G2_three {S : Type} [Group S]
    (hM : LieModel S .G2 0 3 1) : Nat.card (Outer S) ≤ 2 := by
  have hm : UntwistedChevalleyModel S .G2 (3 ^ 1) :=
    (CFSG.GH74.chevalleyExceptionalModel_of_lieModel (by decide) hM).2
  obtain ⟨K, _, _, hKc, ⟨e⟩⟩ := LieType.Chevalley.nonempty_mulEquiv_adjointGroup .G2 hm
  have hK3 : Nat.card K = 3 := by simpa using hKc
  let e' : S ≃* ↥(Chevalley.adjointGroup LieType.Ree.ReeTag.G2.tag K) := e
  have hchar3 : CharP K 3 := by
    have : Fintype K := Fintype.ofFinite K
    have hdvd : ringChar K ∣ Nat.card K :=
      ringChar.dvd (by rw [Nat.card_eq_fintype_card]; exact FiniteField.cast_card_eq_zero K)
    rw [hK3] at hdvd
    have h3 : ringChar K = 3 :=
      ((Nat.dvd_prime Nat.prime_three).1 hdvd).resolve_left CharP.ringChar_ne_one
    have := ringChar.charP K
    rwa [h3] at this
  have hchar : CharP K LieType.Ree.ReeTag.G2.prime := hchar3
  obtain ⟨-, -, ⟨Θ, -, hsurj, hker⟩, -⟩ :=
    LieType.Chevalley.G2_three_exact_automorphism_normal_form (f := 1) le_rfl K
      (by simpa using hK3)
  have hinner : OuterAutomorphisms.inner
      ↥(Chevalley.adjointGroup LieType.Ree.ReeTag.G2.tag K) = Θ.ker := hker.symm
  let e2 : Outer ↥(Chevalley.adjointGroup LieType.Ree.ReeTag.G2.tag K) ≃*
      Multiplicative (ZMod (2 * 1)) :=
    (QuotientGroup.quotientMulEquivOfEq hinner).trans
      (QuotientGroup.quotientKerEquivOfSurjective Θ hsurj)
  rw [Nat.card_congr ((OuterAutomorphisms.equivalence e').trans e2).toEquiv]
  simp [Nat.card_eq_fintype_card]

theorem card_lt_of_isPGroup_mulAut_G2_three {J : Type} [Group J] [Finite J]
    (hs : IsSimpleGroup J) (hna : ∃ a b : J, a * b ≠ b * a) (hM : LieModel J .G2 0 3 1)
    {P : Subgroup (MulAut J)} (hP : IsPGroup 2 P) : Nat.card P < 2 * (2 ^ 3) ^ 4 := by
  have hZ : center J = ⊥ := center_eq_bot_of_simple_nonabelian hs hna
  have hcard := card_mulAut_of_center_eq_bot hZ
  have hJ : Nat.card J = Open.ordG2 (3 ^ 1) := GH74.card_of_lieModel_G2 (by norm_num) hM
  have hO := card_outer_le_two_of_lieModel_G2_three hM
  have : Finite (MulAut J) :=
    Finite.of_injective (fun β : MulAut J => (β : J → J)) DFunLike.coe_injective
  have hOpos : 0 < Nat.card (Outer J) := Nat.card_pos
  have h1 := card_le_of_isPGroup_of_card_dvd hP (N := 64 * Nat.card (Outer J)) (u := 66339)
    (by decide) (by omega) (by
      rw [hcard, hJ, show Open.ordG2 (3 ^ 1) = 4245696 by decide]
      exact dvd_of_eq (by ring))
  have h2 : 64 * Nat.card (Outer J) ≤ 128 := by omega
  have h3 : (128 : ℕ) < 2 * (2 ^ 3) ^ 4 := by norm_num
  omega

theorem catSL2OddLieBound_of_inputs (hGLS : GLS3OddLieAutComponentsInput) {n : ℕ}
    (hX : SL2NotOddLieInputAt n) : CatSL2OddLieBound n := by
  rintro J _ _ hJ hna ⟨t, m, p, e, hp, hp2, hadm, hmJ⟩ τ ⟨hτ, D, hD, hDm, -⟩ P hP
  rcases hGLS J t m p e hp hp2 hadm hmJ τ hτ D hD with ⟨τ', n', f', hadm', hm'⟩ |
      ⟨rfl, hG2, -, hL⟩
  · exact (hX (D ⧸ center D) hDm ⟨τ', n', p, f', hp, hp2, hadm', hm'⟩).elim
  · have hDs : IsSimpleGroup D := LinearPilot.isSimpleGroup_of_lieModel_PSL hL
    have hZ : center D = ⊥ := F4Pilot.center_eq_bot_of_isQuasisimple hD.1 hDs
    have h1 := card_of_lieModel_PSL_two_two
      (LinearPilot.lieModel_quotient_center_of_center_eq_bot hZ hL)
    rw [card_of_lieModel_PSL_two_two hDm] at h1
    have hn : 1 ≤ n := (F4Pilot.statedLieAdmissible_of_lieModel hDm).2.1
    obtain rfl : n = 3 := RankThree.PartOne.S12K.ordA_one_inj hn (by norm_num) h1
    exact card_lt_of_isPGroup_mulAut_G2_three hJ hna hG2 hP

end G2Three

end CFSG.SeitzReduction.RankOne
