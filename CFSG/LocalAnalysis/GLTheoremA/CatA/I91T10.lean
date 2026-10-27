module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T9
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResTwF4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResAll

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace I91T

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.StandardType CFSG.Assembly TauCeti
open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.CatB
open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.Adapters.RankTwoModelTransports
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.ComponentClassification.PresentationLocal
open scoped commutatorElement


theorem excClass_contra {S : Type} [Group S] [Finite S]
    (hcl : catalogIs S isA6 ∨ (∃ k, 2 ≤ k ∧ Even k ∧ catalogIs S (isA2n k)) ∨
      (∃ k, 5 ≤ k ∧ Odd k ∧ catalogIs S (isU3n k)))
    {M N : ℕ} (hM : Nat.card S ≤ M) (hM' : M ≤ 35942400) (hN : N ≤ twoPart (Nat.card S))
    (hA : 360 ≤ M → 8 < N) (hA2 : 20160 ≤ M → 64 < N) : False := by
  rcases hcl with hA6 | ⟨k, hk2, hke, hkc⟩ | ⟨k, hk5, hko, hkc⟩
  · have c := card_isA6 hA6
    have h1 : 360 ≤ M := by omega
    have h2 := hA h1
    have h3 : twoPart (Nat.card S) = 8 := by rw [c]; exact twoPart_360
    omega
  · have c := card_isA2n hkc
    have hR3 : (2 : ℕ) ^ k % 3 = 1 := two_pow_mod_three_even hke
    rcases Nat.lt_or_ge k 4 with hk4 | hk4
    · have hk : k = 2 := by
        obtain ⟨j, hj⟩ := hke
        omega
      subst hk
      have c2 : orderA 2 (2 ^ 2) = 20160 := by
        unfold orderA
        rw [show Finset.Icc 2 (2 + 1) = {2, 3} from by decide]
        norm_num
      have h1 : 20160 ≤ M := by rw [c, c2] at hM; omega
      have h2 := hA2 h1
      have h3 : twoPart (Nat.card S) = 64 := by rw [c, c2]; exact twoPart_20160
      omega
    · have hR16 : 16 ≤ 2 ^ k := by
        calc (16 : ℕ) = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk4
      have := orderA_two_gt hR16 hR3
      rw [c] at hM
      omega
  · have c := card_isU3n hkc
    have hR32 : 32 ≤ 2 ^ k := by
      calc (32 : ℕ) = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk5
    have := orderTwistedA_two_gt hR32
    rw [c] at hM
    omega

theorem card_sp21_exact {t : LargeEvenLieTag} (ht : t = .B ∨ t = .C) (D : Type) [Group D] [Finite D]
    (h : CFSG.Assembly.LargeEvenRawDatum ⟨t, 2, 1⟩ (fun R' _ _ _ => Nonempty (D ≃* R'))) :
    Nat.card D = 720 := by
  obtain ⟨K, _, _, hK, ⟨e'⟩⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ 1 ∧
      Nonempty (D ≃* LargeEvenProj (LargeEvenSpGroup K 2)) := by
    rcases ht with rfl | rfl <;> exact h
  have hK2 : Nat.card K = 2 := by simpa using hK
  obtain ⟨eP⟩ := nonempty_largeEvenProj_equiv_of_card_two hK2 (LargeEvenSpGroup K 2)
  obtain ⟨eS⟩ := nonempty_largeEvenSpGroup_equiv_sympFour hK2
  let eD : D ≃* ↥sympFour := (e'.trans eP).trans eS
  rw [Nat.card_congr eD.toEquiv,
    Nat.card_congr (MulEquiv.ofBijective omegaPerm ⟨omegaPerm_injective, omegaPerm_surjective⟩).toEquiv,
    Nat.card_perm]
  simp [Nat.factorial]

theorem card_g2_exact (D : Type) [Group D] [Finite D]
    (h : CFSG.Assembly.LargeEvenRawDatum ⟨.G2, 0, 1⟩ (fun R' _ _ _ => Nonempty (D ≃* R'))) :
    Nat.card D = 12096 := by
  dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeChevalley] at h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hK
  obtain ⟨e1⟩ := centerQuot_chevGroup_equiv K .G2
  have hZ : Subgroup.center ↥(adjointGroup .G2 K) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  let eQ : AdjointQuotient .G2 K ≃* ↥(adjointGroup .G2 K) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  rw [Nat.card_congr ((e.trans e1).trans eQ).toEquiv,
    CFSG.ComponentClassification.ExcSelector.card_adjointGroup_G2_two hK2]

theorem card_twF4_exact (D : Type) [Group D] [Finite D]
    (h : CFSG.Assembly.LargeEvenRawDatum ⟨.twF4, 0, 1⟩ (fun R' _ _ _ => Nonempty (D ≃* R'))) :
    Nat.card D = 17971200 := by
  dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeTwF4Inherited] at h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have ha : (1 - 1) / 2 = 0 := rfl
  rw [ha] at hK e
  have hR : ReeTitsModel (LargeEvenCenterQuot (LargeEvenTwF4H 0 K)) .Tits 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩, 0, rfl, reeTitsRelationModel_largeEven 0 hK⟩
  obtain ⟨eT⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv _ 2 1 hR
  rw [Nat.card_congr (e.trans eT).toEquiv, CFSG.Sporadic.Schreier.Tits.card_titsD]

theorem markChar_two_of_lambda {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h3 : 3 ∣ lab.n) :
    markChar ⟨lab.tag, lab.rank, lab.n / 3⟩ = 2 := by
  obtain ⟨tag, rank, n⟩ := lab
  cases tag with
  | B2der =>
    exfalso
    simp only [LargeEvenInLambda2] at hlab
    obtain ⟨-, -, h1⟩ := hlab
    subst h1
    norm_num at h3
  | G2der =>
    exfalso
    simp only [LargeEvenInLambda2] at hlab
    obtain ⟨-, -, h1⟩ := hlab
    subst h1
    norm_num at h3
  | _ => rfl

theorem small_datum_cases (lab : LargeEvenLabel) (D : Type) [Group D] [Finite D]
    (hlab : LargeEvenInLambda2 lab) (h3 : 3 ∣ lab.n)
    (hnot : ¬ LargeEvenInLambda2 ⟨lab.tag, lab.rank, lab.n / 3⟩)
    (h : CFSG.Assembly.LargeEvenRawDatum ⟨lab.tag, lab.rank, lab.n / 3⟩ (fun R _ _ _ => Nonempty (D ≃* R))) :
    Group.IsSolvable D ∨
      (lab.n / 3 = 1 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 2 ∧ Nat.card D = 720) ∨
      (lab.n / 3 = 1 ∧ lab.tag = .G2 ∧ Nat.card D = 12096) ∨
      (lab.n / 3 = 1 ∧ lab.tag = .twF4 ∧ Nat.card D = 17971200) := by
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  dsimp only at hn hl h3 hnot h
  obtain ⟨m, rfl⟩ := h3
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      simp at hn
    · exact h0
  have hdiv : 3 * m / 3 = m := Nat.mul_div_cancel_left m (by norm_num)
  rw [hdiv] at hnot h ⊢
  cases tag <;> simp only [LargeEvenInLambda2] at hnot
  case A =>
    have h1 : rank = 1 ∧ m = 1 := by
      by_contra hcon
      apply hnot
      refine ⟨hm, hl.1, fun hr => ?_⟩
      by_cases hm1 : m = 1
      · exact absurd ⟨hr, hm1⟩ hcon
      · omega
    obtain ⟨rfl, rfl⟩ := h1
    exact Or.inl (FR.Res.solvable_A11 D h)
  case twA =>
    have h1 : rank = 2 ∧ m = 1 := by
      by_contra hcon
      apply hnot
      refine ⟨hm, hl.1, fun hr => ?_⟩
      by_cases hm1 : m = 1
      · exact absurd ⟨hr, hm1⟩ hcon
      · omega
    obtain ⟨rfl, rfl⟩ := h1
    exact Or.inl (FR.Res.solvable_twA21 D h)
  case B =>
    have h1 : rank = 2 ∧ m = 1 := by
      by_contra hcon
      apply hnot
      refine ⟨hm, hl.1, fun hr => ?_⟩
      by_cases hm1 : m = 1
      · exact absurd ⟨hr, hm1⟩ hcon
      · omega
    obtain ⟨rfl, rfl⟩ := h1
    exact Or.inr (Or.inl ⟨rfl, Or.inl rfl, rfl, card_sp21_exact (Or.inl rfl) D h⟩)
  case C =>
    have h1 : rank = 2 ∧ m = 1 := by
      by_contra hcon
      apply hnot
      refine ⟨hm, hl.1, fun hr => ?_⟩
      by_cases hm1 : m = 1
      · exact absurd ⟨hr, hm1⟩ hcon
      · omega
    obtain ⟨rfl, rfl⟩ := h1
    exact Or.inr (Or.inl ⟨rfl, Or.inr rfl, rfl, card_sp21_exact (Or.inr rfl) D h⟩)
  case D => exact absurd ⟨hm, hl⟩ hnot
  case twD => exact absurd ⟨hm, hl⟩ hnot
  case E6 => exact absurd ⟨hm, hl⟩ hnot
  case E7 => exact absurd ⟨hm, hl⟩ hnot
  case E8 => exact absurd ⟨hm, hl⟩ hnot
  case F4 => exact absurd ⟨hm, hl⟩ hnot
  case twE6 => exact absurd ⟨hm, hl⟩ hnot
  case triD4 => exact absurd ⟨hm, hl⟩ hnot
  case G2 =>
    have h1 : m = 1 := by
      by_contra hcon
      apply hnot
      exact ⟨hm, hl.1, by omega⟩
    obtain rfl := h1
    obtain rfl := hl.1
    exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, card_g2_exact D h⟩))
  case twB2 =>
    obtain ⟨hr, hodd, h3'⟩ := hl
    have hmodd : Odd m := (Nat.odd_mul.1 hodd).2
    have h1 : m = 1 := by
      by_contra hcon
      apply hnot
      refine ⟨hm, hr, hmodd, ?_⟩
      obtain ⟨k, hk⟩ := hmodd
      omega
    obtain rfl := h1
    obtain rfl := hr
    exact Or.inl (FR.Res.solvable_twB2 D h)
  case twF4 =>
    obtain ⟨hr, hodd, h3'⟩ := hl
    have hmodd : Odd m := (Nat.odd_mul.1 hodd).2
    have h1 : m = 1 := by
      by_contra hcon
      apply hnot
      refine ⟨hm, hr, hmodd, ?_⟩
      obtain ⟨k, hk⟩ := hmodd
      omega
    obtain rfl := h1
    obtain rfl := hr
    exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, card_twF4_exact D h⟩))
  case B2der => exfalso; have := hl.2; omega
  case G2der => exfalso; have := hl.2; omega
  case twF4der => exfalso; have := hl.2; omega

@[expose] def ExcChev2Class : Prop :=
  ∀ (S : Type) [Group S] [Finite S], catalogIs S excIndex → IsChevSimple 2 S →
    catalogIs S isA6 ∨ (∃ k, 2 ≤ k ∧ Even k ∧ catalogIs S (isA2n k)) ∨
      (∃ k, 5 ≤ k ∧ Odd k ∧ catalogIs S (isU3n k))

@[expose] def A6NoChar2Lambda : Prop :=
  ∀ (lab : LargeEvenLabel) (D : Type) [Group D] [Finite D], LargeEvenInLambda2 lab → markChar lab = 2 →
    MarkedModel lab D → ¬ catalogIs D isA6

@[expose] def TD4C1NotExc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X L : Subgroup G) (b : G), GLAPComponent 3 X L →
    IsChevSimple 2 (PSimple 3 L) → IsTD4 3 L → b ^ 3 = 1 → NonInner 3 b L →
    centCard2 3 L b = Nat.sqrt (card2 3 L) → ∀ I : Subgroup G, GLAPComponent 3 (L ⊓ cx b) I → I ≠ ⊥ →
      ¬ catalogIs (PSimple 3 I) excIndex

theorem lieModel_of_catalogIs_isA2n {R : Type} [Group R] {k : ℕ} (hcat : catalogIs R (isA2n k)) :
    CFSG.Blueprint.LieModel R .PSL 3 2 k := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := CatB.exists_lieIndex hcat
  cases d with
  | A r q =>
    rcases r with _ | _ | _ | r
    all_goals first | exact hP.elim | skip
    have hm := CFSG.Models.lieModel_A 2 q hv e
    have hm' := hm.toBlueprint (by decide)
    rw [hP.1, hP.2] at hm'
    exact hm'
  | _ => exact hP.elim

theorem lieModel_of_catalogIs_isU3n {R : Type} [Group R] {k : ℕ} (hcat : catalogIs R (isU3n k)) :
    CFSG.Blueprint.LieModel R .PSU 3 2 k := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := CatB.exists_lieIndex hcat
  cases d with
  | twistedA r q =>
    rcases r with _ | _ | _ | r
    all_goals first | exact hP.elim | skip
    have hm := lieModel_twistedA' 2 q hv e
    have hm' := CFSG.Models.LieModel.toBlueprint (by decide) hm
    rw [hP.1, hP.2] at hm'
    exact hm'
  | _ => exact hP.elim

end I91T

end CFSG.LocalAnalysis.GLTheoremA
