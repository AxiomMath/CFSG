module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Adapters.RankTwoModelTransports
open CFSG.ComponentClassification.PresentationLocal
open CFSG CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LocalAnalysis.GLTheoremA.FR.Res

theorem s265f_perfect_of_simple_sub {S : Type} [Group S] {D : Subgroup S} (hs : IsSimpleGroup ↥D)
    (hna : ∃ x y : ↥D, x * y ≠ y * x) : ⁅D, D⁆ = D := by
  obtain ⟨x, y, hxy⟩ := hna
  have hN : (⁅(⊤ : Subgroup ↥D), ⊤⁆ : Subgroup ↥D) = ⊥ ∨ ⁅(⊤ : Subgroup ↥D), ⊤⁆ = ⊤ :=
    IsSimpleGroup.eq_bot_or_eq_top_of_normal _
  rcases hN with h | h
  · exfalso
    apply hxy
    have hc : ∀ a b : ↥D, a * b = b * a := by
      intro a b
      have hab : a ∈ (⊤ : Subgroup ↥D) := trivial
      have hbb : b ∈ (⊤ : Subgroup ↥D) := trivial
      have hcomm : (⁅(⊤ : Subgroup ↥D), ⊤⁆ : Subgroup ↥D) = ⊥ := h
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm
      exact (Subgroup.mem_centralizer_iff.1 (hcomm hab) b trivial).symm
    exact hc x y
  · have h1 : Subgroup.map D.subtype ⁅(⊤ : Subgroup ↥D), ⊤⁆ = ⁅D, D⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    have h2 : Subgroup.map D.subtype (⊤ : Subgroup ↥D) = D := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    rw [← h1, h, h2]

private theorem s265f_false_of_solvable {D : Type} [Group D] (hsol : Group.IsSolvable D) (E : Subgroup D)
    (hEs : IsSimpleGroup ↥E) (hEna : ∃ x y : ↥E, x * y ≠ y * x) : False := by
  haveI : Group.IsSolvable ↥(⊤ : Subgroup D) :=
    Group.isSolvable_of_isSolvable_injective (f := (⊤ : Subgroup D).subtype)
      (⊤ : Subgroup D).subtype_injective
  have hne : E ≠ ⊥ := by
    intro h
    obtain ⟨x, y, hxy⟩ := hEna
    apply hxy
    have hx : (x : D) ∈ (⊥ : Subgroup D) := by
      rw [← h]
      exact x.2
    have hx1 : (x : D) = 1 := Subgroup.mem_bot.1 hx
    exact Subtype.ext (by simp [hx1])
  exact FR.false_of_perfect_solvable (D := ⊤) le_top (s265f_perfect_of_simple_sub hEs hEna) hne
    inferInstance

private theorem s265f_core_card {D : Type} [Group D] (hC : FR.DatumCore D) (E : Subgroup D)
    (hEs : IsSimpleGroup ↥E) (hEna : ∃ x y : ↥E, x * y ≠ y * x)
    (hEperf : ∀ T : Subgroup D, ⁅T, T⁆ = T → T ≤ E) :
    Nat.card D = Nat.card E ∨ Nat.card D = 2 * Nat.card E := by
  obtain ⟨E₀, hs₀, hna₀, hperf₀, hidx, -⟩ := hC
  have h1 : E ≤ E₀ := hperf₀ E (s265f_perfect_of_simple_sub hEs hEna)
  have h2 : E₀ ≤ E := hEperf E₀ (s265f_perfect_of_simple_sub hs₀ hna₀)
  have : E = E₀ := le_antisymm h1 h2
  subst this
  exact hidx

private theorem s265f_card_sp21 {t : LargeEvenLieTag} (ht : t = .B ∨ t = .C) (D : Type) [Group D]
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
    Nat.card_congr (MulEquiv.ofBijective omegaPerm
      ⟨omegaPerm_injective, omegaPerm_surjective⟩).toEquiv, Nat.card_perm]
  simp [Nat.factorial]

section Orders


private theorem s265f_card_g2 (D : Type) [Group D]
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

end Orders

section TwF4


private theorem s265f_card_twF4 (D : Type) [Group D]
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

theorem s265f_small_card_mem {p : ℕ} (hp : p.Prime) (lab : LargeEvenLabel) (hlab : LargeEvenInLambda2 lab)
    (hpn : p ∣ lab.n) (hnot : ¬ LargeEvenInLambda2 ⟨lab.tag, lab.rank, lab.n / p⟩) {D : Type} [Group D]
    (hdat : CFSG.Assembly.LargeEvenRawDatum ⟨lab.tag, lab.rank, lab.n / p⟩
      (fun R' _ _ _ => Nonempty (D ≃* R')))
    (E : Subgroup D) (hEs : IsSimpleGroup ↥E) (hEna : ∃ x y : ↥E, x * y ≠ y * x)
    (hEperf : ∀ T : Subgroup D, ⁅T, T⁆ = T → T ≤ E) :
    (Nat.card E = 360 ∨ Nat.card E = 720 ∨ Nat.card E = 6048 ∨ Nat.card E = 12096 ∨
      Nat.card E = 8985600 ∨ Nat.card E = 17971200) ∧
      (Nat.card E = 17971200 → lab.tag = .twF4 ∧ lab.n = p) := by
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  dsimp only at hn hl hpn hnot hdat ⊢
  obtain ⟨m, rfl⟩ := hpn
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      simp at hn
    · exact h0
  have hdiv : p * m / p = m := Nat.mul_div_cancel_left m hp.pos
  rw [hdiv] at hnot hdat
  have hp2 := hp.two_le
  have hpm : 2 ≤ p * m := by nlinarith
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
    exact (s265f_false_of_solvable (FR.Res.solvable_A11 D hdat) E hEs hEna).elim
  case twA =>
    have h1 : rank = 2 ∧ m = 1 := by
      by_contra hcon
      apply hnot
      refine ⟨hm, hl.1, fun hr => ?_⟩
      by_cases hm1 : m = 1
      · exact absurd ⟨hr, hm1⟩ hcon
      · omega
    obtain ⟨rfl, rfl⟩ := h1
    exact (s265f_false_of_solvable (FR.Res.solvable_twA21 D hdat) E hEs hEna).elim
  case B =>
    have h1 : rank = 2 ∧ m = 1 := by
      by_contra hcon
      apply hnot
      refine ⟨hm, hl.1, fun hr => ?_⟩
      by_cases hm1 : m = 1
      · exact absurd ⟨hr, hm1⟩ hcon
      · omega
    obtain ⟨rfl, rfl⟩ := h1
    have hc := s265f_core_card (FR.Res.datumCore_sp21 (Or.inl rfl) D hdat) E hEs hEna hEperf
    rw [s265f_card_sp21 (Or.inl rfl) D hdat] at hc
    exact ⟨by omega, fun h => absurd h (by omega)⟩
  case C =>
    have h1 : rank = 2 ∧ m = 1 := by
      by_contra hcon
      apply hnot
      refine ⟨hm, hl.1, fun hr => ?_⟩
      by_cases hm1 : m = 1
      · exact absurd ⟨hr, hm1⟩ hcon
      · omega
    obtain ⟨rfl, rfl⟩ := h1
    have hc := s265f_core_card (FR.Res.datumCore_sp21 (Or.inr rfl) D hdat) E hEs hEna hEperf
    rw [s265f_card_sp21 (Or.inr rfl) D hdat] at hc
    exact ⟨by omega, fun h => absurd h (by omega)⟩
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
    have hc := s265f_core_card (FR.Res.datumCore_g2 D hdat) E hEs hEna hEperf
    rw [s265f_card_g2 D hdat] at hc
    exact ⟨by omega, fun h => absurd h (by omega)⟩
  case twB2 =>
    obtain ⟨hr, hodd, h3⟩ := hl
    have hmodd : Odd m := (Nat.odd_mul.1 hodd).2
    have h1 : m = 1 := by
      by_contra hcon
      apply hnot
      refine ⟨hm, hr, hmodd, ?_⟩
      obtain ⟨k, hk⟩ := hmodd
      omega
    obtain rfl := h1
    obtain rfl := hr
    exact (s265f_false_of_solvable (FR.Res.solvable_twB2 D hdat) E hEs hEna).elim
  case twF4 =>
    obtain ⟨hr, hodd, h3⟩ := hl
    have hmodd : Odd m := (Nat.odd_mul.1 hodd).2
    have h1 : m = 1 := by
      by_contra hcon
      apply hnot
      refine ⟨hm, hr, hmodd, ?_⟩
      obtain ⟨k, hk⟩ := hmodd
      omega
    obtain rfl := h1
    obtain rfl := hr
    have hc := s265f_core_card (FR.Res.datumCore_twF4 D hdat) E hEs hEna hEperf
    rw [s265f_card_twF4 D hdat] at hc
    exact ⟨by omega, fun _ => ⟨rfl, Nat.mul_one p⟩⟩
  case B2der =>
    exfalso
    have h1 : p * m = 1 := hl.2
    have : p ∣ 1 := ⟨m, h1.symm⟩
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  case G2der =>
    exfalso
    have h1 : p * m = 1 := hl.2
    have : p ∣ 1 := ⟨m, h1.symm⟩
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  case twF4der =>
    exfalso
    have h1 : p * m = 1 := hl.2
    have : p ∣ 1 := ⟨m, h1.symm⟩
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)

end TwF4

end CFSG.LocalAnalysis.GLTheoremA.S265

end
