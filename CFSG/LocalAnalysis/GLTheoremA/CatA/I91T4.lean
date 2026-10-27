module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResTwF4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResAll

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace I91T

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.StandardType CFSG.Assembly TauCeti
open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.CatB
open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open CFSG.Adapters.RankTwoModelTransports
open CFSG CFSG.LieType.Chevalley CFSG.LieType.Ree

open scoped commutatorElement

theorem card_subgroup_GL_le {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K]
    (H : Subgroup (GL ι K)) : Nat.card H ≤ Nat.card K ^ (Fintype.card ι * Fintype.card ι) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have h1 : Nat.card H ≤ Nat.card (GL ι K) := Nat.card_le_card_of_injective _ Subtype.val_injective
  have h2 : Nat.card (GL ι K) ≤ Nat.card (Matrix ι ι K) :=
    Nat.card_le_card_of_injective (fun g : GL ι K => (g : Matrix ι ι K)) Units.val_injective
  have h3 : Nat.card (Matrix ι ι K) = Nat.card K ^ (Fintype.card ι * Fintype.card ι) := by
    show Nat.card (ι → ι → K) = _
    rw [Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := ι), ← pow_mul]
  exact h1.trans (h2.trans h3.le)

theorem card_quot_le_of_finite {G : Type} [Group G] [Finite G] (N : Subgroup G) :
    Nat.card (G ⧸ N) ≤ Nat.card G :=
  Nat.card_le_card_of_surjective (QuotientGroup.mk : G → G ⧸ N) QuotientGroup.mk_surjective

theorem card_A11 (D : Type) [Group D] [Finite D]
    (h : CFSG.Assembly.LargeEvenRawDatum ⟨.A, 1, 1⟩ (fun R' _ _ _ => Nonempty (D ≃* R'))) :
    Nat.card D ≤ 35942400 := by
  dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeLinear] at h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hK
  rw [Nat.card_congr e.toEquiv]
  refine (card_quot_le_of_finite _).trans ((card_subgroup_GL_le _).trans ?_)
  rw [hK2]
  norm_num

theorem card_twA21 (D : Type) [Group D] [Finite D]
    (h : CFSG.Assembly.LargeEvenRawDatum ⟨.twA, 2, 1⟩ (fun R' _ _ _ => Nonempty (D ≃* R'))) :
    Nat.card D ≤ 35942400 := by
  dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeUnitary] at h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := hK
  rw [Nat.card_congr e.toEquiv]
  refine (card_quot_le_of_finite _).trans ((card_subgroup_GL_le _).trans ?_)
  rw [hK']
  norm_num

theorem card_sp21 {t : LargeEvenLieTag} (ht : t = .B ∨ t = .C) (D : Type) [Group D] [Finite D]
    (h : CFSG.Assembly.LargeEvenRawDatum ⟨t, 2, 1⟩ (fun R' _ _ _ => Nonempty (D ≃* R'))) :
    Nat.card D ≤ 35942400 := by
  obtain ⟨K, _, _, hK, ⟨e'⟩⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ 1 ∧
      Nonempty (D ≃* LargeEvenProj (LargeEvenSpGroup K 2)) := by
    rcases ht with rfl | rfl <;> exact h
  have hK2 : Nat.card K = 2 := by simpa using hK
  rw [Nat.card_congr e'.toEquiv]
  refine (card_quot_le_of_finite _).trans ((card_subgroup_GL_le _).trans ?_)
  rw [hK2]
  norm_num

theorem card_twB2 (D : Type) [Group D] [Finite D]
    (h : CFSG.Assembly.LargeEvenRawDatum ⟨.twB2, 0, 1⟩ (fun R' _ _ _ => Nonempty (D ≃* R'))) :
    Nat.card D ≤ 35942400 := by
  dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeSuzuki] at h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have ha : (1 - 1) / 2 = 0 := rfl
  rw [ha] at hK e
  have hK' : Nat.card K = 2 ^ (2 * 0 + 1) := hK
  have hK2 : Nat.card K = 2 := by rw [hK']; norm_num
  rw [Nat.card_congr e.toEquiv]
  refine (card_quot_le_of_finite _).trans ((card_subgroup_GL_le _).trans ?_)
  rw [hK2]
  norm_num

theorem card_g2 (D : Type) [Group D] [Finite D]
    (h : CFSG.Assembly.LargeEvenRawDatum ⟨.G2, 0, 1⟩ (fun R' _ _ _ => Nonempty (D ≃* R'))) :
    Nat.card D ≤ 35942400 := by
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
  norm_num

theorem card_twF4 (D : Type) [Group D] [Finite D]
    (h : CFSG.Assembly.LargeEvenRawDatum ⟨.twF4, 0, 1⟩ (fun R' _ _ _ => Nonempty (D ≃* R'))) :
    Nat.card D ≤ 35942400 := by
  dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeTwF4Inherited] at h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have ha : (1 - 1) / 2 = 0 := rfl
  rw [ha] at hK e
  have hR : ReeTitsModel (LargeEvenCenterQuot (LargeEvenTwF4H 0 K)) .Tits 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩, 0, rfl, reeTitsRelationModel_largeEven 0 hK⟩
  obtain ⟨eT⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv _ 2 1 hR
  rw [Nat.card_congr (e.trans eT).toEquiv, CFSG.Sporadic.Schreier.Tits.card_titsD]
  norm_num

theorem smallDatumOrder_holds : SmallDatumOrder := by
  intro p lab D _ _ hp hlab hpn hnot h
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  dsimp only at hn hl hpn hnot h
  obtain ⟨m, rfl⟩ := hpn
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      simp at hn
    · exact h0
  have hdiv : p * m / p = m := Nat.mul_div_cancel_left m hp.pos
  rw [hdiv] at hnot h
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
    exact card_A11 D h
  case twA =>
    have h1 : rank = 2 ∧ m = 1 := by
      by_contra hcon
      apply hnot
      refine ⟨hm, hl.1, fun hr => ?_⟩
      by_cases hm1 : m = 1
      · exact absurd ⟨hr, hm1⟩ hcon
      · omega
    obtain ⟨rfl, rfl⟩ := h1
    exact card_twA21 D h
  case B =>
    have h1 : rank = 2 ∧ m = 1 := by
      by_contra hcon
      apply hnot
      refine ⟨hm, hl.1, fun hr => ?_⟩
      by_cases hm1 : m = 1
      · exact absurd ⟨hr, hm1⟩ hcon
      · omega
    obtain ⟨rfl, rfl⟩ := h1
    exact card_sp21 (Or.inl rfl) D h
  case C =>
    have h1 : rank = 2 ∧ m = 1 := by
      by_contra hcon
      apply hnot
      refine ⟨hm, hl.1, fun hr => ?_⟩
      by_cases hm1 : m = 1
      · exact absurd ⟨hr, hm1⟩ hcon
      · omega
    obtain ⟨rfl, rfl⟩ := h1
    exact card_sp21 (Or.inr rfl) D h
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
    exact card_g2 D h
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
    exact card_twB2 D h
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
    exact card_twF4 D h
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

theorem twF4CentOrder_holds : TwF4CentOrder := by
  intro G _ _ L b hF lab htag hn hM
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨hβp, hβi⟩ := FR.Res.fieldOn_outer hp hp2 hF
  set β := indAut 3 L b hF.1 with hβ
  have hβ1 : β ≠ 1 := fun h => hβi ⟨1, by rw [h]; ext x; simp⟩
  have hβord : orderOf β = 3 := orderOf_eq_prime hβp hβ1
  obtain ⟨t, r, n⟩ := lab
  dsimp only at htag hn
  subst htag
  subst hn
  have hL : LieModel (PSimple 3 L) .twistedF4 0 2 3 := hM
  obtain ⟨-, hadm, a, hfa, K, _, _, hK, ⟨e0⟩⟩ := hL.reeTitsModel (by simp [reeTitsTags])
  have ha : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · subst h0
      exact absurd hfa (by simpa using hp.ne_one)
    · exact h0
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  obtain ⟨-, b₀, hb, k, _, _, _, hk, ⟨eF⟩⟩ :=
    FR.Res.ree_fix_equiv ha hK' hp hp2 e0 β hβord hβi
  have hb0 : b₀ = 0 := by
    have h1 : (2 * b₀ + 1) * 3 = 1 * 3 := by rw [hb, hfa, one_mul]
    have := Nat.eq_of_mul_eq_mul_right hp.pos h1
    omega
  subst hb0
  have hk2 : Nat.card k = 2 := by simpa using hk
  have hk' : Nat.card k = 2 ^ (2 * 0 + 1) := by simpa using hk2
  have hΓcard : Nat.card ↥(ReeTag.F4.reeGamma k 0) = 35942400 := by
    have := (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
      0 k hk').1
    rw [this]
    norm_num
  rw [Nat.card_congr eF.toEquiv, hΓcard]

theorem i91U6At_holds (G : Type) [Group G] [Finite G] : I91U6At G :=
  i91U6At_of_residuals G smallDatumOrder_holds twF4CentOrder_holds u6CardLarge_holds

end I91T


end CFSG.LocalAnalysis.GLTheoremA
