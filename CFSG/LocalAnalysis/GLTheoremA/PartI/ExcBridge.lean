module

public import CFSG.LocalAnalysis.GLTheoremA.ExcClubList
public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs2
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_Defs
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_TablesA
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.Open.StatedCenterThree
import CFSG.Open.StatedSUFieldChange
import CFSG.Quasithin.Background.GoldschmidtListedSolv
import CFSG.ClassicalInvolution.PerfectCase.Basic
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index
public import CFSG.Adapters.LinearCatalog

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.ComponentBalance

@[expose] def IsExcShape (X : Type) [Group X] : Prop :=
  Nat.card (Subgroup.center X) = 3 ∧ catalogIs (X ⧸ Subgroup.center X) excIndex

theorem isExcShape_of_isHatSix {X : Type} [Group X] (h : IsHatSix X) : IsExcShape X :=
  ⟨h.2.1, .alternating 6 (by norm_num), Or.inl rfl, by exact h.2.2⟩

theorem isExcShape_of_isHatSeven {X : Type} [Group X] (h : IsHatSeven X) : IsExcShape X :=
  ⟨h.2.1, .alternating 7 (by norm_num), Or.inr rfl, by exact h.2.2⟩

theorem isExcShape_of_isHatMTwentyTwo {X : Type} [Group X] (h : IsHatMTwentyTwo X) :
    IsExcShape X :=
  ⟨h.2.1, .sporadic .M22, rfl, h.2.2⟩

theorem isL2TwoPowOdd_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsL2TwoPowOdd X) : IsL2TwoPowOdd Y := by
  obtain ⟨n, hn, hn1, ⟨f⟩⟩ := h
  exact ⟨n, hn, hn1, ⟨e.symm.trans f⟩⟩

theorem isL2TwoPowOdd_of_isLTwoOddPow {X : Type*} [Group X] (h : IsLTwoOddPow X) :
    IsL2TwoPowOdd X := by
  obtain ⟨F, hF, hfin, n, hn, hn1, hcard, ⟨e⟩⟩ := h
  have : Fintype F := Fintype.ofFinite F
  have : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hn0 : n ≠ 0 := by omega
  have hchar : CharP F 2 := by
    refine charP_of_card_eq_prime_pow (f := n) ?_
    rw [← Nat.card_eq_fintype_card, hcard]
  have hc : Fintype.card F = Fintype.card (GaloisField 2 n) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard, GaloisField.card 2 n hn0]
  refine ⟨n, Nat.odd_iff.2 hn, hn1, ⟨e.trans ?_⟩⟩
  exact ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm.trans
    (SL2Char2.mulEquivPSL F)).trans
    (CFSG.Adapters.RankTwoModelTransports.projectiveSpecialLinearGroupCongr (Fin 2)
      (FiniteField.ringEquivOfCardEq hc))

theorem exists_primePower_card_eq (F : Type) [Field F] [Finite F] :
    ∃ (q : TauCeti.PrimePower) (_ : Fact q.p.Prime), q.card = Nat.card F ∧
      Nonempty (F ≃+* GaloisField q.p q.exponent) := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨m, hp, hm⟩ := FiniteField.card F (ringChar F)
  have : Fact (ringChar F).Prime := ⟨hp⟩
  refine ⟨⟨ringChar F, m, hp, m.pos⟩, ⟨hp⟩, ?_, ⟨?_⟩⟩
  · rw [TauCeti.PrimePower.card_def, Nat.card_eq_fintype_card, hm]
  · have : Fintype (GaloisField (ringChar F) m) := Fintype.ofFinite _
    refine FiniteField.ringEquivOfCardEq (K := F) (K' := GaloisField (ringChar F) m) ?_
    rw [hm, ← Nat.card_eq_fintype_card, GaloisField.card _ _ m.ne_zero]

theorem isExcShape_of_isSLThreeExc {X : Type} [Group X] (h : IsSLThreeExc X) : IsExcShape X := by
  obtain ⟨F, hF, hfin, h9, ⟨e⟩⟩ := h
  have h3 : 3 ∣ Nat.card F - 1 := by omega
  obtain ⟨q, _, hqc, ⟨φ⟩⟩ := exists_primePower_card_eq F
  have hv : (TauCeti.LieTypeIndex.A 2 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp only [hqc]
    omega
  refine ⟨?_, .lie ⟨.A 2 q, hv⟩, ?_, ⟨?_⟩⟩
  · rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact CFSG.Open.StatedCenterThree.card_center_statedSL_three h3
  · show q.card % 9 = 4 ∨ q.card % 9 = 7
    rw [hqc]
    exact h9
  · let e₁ : X ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
      e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm
    exact ((QuotientGroup.congr _ _ e₁ (Subgroup.map_center_eq e₁)).trans
      (CFSG.Adapters.RankTwoModelTransports.projectiveSpecialLinearGroupCongr (Fin 3) φ)).trans
      (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv).symm

theorem exists_primePower_sq_card_eq (F : Type) [Field F] [Finite F] {q : ℕ}
    (hFq : Nat.card F = q ^ 2) (hq : 2 ≤ q) :
    ∃ (Q : TauCeti.PrimePower) (_ : Fact Q.p.Prime), Q.card = q ∧
      Nonempty (F ≃+* GaloisField Q.p (2 * Q.exponent)) := by
  obtain ⟨⟨p, e, hp, he⟩, hpf, hQ₀, ⟨φ⟩⟩ := exists_primePower_card_eq F
  rw [TauCeti.PrimePower.card_def, hFq] at hQ₀
  have hqd : q ∣ p ^ e := ⟨q, by rw [hQ₀, pow_two]⟩
  obtain ⟨k, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hqd
  have hk : k ≠ 0 := by
    rintro rfl
    simp at hq
  have hek : e = 2 * k := by
    refine Nat.pow_right_injective hp.two_le ?_
    show p ^ e = p ^ (2 * k)
    rw [hQ₀, ← pow_mul, mul_comm]
  subst hek
  exact ⟨⟨p, k, hp, Nat.pos_of_ne_zero hk⟩, ⟨hp⟩, TauCeti.PrimePower.card_def _, ⟨φ⟩⟩

theorem center_statedSU_three_eq {F : Type} [Field F] [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2)
    (h3 : 3 ∣ q + 1) :
    Subgroup.center (StatedSU 3 q F) = (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 q F) := by
  have hq2 := CFSG.Open.StatedCenterThree.two_le_of_card_eq_sq hF
  have hq : q ≠ 0 := by omega
  symm
  refine Subgroup.eq_of_le_of_card_ge (CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _) ?_
  rw [CFSG.Open.StatedCenterThree.card_center_statedSU_three hF h3]
  have h3F : 3 ∣ Nat.card F - 1 := by
    rw [hF, CFSG.Open.StatedCenterThree.sq_sub_one_eq (by omega)]
    exact Dvd.dvd.mul_left h3 _
  have hr : Nat.card (rootsOfUnity 3 F) = 3 :=
    CFSG.Open.StatedCenterThree.card_rootsOfUnity_three h3F
  let f : rootsOfUnity 3 F → ↥((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 q F)) := fun ζ =>
    ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin 3) (ζ : Fˣ),
      CFSG.Open.StatedCenterThree.scalar_mem hq h3 ((mem_rootsOfUnity 3 (ζ : Fˣ)).mp ζ.2)⟩,
      Subgroup.mem_subgroupOf.2 ⟨(ζ : Fˣ), rfl⟩⟩
  refine hr.symm.le.trans (Nat.card_le_card_of_injective f fun ζ₁ ζ₂ h => ?_)
  have h' : ((Matrix.GeneralLinearGroup.scalar (Fin 3) (ζ₁ : Fˣ) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 0 =
      ((Matrix.GeneralLinearGroup.scalar (Fin 3) (ζ₂ : Fˣ) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) 0 0 :=
    congrArg (fun z : ↥((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 q F)) =>
      ((((z : StatedSU 3 q F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0)) h
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_eq] at h'
  exact Subtype.ext (Units.ext h')

theorem isExcShape_of_isSUThreeExc {X : Type} [Group X] (hX : CFSG.Open.IsQuasisimple X)
    (h : IsSUThreeExc X) : IsExcShape X := by
  obtain ⟨F, hF, hfin, q, hFq, hq9, ⟨e⟩⟩ := h
  have hq2 := CFSG.Open.StatedCenterThree.two_le_of_card_eq_sq hFq
  have h3 : 3 ∣ q + 1 := by omega
  have hq3 : 3 ≤ q := by
    by_contra hlt
    obtain rfl : q = 2 := by omega
    have hs : Group.IsSolvable (StatedSU 3 (2 ^ 1) F) :=
      CFSG.Quasithin.isSolvable_statedSU_one (by simpa using hFq)
    exact CFSG.ClassicalInvolution.not_isSolvable_of_open_isQuasisimple hX
      (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)
  obtain ⟨Q, _, hQc, ⟨φ⟩⟩ := exists_primePower_sq_card_eq F hFq hq2
  have hv : (TauCeti.LieTypeIndex.twistedA 2 Q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff]
    refine ⟨⟨le_rfl, fun _ => ?_⟩, fun h => h⟩
    show 3 ≤ Q.card
    rw [hQc]
    exact hq3
  have hQ' : Q.p ^ Q.exponent = q := (TauCeti.PrimePower.card_def Q).symm.trans hQc
  subst hQ'
  have hFq' : Nat.card (GaloisField Q.p (2 * Q.exponent)) = (Q.p ^ Q.exponent) ^ 2 := by
    rw [GaloisField.card _ _ (by have := Q.exponent_pos; omega), ← pow_mul, mul_comm]
  have e₃ : X ≃* StatedSU 3 (Q.p ^ Q.exponent) (GaloisField Q.p (2 * Q.exponent)) :=
    e.trans (CFSG.Open.StatedSUFieldChange.statedSUEquiv φ 3 _)
  refine ⟨?_, .lie ⟨.twistedA 2 Q, hv⟩, ?_, ⟨?_⟩⟩
  · rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact CFSG.Open.StatedCenterThree.card_center_statedSU_three hFq h3
  · show Q.card % 9 = 2 ∨ Q.card % 9 = 5
    rw [TauCeti.PrimePower.card_def]
    exact hq9
  · exact ((QuotientGroup.congr _ _ e₃ (Subgroup.map_center_eq e₃)).trans
      (QuotientGroup.quotientMulEquivOfEq (center_statedSU_three_eq hFq' h3))).trans
      (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 Q hv).symm

theorem two_pow_mod_nine_of_odd {n : ℕ} (h2 : n % 2 = 1) (h3 : n % 3 ≠ 0) :
    2 ^ n % 9 = 2 ∨ 2 ^ n % 9 = 5 := by
  have h6 : 2 ^ n % 9 = 2 ^ (n % 6) % 9 := by
    conv_lhs => rw [← Nat.div_add_mod n 6, pow_add, pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hr : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
  rw [h6]
  interval_cases hn : n % 6 <;> simp <;> omega

theorem isSUThreeExc_of_isSUThreeTwoPow {X : Type*} [Group X] (h : IsSUThreeTwoPow X) :
    IsSUThreeExc X := by
  obtain ⟨F, hF, hfin, n, h1, -, h3, hcard, ⟨e⟩⟩ := h
  exact ⟨F, hF, hfin, 2 ^ n, hcard, two_pow_mod_nine_of_odd h1 h3, ⟨e⟩⟩

theorem isExcShape_of_types {X : Type} [Group X] (hX : CFSG.Open.IsQuasisimple X)
    (h : IsHatSix X ∨ IsHatSeven X ∨ IsHatMTwentyTwo X ∨ IsSLThreeExc X ∨ IsSUThreeExc X ∨
      IsSUThreeTwoPow X) : IsExcShape X := by
  rcases h with h | h | h | h | h | h
  · exact isExcShape_of_isHatSix h
  · exact isExcShape_of_isHatSeven h
  · exact isExcShape_of_isHatMTwentyTwo h
  · exact isExcShape_of_isSLThreeExc h
  · exact isExcShape_of_isSUThreeExc hX h
  · exact isExcShape_of_isSUThreeExc hX (isSUThreeExc_of_isSUThreeTwoPow h)

end CFSG.LocalAnalysis.GLTheoremA
