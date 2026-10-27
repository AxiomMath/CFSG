module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShNormDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.CtxHolds
public import CFSG.LocalAnalysis.GLTheoremA.PartI.ExcBridge
public import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinctShapes
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428ExcHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Comp
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofInner
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112NotLieOrd
public import CFSG.Timmesfeld.Orders.ClassicalLinearThree
public import CFSG.Timmesfeld.Orders.ClassicalUnitaryThree
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_TablesA

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.CatDistinct

theorem exists_charTwo_index_of_shape {i : TauCeti.CFSGIndex} (h : t158Shape 3 i) :
    ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧ d.1.characteristic = 2 := by
  rcases h with h | h | h | h
  · cases i with
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      cases d with
      | A n q =>
        exact ⟨⟨.A n q, hv⟩, rfl, by
          rw [TauCeti.LieTypeIndex.characteristic_A]
          simpa [t158ShapeA, onLie] using h.1⟩
      | _ => simp [t158ShapeA, onLie] at h
    | cyclic _ _ => simp [t158ShapeA, onLie] at h
    | alternating _ _ => simp [t158ShapeA, onLie] at h
    | sporadic _ => simp [t158ShapeA, onLie] at h
  · cases i with
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      cases d with
      | twistedA n q =>
        exact ⟨⟨.twistedA n q, hv⟩, rfl, by
          rw [TauCeti.LieTypeIndex.characteristic_twistedA]
          simpa [t158ShapeTwA, onLie] using h.1⟩
      | _ => simp [t158ShapeTwA, onLie] at h
    | cyclic _ _ => simp [t158ShapeTwA, onLie] at h
    | alternating _ _ => simp [t158ShapeTwA, onLie] at h
    | sporadic _ => simp [t158ShapeTwA, onLie] at h
  · cases i with
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      cases d with
      | E6 q =>
        exact ⟨⟨.E6 q, hv⟩, rfl, by
          rw [TauCeti.LieTypeIndex.characteristic_E6]
          simpa [t158ShapeE6, onLie] using h.2.1⟩
      | _ => simp [t158ShapeE6, onLie] at h
    | cyclic _ _ => simp [t158ShapeE6, onLie] at h
    | alternating _ _ => simp [t158ShapeE6, onLie] at h
    | sporadic _ => simp [t158ShapeE6, onLie] at h
  · cases i with
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      cases d with
      | twistedE6 q =>
        exact ⟨⟨.twistedE6 q, hv⟩, rfl, by
          rw [TauCeti.LieTypeIndex.characteristic_twistedE6]
          simpa [t158ShapeTwE6, onLie] using h.2.1⟩
      | _ => simp [t158ShapeTwE6, onLie] at h
    | cyclic _ _ => simp [t158ShapeTwE6, onLie] at h
    | alternating _ _ => simp [t158ShapeTwE6, onLie] at h
    | sporadic _ => simp [t158ShapeTwE6, onLie] at h

theorem exists_order_eq_of_shape (hc : CatDistinct.Ctx) {S : Type} [Group S] [Finite S]
    (h : catalogIs S (t158Shape 3)) :
    (∃ N m : ℕ, 3 ≤ N ∧ 1 ≤ m ∧ 3 ∣ N ∧
        Nat.card S = CFSG.Open.orderA (N - 1) (2 ^ m)) ∨
      (∃ N m : ℕ, 3 ≤ N ∧ 1 ≤ m ∧ 3 ∣ N ∧ (N - 1, m) ≠ (2, 1) ∧
        Nat.card S = CFSG.Open.orderTwistedA (N - 1) (2 ^ m)) ∨
      (∃ m : ℕ, 1 ≤ m ∧ Nat.card S = CFSG.Open.orderE6 (2 ^ m)) ∨
      (∃ m : ℕ, 1 ≤ m ∧ Nat.card S = CFSG.Open.orderTwistedE6 (2 ^ m)) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    have hcard : Nat.card S = lieOrderFormula d := hc.bridge ⟨d, hv⟩ S ⟨e⟩
    rcases hi with hi | hi | hi | hi
    · cases d with
      | A n q =>
        simp only [t158ShapeA, onLie] at hi
        obtain ⟨hq2, hdiv⟩ := hi
        have h3d : 3 ∣ n + 1 := hdiv.trans (Nat.gcd_dvd_left _ _)
        have h3 : 3 ≤ n + 1 := Nat.le_of_dvd (by omega) h3d
        refine Or.inl ⟨n + 1, q.exponent, h3, q.exponent_pos, h3d, ?_⟩
        rw [hcard]
        show CFSG.Open.orderA n q.card = CFSG.Open.orderA (n + 1 - 1) (2 ^ q.exponent)
        rw [Nat.add_sub_cancel, TauCeti.PrimePower.card_def, hq2]
      | _ => simp [t158ShapeA, onLie] at hi
    · cases d with
      | twistedA n q =>
        simp only [t158ShapeTwA, onLie] at hi
        obtain ⟨hq2, hdiv⟩ := hi
        have h3d : 3 ∣ n + 1 := hdiv.trans (Nat.gcd_dvd_left _ _)
        have h3 : 3 ≤ n + 1 := Nat.le_of_dvd (by omega) h3d
        have hne : (n, q.exponent) ≠ (2, 1) := by
          intro h
          have hn : n = 2 := congrArg Prod.fst h
          have hm1 : q.exponent = 1 := congrArg Prod.snd h
          rw [hn] at hv
          have hq3 : 3 ≤ q.card :=
            CFSG.RankThree.PartTwo.Sec19.SeitzScopeProof.three_le_card_of_valid_twistedA_two hv
          have hqcard : q.card = 2 := by
            rw [TauCeti.PrimePower.card_def, hm1, hq2, pow_one]
          omega
        refine Or.inr (Or.inl ⟨n + 1, q.exponent, h3, q.exponent_pos, h3d, ?_, ?_⟩)
        · simpa [Nat.add_sub_cancel] using hne
        rw [hcard]
        show CFSG.Open.orderTwistedA n q.card =
          CFSG.Open.orderTwistedA (n + 1 - 1) (2 ^ q.exponent)
        rw [Nat.add_sub_cancel, TauCeti.PrimePower.card_def, hq2]
      | _ => simp [t158ShapeTwA, onLie] at hi
    · cases d with
      | E6 q =>
        simp only [t158ShapeE6, onLie] at hi
        obtain ⟨-, hq2, -⟩ := hi
        refine Or.inr (Or.inr (Or.inl ⟨q.exponent, q.exponent_pos, ?_⟩))
        rw [hcard]
        show CFSG.Open.orderE6 q.card = CFSG.Open.orderE6 (2 ^ q.exponent)
        rw [TauCeti.PrimePower.card_def, hq2]
      | _ => simp [t158ShapeE6, onLie] at hi
    · cases d with
      | twistedE6 q =>
        simp only [t158ShapeTwE6, onLie] at hi
        obtain ⟨-, hq2, -⟩ := hi
        refine Or.inr (Or.inr (Or.inr ⟨q.exponent, q.exponent_pos, ?_⟩))
        rw [hcard]
        show CFSG.Open.orderTwistedE6 q.card = CFSG.Open.orderTwistedE6 (2 ^ q.exponent)
        rw [TauCeti.PrimePower.card_def, hq2]
      | _ => simp [t158ShapeTwE6, onLie] at hi
  | cyclic _ _ =>
    simp [t158Shape, t158ShapeA, t158ShapeTwA, t158ShapeE6, t158ShapeTwE6, onLie] at hi
  | alternating _ _ =>
    simp [t158Shape, t158ShapeA, t158ShapeTwA, t158ShapeE6, t158ShapeTwE6, onLie] at hi
  | sporadic _ =>
    simp [t158Shape, t158ShapeA, t158ShapeTwA, t158ShapeE6, t158ShapeTwE6, onLie] at hi

theorem isLThreeEvenExc_of_isSLThreeExc (hc : CatDistinct.Ctx) {Q : Type} [Group Q] [Finite Q]
    (h : CFSG.HardMathSupport.Solomon.LocalBalance.IsSLThreeExc Q)
    (hsh : catalogIs (Q ⧸ Subgroup.center Q) (t158Shape 3)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Even (Nat.card F) ∧
      (Nat.card F % 9 = 4 ∨ Nat.card F % 9 = 7) ∧ Nonempty (Q ≃* ↥(StatedSL 3 F)) := by
  obtain ⟨F, hF, hFin, h9, ⟨e⟩⟩ := h
  by_cases hEven : Even (Nat.card F)
  · exact ⟨F, hF, hFin, hEven, h9, ⟨e⟩⟩
  · exfalso
    have hFodd : Odd (Nat.card F) := Nat.not_even_iff_odd.mp hEven
    have h3F : 3 ∣ Nat.card F - 1 := by omega
    obtain ⟨q, -, hqc, -⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.exists_primePower_card_eq F
    have hv : (TauCeti.LieTypeIndex.A 2 q).Valid := by
      rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      simp only [hqc]
      omega
    let e₁ : Q ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
      e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm
    have eZ : Q ⧸ Subgroup.center Q ≃* StatedProj (StatedSL 3 F) :=
      (QuotientGroup.congr _ _ e₁ (Subgroup.map_center_eq e₁)).trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F)
    have hM0 : Nat.card (Q ⧸ Subgroup.center Q) * Nat.gcd 3 (Nat.card F - 1) =
        Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) := by
      rw [Nat.card_congr eZ.toEquiv]
      exact CFSG.Timmesfeld.ClassicalOrders.card_psl_three_mul_gcd
    have hp2 : q.p ≠ 2 := by
      intro hp
      rw [← hqc, TauCeti.PrimePower.card_def, hp] at hFodd
      exact (Nat.not_even_iff_odd.mpr hFodd)
        (Nat.even_pow.2 ⟨even_two, q.exponent_pos.ne'⟩)
    have hM' : Nat.card (Q ⧸ Subgroup.center Q) *
        CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSL 3 (q.p ^ q.exponent) =
        CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSL 3 (q.p ^ q.exponent) := by
      rw [show CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSL 3 (q.p ^ q.exponent)
          = Nat.gcd 3 (q.p ^ q.exponent - 1) from rfl,
        CFSG.LocalAnalysis.GLTheoremA.HDesc.num_L3, ← TauCeti.PrimePower.card_def, hqc]
      exact hM0
    have hadm : StatedLieAdmissible .PSL 3 q.p q.exponent := by
      refine ⟨q.prime_p, q.exponent_pos, by norm_num, ?_, ?_⟩ <;> simp
    obtain ⟨i, hi, ⟨e_shape⟩⟩ := hsh
    obtain ⟨d, rfl, hd⟩ := exists_charTwo_index_of_shape hi
    exact CatDistinct.xc hc (by simp) hadm hp2 hM' d hd e_shape

theorem isLThreeEvenExc_of_isSUThreeExc (hc : CatDistinct.Ctx) {Q : Type} [Group Q] [Finite Q]
    (h : CFSG.HardMathSupport.Solomon.LocalBalance.IsSUThreeExc Q)
    (hsh : catalogIs (Q ⧸ Subgroup.center Q) (t158Shape 3)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (q : ℕ), Even q ∧ Nat.card F = q ^ 2 ∧
      (q % 9 = 2 ∨ q % 9 = 5) ∧ Nonempty (Q ≃* ↥(StatedSU 3 q F)) := by
  obtain ⟨F, hF, hFin, q, hFq, hq9, ⟨e⟩⟩ := h
  by_cases hEven : Even q
  · exact ⟨F, hF, hFin, q, hEven, hFq, hq9, ⟨e⟩⟩
  · exfalso
    have hqodd : Odd q := Nat.not_even_iff_odd.mp hEven
    obtain ⟨Q', -, hQc, -⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.exists_primePower_sq_card_eq F hFq
        (CFSG.Open.StatedCenterThree.two_le_of_card_eq_sq hFq)
    have hQ' : Q'.p ^ Q'.exponent = q := (TauCeti.PrimePower.card_def Q').symm.trans hQc
    subst hQ'
    have hq3 : 3 ∣ Q'.p ^ Q'.exponent + 1 := by omega
    have eZ : Q ⧸ Subgroup.center Q ≃* StatedProj (StatedSU 3 (Q'.p ^ Q'.exponent) F) :=
      (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans
        (QuotientGroup.quotientMulEquivOfEq
          (CFSG.LocalAnalysis.GLTheoremA.center_statedSU_three_eq hFq hq3))
    have hM0 : Nat.card (Q ⧸ Subgroup.center Q) * Nat.gcd 3 (Q'.p ^ Q'.exponent + 1) =
        (Q'.p ^ Q'.exponent) ^ 3 *
          (((Q'.p ^ Q'.exponent) ^ 2 - 1) * ((Q'.p ^ Q'.exponent) ^ 3 + 1)) := by
      rw [Nat.card_congr eZ.toEquiv]
      exact CFSG.Timmesfeld.ClassicalOrders.card_psu_three_mul_gcd Q'.prime_p Q'.exponent_pos hFq
    have hp2 : Q'.p ≠ 2 := by
      intro hp
      rw [hp] at hqodd
      exact (Nat.not_even_iff_odd.mpr hqodd)
        (Nat.even_pow.2 ⟨even_two, Q'.exponent_pos.ne'⟩)
    have hM' : Nat.card (Q ⧸ Subgroup.center Q) *
        CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSU 3 (Q'.p ^ Q'.exponent) =
        CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSU 3 (Q'.p ^ Q'.exponent) := by
      rw [show CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSU 3 (Q'.p ^ Q'.exponent)
          = Nat.gcd 3 (Q'.p ^ Q'.exponent + 1) from rfl,
        CFSG.LocalAnalysis.GLTheoremA.HDesc.num_U3]
      exact hM0
    have hadm : StatedLieAdmissible .PSU 3 Q'.p Q'.exponent := by
      refine ⟨Q'.prime_p, Q'.exponent_pos, by norm_num, ?_⟩
      intro h2
      have hqeq : Q'.p ^ Q'.exponent = 2 := by
        have := congrArg (fun p : ℕ × ℕ => p.2) h2
        simpa using this
      rw [hqeq] at hqodd
      exact (Nat.not_even_iff_odd.mpr hqodd) ⟨1, rfl⟩
    obtain ⟨i, hi, ⟨e_shape⟩⟩ := hsh
    obtain ⟨d, rfl, hd⟩ := exists_charTwo_index_of_shape hi
    exact CatDistinct.xc hc (by simp) hadm hp2 hM' d hd e_shape

theorem t158NormCat_of (hc : CatDistinct.Ctx) : T158NormCat := by
  intro Q _ _ hQ htype hsh
  rcases htype with hL2 | h6 | h7 | h22 | hSL | hSU
  ·
    exfalso
    have hL2' : CFSG.HardMathSupport.Timmesfeld.ComponentBalance.IsL2TwoPowOdd Q :=
      isL2TwoPowOdd_of_isLTwoOddPow hL2
    obtain ⟨K, hK, hKfin, n, hn, hn1, hKcard, ⟨e⟩⟩ := hL2
    have hn0 : 1 ≤ n := by omega
    have hcent : Subgroup.center Q = ⊥ :=
      CFSG.HardMathSupport.Timmesfeld.ComponentBalance.IsL2TwoPowOdd.center_eq_bot hL2'
    have hcat : catalogIs Q (t158Shape 3) := by
      have eQ : Q ⧸ Subgroup.center Q ≃* Q :=
        (QuotientGroup.quotientMulEquivOfEq hcent).trans QuotientGroup.quotientBot
      exact (catalogIs_congr eQ).1 hsh
    have hcard : Nat.card Q = CFSG.Open.orderA 1 (2 ^ n) := by
      rw [Nat.card_congr e.toEquiv,
        ← Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).toEquiv,
        CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hKcard,
        CatDistinct.orderA_one_eq hn0]
    rcases exists_order_eq_of_shape hc hcat with ⟨N, m, hN, hm, hdiv, hS⟩ |
      ⟨N, m, hN, hm, hdiv, -, hS⟩ | ⟨m, hm, hS⟩ | ⟨m, hm, hS⟩
    · exact CFSG.RankThree.PartOne.S12K.ordA_ne_ordA_one (n := N - 1) (f := m) (g := n)
        (by omega) hm hn0 (hS.symm.trans hcard)
    · have hbridge : CFSG.Open.ordTwistedA (N - 1) (2 ^ m) =
          CFSG.Open.orderTwistedA (N - 1) (2 ^ m) :=
        CFSG.LocalAnalysis.GLTheoremA.T1428.ordTwistedA_eq_orderTwistedA _ _ Nat.one_le_two_pow
      exact CFSG.Timmesfeld.Orders.ordA_ne_ordTwistedA (n := 1) (f := n) (u := N - 1) (g := m)
        le_rfl hn0 (by omega) hm (by
          rw [hbridge]
          exact hcard.symm.trans hS)
    · exact CFSG.RankThree.PartOne.S12K.ordE6_ne_ordA_one (f := m) (g := n) hm hn0
        (hS.symm.trans hcard)
    · exact CFSG.RankThree.PartOne.S12K.ordTwistedE6_ne_ordA_one (f := m) (g := n) hm hn0
        (hS.symm.trans hcard)
  ·
    exfalso
    obtain ⟨-, -, ⟨e⟩⟩ := h6
    have hcard : Nat.card (Q ⧸ Subgroup.center Q) = 360 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      norm_num [Nat.factorial]
    rcases exists_order_eq_of_shape hc hsh with ⟨N, m, hN, hm, hdiv, hS⟩ |
      ⟨N, m, hN, hm, hdiv, hne, hS⟩ | ⟨m, hm, hS⟩ | ⟨m, hm, hS⟩
    · exact (CFSG.Quasithin.H13.EvenOrd.excl_360.psl (N - 1) m (by omega) hm
        (by intro h; have h1 := congrArg Prod.fst h; omega)) (hS.symm.trans hcard)
    · have hbridge : CFSG.Open.ordTwistedA (N - 1) (2 ^ m) =
          CFSG.Open.orderTwistedA (N - 1) (2 ^ m) :=
        CFSG.LocalAnalysis.GLTheoremA.T1428.ordTwistedA_eq_orderTwistedA _ _
          Nat.one_le_two_pow
      exact (CFSG.Quasithin.H13.EvenOrd.excl_360.psu (N - 1) m (by omega) hm hne) (by
        rw [hbridge]
        exact hS.symm.trans hcard)
    · exact (CFSG.Quasithin.H13.EvenOrd.excl_360.e6 m hm) (hS.symm.trans hcard)
    · exact (CFSG.Quasithin.H13.EvenOrd.excl_360.e6' m hm) (hS.symm.trans hcard)
  ·
    exfalso
    obtain ⟨-, -, ⟨e⟩⟩ := h7
    have hcard : Nat.card (Q ⧸ Subgroup.center Q) = 2520 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      norm_num [Nat.factorial]
    rcases exists_order_eq_of_shape hc hsh with ⟨N, m, hN, hm, hdiv, hS⟩ |
      ⟨N, m, hN, hm, hdiv, hne, hS⟩ | ⟨m, hm, hS⟩ | ⟨m, hm, hS⟩
    · exact (CFSG.Quasithin.H13.EvenOrd.excl_2520.psl (N - 1) m (by omega) hm
        (by intro h; have h1 := congrArg Prod.fst h; omega)) (hS.symm.trans hcard)
    · have hbridge : CFSG.Open.ordTwistedA (N - 1) (2 ^ m) =
          CFSG.Open.orderTwistedA (N - 1) (2 ^ m) :=
        CFSG.LocalAnalysis.GLTheoremA.T1428.ordTwistedA_eq_orderTwistedA _ _
          Nat.one_le_two_pow
      exact (CFSG.Quasithin.H13.EvenOrd.excl_2520.psu (N - 1) m (by omega) hm hne) (by
        rw [hbridge]
        exact hS.symm.trans hcard)
    · exact (CFSG.Quasithin.H13.EvenOrd.excl_2520.e6 m hm) (hS.symm.trans hcard)
    · exact (CFSG.Quasithin.H13.EvenOrd.excl_2520.e6' m hm) (hS.symm.trans hcard)
  ·
    exfalso
    obtain ⟨-, -, ⟨e⟩⟩ := h22
    have hcard : Nat.card (Q ⧸ Subgroup.center Q) = 443520 := by
      rw [Nat.card_congr e.toEquiv, hc.m22]
    rcases exists_order_eq_of_shape hc hsh with ⟨N, m, hN, hm, hdiv, hS⟩ |
      ⟨N, m, hN, hm, hdiv, hne, hS⟩ | ⟨m, hm, hS⟩ | ⟨m, hm, hS⟩
    · exact (CFSG.Quasithin.H13.EvenOrd.excl_443520.psl (N - 1) m (by omega) hm
        (by intro h; have h1 := congrArg Prod.fst h; omega)) (hS.symm.trans hcard)
    · have hbridge : CFSG.Open.ordTwistedA (N - 1) (2 ^ m) =
          CFSG.Open.orderTwistedA (N - 1) (2 ^ m) :=
        CFSG.LocalAnalysis.GLTheoremA.T1428.ordTwistedA_eq_orderTwistedA _ _
          Nat.one_le_two_pow
      exact (CFSG.Quasithin.H13.EvenOrd.excl_443520.psu (N - 1) m (by omega) hm hne) (by
        rw [hbridge]
        exact hS.symm.trans hcard)
    · exact (CFSG.Quasithin.H13.EvenOrd.excl_443520.e6 m hm) (hS.symm.trans hcard)
    · exact (CFSG.Quasithin.H13.EvenOrd.excl_443520.e6' m hm) (hS.symm.trans hcard)
  ·
    exact Or.inl (isLThreeEvenExc_of_isSLThreeExc hc hSL hsh)
  ·
    exact Or.inr (isLThreeEvenExc_of_isSUThreeExc hc hSU hsh)


theorem t158NormCat_holds : T158NormCat := t158NormCat_of CatDistinct.ctx_holds

end CFSG.LocalAnalysis.GLTheoremA.T158

end
