module

public import CFSG.LieType.ChevTwo.Layered
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSL
public import CFSG.RankThree.PartOne.KFCL.BlockSL
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandStructPSL
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSp
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpModel
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSU
public import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.CoverSU3
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeDiagParTw
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorOmega
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LieType.ChevTwo

open CFSG.Open Matrix

private theorem four_le_card_of_charP_two_of_ne_two (E : Type) [Field E] [Fintype E]
    [CharP E 2] (h : Fintype.card E ≠ 2) : 4 ≤ Fintype.card E := by
  obtain ⟨n, -, hn⟩ := FiniteField.card E 2
  have h2 : 2 ≤ Fintype.card E := Fintype.one_lt_card
  rw [hn] at h h2 ⊢
  have hn2 : 2 ≤ (n : ℕ) := by
    by_contra hlt
    have hle : (n : ℕ) ≤ 1 := by omega
    have hp2 : 2 ^ (n : ℕ) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hle
    simp only [pow_one] at hp2
    have hge3 : 3 ≤ 2 ^ (n : ℕ) := by omega
    omega
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) hn2

theorem isChevTwoLayered_specialLinear (n : Type) [Fintype n] [DecidableEq n]
    (E : Type) [Field E] [Fintype E] [CharP E 2] :
    IsChevTwoLayered (Matrix.SpecialLinearGroup n E) := by
  let m := Fintype.card n
  let e : n ≃ Fin m := Fintype.equivFin n
  let ere : Matrix.SpecialLinearGroup n E ≃* Matrix.SpecialLinearGroup (Fin m) E :=
    CFSG.RankThree.PartOne.KFCL.BlockSL.reindexSL e
  haveI : Finite (Matrix.SpecialLinearGroup n E) := inferInstance
  by_cases hm : m ≤ 1
  · haveI : Subsingleton (Matrix.SpecialLinearGroup (Fin m) E) := by
      have hm01 : m = 0 ∨ m = 1 := by omega
      rcases hm01 with hm0 | hm1
      · rw [hm0]; exact inferInstance
      · rw [hm1]; exact inferInstance
    haveI : Subsingleton (Matrix.SpecialLinearGroup n E) :=
      ⟨fun a b => ere.injective (Subsingleton.elim (ere a) (ere b))⟩
    exact isChevTwoLayered_of_isSolvable
      (Group.isSolvable_of_comm fun a b => Subsingleton.elim _ _)
  · push Not at hm
    have hm2 : 2 ≤ m := by omega
    by_cases h22 : m = 2 ∧ Fintype.card E = 2
    · obtain ⟨hm2', hcardE⟩ := h22
      have hcardn : Fintype.card n = 2 := by simpa [m] using hm2'
      let e2n : n ≃ Fin 2 := Fintype.equivFinOfCardEq hcardn
      let ere2 : Matrix.SpecialLinearGroup n E ≃* Matrix.SpecialLinearGroup (Fin 2) E :=
        CFSG.RankThree.PartOne.KFCL.BlockSL.reindexSL e2n
      obtain ⟨e2⟩ := CFSG.StandardType.RCSPSL.nonempty_sl2_equiv_perm
        (F := E) (by rwa [Nat.card_eq_fintype_card])
      haveI : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
      have hsolv2 : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) E) :=
        Group.isSolvable_of_isSolvable_injective (f := e2.toMonoidHom) e2.injective
      have hsolv : Group.IsSolvable (Matrix.SpecialLinearGroup n E) :=
        Group.isSolvable_of_isSolvable_injective (f := ere2.toMonoidHom) ere2.injective
      exact isChevTwoLayered_of_isSolvable hsolv
    · have hring : ringChar E = 2 := ringChar.eq E 2
      have hE4 : m = 2 → 4 ≤ Fintype.card E := by
        intro hm2'
        exact four_le_card_of_charP_two_of_ne_two E (fun hc => h22 ⟨hm2', hc⟩)
      have hFD : CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LieFactorData 2
          (Matrix.SpecialLinearGroup (Fin m) E) := by
        simpa [hring] using
          CFSG.HardMathSupport.Solomon.Coordinator.LieComp.slFactorFacts_holds E m hm2 hE4
      have h22' : m ≠ 2 ∨ Nat.card E ≠ 2 := by
        by_cases hm2' : m = 2
        · right
          intro hc
          exact h22 ⟨hm2', by rwa [Nat.card_eq_fintype_card] at hc⟩
        · left; exact hm2'
      have h23' : m ≠ 2 ∨ Nat.card E ≠ 3 := by
        by_cases hm2' : m = 2
        · right
          have h4 := hE4 hm2'
          have hc := Nat.card_eq_fintype_card (α := E)
          omega
        · left; exact hm2'
      have hQ : CFSG.Open.IsQuasisimple (Matrix.SpecialLinearGroup (Fin m) E) :=
        CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.mp
          (CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple
            m E hm2 h22' h23')
      have hL : IsChevTwoLayered (Matrix.SpecialLinearGroup (Fin m) E) :=
        isChevTwoLayered_of_isQuasisimple hQ hFD.chev
      exact hL.of_mulEquiv ere

theorem isChevTwoLayered_statedSp (m : ℕ) (E : Type) [Field E] [Fintype E] [CharP E 2] :
    IsChevTwoLayered ↥(CFSG.Open.StatedSp m E) := by
  haveI : Finite ↥(CFSG.Open.StatedSp m E) := inferInstance
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst m
    haveI : Subsingleton ↥(CFSG.Open.StatedSp 0 E) := inferInstance
    exact isChevTwoLayered_of_isSolvable
      (Group.isSolvable_of_comm fun a b => Subsingleton.elim _ _)
  · by_cases hm1 : m = 1
    · subst m
      exact (isChevTwoLayered_specialLinear (Fin 2) E).of_mulEquiv
        (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne E).symm
    · have hm2 : 2 ≤ m := by omega
      by_cases h22 : m = 2 ∧ Fintype.card E = 2
      · obtain ⟨hm2', hcardE⟩ := h22
        subst hm2'
        have hcardE' : Nat.card E = 2 := by rwa [Nat.card_eq_fintype_card]
        haveI : (commutator ↥(CFSG.Open.StatedSp 2 E)).Normal := inferInstance
        have hQN : CFSG.Open.IsQuasisimple ↥(commutator ↥(CFSG.Open.StatedSp 2 E)) :=
          CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.mp
            (CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.isChevComponent_comm_sp_four_two
              hcardE').1
        have hNFD : CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LieFactorData 2
            ↥(commutator ↥(CFSG.Open.StatedSp 2 E)) :=
          CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFourTwoFacts_holds E hcardE
        have hN : IsChevTwoLayered ↥(commutator ↥(CFSG.Open.StatedSp 2 E)) :=
          isChevTwoLayered_of_isQuasisimple hQN hNFD.chev
        haveI : IsMulCommutative
            (↥(CFSG.Open.StatedSp 2 E) ⧸ commutator ↥(CFSG.Open.StatedSp 2 E)) :=
          Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl
        have hq : Group.IsSolvable
            (↥(CFSG.Open.StatedSp 2 E) ⧸ commutator ↥(CFSG.Open.StatedSp 2 E)) :=
          Group.isSolvable_of_comm fun a b => mul_comm' a b
        exact IsChevTwoLayered.of_normal_of_solvable_quotient _ hN hq
      · have hne : (m, Fintype.card E) ≠ (2, 2) := fun h => h22 (by simpa using h)
        have hring : ringChar E = 2 := ringChar.eq E 2
        have hFD : CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LieFactorData 2
            ↥(CFSG.Open.StatedSp m E) := by
          simpa [hring] using
            CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFactorFacts_holds E m hm2 hne
        have hF : (Infinite E ∨ 4 ≤ Nat.card E) ∨ (Nat.card E = 3 ∧ 2 ≤ m) ∨
            (Nat.card E = 2 ∧ 3 ≤ m) := by
          by_cases h2 : Nat.card E = 2
          · right; right
            have hcardE : Fintype.card E = 2 := by rwa [Nat.card_eq_fintype_card] at h2
            have hmne : m ≠ 2 := fun hm' => hne (by rw [hm', hcardE])
            exact ⟨h2, by omega⟩
          · left; right
            have hc : Fintype.card E ≠ 2 := fun hc =>
              h2 (by rwa [Nat.card_eq_fintype_card])
            simpa [Nat.card_eq_fintype_card] using
              four_le_card_of_charP_two_of_ne_two E hc
        have hQ : CFSG.Open.IsQuasisimple ↥(CFSG.Open.StatedSp m E) :=
          CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.mp
            (CFSG.LieType.Universal.Symplectic.isQuasisimple m E (by omega) hF)
        exact isChevTwoLayered_of_isQuasisimple hQ hFD.chev

theorem isChevTwoLayered_statedSU (m q : ℕ) (K : Type) [Field K] [Fintype K] [CharP K 2]
    (hK : Fintype.card K = q ^ 2) : IsChevTwoLayered ↥(CFSG.Open.StatedSU m q K) := by
  haveI : Finite ↥(CFSG.Open.StatedSU m q K) := inferInstance
  have hq2 : 2 ≤ q := by
    by_contra h
    have hq1 : q ≤ 1 := by omega
    have hle : q ^ 2 ≤ 1 := by nlinarith
    have hcard := Fintype.one_lt_card (α := K)
    omega
  have hKq : Nat.card K = q ^ 2 := by rwa [Nat.card_eq_fintype_card]
  obtain ⟨hp, f, hf, hqf⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.prime_ringChar_and_eq_pow_of_card_sq
      K q hKq hq2
  have hring : ringChar K = 2 := ringChar.eq K 2
  have hqpow : q = 2 ^ f := by rw [hring] at hqf; exact hqf
  rw [hqpow] at hK hKq ⊢
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  ·
    have hm01 : m = 0 ∨ m = 1 := by omega
    rcases hm01 with hm0 | hm1
    · subst m
      haveI : Subsingleton ↥(CFSG.Open.StatedSU 0 (2 ^ f) K) := inferInstance
      exact isChevTwoLayered_of_isSolvable
        (Group.isSolvable_of_comm fun a b => Subsingleton.elim _ _)
    · subst m
      have hcomm : ∀ A B : ↥(CFSG.Open.StatedSU 1 (2 ^ f) K), A * B = B * A := by
        intro A B
        apply Subtype.ext
        apply Units.ext
        ext i j
        fin_cases i
        fin_cases j
        simp [Matrix.mul_apply, mul_comm]
      exact isChevTwoLayered_of_isSolvable (Group.isSolvable_of_comm hcomm)
  · by_cases hm2' : m = 2
    · subst m
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hK' : Nat.card K = (2 ^ f) ^ 2 := hKq
      obtain ⟨e⟩ :=
        CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two
          (K := K) (r := 2) (f := f) hK'
      haveI : Fintype ↥(CFSG.LieType.Steinberg.fixedSubfield K 2 f) := Fintype.ofFinite _
      exact (isChevTwoLayered_specialLinear (Fin 2)
        ↥(CFSG.LieType.Steinberg.fixedSubfield K 2 f)).of_mulEquiv e.symm
    · by_cases h32 : m = 3 ∧ q = 2
      · obtain ⟨hm3, hq3⟩ := h32
        have hf2 : 2 ^ f = 2 := by rw [← hqpow, hq3]
        subst hm3
        subst q
        rw [hf2]
        have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hKq, hf2]; norm_num
        have h216 :=
          CFSG.Quasithin.Background.Harris.OrdinaryProofs.card_statedSU_three_two_of_card_four
            hK'
        have h216' : Nat.card ↥(CFSG.Open.StatedSU 3 2 K) = 216 := by
          simpa using h216
        haveI : Fintype ↥(CFSG.Open.StatedSU 3 2 K) := Fintype.ofFinite _
        have hcard : Fintype.card ↥(CFSG.Open.StatedSU 3 2 K) = 2 ^ 3 * 3 ^ 3 := by
          rw [← Nat.card_eq_fintype_card, h216']
          norm_num
        have hsolv : Group.IsSolvable ↥(CFSG.Open.StatedSU 3 2 K) :=
          CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
            Nat.prime_two Nat.prime_three (by norm_num) hcard
        exact isChevTwoLayered_of_isSolvable hsolv
      · have hm3 : 3 ≤ m := by omega
        have hmq : (m, 2 ^ f) ≠ (3, 2) := by
          intro h
          exact h32 ⟨congrArg Prod.fst h, hqpow.trans (congrArg Prod.snd h)⟩
        have hFD : CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LieFactorData 2
            ↥(CFSG.Open.StatedSU m (2 ^ f) K) := by
          simpa [hring] using
            CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suFactorFacts_holds
              K m (2 ^ f) hK hm3 hmq
        have hF' : Nat.card K = (2 ^ f) ^ 2 := hKq
        have hQ : CFSG.Open.IsQuasisimple ↥(CFSG.Open.StatedSU m (2 ^ f) K) :=
          CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.mp
            (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
              (p := 2) (f := f) (F := K) (n := m) hF' hm3 hmq).1
        exact isChevTwoLayered_of_isQuasisimple hQ hFD.chev

theorem isChevTwoLayered_orthDerived_of_isQuasisimple {K V : Type} [Field K] [Fintype K]
    [CharP K 2] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hΩ : CFSG.IsQuasisimple ↥(CFSG.RankThree.Classical2.orthDerived Q)) :
    IsChevTwoLayered ↥(CFSG.RankThree.Classical2.orthDerived Q) := by
  have hring : ringChar K = 2 := ringChar.eq K 2
  have hΩopen : CFSG.Open.IsQuasisimple ↥(CFSG.RankThree.Classical2.orthDerived Q) :=
    CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.mp hΩ
  have hΩtop : CFSG.IsQuasisimple
      ↥(⊤ : Subgroup ↥(CFSG.RankThree.Classical2.orthDerived Q)) :=
    hΩ.of_mulEquiv Subgroup.topEquiv
  obtain ⟨X, _, _, hX, f, hf, hk⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.omegaFactorFacts_holds
      K V Q hQ ⊤ (inferInstance) hΩtop
  let f' : X →* ↥(CFSG.RankThree.Classical2.orthDerived Q) :=
    (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥(CFSG.RankThree.Classical2.orthDerived Q)) ≃*
      ↥(CFSG.RankThree.Classical2.orthDerived Q)).toMonoidHom.comp f
  have hf' : Function.Surjective f' := Subgroup.topEquiv.surjective.comp hf
  have hk' : f'.ker ≤ Subgroup.center X := by
    intro x hx
    exact hk (by simpa [f'] using hx)
  have hLC : CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LieCompData (ringChar K)
      ↥(CFSG.RankThree.Classical2.orthDerived Q) :=
    hX.lieCompData f' hf' hk'
  have hchev : CFSG.Yardstones.Md0ec50421ce4.IsChevSimple 2
      (↥(CFSG.RankThree.Classical2.orthDerived Q) ⧸
        Subgroup.center ↥(CFSG.RankThree.Classical2.orthDerived Q)) := by
    simpa [hring] using hLC.chev
  exact isChevTwoLayered_of_isQuasisimple hΩopen hchev

end CFSG.LieType.ChevTwo
