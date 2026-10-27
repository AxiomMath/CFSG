module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1412Levels
public import CFSG.LocalAnalysis.GLTheoremA.PartI.RankTwoDownField
import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma49i
import CFSG.HardMathSupport.Solomon.Coordinator.L2FldAut3
import CFSG.HardMathSupport.Solomon.Coordinator.L2FldFixed
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

theorem kLevel_psl_two_le (F : Type) [Field F] [Finite F] (h3 : Nat.card F % 3 ≠ 0)
    (h4 : 4 ≤ Nat.card F) : kLevel 3 (StatedProj (StatedSL 2 F)) ≤ 2 :=
  rtd_kLevel_psl_two_le F h3 h4

theorem downLe_l2 (F : Type) [Field F] [Finite F] (h3 : Nat.card F % 3 ≠ 0)
    (h4 : 4 ≤ Nat.card F) : DownLe 3 2 (StatedProj (StatedSL 2 F)) := by
  obtain ⟨hsimple, hnc⟩ := rtd_isSimple_nonab_statedProj_two h4
  intro β hβ3 I hI
  by_cases hβ1 : β = 1
  · subst hβ1
    rw [rtd_fixSubgroup_one] at hI
    obtain ⟨g⟩ := rtd_nonempty_pSimple_equiv_top Nat.prime_three hnc hI
    rw [kLevel_congr 3 g]
    exact kLevel_psl_two_le F h3 h4
  · rcases CFSG.HardMathSupport.Solomon.Coordinator.l2Aut3Classification_holds F β hβ3 with
      h | hsolv | ⟨σ, φ, γ, hφ, hβ⟩
    · exact absurd h hβ1
    · exact (rtd_false_of_component_of_solvable hsolv (rtd_commutator_le_self _) hI).elim
    · obtain ⟨F₀, _, _, hcard, ⟨ψ⟩⟩ :=
        CFSG.HardMathSupport.Solomon.Coordinator.l2FieldFixed_holds F β hβ3 hβ1 σ φ γ hφ hβ
      have hF₀3 : Nat.card F₀ % 3 ≠ 0 := by
        intro h0
        apply h3
        rw [hcard, Nat.pow_mod, h0]
      by_cases hF₀ : 4 ≤ Nat.card F₀
      · obtain ⟨hs₀, hnc₀⟩ := rtd_isSimple_nonab_statedProj_two hF₀
        haveI : IsSimpleGroup ↥(fixSubgroup β) := ψ.isSimpleGroup
        have hnc' : ∃ a b : ↥(fixSubgroup β), a * b ≠ b * a := by
          obtain ⟨a, b, hab⟩ := hnc₀
          refine ⟨ψ.symm a, ψ.symm b, fun h => hab (ψ.symm.injective ?_)⟩
          rw [map_mul, map_mul]
          exact h
        obtain ⟨g⟩ := rtd_nonempty_pSimple_equiv_of_simple Nat.prime_three hnc' hI
        rw [kLevel_congr 3 (g.trans ψ)]
        exact kLevel_psl_two_le F₀ hF₀3 hF₀
      · have h2 : Nat.card F₀ = 2 := by
          have := Finite.one_lt_card (α := F₀)
          omega
        haveI := rtd_isSolvable_statedProj_two_of_card_two h2
        haveI : Group.IsSolvable ↥(fixSubgroup β) :=
          Group.isSolvable_of_isSolvable_injective (f := ψ.toMonoidHom) ψ.injective
        exact (rtd_false_of_component_of_solvable inferInstance (rtd_commutator_le_self _)
          hI).elim

theorem downLe_l3 (K : Type) [Field K] [Finite K] (hK : Nat.card K % 3 = 1) :
    DownLe 3 (if Nat.card K % 2 = 0 then 2 else 3) (StatedProj (StatedSL 3 K)) := by
  obtain ⟨p, f, hKp, hmod, h2⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_true_data K hK
  have hc : Nat.card K = p ^ f := by
    rw [hKp.card, CFSG.RankThree.PartTwo.Sec4.piCard, Bool.cond_true]
  have e : StatedProj (StatedSL 3 K) ≃*
      (↥(CFSG.RankThree.PartTwo.Sec4.slPi true 3 (p ^ f) K) ⧸
        Subgroup.center ↥(CFSG.RankThree.PartTwo.Sec4.slPi true 3 (p ^ f) K)) :=
    (MulEquiv.refl _).trans (QuotientGroup.quotientMulEquivOfEq
      (CFSG.HardMathSupport.Solomon.Coordinator.center_slPi_eq hKp hmod)).symm
  have h := rtd_downLe_projModel hKp hmod h2
  have hpar := rtd_prime_pow_mod_two hKp.prime hKp.one_le
  by_cases hp2 : p = 2
  · rw [hc, if_pos (hpar.2 hp2)]
    rw [if_pos hp2] at h
    exact downLe_of_mulEquiv e.symm h
  · rw [hc, if_neg (fun h' => hp2 (hpar.1 h'))]
    rw [if_neg hp2] at h
    exact downLe_of_mulEquiv e.symm h

theorem downLe_u3 (K : Type) [Field K] [Finite K] (q : ℕ) (hKq : Nat.card K = q ^ 2)
    (hq : q % 3 = 2) (hq2 : q ≠ 2) :
    DownLe 3 (if q % 2 = 0 then 2 else 3) (StatedProj (StatedSU 3 q K)) := by
  obtain ⟨p, f, rfl, ⟨hF⟩⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_unitaryFieldData hKq
  have hK : CFSG.RankThree.PartTwo.Sec4.PiField false p f K :=
    ⟨hF.prime, hF.one_le, by rw [CFSG.RankThree.PartTwo.Sec4.piCard, Bool.cond_false]; exact hKq⟩
  have hmod : CFSG.RankThree.PartTwo.Sec4.ModThree false (p ^ f) := by
    change p ^ f % 3 = 2
    omega
  have e : StatedProj (StatedSU 3 (p ^ f) K) ≃*
      (↥(CFSG.RankThree.PartTwo.Sec4.slPi false 3 (p ^ f) K) ⧸
        Subgroup.center ↥(CFSG.RankThree.PartTwo.Sec4.slPi false 3 (p ^ f) K)) :=
    (MulEquiv.refl _).trans (QuotientGroup.quotientMulEquivOfEq
      (CFSG.HardMathSupport.Solomon.Coordinator.center_slPi_eq hK hmod)).symm
  have h := rtd_downLe_projModel hK hmod (by omega)
  have hpar := rtd_prime_pow_mod_two hF.prime hF.one_le
  by_cases hp2 : p = 2
  · rw [if_pos (hpar.2 hp2)]
    rw [if_pos hp2] at h
    exact downLe_of_mulEquiv e.symm h
  · rw [if_neg (fun h' => hp2 (hpar.1 h'))]
    rw [if_neg hp2] at h
    exact downLe_of_mulEquiv e.symm h

theorem kdRankTwoDown_holds : KDRankTwoDown := by
  refine ⟨fun q hv h3 => ?_, fun q hv h1 => ?_, fun q hv h2 => ?_⟩
  ·
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
      rw [TauCeti.PrimePower.card_def]
      exact GaloisField.card q.p q.exponent q.exponent_pos.ne'
    have hq4 : 4 ≤ q.card :=
      ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
        ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).2 rfl
    have e := (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
        (GaloisField q.p q.exponent))
    exact downLe_of_mulEquiv e.symm
      (downLe_l2 (GaloisField q.p q.exponent) (by rw [hK]; omega) (by rw [hK]; exact hq4))
  ·
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
      rw [TauCeti.PrimePower.card_def]
      exact GaloisField.card q.p q.exponent q.exponent_pos.ne'
    have e := (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3
        (GaloisField q.p q.exponent))
    have h := downLe_l3 (GaloisField q.p q.exponent) (by rw [hK]; exact h1)
    have hpar := rtd_prime_pow_mod_two q.prime_p q.exponent_pos
    rw [hK, TauCeti.PrimePower.card_def] at h
    by_cases hp2 : q.p = 2
    · rw [if_pos (hpar.2 hp2)] at h
      rw [if_pos hp2]
      exact downLe_of_mulEquiv e.symm h
    · rw [if_neg (fun h' => hp2 (hpar.1 h'))] at h
      rw [if_neg hp2]
      exact downLe_of_mulEquiv e.symm h
  ·
    have hq3 : 3 ≤ q.card :=
      ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
        ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).2 rfl
    have hchar : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = q.p :=
      TauCeti.LieTypeIndex.characteristic_twistedA 2 q
    have hexp : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = q.exponent :=
      TauCeti.LieTypeIndex.fieldExponent_twistedA 2 q
    have e := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 q hv
    have hpe : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ ^
        TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = q.card := by
      rw [hchar, hexp]
      exact (TauCeti.PrimePower.card_def q).symm
    have hK : Nat.card (GaloisField (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩)
        (2 * TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩)) =
        (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ ^
          TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩) ^ 2 := by
      rw [GaloisField.card _ _ (by rw [hexp]; have := q.exponent_pos; omega), pow_mul']
    have h := downLe_u3 _ _ hK (by rw [hpe]; exact h2) (by rw [hpe]; omega)
    have hcond : (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ ^
        TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩) % 2 = 0 ↔ q.p = 2 := by
      rw [hchar, hexp]
      exact rtd_prime_pow_mod_two q.prime_p q.exponent_pos
    by_cases hp2 : q.p = 2
    · rw [if_pos (hcond.2 hp2)] at h
      rw [if_pos hp2]
      exact downLe_of_mulEquiv e.symm h
    · rw [if_neg (fun h' => hp2 (hcond.1 h'))] at h
      rw [if_neg hp2]
      exact downLe_of_mulEquiv e.symm h

end CFSG.LocalAnalysis.GLTheoremA
