module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Vacuous
public import CFSG.Quasithin.Background.C31NonLie
public import CFSG.Quasithin.EmptyFaithful.S146xB2Aut
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderLinearBorel
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel
public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.Quasithin.Vol2.Ch4Sec4F4411B
public import CFSG.Quasithin.Vol2.Ch4Sec4F4411D
public import CFSG.StronglyEmbedded.BenderUnitaryBorel
public import CFSG.Walter.J1Props.Hyp
public import CFSG.Walter.Models
public import Certificates.Data.A5

public section

namespace CFSG.SectionRank.QTK.Insp443

open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.H13.Ch4.E443.F4411

private def alt5Elt : alternatingGroup (Fin 5) :=
  ⟨List.formPerm [0, 1] * List.formPerm [2, 3], by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide⟩

private theorem orderOf_alt5Elt : orderOf alt5Elt = 2 ^ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime_pow (n := 0)
  · decide
  · decide

private theorem factorization_two_card_alt5 :
    (Nat.card (alternatingGroup (Fin 5))).factorization 2 = 2 := by
  have h : Nat.card (alternatingGroup (Fin 5)) = 2 ^ 2 * 15 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  rw [h]
  exact CFSG.GH74.SmallRanks.factorization_two_pow_mul_odd (by decide)

private theorem twoRank_alternatingGroup_five_le_two :
    CFSG.Open.twoRank (alternatingGroup (Fin 5)) ≤ 2 :=
  CFSG.GH74.SmallRanks.twoRank_le_two_of_orderOf alt5Elt 1 orderOf_alt5Elt
    factorization_two_card_alt5

private def alt6Elt : alternatingGroup (Fin 6) :=
  ⟨List.formPerm [0, 1, 2, 3] * List.formPerm [4, 5], by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide⟩

private theorem orderOf_alt6Elt : orderOf alt6Elt = 2 ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime_pow (n := 1)
  · decide
  · decide

private theorem factorization_two_card_alt6 :
    (Nat.card (alternatingGroup (Fin 6))).factorization 2 = 3 := by
  have h : Nat.card (alternatingGroup (Fin 6)) = 2 ^ 3 * 45 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  rw [h]
  exact CFSG.GH74.SmallRanks.factorization_two_pow_mul_odd (by decide)

private theorem twoRank_alternatingGroup_six_le_two :
    CFSG.Open.twoRank (alternatingGroup (Fin 6)) ≤ 2 :=
  CFSG.GH74.SmallRanks.twoRank_le_two_of_orderOf alt6Elt 2 orderOf_alt6Elt
    factorization_two_card_alt6

theorem for_alt_le_seven :
    For (fun S _ => ∃ n : ℕ, 5 ≤ n ∧ n ≤ 7 ∧ Nonempty (S ≃* alternatingGroup (Fin n))) := by
  refine For.of_card_elemAbelian_le_four (fun S _ _ hP E hE => ?_)
  obtain ⟨n, hn5, hn7, ⟨e⟩⟩ := hP
  have h2 : CFSG.Open.twoRank S ≤ 2 := by
    rw [CFSG.GH74.twoRank_eq_of_mulEquiv e]
    interval_cases n
    · exact twoRank_alternatingGroup_five_le_two
    · exact twoRank_alternatingGroup_six_le_two
    · exact CFSG.GH74.SmallRanks.twoRank_alternatingGroup_seven_le_two
  exact CFSG.Quasithin.card_le_four_of_twoRank_le_two h2 hE

theorem for_odd_twoRank_two :
    For (fun S _ => ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      ((∃ f : ℕ, 1 ≤ f ∧ StatedClassicalModel S .PSL 2 p f) ∨
        (∃ f : ℕ, (f = 1 ∨ f = 2) ∧
          (StatedClassicalModel S .PSL 3 p f ∨ StatedClassicalModel S .PSU 3 p f)))) := by
  refine For.of_card_elemAbelian_le_four (fun S _ _ hP E hE => ?_)
  obtain ⟨p, hp, hp2, hPSL2 | ⟨f, -, hPSL3 | hPSU3⟩⟩ := hP
  · obtain ⟨f, -, h⟩ := hPSL2
    exact CFSG.Quasithin.card_le_four_of_twoRank_le_two
      (CFSG.GH74.SmallRanks.twoRank_le_two_of_statedClassicalModel_PSL_two_odd hp hp2 h) hE
  · have hLie : LieModel S .PSL 3 p f := Or.inl ⟨by decide, hPSL3⟩
    have h2 : CFSG.Open.twoRank S ≤ 2 := by
      simpa [CFSG.Open.twoRank] using
        CFSG.GH74.GLS.Stage2.Signalizer.Odd87.pRank_two_le_two_of_PSL3 hp hp2 hLie
    exact CFSG.Quasithin.card_le_four_of_twoRank_le_two h2 hE
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hPSU3
    have h2 : CFSG.Open.twoRank S ≤ 2 := by
      rw [CFSG.GH74.twoRank_eq_of_mulEquiv e]
      exact CFSG.Quasithin.C31NL.twoRank_psu3_le_two (p := p) (f := f) hp hp2 hK
    exact CFSG.Quasithin.card_le_four_of_twoRank_le_two h2 hE

theorem for_bender :
    For (fun S _ => ∃ f : ℕ, (2 ≤ f ∧ StatedClassicalModel S .PSL 2 2 f) ∨
      (2 ≤ f ∧ StatedClassicalModel S .PSU 3 2 f) ∨ (Odd f ∧ 3 ≤ f ∧ SuzukiModel S 2 f)) := by
  refine For.of_perfCentral (fun S _ _ hP => ?_)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, hPSL2 | hPSU3 | hSz⟩ := hP
  · obtain ⟨hf, h⟩ := hPSL2
    obtain ⟨e⟩ := CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField S 2 2 f h
    haveI : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
      Finite.of_equiv S e.toEquiv
    exact perfCentral_of_mulEquiv e
      (perfCentral_of_fusionBenderBorel (CFSG.Open.bender_psl2_borel_full f hf))
  · obtain ⟨hf, h⟩ := hPSU3
    obtain ⟨e⟩ := (CFSG.RankTwoShapes.open_statedClassicalModel_PSU_three_two_iff S f hf).mp h
    let e2 : S ≃* CFSG.Open.PSU3 2 f :=
      e.trans (MulEquiv.subgroupCongr (CFSG.Models.benderPSU3Model_eq_psu3 f))
    haveI : Finite (CFSG.Open.PSU3 2 f) := Finite.of_equiv S e2.toEquiv
    exact perfCentral_of_mulEquiv e2
      (perfCentral_of_fusionBenderBorel (CFSG.Open.bender_psu3_borel_full f hf))
  · obtain ⟨-, -, h⟩ := hSz
    obtain ⟨a, ha, ⟨e⟩⟩ :=
      CFSG.LieType.Simplicity.exists_mulEquiv_suzukiMatrixGroup_of_suzukiModel h
    have hSzEq : CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a = CFSG.Open.Sz a :=
      (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup a).symm.trans
        (CFSG.Models.benderSzModel_eq_sz a)
    let e2 : S ≃* CFSG.Open.Sz a := e.trans (MulEquiv.subgroupCongr hSzEq)
    haveI : Finite (CFSG.Open.Sz a) := Finite.of_equiv S e2.toEquiv
    exact perfCentral_of_mulEquiv e2
      (perfCentral_of_fusionBenderBorel (CFSG.Open.bender_suzuki_borel_full a ha))

theorem for_M11 :
    For (fun S _ => Nonempty (S ≃* NativeSporadic.Carrier .M11)) := by
  refine For.of_card_elemAbelian_le_four (fun S _ _ hP E hE => ?_)
  obtain ⟨e⟩ := hP
  haveI : Finite (NativeSporadic.Carrier .M11) := Finite.of_equiv S e.toEquiv
  have h2 : CFSG.Open.twoRank S ≤ 2 := by
    rw [CFSG.GH74.twoRank_eq_of_mulEquiv e]
    exact CFSG.GH74.SmallRanks.twoRank_M11_le_two
  exact CFSG.Quasithin.card_le_four_of_twoRank_le_two h2 hE

theorem for_J1 : For (fun S _ => Nonempty (S ≃* NativeSporadic.Carrier .J1)) := by
  refine For.of_perfCentral (fun S _ _ hP => ?_)
  obtain ⟨e⟩ := hP
  exact perfCentral_of_mulEquiv (e.trans CFSG.Walter.walterJ1EquivNative.symm)
    (perfCentral_of_jankoHyp CFSG.Walter.J1Props.jankoHyp)

end CFSG.SectionRank.QTK.Insp443
