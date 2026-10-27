module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma118
public import CFSG.GH74.GLS.C3.Layer1.St1C2L29

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74.GLS CFSG.Assembly.LowTwoRank

theorem inC2_of_hasL2Model_fm9
    {K : Type} [Group K] (hq : IsQuasisimple K)
    (h : HasL2Model K IsFM9) : InC2 K := by
  obtain ⟨p, f, hp, hf, hfm, hL⟩ := h
  obtain ⟨hfin, -, hs⟩ := CFSG.LieType.Catalog.lieModel_finite_simple K _ _ p f hL
  have hc : center K = ⊥ := center_eq_bot_of_simple_quasisimple hs hq
  have hp2 : pCore 2 K = ⊥ := pCore_eq_bot_of_simple hs hc
  refine ⟨hq, hc.trans hp2.symm, ?_, ?_⟩
  · have e : K ⧸ center K ≃* K :=
      (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
    exact E2.simpleInC2_of_mulEquiv e.symm
      (Generic.simpleInC2_of_fm9 hs hp hf hfm hL)
  · exact not_excludedFromC2_of_center_eq_bot hc


theorem even_card_of_simple_quasisimple {K : Type} [Group K] [Finite K] (hs : IsSimpleGroup K)
    (hq : IsQuasisimple K) : 2 ∣ Nat.card K := by
  by_contra h
  have hodd : Odd (Nat.card K) := Nat.odd_iff.2 (by omega)
  have hsolv : Group.IsSolvable K := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  obtain ⟨-, -, a', b', hab'⟩ := hq
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a'
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b'
  apply hab'
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, IsSimpleGroup.comm_iff_isSolvable.mpr hsolv a b]

theorem exists_involution_oddcore
    {Kb : Type} [Group Kb] [Finite Kb] (hU2 : InU2 Kb)
    (hnC2 : ¬ InC2 Kb)
    (hL34 : ¬ (IsL34Quotient Kb ∧ CFSG.IsElementaryAbelian 2 ↥(center Kb) ∧
      Nat.card ↥(center Kb) ≤ 4)) :
    center Kb = ⊥ ∧ ∃ ub : Kb, orderOf ub = 2 ∧ xu (MulAut.conj ub) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hq, hcls⟩ := hU2
  rcases hcls with hA | hB | hC
  ·
    obtain ⟨p, f, hp, hf, hodd, hL⟩ := hA
    by_cases hfm : IsFM9 (p ^ f)
    · exact absurd (inC2_of_hasL2Model_fm9 hq ⟨p, f, hp, hf, hfm, hL⟩) hnC2
    · have hs : IsSimpleGroup Kb :=
        (CFSG.LieType.Catalog.lieModel_finite_simple _ _ _ _ _ hL).2.2
      have hc : center Kb = ⊥ := center_eq_bot_of_simple_quasisimple hs hq
      obtain ⟨ub, hub⟩ := exists_prime_orderOf_dvd_card' (G := Kb) 2
        (even_card_of_simple_quasisimple hs hq)
      refine ⟨hc, ub, hub, ?_⟩
      rcases hL with ⟨-, hadm, F, hF, hFin, hcard, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · have hL2F : L2Field F := by
          refine ⟨by rw [hcard]; exact hodd, ?_⟩
          have h1 : 1 < p ^ f := Nat.one_lt_pow (by omega) hp.one_lt
          have h2 : (2, p ^ f) ≠ (2, 3) := hadm.2.2.2.2
          have h3 : p ^ f ≠ 3 := fun h => h2 (by rw [h])
          have h4 : (p ^ f) % 2 = 1 := Nat.odd_iff.1 hodd
          rw [hcard]
          omega
        have hnfm : ¬ IsFM9 (Nat.card F) := by rw [hcard]; exact hfm
        have hx : (MulAut.conj ub : MulAut Kb) ∈ innDiagSub e := innAut_le_innDiagSub e ⟨ub, rfl⟩
        have hx2 : orderOf (MulAut.conj ub : MulAut Kb) = 2 := by
          rw [orderOf_conj_eq e ub]; exact hub
        exact (ivk_1_18.1 F hL2F hnfm Kb e _ hx hx2).1
      all_goals exact absurd h0 (by norm_num)
  ·
    have hs : IsSimpleGroup Kb := by
      obtain ⟨e⟩ := hB
      have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
      exact e.isSimpleGroup
    have hc : center Kb = ⊥ := center_eq_bot_of_simple_quasisimple hs hq
    obtain ⟨ub, hub⟩ := exists_prime_orderOf_dvd_card' (G := Kb) 2
      (even_card_of_simple_quasisimple hs hq)
    exact ⟨hc, ub, hub, (ivk_1_18.2 Kb hB ub hub).1⟩
  · exact absurd hC hL34

end CFSG.GH74.GLS.IVK.Proofs2
