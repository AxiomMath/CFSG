module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10RSeitzCubeCore
public import CFSG.HardMathSupport.Solomon.Proving.AutSixBalance
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticSigTits
public import CFSG.RankThree.PartOne.KE.TitsPlaneLocalCores
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTSolvable
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux.Local

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.LieType.BorelTits CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

open CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix
  (inner_conjugation_injective)

theorem seitzSimpleStmt_alternatingGroup_six : SeitzSimpleStmt (alternatingGroup (Fin 6)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine seitzSimpleStmt_of_vacuous (alternatingGroup.isSimpleGroup (by simp)) ?_ ?_
  · rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card]
    norm_num
  · intro q hq hq2 E hE hbig U hU2 hUinv
    haveI : Fact q.Prime := ⟨hq⟩
    have hEdvd : Nat.card E ∣ 1440 := by
      have := Subgroup.card_subgroup_dvd_card E
      rwa [CFSG.HardMathSupport.Solomon.Proving.AutSixBalance.card_mulAut_alt6] at this
    obtain ⟨n, hn⟩ := hE.isPGroup.exists_card_eq
    have hn2 : 2 ≤ n := by
      by_contra h
      have hnle : n ≤ 1 := by omega
      have hle : q ^ n ≤ q := by
        simpa using Nat.pow_le_pow_right hq.pos hnle
      have : q ^ 2 ≤ q := le_trans hbig (hn ▸ hle)
      nlinarith [hq.one_lt]
    have hqdvd : q ^ n ∣ 1440 := by
      rw [← hn]
      exact hEdvd
    have hq3 : q = 3 := by
      have hq_dvd : q ∣ 1440 := dvd_trans (dvd_pow_self q (by omega)) hqdvd
      have h1440 : (1440 : ℕ) = 2 ^ 5 * 3 ^ 2 * 5 := by norm_num
      rw [h1440] at hq_dvd
      rcases (Nat.Prime.dvd_mul hq).1 hq_dvd with h | h5
      · rcases (Nat.Prime.dvd_mul hq).1 h with h2 | h3
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1
            (hq.dvd_of_dvd_pow h2)) hq2
        · exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 (hq.dvd_of_dvd_pow h3)
      · exfalso
        have hq5 : q = 5 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).1 h5
        have h25 : 5 ^ 2 ∣ q ^ n := by
          rw [hq5]
          exact pow_dvd_pow 5 hn2
        have : 25 ∣ 1440 := h25.trans hqdvd
        norm_num at this
    have hn_eq : n = 2 := by
      have h3n : 3 ^ n ∣ 1440 := by rwa [hq3] at hqdvd
      have hnle : n ≤ 2 := by
        by_contra h
        have h27 : 3 ^ 3 ∣ 3 ^ n := pow_dvd_pow 3 (by omega)
        have : 3 ^ 3 ∣ 1440 := h27.trans h3n
        norm_num at this
      omega
    have hEcard : Nat.card E = 9 := by
      rw [hn, hq3, hn_eq]
      norm_num
    have hE3 : IsElemAbelian 3 E := by rwa [hq3] at hE
    set T : Subgroup (MulAut (alternatingGroup (Fin 6))) :=
      U.map (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))) with hT
    have hT2 : IsPGroup 2 T := hU2.map _
    have hTcop : Nat.Coprime 3 (Nat.card T) := by
      obtain ⟨k, hk⟩ := hT2.exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_right k (by norm_num)
    have hUmap : ∀ φ ∈ E, U.map φ.toMonoidHom = U := by
      intro φ hφ
      refine le_antisymm ?_ ?_
      · rintro _ ⟨u, hu, rfl⟩
        exact hUinv φ hφ u hu
      · intro u hu
        exact ⟨φ.symm u, hUinv φ.symm (E.inv_mem hφ) u hu, by simp⟩
    have hET : E ≤ Subgroup.normalizer (T : Set (MulAut (alternatingGroup (Fin 6)))) := by
      intro φ hφ
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      ext t
      constructor
      · rintro ⟨s, hs, rfl⟩
        obtain ⟨u, hu, rfl⟩ := hs
        exact ⟨φ u, hUinv φ hφ u hu, by
          ext z
          simp [MulAut.conj_apply, map_mul]⟩
      · intro ht
        obtain ⟨u, hu, rfl⟩ := ht
        refine ⟨MulAut.conj (φ.symm u), ⟨φ.symm u, hUinv φ.symm (E.inv_mem hφ) u hu, rfl⟩, ?_⟩
        ext z
        simp [MulAut.conj_apply, map_mul]
    have hTbot : T = ⊥ :=
      CFSG.HardMathSupport.Solomon.Coordinator.i271AutBalanceAltSix_holds E hE3
        (by rw [hEcard]; norm_num) T hTcop hET
    exact (Subgroup.map_eq_bot_iff_of_injective U inner_conjugation_injective).mp hTbot


private theorem map_conj_le_normalizer_of_invariant {K : Type} [Group K]
    {E : Subgroup (MulAut K)} {U : Subgroup K}
    (hUinv : ∀ φ ∈ E, ∀ u ∈ U, φ u ∈ U) :
    E ≤ Subgroup.normalizer
      ((U.map (MulAut.conj : K →* MulAut K) : Subgroup (MulAut K)) : Set (MulAut K)) := by
  intro φ hφ
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨u, hu, rfl⟩ := hs
    exact ⟨φ u, hUinv φ hφ u hu, by
      ext z
      simp [MulAut.conj_apply, map_mul]⟩
  · intro ht
    obtain ⟨u, hu, rfl⟩ := ht
    refine ⟨MulAut.conj (φ.symm u), ⟨φ.symm u, hUinv φ.symm (E.inv_mem hφ) u hu, rfl⟩, ?_⟩
    ext z
    simp [MulAut.conj_apply, map_mul]

section TitsCerts


open CFSG.Sporadic.Schreier.Tits

theorem seitzSimpleStmt_titsD : SeitzSimpleStmt titsD := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine seitzSimpleStmt_of_vacuous titsD_simple ?_ ?_
  · rw [card_titsD]
    norm_num
  · intro q hq hq2 E hE hbig U hU2 hUinv
    haveI : Fact q.Prime := ⟨hq⟩
    have hEdvd : Nat.card E ∣ 35942400 := by
      have := Subgroup.card_subgroup_dvd_card E
      rwa [CFSG.RankThree.PartOne.KE.card_mulAut_titsD] at this
    obtain ⟨n, hn⟩ := hE.isPGroup.exists_card_eq
    have hn2 : 2 ≤ n := by
      by_contra h
      have hnle : n ≤ 1 := by omega
      have hle : q ^ n ≤ q := by
        simpa using Nat.pow_le_pow_right hq.pos hnle
      have : q ^ 2 ≤ q := le_trans hbig (hn ▸ hle)
      nlinarith [hq.one_lt]
    have hqdvd : q ^ n ∣ 35942400 := by
      rw [← hn]
      exact hEdvd
    have hq35 : q = 3 ∨ q = 5 := by
      have hq_dvd : q ∣ 35942400 := dvd_trans (dvd_pow_self q (by omega)) hqdvd
      have hN : (35942400 : ℕ) = 2 ^ 12 * 3 ^ 3 * 5 ^ 2 * 13 := by norm_num
      rw [hN] at hq_dvd
      rcases (Nat.Prime.dvd_mul hq).1 hq_dvd with h | h13
      · rcases (Nat.Prime.dvd_mul hq).1 h with h | h5
        · rcases (Nat.Prime.dvd_mul hq).1 h with h2 | h3
          · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1
              (hq.dvd_of_dvd_pow h2)) hq2
          · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1
              (hq.dvd_of_dvd_pow h3))
        · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).1
            (hq.dvd_of_dvd_pow h5))
      · exfalso
        have hq13 : q = 13 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 h13
        have h169 : 13 ^ 2 ∣ q ^ n := by
          rw [hq13]
          exact pow_dvd_pow 13 hn2
        have : 169 ∣ 35942400 := h169.trans hqdvd
        norm_num at this
    set T : Subgroup (MulAut titsD) := U.map (MulAut.conj : titsD →* MulAut titsD) with hT
    have hT2 : IsPGroup 2 T := hU2.map _
    have hET : E ≤ Subgroup.normalizer (T : Set (MulAut titsD)) := by
      rw [hT]
      exact map_conj_le_normalizer_of_invariant hUinv
    have hTnot3 : ¬ 3 ∣ Nat.card T := by
      obtain ⟨k, hk⟩ := hT2.exists_card_eq
      rw [hk]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
        (Nat.Coprime.pow_right k (by norm_num))
    have hTnot5 : ¬ 5 ∣ Nat.card T := by
      obtain ⟨k, hk⟩ := hT2.exists_card_eq
      rw [hk]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).1
        (Nat.Coprime.pow_right k (by norm_num))
    rcases hq35 with rfl | rfl
    ·
      have hn3 : n ≤ 3 := by
        have h3n : 3 ^ n ∣ 35942400 := hqdvd
        by_contra h
        have h81 : 3 ^ 4 ∣ 3 ^ n := pow_dvd_pow 3 (by omega)
        have : 3 ^ 4 ∣ 35942400 := h81.trans h3n
        norm_num at this
      have hEin : E ≤ (MulAut.conj : titsD →* MulAut titsD).range := by
        intro α hα
        exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.titsD_mem_inner_of_pow_eq_one
          Nat.prime_three (by norm_num) (hE.2 α hα)
      set P : Subgroup titsD := E.comap (MulAut.conj : titsD →* MulAut titsD) with hP
      have hPcard : Nat.card P = Nat.card E := by
        rw [hP, ← Subgroup.card_map_of_injective (K := P) CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux.conj_injective_titsD,
          Subgroup.map_comap_eq_self hEin]
      have hPe : IsElemAbelian 3 P := CFSG.Open.IsElemAbelian.comap hE CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux.conj_injective_titsD
      by_cases hn3eq : n = 3
      · have hP27 : Nat.card P = 27 := by
          rw [hPcard, hn, hn3eq]
          norm_num
        exact absurd hP27 (fun h => CFSG.RankThree.PartTwo.Sec4.Item434RemTits.false_of_e27
          hPe h)
      · have hn2eq : n = 2 := by omega
        have hP9 : Nat.card P = 9 := by
          rw [hPcard, hn, hn2eq]
          norm_num
        have hPT : P.map (MulAut.conj : titsD →* MulAut titsD) ≤
            Subgroup.normalizer (T : Set (MulAut titsD)) := by
          rw [Subgroup.map_comap_eq_self hEin]
          exact hET
        have hTbot : T = ⊥ :=
          CFSG.RankThree.PartTwo.Sec4.Item434RemTits.noSignalizer hPe hP9 T hTnot3 hPT
        exact (Subgroup.map_eq_bot_iff_of_injective U CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux.conj_injective_titsD).mp hTbot
    ·
      have hn5 : n ≤ 2 := by
        have h5n : 5 ^ n ∣ 35942400 := hqdvd
        by_contra h
        have h125 : 5 ^ 3 ∣ 5 ^ n := pow_dvd_pow 5 (by omega)
        have : 5 ^ 3 ∣ 35942400 := h125.trans h5n
        norm_num at this
      have hn2eq : n = 2 := by omega
      have hEcard25 : Nat.card E = 25 := by
        rw [hn, hn2eq]
        norm_num
      have hEin : E ≤ (MulAut.conj : titsD →* MulAut titsD).range := by
        intro α hα
        exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.titsD_mem_inner_of_pow_eq_one
          Nat.prime_five (by norm_num) (hE.2 α hα)
      set P : Subgroup titsD := E.comap (MulAut.conj : titsD →* MulAut titsD) with hP
      have hPcard : Nat.card P = 25 := by
        rw [hP, ← Subgroup.card_map_of_injective (K := P) CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux.conj_injective_titsD,
          Subgroup.map_comap_eq_self hEin, hEcard25]
      let hv : TauCeti.LieTypeIndex.tits.Valid := by simp
      let d : TauCeti.ValidLieTypeIndex := ⟨.tits, hv⟩
      have hmodelT : CFSG.Blueprint.ReeTitsModel (TauCeti.CFSGIndex.lie d).Group .Tits 2 1 :=
        CFSG.RankThree.PartOne.CTP.reeTitsModel_tits ⟨hv, ⟨MulEquiv.refl _⟩⟩
      obtain ⟨eT⟩ := titsModelEquiv (TauCeti.CFSGIndex.lie d).Group 2 1 hmodelT
      have hSig := CFSG.LocalAnalysis.RankFourTheoremC.signalizerAutAt_tits
        (p := 5) (d := d) rfl rfl
      have hcen : E ≤ Subgroup.centralizer (T : Set (MulAut titsD)) :=
        hSig titsD ⟨eT.symm⟩ E T hE hEcard25
          ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hTnot5) hET (Or.inl hEin)
      have hTbot : T = ⊥ := by
        rw [eq_bot_iff]
        intro y hy
        rw [Subgroup.mem_bot]
        have hfix : ∀ x ∈ P, y x = x := by
          intro x hx
          have hxE : MulAut.conj x ∈ E := by
            rw [hP, Subgroup.mem_comap] at hx
            exact hx
          have hcomm : y * MulAut.conj x = MulAut.conj x * y :=
            Subgroup.mem_centralizer_iff.1 (hcen hxE) y hy
          exact CFSG.HardMathSupport.Timmesfeld.CrossChar.mem_fixSub.1
            (CFSG.HardMathSupport.Timmesfeld.CrossChar.mem_fixSub_of_commute
              CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux.conj_injective_titsD hcomm)
        have hcop5 : Nat.Coprime 5 (orderOf y) := by
          obtain ⟨k, hk⟩ := hT2 ⟨y, hy⟩
          have hdiv : orderOf (⟨y, hy⟩ : T) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
          have hdiv' : orderOf y ∣ 2 ^ k := by simpa using hdiv
          exact Nat.Coprime.coprime_dvd_right hdiv' (Nat.Coprime.pow_right k (by norm_num))
        exact CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux.tits_five_faithful
          hPcard y hcop5 hfix
      exact (Subgroup.map_eq_bot_iff_of_injective U CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux.conj_injective_titsD).mp hTbot

theorem seitzSimpleStmt_of_titsModel {S : Type} [Group S] [Finite S]
    (h : ReeTitsModel S .Tits 2 1) : SeitzSimpleStmt S := by
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv S 2 1 h
  exact seitzSimpleStmt_of_mulEquiv e.symm seitzSimpleStmt_titsD

end TitsCerts

end CFSG.LocalAnalysis.GLTheoremA.Y10F

