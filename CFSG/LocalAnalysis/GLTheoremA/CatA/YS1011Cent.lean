module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Shared
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.SeitzReduction.CrossChar
public import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section DicksonI3013

private theorem psl_of_sl2_surj (r : ℕ) [hr : Fact r.Prime] (hr2 : r ≠ 2) {S : Type} [Group S]
    [IsSimpleGroup S] [Group.IsPerfect S]
    (ψ : Matrix.SpecialLinearGroup (Fin 2) (ZMod r) →* S) (hψ : Function.Surjective ψ) :
    ∃ r' : ℕ, r'.Prime ∧ 5 ≤ r' ∧ Nonempty (S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod r')) := by
  by_cases h3 : r = 3
  · subst h3
    exact (i7_false_of_three ψ hψ).elim
  · have h2 := hr.out.two_le
    have hne4 : r ≠ 4 := fun h => by
      have := hr.out
      rw [h] at this
      norm_num at this
    have h5 : 5 ≤ r := by omega
    exact ⟨r, hr.out, h5, i7_psl_iso_of_surjective r h5 ψ hψ⟩

private theorem psl_of_involvedSL2 {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] [Group.IsPerfect S]
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod q))) (φ : H →* S)
    (hφ : Function.Surjective φ) :
    ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ Nonempty (S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod r)) := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Finite (Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) := inferInstance
  obtain ⟨K, hKtop, hKperf, hK0⟩ := i7_exists_perfect_cover φ hφ
  haveI := hKperf
  have hεK := Subgroup.equivMapOfInjective K H.subtype H.subtype_injective
  haveI : Group.IsPerfect ↥(K.map H.subtype) :=
    Group.IsPerfect.ofSurjective (f := hεK.toMonoidHom) hεK.surjective
  have hJne : K.map H.subtype ≠ ⊥ := by
    intro h
    apply hK0
    apply Subgroup.map_injective H.subtype_injective
    rw [h, Subgroup.map_bot]
  have hφK : Function.Surjective (φ.comp K.subtype) := by
    intro s
    have hs : s ∈ K.map φ := by
      rw [hKtop]
      exact Subgroup.mem_top s
    obtain ⟨x, hx, hxs⟩ := Subgroup.mem_map.mp hs
    exact ⟨⟨x, hx⟩, hxs⟩
  rcases CFSG.RankThree.SubgroupLists.perfect_gl2_mulEquiv hq2 (K.map H.subtype) hJne with
    ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact psl_of_sl2_surj q hq2 ((φ.comp K.subtype).comp (e.symm.trans hεK.symm).toMonoidHom)
      (hφK.comp (e.symm.trans hεK.symm).surjective)
  · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact psl_of_sl2_surj 5 (by norm_num)
      ((φ.comp K.subtype).comp (e.symm.trans hεK.symm).toMonoidHom)
      (hφK.comp (e.symm.trans hεK.symm).surjective)

end DicksonI3013

section I3013

private theorem card_alt_five_i3013 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

private theorem card_alt_six_i3013 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

private theorem card_alt_eight_i3013 : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

private theorem exists_valid_of_onLie_two {S : Type} [Group S] (i : TauCeti.CFSGIndex)
    (hi : CFSG.Yardstones.Md0ec50421ce4.onLie (fun d => d.characteristic = 2) i)
    (e : S ≃* i.Group) :
    ∃ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 ∧ Nonempty (S ≃* d.Group) := by
  cases i with
  | cyclic p hp => exact (hi : False).elim
  | alternating n hn => exact (hi : False).elim
  | lie d => exact ⟨d, hi, ⟨e⟩⟩
  | sporadic s => exact (hi : False).elim

private theorem amb2_lie_cases (d : TauCeti.ValidLieTypeIndex)
    (hi : CFSG.Yardstones.Md0ec50421ce4.ambiguousChev 2 (TauCeti.CFSGIndex.lie d)) :
    (∃ q : TauCeti.PrimePower, d.1 = TauCeti.LieTypeIndex.A 1 q ∧ q.card = 7) ∨
      (∃ q : TauCeti.PrimePower, d.1 = TauCeti.LieTypeIndex.twistedA 2 q ∧ q.card = 3) := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q =>
    rcases r with _ | _ | r
    · exact (hi : False).elim
    · rcases hi with ⟨h7, -⟩ | ⟨-, h23⟩
      · exact Or.inl ⟨q, rfl, h7⟩
      · exact absurd h23 (by norm_num)
    · exact (hi : False).elim
  | twistedA r q =>
    rcases r with _ | _ | _ | _ | r
    · exact (hi : False).elim
    · exact (hi : False).elim
    · rcases hi with ⟨h3, -⟩
      exact Or.inr ⟨q, rfl, h3⟩
    · rcases hi with ⟨-, h23⟩
      exact absurd h23 (by norm_num)
    · exact (hi : False).elim
  | _ => exact (hi : False).elim

private theorem prime_formula_lt {r N : ℕ} (h5 : 5 ≤ r) (h : r * (r ^ 2 - 1) = N) (hN : N ≤ 51840) :
    r < 41 := by
  by_contra hc
  push Not at hc
  have h1 : 41 * (41 ^ 2 - 1) ≤ r * (r ^ 2 - 1) :=
    Nat.mul_le_mul hc (Nat.sub_le_sub_right (Nat.pow_le_pow_left hc 2) 1)
  rw [h] at h1
  norm_num at h1
  omega

private theorem no_formula {r N : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (h : r * (r ^ 2 - 1) = N)
    (hN : N ≤ 51840) (hne : ∀ k < 41, k.Prime → 5 ≤ k → k * (k ^ 2 - 1) ≠ N) : False :=
  hne r (prime_formula_lt h5 h hN) hr h5 h

end I3013

theorem i3013_holds (G : Type) [Group G] [Finite G] :
    I3013At G := by
  intro p q X K hp hq hq2 _hX hK hChev hinv
  have hQ := isQuasisimple_pQuot_of_glaPComponent hp hK
  haveI : Group.IsPerfect (PQuot p K) := ⟨hQ.1⟩
  haveI : IsSimpleGroup (PSimple p K) := hQ.2
  haveI : Group.IsPerfect (PSimple p K) := inferInstance
  obtain ⟨H, φ, hφ⟩ := hinv
  obtain ⟨r, hr, h5, ⟨eS⟩⟩ := psl_of_involvedSL2 hq hq2 H φ hφ
  haveI : Fact r.Prime := ⟨hr⟩
  have hcardZ : Nat.card (ZMod r) = r ^ 1 := by rw [Nat.card_zmod, pow_one]
  let T : ZMod r ≃+* GaloisField r 1 :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField (ZMod r) r 1 Nat.one_pos hcardZ
  let eF := eS.trans (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv T (Fin 2))
  have hM : CFSG.Models.LieModel (PSimple p K) .PSL 2 r 1 :=
    CFSG.Models.lieModel_of_statedClassicalModel
      (CFSG.Assembly.LowTwoRank.statedClassicalModel_psl_two_of_mulEquiv (PSimple p K) r 1
        (by simpa using h5) eF)
  have hBP : CFSG.Blueprint.LieModel (PSimple p K) .PSL 2 r 1 :=
    CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel (t := .PSL) (by decide) hM
  have hadmOdd := CFSG.SeitzReduction.CrossChar.statedLieAdmissible_of_lieModel hBP
  have hr2 : r ≠ 2 := by omega
  have hodd : CFSG.Blueprint.OddLieType (PSimple p K) :=
    ⟨.PSL, 2, r, 1, hr, hr2, hadmOdd, hBP⟩
  have hO := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  have hformOdd : Nat.card (PSimple p K) * 2 = r * (r ^ 2 - 1) := by
    obtain ⟨-, h, -⟩ := hO (PSimple p K) .PSL 2 r 1 hadmOdd hBP
    obtain ⟨k, hk⟩ := hr.odd_of_ne_two hr2
    have hd : CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSL 2 (r ^ 1) = 2 := by
      simp only [CFSG.ComponentClassification.CatLeaf.lieOrderDivisor, pow_one]
      exact Nat.gcd_eq_left (by omega)
    have hn : CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSL 2 (r ^ 1) =
        r * (r ^ 2 - 1) := by
      simp only [CFSG.ComponentClassification.CatLeaf.lieOrderNumerator, pow_one]
      norm_num
    rw [hd, hn] at h
    exact h
  have e_PSL24_div : CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSL 2 (2 ^ 2) = 1 := by
    decide
  have e_PSL24_num : CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSL 2 (2 ^ 2) = 60 := by
    decide
  have e_PSL32_div : CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSL 3 (2 ^ 1) = 1 := by
    decide
  have e_PSL32_num : CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSL 3 (2 ^ 1) = 168 := by
    decide
  have e_PSU41_div : CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSU 4 (2 ^ 1) = 1 := by
    decide
  have e_PSU41_num : CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSU 4 (2 ^ 1) = 25920 := by
    decide
  rcases hChev with hc2 | hamb
  ·
    obtain ⟨i, hi, ⟨e⟩⟩ := hc2
    obtain ⟨d, hd, ⟨e'⟩⟩ := exists_valid_of_onLie_two i hi e
    obtain ⟨t, n, f, hX⟩ := CFSG.StandardType.ChevTwo.exists_lieModel_two_of_valid d hd e'
    have hadm := CFSG.SeitzReduction.CrossChar.statedLieAdmissible_of_lieModel hX
    rcases CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType hO hX hodd with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · left
      obtain ⟨-, h, -⟩ := hO (PSimple p K) .PSL 2 2 2 hadm hX
      rw [e_PSL24_div, e_PSL24_num, mul_one] at h
      exact h
    · right
      obtain ⟨-, h, -⟩ := hO (PSimple p K) .PSL 3 2 1 hadm hX
      rw [e_PSL32_div, e_PSL32_num, mul_one] at h
      exact h
    · exfalso
      obtain ⟨-, h, -⟩ := hO (PSimple p K) .PSU 4 2 1 hadm hX
      rw [e_PSU41_div, e_PSU41_num, mul_one] at h
      have hN : r * (r ^ 2 - 1) = 51840 := by rw [← hformOdd, h]
      exact no_formula hr h5 hN (by norm_num) (by decide)
  ·
    obtain ⟨i, hi, ⟨e⟩⟩ := hamb
    cases i with
    | cyclic p' hp' => exact (hi : False).elim
    | alternating n hn =>
      have hi' : (n = 5 ∧ (2 = 2 ∨ 2 = 5)) ∨ (n = 6 ∧ (2 = 2 ∨ 2 = 3)) ∨ (n = 8 ∧ 2 = 2) := hi
      rcases hi' with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
      · left
        exact (Nat.card_congr e.toEquiv).trans card_alt_five_i3013
      · exfalso
        have h360 : Nat.card (PSimple p K) = 360 :=
          (Nat.card_congr e.toEquiv).trans card_alt_six_i3013
        have hN : r * (r ^ 2 - 1) = 720 := by rw [← hformOdd, h360]
        exact no_formula hr h5 hN (by norm_num) (by decide)
      · exfalso
        have h20160 : Nat.card (PSimple p K) = 20160 :=
          (Nat.card_congr e.toEquiv).trans card_alt_eight_i3013
        have hN : r * (r ^ 2 - 1) = 40320 := by rw [← hformOdd, h20160]
        exact no_formula hr h5 hN (by norm_num) (by decide)
    | lie d =>
      rcases amb2_lie_cases d hi with ⟨q, hdq, hq7⟩ | ⟨q, hdq, hq3⟩
      · right
        have h := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds d
          (PSimple p K) ⟨e⟩
        rw [hdq] at h
        simp only [CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula,
          CFSG.Open.orderA, hq7] at h
        exact h.trans (by decide)
      · exfalso
        have h := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds d
          (PSimple p K) ⟨e⟩
        rw [hdq] at h
        simp only [CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula,
          CFSG.Open.orderTwistedA, hq3] at h
        have h6048 : Nat.card (PSimple p K) = 6048 := h.trans (by decide)
        have hN : r * (r ^ 2 - 1) = 12096 := by rw [← hformOdd, h6048]
        exact no_formula hr h5 hN (by norm_num) (by decide)
    | sporadic s => exact (hi : False).elim

end CFSG.LocalAnalysis.GLTheoremA
