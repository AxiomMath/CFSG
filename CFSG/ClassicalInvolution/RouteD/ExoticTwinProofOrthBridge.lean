module

public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofOrthGeom
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofOrthWitt
public import CFSG.ClassicalInvolution.RouteD.GapsOrthSpin
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpin
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectBridge
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Central

variable {X Y : Type} [Group X] [Group Y]

theorem TwinFamily.of_central (π : X →* Y) (hker : π.ker ≤ Subgroup.center X)
    {𝓕 : Set (Subgroup X)} {𝓖 : Set (Subgroup Y)} (hperf : ∀ R ∈ 𝓕, ⁅R, R⁆ = R)
    (hmap : ∀ R ∈ 𝓕, R.map π ∈ 𝓖) (hsurj : ∀ L ∈ 𝓖, ∃ R ∈ 𝓕, R.map π = L) {a : ℕ}
    (hT : TwinFamily 𝓕 a) : TwinFamily 𝓖 a := by
  obtain ⟨F, hF, hinj, hcomm, htw⟩ := hT
  refine ⟨fun i => (F i).map π, fun i => hmap _ (hF i), fun i j hij => ?_,
    fun i j hij => ?_, fun i j S' hS' => ?_⟩
  · exact hinj (ModelFacts.eq_of_map_eq_of_isPerfect π hker (hperf _ (hF i)) (hperf _ (hF j)) hij)
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm i j hij x hx y hy]
  · obtain ⟨S, hS, rfl⟩ := hsurj S' hS'
    have key : ∀ k, (S.map π = (F k).map π ∨ Commutes (S.map π) ((F k).map π)) ↔
        (S = F k ∨ Commutes S (F k)) := by
      intro k
      rw [Gaps.commutes_map_iff hker (hperf S hS)]
      constructor
      · rintro (h | h)
        · exact Or.inl (ModelFacts.eq_of_map_eq_of_isPerfect π hker (hperf _ hS)
            (hperf _ (hF k)) h)
        · exact Or.inr h
      · rintro (h | h)
        · exact Or.inl (by rw [h])
        · exact Or.inr h
    rw [key i, key j]
    exact htw i j S hS

end Central

section Correspondence

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  [Nontrivial V] {Q : QuadraticForm F V}

theorem spin_fund_correspondence (hodd : Odd (Nat.card F)) (hQ : (polarBilin Q).Nondegenerate)
    {fund : Set (Subgroup (spinGroup Q))} {R₀ : Subgroup (spinGroup Q)} (hR₀ : R₀ ∈ fund)
    (hconj : ∀ R ∈ fund, ∀ g : spinGroup Q, conjSub g R ∈ fund)
    (hsc : ∀ R ∈ fund, ∃ g : spinGroup Q, R = conjSub g R₀) (fr₀ : OFrame Q)
    (himg : R₀.map (spinAction Q) = fr₀.La.range) (hperp : 2 ≤ Module.finrank F fr₀.perp) :
    (∀ R ∈ fund, R.map (spinAction Q) ∈ fundSet Q) ∧
      ∀ L ∈ fundSet Q, ∃ R ∈ fund, R.map (spinAction Q) = L := by
  have h2 : (2 : F) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have : Invertible (2 : F) := invertibleOfNonzero h2
  constructor
  · intro R hR
    obtain ⟨g, rfl⟩ := hsc R hR
    have hg : spinAction Q g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ g v
    have key : (conjSub g R₀).map (spinAction Q) =
        fr₀.La.range.map (MulAut.conj (spinAction Q g)).toMonoidHom := by
      show (R₀.map (MulAut.conj g).toMonoidHom).map (spinAction Q) = _
      rw [ModelFacts.map_conj_map, himg]
    rw [key]
    exact ⟨_, IsFundamental.conj hg (IsFundamental.of_frame fr₀)⟩
  · rintro L ⟨i, fr, rfl, -⟩
    obtain ⟨x, hx⟩ := ModelFacts.exists_spin_conj hodd hQ fr₀ fr hperp
    refine ⟨conjSub x R₀, hconj R₀ hR₀ x, ?_⟩
    show (R₀.map (MulAut.conj x).toMonoidHom).map (spinAction Q) = _
    rw [ModelFacts.map_conj_map, himg, ModelFacts.La_range_eq_map_conj hx]

end Correspondence

section Odd

variable {p f : ℕ} [Fact p.Prime]

theorem fundCorr_odd (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaOdd n p f) :
    (∀ R ∈ fundamentalSubgroups .POmegaOdd (oddDatum n (GaloisField p f)),
        R.map (spinAction (quadOdd n (GaloisField p f))) ∈
          fundSet (quadOdd n (GaloisField p f))) ∧
      ∀ L ∈ fundSet (quadOdd n (GaloisField p f)),
        ∃ R ∈ fundamentalSubgroups .POmegaOdd (oddDatum n (GaloisField p f)),
          R.map (spinAction (quadOdd n (GaloisField p f))) = L := by
  have hn3 : 3 ≤ n := hadm.2.2.1
  obtain ⟨hodd, h4⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have hlong := ModelFacts.isLongestRoot_single .POmegaOdd n p f Fact.out trivial hadm
  have hsc := ModelFacts.fundamentalSingleClass .POmegaOdd n p f Fact.out trivial hadm
    (by decide) (by decide)
  have hk : (0 : ℕ) + 1 < n := by omega
  set k₀ : Fin n := ⟨0, by omega⟩ with hk₀
  set j₀ : Fin n := ⟨0 + 1, hk⟩ with hj₀
  have hij : k₀ ≠ j₀ := Fin.ne_of_val_ne (by simp [hk₀, hj₀])
  have hR : CFSG.LieType.CurtisTits.rankOne (oddRootGroup n (GaloisField p f)) k₀ =
      ((oddFrame n (GaloisField p f)).toHypFrame.longSL2 hij true false).range := by
    have h1 : CFSG.LieType.CurtisTits.rankOne (oddRootGroup n (GaloisField p f)) k₀ =
        (rankOneB (GaloisField p f) k₀).range :=
      le_antisymm (OddCT.rankOne_le_range k₀) (by
        rintro _ ⟨M, rfl⟩
        exact OddCT.rankOneB_mem_rankOne k₀ M)
    rw [h1, rankOneB_of_lt (GaloisField p f) hk rfl hij]
  have hR₀ : CFSG.LieType.CurtisTits.rankOne (oddRootGroup n (GaloisField p f)) k₀ ∈
      fundamentalSubgroups .POmegaOdd (oddDatum n (GaloisField p f)) :=
    ⟨1, Pi.single k₀ 1, Or.inl (hlong k₀ (by show 0 + 1 < n; omega)), by
      rw [conjSub_one]; rfl⟩
  have hdim : Module.finrank (GaloisField p f) (Fin n ⊕ Fin n ⊕ Unit → GaloisField p f) =
      2 * n + 1 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
    ring
  have hperp : 2 ≤ Module.finrank (GaloisField p f)
      ((oddFrame n (GaloisField p f)).toHypFrame.toFrame hij true false).perp := by
    have := ModelFacts.finrank_perp_add_four
      ((oddFrame n (GaloisField p f)).toHypFrame.toFrame hij true false)
    omega
  have himg : (CFSG.LieType.CurtisTits.rankOne (oddRootGroup n (GaloisField p f)) k₀).map
      (spinAction (quadOdd n (GaloisField p f))) =
      ((oddFrame n (GaloisField p f)).toHypFrame.toFrame hij true false).La.range := by
    rw [hR]
    exact ModelFacts.map_longSL2_range (oddFrame n (GaloisField p f)).toHypFrame hij true false
  exact spin_fund_correspondence hodd
    (nondegenerate_polarBilin_quadOdd n (GaloisField p f)
      (ModelFacts.two_ne_zero_galoisField f hp2))
    hR₀ (fun R hR g => conjSub_mem_fundamentalSubgroups hR g)
    (fun R hR => hsc _ hR₀ R hR) _ himg hperp

end Odd

section Minus

variable {p f : ℕ} [Fact p.Prime]

theorem fundCorr_minus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus n p f) :
    (∀ R ∈ fundamentalSubgroups .POmegaMinus (Twisted.minusDatum n (minusCoeffs_irr p f)),
        R.map (spinAction (quadMinus n (GaloisField p f) (minusCoeffs p f).1
          (minusCoeffs p f).2)) ∈
          fundSet (quadMinus n (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2)) ∧
      ∀ L ∈ fundSet (quadMinus n (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2),
        ∃ R ∈ fundamentalSubgroups .POmegaMinus (Twisted.minusDatum n (minusCoeffs_irr p f)),
          R.map (spinAction (quadMinus n (GaloisField p f) (minusCoeffs p f).1
            (minusCoeffs p f).2)) = L := by
  have hn4 : 4 ≤ n := hadm.2.2
  obtain ⟨hodd, h4⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have hlong := ModelFacts.isLongestRoot_single .POmegaMinus n p f Fact.out trivial hadm
  have hsc := ModelFacts.fundamentalSingleClass .POmegaMinus n p f Fact.out trivial hadm
    (by decide) (by decide)
  have hk : (0 : ℕ) + 1 < n - 1 := by omega
  set k₀ : Fin (n - 1) := ⟨0, by omega⟩ with hk₀
  have hij := Twisted.succ_ne_of_lt n (k := k₀) hk
  have hR := Twisted.rankOne_minusRootGroup_of_lt n (minusCoeffs_irr p f) (k := k₀) hk
  have hR₀ : CFSG.LieType.CurtisTits.rankOne (Twisted.minusRootGroup n (minusCoeffs_irr p f)) k₀ ∈
      fundamentalSubgroups .POmegaMinus (Twisted.minusDatum n (minusCoeffs_irr p f)) :=
    ⟨1, Pi.single k₀ 1, Or.inl (hlong k₀ (by show 0 + 2 < n; omega)), by
      rw [conjSub_one]; rfl⟩
  have hdim : Module.finrank (GaloisField p f)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField p f) = 2 * (n - 1) + 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    ring
  have hperp : 2 ≤ Module.finrank (GaloisField p f)
      ((Twisted.minusFrame n (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame.toFrame hij
        true false).perp := by
    have := ModelFacts.finrank_perp_add_four
      ((Twisted.minusFrame n (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame.toFrame hij
        true false)
    omega
  have himg : (CFSG.LieType.CurtisTits.rankOne (Twisted.minusRootGroup n (minusCoeffs_irr p f))
        k₀).map (spinAction (quadMinus n (GaloisField p f) (minusCoeffs p f).1
          (minusCoeffs p f).2)) =
      ((Twisted.minusFrame n (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame.toFrame hij
        true false).La.range := by
    rw [hR]
    exact ModelFacts.map_longSL2_range
      (Twisted.minusFrame n (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame hij true false
  exact spin_fund_correspondence hodd
    (nondegenerate_polarBilin_quadMinus_of_finite n (GaloisField p f) (minusCoeffs_irr p f))
    hR₀ (fun R hR g => conjSub_mem_fundamentalSubgroups hR g)
    (fun R hR => hsc _ hR₀ R hR) _ himg hperp

end Minus

section Plus

variable {p f : ℕ} [Fact p.Prime]

theorem fundCorr_plus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ} (hn : 4 ≤ n) :
    (∀ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum n (GaloisField p f) (by omega)),
        R.map (spinAction (quadPlus n (GaloisField p f))) ∈
          fundSet (quadPlus n (GaloisField p f))) ∧
      ∀ L ∈ fundSet (quadPlus n (GaloisField p f)),
        ∃ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum n (GaloisField p f) (by omega)),
          R.map (spinAction (quadPlus n (GaloisField p f))) = L :=
  ⟨(Gaps.centralQuot_plus hp2 hn (by omega) hq).map_mem,
    (Gaps.centralQuot_plus hp2 hn (by omega) hq).surj⟩

end Plus

section Models

variable {p f : ℕ} [Fact p.Prime]

private theorem commutator_self_eq {G : Type} [Group G] {R : Subgroup G} (h : R ≤ ⁅R, R⁆) :
    ⁅R, R⁆ = R :=
  le_antisymm (Subgroup.commutator_le.mpr fun _ ha _ hb =>
    R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb)) h

theorem modelTwinClass_odd (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n a : ℕ}
    (hadm : StatedLieAdmissible .POmegaOdd n p f) (ha : 2 ≤ a)
    (h : ModelTwinClass p .POmegaOdd n f a) : a = 2 := by
  have hn3 : 3 ≤ n := hadm.2.2.1
  obtain ⟨hodd, h4⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have hT : TwinFamily (fundamentalSubgroups .POmegaOdd (oddDatum n (GaloisField p f))) a := h
  have hperf : Gaps.FundPerfect .POmegaOdd (modelUniv .POmegaOdd n p f Fact.out).D :=
    Gaps.fundPerfect_modelUniv hp2 trivial hadm (by omega)
  have hG : TwinFamily (fundSet (quadOdd n (GaloisField p f))) a :=
    TwinFamily.of_central (spinAction (quadOdd n (GaloisField p f)))
      (ker_spinAction_le_center _) (fun R hR => commutator_self_eq (hperf R hR))
      (fundCorr_odd hp2 hq hadm).1 (fundCorr_odd hp2 hq hadm).2 hT
  have hdim : Module.finrank (GaloisField p f) (Fin n ⊕ Fin n ⊕ Unit → GaloisField p f) =
      2 * n + 1 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
    ring
  refine le_antisymm ?_ ha
  by_cases hn : n = 3
  · exact twinFamily_le_two_of_lt_eight hodd (by omega) hG
  · exact twinFamily_le_two_of_nine_le hodd
      (nondegenerate_polarBilin_quadOdd n (GaloisField p f)
        (ModelFacts.two_ne_zero_galoisField f hp2))
      (by omega) hG

theorem modelTwinClass_plus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n a : ℕ}
    (hadm : StatedLieAdmissible .POmegaPlus n p f)
    (h : ModelTwinClass p .POmegaPlus n f a) : a ≤ 2 ∨ (n = 4 ∧ a ≤ 4) := by
  have hn4 : 4 ≤ n := hadm.2.2
  have hn3 : 3 ≤ n := by omega
  obtain ⟨hodd, h4⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have hT : TwinFamily
      (fundamentalSubgroups .POmegaPlus (plusDatum n (GaloisField p f) hn3)) a := by
    have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus n (GaloisField p f)),
        plusDatum n (GaloisField p f) hn3⟩ →
        TwinFamily (fundamentalSubgroups .POmegaPlus M.D) a →
        TwinFamily (fundamentalSubgroups .POmegaPlus (plusDatum n (GaloisField p f) hn3)) a := by
      intro M hM hT
      subst hM
      exact hT
    exact key _ (ModelFacts.modelUniv_POmegaPlus hn3) h
  have hperf : Gaps.FundPerfect .POmegaPlus (modelUniv .POmegaPlus n p f Fact.out).D :=
    Gaps.fundPerfect_modelUniv hp2 trivial hadm (by omega)
  have hperf' : ∀ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum n (GaloisField p f) hn3),
      ⁅R, R⁆ = R := by
    have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus n (GaloisField p f)),
        plusDatum n (GaloisField p f) hn3⟩ → Gaps.FundPerfect .POmegaPlus M.D →
        ∀ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum n (GaloisField p f) hn3), ⁅R, R⁆ = R := by
      intro M hM hP
      subst hM
      exact fun R hR => commutator_self_eq (hP R hR)
    exact key _ (ModelFacts.modelUniv_POmegaPlus hn3) hperf
  have hG : TwinFamily (fundSet (quadPlus n (GaloisField p f))) a :=
    TwinFamily.of_central (spinAction (quadPlus n (GaloisField p f)))
      (ker_spinAction_le_center _) hperf' (fundCorr_plus hp2 hq hn4).1 (fundCorr_plus hp2 hq hn4).2
      hT
  have hdim : Module.finrank (GaloisField p f) (Fin n ⊕ Fin n → GaloisField p f) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  by_cases hn : n = 4
  · right
    exact ⟨hn, twinFamily_le_four_of_eight hodd (by omega) hG⟩
  · left
    exact twinFamily_le_two_of_nine_le hodd (nondegenerate_polarBilin_quadPlus n (GaloisField p f))
      (by omega) hG

theorem modelTwinClass_minus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n a : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus n p f) (ha : 2 ≤ a)
    (h : ModelTwinClass p .POmegaMinus n f a) : a = 2 := by
  have hn4 : 4 ≤ n := hadm.2.2
  obtain ⟨hodd, h4⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have hT : TwinFamily (fundamentalSubgroups .POmegaMinus
      (Twisted.minusDatum n (minusCoeffs_irr p f))) a := h
  have hperf : Gaps.FundPerfect .POmegaMinus (modelUniv .POmegaMinus n p f Fact.out).D :=
    Gaps.fundPerfect_modelUniv hp2 trivial hadm (by omega)
  have hG : TwinFamily (fundSet (quadMinus n (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2)) a :=
    TwinFamily.of_central (spinAction (quadMinus n (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2)) (ker_spinAction_le_center _)
      (fun R hR => commutator_self_eq (hperf R hR))
      (fundCorr_minus hp2 hq hadm).1 (fundCorr_minus hp2 hq hadm).2 hT
  have hdim : Module.finrank (GaloisField p f)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField p f) = 2 * (n - 1) + 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    ring
  refine le_antisymm ?_ ha
  by_cases hn : n = 4
  · subst hn
    exact twinFamily_le_two_of_noOrth hodd
      (fun F₀ F₁ hF => false_of_orth_quadMinus_four (ModelFacts.two_ne_zero_galoisField f hp2)
        (minusCoeffs_irr p f) h4 F₀ F₁ hF) hG
  · exact twinFamily_le_two_of_nine_le hodd
      (nondegenerate_polarBilin_quadMinus_of_finite n (GaloisField p f) (minusCoeffs_irr p f))
      (by omega) hG

end Models

end CFSG.ClassicalInvolution.RouteD.Exotic
