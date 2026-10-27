module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4Outer

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.Timmesfeld.RankTwo
  CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.OddAut CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.CentralExt.TrialityClosed CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Lang.E6Descent
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual

set_option linter.unusedSectionVars false

@[expose] def A2PlusComps : Prop :=
  ∀ {p f : ℕ}, p.Prime → p ≠ 2 → p ≠ 3 → 1 ≤ f → (p ^ f) % 3 = 1 →
    ∀ {K : Type} [Field K] [Finite K], Nat.card K = (p ^ f) ^ 3 → ∀ {σ : K ≃+* K},
    (∀ c, σ c = c ^ (p ^ f)) → ∀ {d : Kˣ}, Units.map σ.toRingHom.toMonoidHom d = d → d ^ 3 = 1 →
    d ≠ 1 → ∀ {s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom},
      (s : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![1, 1, d, 1] →
      CompsFine p ↥(fixSubgroup (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ))

@[expose] def A2MinusComps : Prop :=
  ∀ {p f : ℕ} (hp : p.Prime), p ≠ 2 → p ≠ 3 → 1 ≤ f → (p ^ f) % 3 = 2 →
    ∀ {K : Type} [Field K] [Finite K], Nat.card K = (p ^ f) ^ 3 → ∀ {σ : K ≃+* K},
    (∀ c, σ c = c ^ (p ^ f)) → ∀ {s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom},
      D4MinusToral p f hp K σ s →
      CompsFine p ↥(fixSubgroup (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ))

@[expose] def A2PlusCompsWith (P : (X : Type) → [Group X] → Prop) (p f : ℕ) : Prop :=
  p.Prime → p ≠ 2 → p ≠ 3 → 1 ≤ f → (p ^ f) % 3 = 1 →
    ∀ {K : Type} [Field K] [Finite K], Nat.card K = (p ^ f) ^ 3 → ∀ {σ : K ≃+* K},
    (∀ c, σ c = c ^ (p ^ f)) → ∀ {d : Kˣ}, Units.map σ.toRingHom.toMonoidHom d = d → d ^ 3 = 1 →
    d ≠ 1 → ∀ {s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom},
      (s : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![1, 1, d, 1] →
      CompsWith P ↥(fixSubgroup (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ))

@[expose] def A2MinusCompsWith (P : (X : Type) → [Group X] → Prop) (p f : ℕ) : Prop :=
  ∀ (hp : p.Prime), p ≠ 2 → p ≠ 3 → 1 ≤ f → (p ^ f) % 3 = 2 →
    ∀ {K : Type} [Field K] [Finite K], Nat.card K = (p ^ f) ^ 3 → ∀ {σ : K ≃+* K},
    (∀ c, σ c = c ^ (p ^ f)) → ∀ {s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom},
      D4MinusToral p f hp K σ s →
      CompsWith P ↥(fixSubgroup (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ))

theorem compsWith_of_conj_eq {P : (X : Type) → [Group X] → Prop} (hP : IsComponentProperty P)
    {Y : Type} [Group Y] (y : Y) {φ ψ : MulAut Y}
    (h : MulAut.conj y * φ * (MulAut.conj y)⁻¹ = ψ) (hψ : CompsWith P ↥(fixSubgroup ψ)) :
    CompsWith P ↥(fixSubgroup φ) := by
  rw [← h] at hψ
  exact CompsWith.of_mulEquiv hP (fixSubgroupConjEquiv (MulAut.conj y) φ) hψ

theorem compsWith_inv_iff {P : (X : Type) → [Group X] → Prop} (hP : IsComponentProperty P)
    {Y : Type} [Group Y] (φ : MulAut Y) :
    CompsWith P ↥(fixSubgroup φ⁻¹) ↔ CompsWith P ↥(fixSubgroup φ) := by
  constructor
  · intro h
    exact CompsWith.of_mulEquiv hP (MulEquiv.subgroupCongr (fixSubgroup_inv_eq φ)).symm h
  · intro h
    exact CompsWith.of_mulEquiv hP (MulEquiv.subgroupCongr (fixSubgroup_inv_eq φ)) h

section Odd

variable {p f : ℕ}

theorem compsWith_cocycle_q1 {P : (X : Type) → [Group X] → Prop} (hP : IsComponentProperty P)
    {p f : ℕ} (h1 : A2PlusCompsWith P p f)
    (hPG2 : ∀ {F : Type} [Field F] [Finite F], Nat.card F = p ^ f →
      CompsWith P ↥(adjointGroup Tag.G2 F))
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 1) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hg : normSeq (fieldActor (t := TwistTag.D4) σ σ) g 3 = 1) :
    CompsWith P ↥(fixSubgroup (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ)) := by
  have hRot := rotLang_holds
  have hK3 : Nat.card K = p ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hCh : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp (by omega) hK3
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    have h4 : p ≠ 4 := fun h => by rw [h] at hp; exact absurd hp (by norm_num)
    omega
  haveI : Fact p.Prime := ⟨hp⟩
  have hq2 : 2 ≤ p ^ f := by
    have h3 : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    have h2 := hp.two_le
    omega
  have hG2 : CompsWith P ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ σ)) :=
    compsWith_fixSubgroup_fieldActor hP hp3 hf (Or.inr hp5) hK σ hσ
      (hPG2 (card_fixedField_of_cube σ.toRingHom hq2 hK hσ))
  obtain ⟨y, n, hn, hyn⟩ := d4MonoNF p f hp hp2 hp3 hf hq K hK σ hσ g hg
  refine compsWith_of_conj_eq hP y hyn ?_
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hψ3 := d4_fieldActor_pow_three K hK σ hσ
  have hcube : (MulAut.conj n * fieldActor (t := TwistTag.D4) σ σ) ^ 3 = 1 := by
    rw [← hyn, conj_pow, conj_mul_pow_eq, hg, hψ3, map_one, one_mul, mul_one]
    exact mul_inv_cancel _
  have hN := normSeq_eq_one_of_pow_eq_one hZ hψ3 hcube
  by_cases hnT : (n : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom
  · obtain ⟨y', s, -, -, hconj, d, hd, hd3, hsd⟩ := d4_toral_conj hp hp2 hf K hK σ hσ n hnT hN
    refine compsWith_of_conj_eq hP y' hconj ?_
    by_cases hd1 : d = 1
    · have hs1 : s = 1 := by
        apply Subtype.ext
        show (s : ModGL TwistTag.D4.tag K) = 1
        rw [hsd, hd1, ← rootDiagUnit_one (τ := TwistTag.D4.tag) (K := K)]
        exact congrArg _ (funext fun i => by fin_cases i <;> rfl)
      rw [hs1, map_one, one_mul]
      exact hG2
    · exact h1 hp hp2 hp3 hf hq hK hσ hd hd3 hd1 hsd
  · obtain ⟨y₀, s, d, hconj, hd, hd3, hd1, hsd⟩ :=
      ellQ1_conj_toral hRot hp hp2 hp3 hf hq hK σ hσ n hn hnT hN
    refine compsWith_of_conj_eq hP y₀ hconj ?_
    exact h1 hp hp2 hp3 hf hq hK hσ hd hd3 hd1 hsd

theorem compsWith_outer_three_odd_one {P : (X : Type) → [Group X] → Prop}
    (hP : IsComponentProperty P) {ℓ f : ℕ} [Fact ℓ.Prime]
    (h1 : A2PlusCompsWith P ℓ f)
    (hPG2 : ∀ {F : Type} [Field F] [Finite F], Nat.card F = ℓ ^ f →
      CompsWith P ↥(adjointGroup Tag.G2 F))
    (hℓ5 : 5 ≤ ℓ) (hf : 1 ≤ f) (hq : (ℓ ^ f) % 3 = 1) {K₃ : Type} [Field K₃] [Finite K₃]
    (hK₃ : Nat.card K₃ = (ℓ ^ f) ^ 3) (Fr : K₃ ≃+* K₃) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)) (hφ3 : φ ^ 3 = 1)
    (hφ : φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)).range) :
    CompsWith P ↥(fixSubgroup φ) := by
  have hp : ℓ.Prime := Fact.out
  have hp2 : ℓ ≠ 2 := by omega
  have hp3 : ℓ ≠ 3 := by omega
  have hφ1 : φ ≠ 1 := fun h => hφ ⟨1, by rw [h]; exact map_one _⟩
  have hφord : orderOf φ = 3 := orderOf_eq_prime hφ3 hφ1
  obtain ⟨g, hg, hφ' | hφ'⟩ := d4_outer_three_normal_form hp hp2 hf K₃ hK₃ Fr hFr φ hφord hφ
  · rw [hφ']
    exact compsWith_cocycle_q1 hP h1 hPG2 hp hp2 hp3 hf hq hK₃ Fr hFr g hg
  · have h := compsWith_cocycle_q1 hP h1 hPG2 hp hp2 hp3 hf hq hK₃ Fr hFr g hg
    rw [← hφ'] at h
    exact (compsWith_inv_iff hP φ).1 h

theorem compsWith_outer_three_odd_two {P : (X : Type) → [Group X] → Prop}
    (hP : IsComponentProperty P) {ℓ f : ℕ} [Fact ℓ.Prime]
    (h2 : A2MinusCompsWith P ℓ f)
    (hPG2 : ∀ {F : Type} [Field F] [Finite F], Nat.card F = ℓ ^ f →
      CompsWith P ↥(adjointGroup Tag.G2 F))
    (hℓ5 : 5 ≤ ℓ) (hf : 1 ≤ f) (hq : (ℓ ^ f) % 3 = 2) {K₃ : Type} [Field K₃] [Finite K₃]
    (hK₃ : Nat.card K₃ = (ℓ ^ f) ^ 3) (Fr : K₃ ≃+* K₃) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (φ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)) (hφ3 : φ ^ 3 = 1)
    (hφ : φ ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom)).range) :
    CompsWith P ↥(fixSubgroup φ) := by
  have hp : ℓ.Prime := Fact.out
  have hp2 : ℓ ≠ 2 := by omega
  have hp3 : ℓ ≠ 3 := by omega
  have hφ1 : φ ≠ 1 := fun h => hφ ⟨1, by rw [h]; exact map_one _⟩
  have hφord : orderOf φ = 3 := orderOf_eq_prime hφ3 hφ1
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K₃ Fr.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot Fr.surjective
  have hψ3 := d4_fieldActor_pow_three K₃ hK₃ Fr hFr
  have hq2 : 2 ≤ ℓ ^ f := by
    have h3 : ℓ ≤ ℓ ^ f := Nat.le_self_pow (by omega) ℓ
    have h2 := hp.two_le
    omega
  have hG2 : CompsWith P ↥(fixSubgroup (fieldActor (t := TwistTag.D4) Fr Fr)) :=
    compsWith_fixSubgroup_fieldActor hP hp3 hf (Or.inr hℓ5) hK₃ Fr hFr
      (hPG2 (card_fixedField_of_cube Fr.toRingHom hq2 hK₃ hFr))
  have hTor : ∀ s, D4MinusToral ℓ f hp K₃ Fr s →
      CompsWith P ↥(fixSubgroup (MulAut.conj s * fieldActor (t := TwistTag.D4) Fr Fr)) :=
    fun s hs => h2 hp hp2 hp3 hf hq hK₃ hFr hs
  rcases d4Minus_outer_three_nf hp hp2 hp3 hf hq K₃ hK₃ Fr hFr φ hφord hφ with
    ⟨y, hy⟩ | ⟨y, s, hs, hys⟩ | ⟨y, n, hn, hyn⟩
  · rcases hy with hy | hy
    · exact compsWith_of_conj_eq hP y hy hG2
    · exact compsWith_of_conj_eq hP y hy ((compsWith_inv_iff hP _).2 hG2)
  · rcases hys with hys | hys
    · exact compsWith_of_conj_eq hP y hys (hTor s hs)
    · exact compsWith_of_conj_eq hP y hys ((compsWith_inv_iff hP _).2 (hTor s hs))
  · have hc := pow_three_of_conj_eq y hφ3 hyn
    have hN := normSeq_eq_one_of_pow_eq_one hZ hψ3 hc
    obtain ⟨y₀, s, hsT, hconj⟩ :=
      minusEll_conj_toral rotLang_holds hp hp2 hp3 hf hq hK₃ Fr hFr n hn hN
    have hPL := compsWith_of_conj_eq hP y₀ hconj (hTor s hsT)
    rcases hyn with hyn | hyn
    · exact compsWith_of_conj_eq hP y hyn hPL
    · exact compsWith_of_conj_eq hP y hyn ((compsWith_inv_iff hP _).2 hPL)

end Odd

theorem trialityOddA2CompsWith_of_toral {P : (X : Type) → [Group X] → Prop}
    (hP : IsComponentProperty P) {ℓ f : ℕ} [Fact ℓ.Prime]
    (h1 : A2PlusCompsWith P ℓ f) (h2 : A2MinusCompsWith P ℓ f)
    (hPG2 : ∀ {F : Type} [Field F] [Finite F], Nat.card F = ℓ ^ f →
      CompsWith P ↥(adjointGroup Tag.G2 F)) :
    TrialityOddA2CompsWith P ℓ f := by
  intro hℓ5 hf K₃ _ _ hK₃ Fr hFr φ hφ3 hφ _
  have hℓ : ℓ.Prime := Fact.out
  have hq3 : ¬ 3 ∣ ℓ ^ f := fun h =>
    absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
      (Nat.prime_three.dvd_of_dvd_pow h)) (by omega)
  rcases (show (ℓ ^ f) % 3 = 1 ∨ (ℓ ^ f) % 3 = 2 by omega) with hq | hq
  · exact compsWith_outer_three_odd_one hP h1 hPG2 hℓ5 hf hq hK₃ Fr hFr φ hφ3 hφ
  · exact compsWith_outer_three_odd_two hP h2 hPG2 hℓ5 hf hq hK₃ Fr hFr φ hφ3 hφ

theorem trialityOddA2Comps_of_toral (h1 : A2PlusComps) (h2 : A2MinusComps) :
    TrialityOddA2Comps := by
  intro ℓ f _ hℓ5 hf K₃ _ _ hK₃ Fr hFr φ hφ3 hφ hconj
  rw [compsFine_iff_compsWith]
  refine trialityOddA2CompsWith_of_toral (isComponentProperty_componentFactor ℓ) ?_ ?_ ?_
    hℓ5 hf K₃ hK₃ Fr hFr φ hφ3 hφ hconj
  · intro hp hp2 hp3 hf' hq' K' _ _ hK' σ' hσ' d' hd' hd3' hd1' s' hs'
    exact (compsFine_iff_compsWith _ _).1
      (h1 (K := K') (σ := σ') (d := d') (s := s') hp hp2 hp3 hf' hq' hK' hσ' hd' hd3' hd1' hs')
  · intro hp hp2 hp3 hf' hq' K' _ _ hK' σ' hσ' s' hs'
    exact (compsFine_iff_compsWith _ _).1
      (h2 (K := K') (σ := σ') (s := s') hp hp2 hp3 hf' hq' hK' hσ' hs')
  · intro F _ _ hF
    haveI : Fintype F := Fintype.ofFinite F
    haveI : Fact ℓ.Prime := ⟨Fact.out⟩
    have hFc : Fintype.card F = ℓ ^ f := by rw [← Nat.card_eq_fintype_card]; exact hF
    have hcharP : CharP F ℓ := charP_of_card_eq_prime_pow hFc
    exact (compsFine_iff_compsWith _ _).1 (compsFine_adjointGroup_G2 (ringChar.eq F ℓ))

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
