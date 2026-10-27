module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThreeG2
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThreeRank
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcThreeSplit
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MinusStmt

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.LieType.SeitzGeneration CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Residuals


@[expose] def TrialityThreeRest : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 3 → 1 ≤ f →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (ℓ ^ f) ^ 3 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), φ ^ 3 = 1 →
      φ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range →
      (¬ ∃ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        MulAut.conj y * φ * (MulAut.conj y)⁻¹ = fieldActor (t := TwistTag.D4) σ σ ∨
        MulAut.conj y * φ * (MulAut.conj y)⁻¹ = (fieldActor (t := TwistTag.D4) σ σ)⁻¹) →
      CoreFreeAt 3 φ

@[expose] def TrialityA2Rep (ℓ f : ℕ) (hℓ : ℓ.Prime) (K : Type) [Field K] [Finite K]
    (σ : K ≃+* K) (s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : Prop :=
  ((ℓ ^ f) % 3 = 1 ∧ ∃ d : Kˣ, Units.map σ.toRingHom.toMonoidHom d = d ∧ d ^ 3 = 1 ∧ d ≠ 1 ∧
      (s : ModGL TwistTag.D4.tag K) =
        CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit TwistTag.D4.tag
          ![1, 1, d, 1]) ∨
    ((ℓ ^ f) % 3 = 2 ∧ CFSG.GH74.GLS.Stage2.Bender.Thm1.D4MinusToral ℓ f hℓ K σ s)

@[expose] def TrialityCocycleNF : Prop :=
  ∀ (ℓ f : ℕ) (hℓ : ℓ.Prime), ℓ ≠ 3 → 1 ≤ f →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (ℓ ^ f) ^ 3 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), φ ^ 3 = 1 →
      φ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range →
      (∃ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
        MulAut.conj y * φ * (MulAut.conj y)⁻¹ = fieldActor (t := TwistTag.D4) σ σ ∨
        MulAut.conj y * φ * (MulAut.conj y)⁻¹ = (fieldActor (t := TwistTag.D4) σ σ)⁻¹) ∨
      ∃ y s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, TrialityA2Rep ℓ f hℓ K σ s ∧
        (MulAut.conj y * φ * (MulAut.conj y)⁻¹ =
            MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ ∨
          MulAut.conj y * φ * (MulAut.conj y)⁻¹ =
            (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)⁻¹)

@[expose] def TrialityA2CoreFree : Prop :=
  ∀ (ℓ f : ℕ) (hℓ : ℓ.Prime), ℓ ≠ 3 → 1 ≤ f →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (ℓ ^ f) ^ 3 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, TrialityA2Rep ℓ f hℓ K σ s →
      CoreFreeAt 3 (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)

theorem trialityTwoG2Core_holds :
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = 8 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ 2) →
      ∀ N : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        N ≤ fixSub (fieldActor (t := TwistTag.D4) σ σ) →
        (∀ g ∈ fixSub (fieldActor (t := TwistTag.D4) σ σ), ∀ n ∈ N, g * n * g⁻¹ ∈ N) →
        Nat.Coprime 3 (Nat.card N) → N = ⊥ := by
  intro K _ _ hK σ hσ N hNT hNn hcop
  exact fixSub_fieldActor_self_normal_eq_bot Nat.prime_two (by norm_num) le_rfl
    (by rw [hK]; norm_num) σ (fun c => by rw [hσ c]; norm_num) N hNT hNn hcop

end Residuals

section Model


variable {K : Type} [Field K] [Finite K]

theorem exists_fieldHom_D4 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    (∃ Θ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* (K ≃+* K),
      (∀ α g δ, α = MulAut.conj g * fieldActor σ δ → Θ α = δ) ∧
      Θ.ker = (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) ∧
    IsCyclic (K ≃+* K) ∧ Nat.card (K ≃+* K) = 3 * f := by
  by_cases h2 : ℓ = 2
  · subst h2
    obtain ⟨-, -, ⟨Θ, hΘ, -, hker, -⟩, hcyc, hcard, -⟩ :=
      even_triality_exact_automorphism_normal_form hf K hK σ hσ
    exact ⟨⟨Θ, hΘ, hker⟩, hcyc, hcard⟩
  · obtain ⟨-, -, ⟨Θ, hΘ, -, hker, -⟩, hcyc, hcard, -⟩ :=
      odd_triality_exact_automorphism_normal_form hℓ h2 hf K hK σ hσ
    exact ⟨⟨Θ, hΘ, hker⟩, hcyc, hcard⟩

theorem exists_eq_conj_mul_fieldActor_self_of_pow_three {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hα3 : α ^ 3 = 1)
    (hαin : α ∉ innerAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    ∃ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      α = MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ ∨
        α⁻¹ = MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ := by
  classical
  obtain ⟨⟨Θ, hΘ, hker⟩, hcyc, hcard⟩ := exists_fieldHom_D4 hℓ hf hK σ hσ
  have hσ3 : σ ^ 3 = 1 := by
    ext c
    exact ringEquiv_cube_apply_eq hK hσ c
  have hσ1 : σ ≠ 1 := by
    intro h
    have hc := CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube hℓ hf hK σ hσ
    have htop : fixSubfield σ = ⊤ := by
      ext c
      simp [h]
    rw [htop] at hc
    have hc' : Nat.card K = ℓ ^ f := by
      rw [← hc]
      exact (Nat.card_congr Subfield.topEquiv.toEquiv).symm
    have hp1 : 1 < ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
    rw [hK] at hc'
    nlinarith [hp1, pow_pos (lt_trans Nat.zero_lt_one hp1) 2]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hσord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  have hδ3 : Θ α ^ 3 = 1 := (map_pow Θ α 3).symm.trans ((congrArg Θ hα3).trans (map_one Θ))
  have hδ1 : Θ α ≠ 1 := fun h => hαin (by
    have hmem : α ∈ Θ.ker := h
    rwa [hker] at hmem)
  have hδord : orderOf (Θ α) = 3 := orderOf_eq_prime hδ3 hδ1
  have hδσ : Θ α = σ ∨ Θ α = σ⁻¹ := by
    have hfin : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
    have : Fintype (K ≃+* K) := Fintype.ofFinite _
    have h3dvd : 3 ∣ Fintype.card (K ≃+* K) := by
      rw [← Nat.card_eq_fintype_card, hcard]
      exact Dvd.intro _ rfl
    have hcnt := IsCyclic.card_orderOf_eq_totient (α := K ≃+* K) h3dvd
    have hφ : Nat.totient 3 = 2 := by decide
    set S : Finset (K ≃+* K) := Finset.univ.filter fun a => orderOf a = 3 with hS
    have hσinv : σ ≠ σ⁻¹ := by
      intro h
      have h2 : σ ^ 2 = 1 := by
        calc σ ^ 2 = σ * σ := sq σ
          _ = σ * σ⁻¹ := by rw [← h]
          _ = 1 := mul_inv_cancel σ
      apply hσ1
      calc σ = σ ^ 3 * (σ ^ 2)⁻¹ := by group
        _ = 1 := by rw [hσ3, h2]; simp
    have hsub : ({σ, σ⁻¹} : Finset (K ≃+* K)) ⊆ S := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases ha with rfl | rfl
      · exact hσord
      · rw [orderOf_inv]
        exact hσord
    have hSeq : ({σ, σ⁻¹} : Finset (K ≃+* K)) = S :=
      Finset.eq_of_subset_of_card_le hsub (by
        rw [Finset.card_pair hσinv]
        have : S.card = 2 := by rw [hS, hcnt, hφ]
        omega)
    have hδS : Θ α ∈ S := by
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hδord
    rw [← hSeq] at hδS
    simpa using hδS
  obtain ⟨⟨g, δ'⟩, hgδ, -⟩ := existsUnique_conj_mul_fieldActor_D4 hℓ hf hK σ hσ α
  have hα : α = MulAut.conj g * fieldActor (t := TwistTag.D4) σ δ' := hgδ
  have hδ'eq : Θ α = δ' := hΘ α g δ' hα
  rcases hδσ with h | h
  · rw [← hδ'eq, h] at hα
    exact ⟨g, Or.inl hα⟩
  · rw [← hδ'eq, h] at hα
    have hEinv : (fieldActor (t := TwistTag.D4) σ σ⁻¹)⁻¹ = fieldActor (t := TwistTag.D4) σ σ := by
      have h1 := fieldActor_mul (t := TwistTag.D4) σ σ⁻¹ σ
      rw [inv_mul_cancel, fieldActor_one] at h1
      exact inv_eq_of_mul_eq_one_right h1.symm
    refine ⟨fieldActor (t := TwistTag.D4) σ σ g⁻¹, Or.inr ?_⟩
    rw [hα, mul_inv_rev, hEinv,
      ← map_inv (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →* _) g]
    refine MulEquiv.ext fun x => ?_
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul]
    simp only [map_inv]

theorem trialityThreeRest_of_cocycleNF (hnf : TrialityCocycleNF) (hA2 : TrialityA2CoreFree) :
    TrialityThreeRest := by
  intro ℓ f hℓ hℓ3 hf K _ _ hK σ hσ φ hφ3 hφo hnot
  rcases hnf ℓ f hℓ hℓ3 hf K hK σ hσ φ hφ3 hφo with hG2 | ⟨y, s, hs, hy | hy⟩
  · exact (hnot hG2).elim
  · rw [← coreFreeAt_conj_iff φ (MulAut.conj y), hy]
    exact hA2 ℓ f hℓ hℓ3 hf K hK σ hσ s hs
  · rw [← coreFreeAt_conj_iff φ (MulAut.conj y), hy]
    exact (hA2 ℓ f hℓ hℓ3 hf K hK σ hσ s hs).inv

theorem coreFreeAt_three_graphFixedRootGroup_D4 (hR : TrialityThreeRest) {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (x : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hx3 : x ^ 3 = 1)
    (hxo : x ∉ innerAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) : CoreFreeAt 3 x := by
  by_cases hconj : ∃ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      MulAut.conj y * x * (MulAut.conj y)⁻¹ = fieldActor (t := TwistTag.D4) σ σ ∨
      MulAut.conj y * x * (MulAut.conj y)⁻¹ = (fieldActor (t := TwistTag.D4) σ σ)⁻¹
  · obtain ⟨y, hy | hy⟩ := hconj
    · rw [← coreFreeAt_conj_iff x (MulAut.conj y), hy]
      exact coreFreeAt_three_fieldActor_self hℓ hℓ3 hf hK σ hσ
    · rw [← coreFreeAt_conj_iff x (MulAut.conj y), hy]
      exact (coreFreeAt_three_fieldActor_self hℓ hℓ3 hf hK σ hσ).inv
  · exact hR ℓ f hℓ hℓ3 hf K hK σ hσ x hx3 hxo hconj

end Model

section Family


variable {K : Type} [Field K] [Finite K]

theorem isLocallyBalancedAbs_three_graphFixedRootGroup_D4 (hR : TrialityThreeRest) {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    IsLocallyBalancedAbs 3 3 (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  have hinj := mulAut_conj_injective_of_center_eq_bot
    (exceptional_fixed_center_trivial TwistTag.D4 K σ)
  have hr : RankLE2 3 (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := fun F hF =>
    (card_le_nine_of_graphFixedRootGroup_ne_three hℓ hℓ3 hf hK (σ := σ.toRingHom) hσ F
      ⟨hF.1, hF.2⟩).trans (by norm_num)
  exact isLocallyBalancedAbs_of_coreFree Nat.prime_three hinj
    (fun D hD hcard hin => false_of_inner_cube_of_rankLE2 Nat.prime_three hinj hr hD hcard hin)
    (fun x hx3 hxo => coreFreeAt_three_graphFixedRootGroup_D4 hR hℓ hℓ3 hf hK σ hσ x hx3 hxo)


theorem crossCharFamAt_trialityD4_three_of_rest (hR : TrialityThreeRest) :
    CrossCharFamAt .trialityD4 fun _ p => p = 3 := by
  rintro ⟨d, hv⟩ ⟨q, hd⟩ p - - hc rfl
  change d = _ at hd
  subst hd
  have hq3 : q.p ≠ 3 := fun h => hc (by simp [h])
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨e⟩⟩ := exists_catEquiv_trialityD4 q hv
  exact IsLocallyBalancedAbs.of_mulEquiv e
    (isLocallyBalancedAbs_three_graphFixedRootGroup_D4 hR q.prime_p hq3 q.exponent_pos hK σ hσ)

theorem crossCharFamAt_trialityD4_three_of_cocycleNF (hnf : TrialityCocycleNF)
    (hA2 : TrialityA2CoreFree) : CrossCharFamAt .trialityD4 fun _ p => p = 3 :=
  crossCharFamAt_trialityD4_three_of_rest (trialityThreeRest_of_cocycleNF hnf hA2)

theorem crossCharFamAt_trialityD4_open_of_rest (hR : TrialityThreeRest) :
    CrossCharFamAt .trialityD4 fun idx p => ¬ regimeTrialityD4Vac idx p :=
  crossCharFamAt_trialityD4_open_of_three (crossCharFamAt_trialityD4_three_of_rest hR)

theorem crossCharFamAt_trialityD4_open_of_cocycleNF (hnf : TrialityCocycleNF)
    (hA2 : TrialityA2CoreFree) :
    CrossCharFamAt .trialityD4 fun idx p => ¬ regimeTrialityD4Vac idx p :=
  crossCharFamAt_trialityD4_open_of_rest (trialityThreeRest_of_cocycleNF hnf hA2)

end Family

end CFSG.HardMathSupport.Timmesfeld.CrossChar
