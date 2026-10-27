module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TriOddShape
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.DualOddOne
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.A2Uni

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.OddAut CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual
  CFSG.HardMathSupport.Lang.E6Descent CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Fischer CFSG.RankThree.PartTwo.Sec19 CFSG.LieType.SeitzGeneration.ExcWideThree


theorem exists_conj_toral_of_cocycle {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) (hq : (ℓ ^ f) % 3 = 1) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (g : C0 σ) (hg : normSeq (fieldActor (t := TwistTag.D4) σ σ) g 3 = 1) :
    ∃ (y s : C0 σ) (d : Kˣ),
      MulAut.conj y * (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ) *
          (MulAut.conj y)⁻¹ = MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ ∧
        Units.map σ.toRingHom.toMonoidHom d = d ∧ d ^ 3 = 1 ∧
        (s : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![1, 1, d, 1] := by
  obtain ⟨y, n, hn, hyn⟩ := d4MonoNF ℓ f hℓ hℓ2 hℓ3 hf hq K hK σ hσ g hg
  have hZ : Subgroup.center (C0 σ) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hψ3 := d4_fieldActor_pow_three K hK σ hσ
  have hcube : (MulAut.conj n * fieldActor (t := TwistTag.D4) σ σ) ^ 3 = 1 := by
    rw [← hyn, conj_pow, conj_mul_pow_eq, hg, hψ3, map_one, one_mul, mul_one]
    exact mul_inv_cancel _
  have hN := normSeq_eq_one_of_pow_eq_one hZ hψ3 hcube
  by_cases hnT : (n : ModGL TwistTag.D4.tag K) ∈
      graphFixedTorus TwistTag.D4 K σ.toRingHom
  · obtain ⟨y', s, -, -, hconj, d, hd, hd3, hsd⟩ :=
      d4_toral_conj hℓ hℓ2 hf K hK σ hσ n hnT hN
    refine ⟨y' * y, s, d, ?_, hd, hd3, hsd⟩
    calc MulAut.conj (y' * y) * (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ) *
          (MulAut.conj (y' * y))⁻¹
        = MulAut.conj y' * (MulAut.conj y *
            (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ) * (MulAut.conj y)⁻¹) *
            (MulAut.conj y')⁻¹ := by
          rw [map_mul]; group
      _ = MulAut.conj y' * (MulAut.conj n * fieldActor (t := TwistTag.D4) σ σ) *
            (MulAut.conj y')⁻¹ := by rw [hyn]
      _ = _ := hconj
  · obtain ⟨y₀, s, d, hconj, hd, hd3, -, hsd⟩ :=
      ellQ1_conj_toral rotLang_holds hℓ hℓ2 hℓ3 hf hq hK σ hσ n hn hnT hN
    refine ⟨y₀ * y, s, d, ?_, hd, hd3, hsd⟩
    calc MulAut.conj (y₀ * y) * (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ) *
          (MulAut.conj (y₀ * y))⁻¹
        = MulAut.conj y₀ * (MulAut.conj y *
            (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ) * (MulAut.conj y)⁻¹) *
            (MulAut.conj y₀)⁻¹ := by
          rw [map_mul]; group
      _ = MulAut.conj y₀ * (MulAut.conj n * fieldActor (t := TwistTag.D4) σ σ) *
            (MulAut.conj y₀)⁻¹ := by rw [hyn]
      _ = _ := hconj

theorem exists_conj_toral {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) (hq : (ℓ ^ f) % 3 = 1) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (β : MulAut (C0 σ)) (hβ3 : β ^ 3 = 1) (hβout : β ∉ innerAut (C0 σ))
    (hβG : ¬ TriOddIsGLine σ β) :
    ∃ (y s : C0 σ) (d : Kˣ) (e : ℤ), (e = 1 ∨ e = -1) ∧
      MulAut.conj y * β ^ e * (MulAut.conj y)⁻¹ =
        MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ ∧
      Units.map σ.toRingHom.toMonoidHom d = d ∧ d ^ 3 = 1 ∧ d ≠ 1 ∧
      (s : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![1, 1, d, 1] := by
  have hβ1 : β ≠ 1 := fun h => hβout (h ▸ one_mem _)
  have hβord : orderOf β = 3 := orderOf_eq_prime hβ3 hβ1
  obtain ⟨g, hg, hβ | hβ⟩ :=
    d4_outer_three_normal_form hℓ hℓ2 hf K hK σ hσ β hβord hβout
  · obtain ⟨y, s, d, hconj, hd, hd3, hsd⟩ :=
      exists_conj_toral_of_cocycle hℓ hℓ2 hℓ3 hf hq hK σ hσ g hg
    by_cases hd1 : d = 1
    · exfalso
      apply hβG
      have hs1 : s = 1 := by
        apply Subtype.ext
        show (s : ModGL TwistTag.D4.tag K) = 1
        rw [hsd, hd1, ← rootDiagUnit_one (τ := TwistTag.D4.tag) (K := K)]
        exact congrArg _ (funext fun i => by fin_cases i <;> rfl)
      refine ⟨MulAut.conj y, Or.inl ?_⟩
      have h : MulAut.conj y * β * (MulAut.conj y)⁻¹ =
          fieldActor (t := TwistTag.D4) σ σ := by
        rw [hβ]
        have hR : MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ =
            fieldActor (t := TwistTag.D4) σ σ := by
          rw [hs1, map_one, one_mul]
        rw [hR] at hconj
        exact hconj
      simpa [tauAut] using h
    · exact ⟨y, s, d, 1, Or.inl rfl, by rw [hβ]; exact hconj, hd, hd3, hd1, hsd⟩
  · obtain ⟨y, s, d, hconj, hd, hd3, hsd⟩ :=
      exists_conj_toral_of_cocycle hℓ hℓ2 hℓ3 hf hq hK σ hσ g hg
    by_cases hd1 : d = 1
    · exfalso
      apply hβG
      have hs1 : s = 1 := by
        apply Subtype.ext
        show (s : ModGL TwistTag.D4.tag K) = 1
        rw [hsd, hd1, ← rootDiagUnit_one (τ := TwistTag.D4.tag) (K := K)]
        exact congrArg _ (funext fun i => by fin_cases i <;> rfl)
      have h : MulAut.conj y * β⁻¹ * (MulAut.conj y)⁻¹ =
          fieldActor (t := TwistTag.D4) σ σ := by
        rw [hβ]
        have hR : MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ =
            fieldActor (t := TwistTag.D4) σ σ := by
          rw [hs1, map_one, one_mul]
        rw [hR] at hconj
        exact hconj
      refine ⟨MulAut.conj y, Or.inr ?_⟩
      have hinv := congrArg (fun φ : MulAut (C0 σ) => φ⁻¹) h
      have e : (MulAut.conj y * β⁻¹ * (MulAut.conj y)⁻¹)⁻¹ =
          MulAut.conj y * β * (MulAut.conj y)⁻¹ := by group
      rw [e] at hinv
      simpa [tauAut] using hinv
    · refine ⟨y, s, d, -1, Or.inr rfl, ?_, hd, hd3, hd1, hsd⟩
      simp only [zpow_neg_one]
      rw [hβ]
      exact hconj

end CFSG.LieType.SeitzGeneration.ExcWideThree.A2Uni
