module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Types
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Plane
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Red
public import CFSG.LieType.SeitzGeneration.SeitzStatus

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.HardMathSupport.Timmesfeld.CrossChar

section Eight

set_option linter.unusedSectionVars false


@[expose] def TwE6EightA1A4 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (E : Subgroup (MulAut (twistedE6RootGroup K σ))), TwE6Cube K σ q E → q = 8 →
      ∀ f ∈ E, f ≠ 1 → TwE6LineDim K σ f 28 →
        fixedPoints (Subgroup.zpowers f) ≤ seitzHyperGamma 3 E

theorem fixedPoints_le_hyperGamma_of_line (hS : AGLEmbeddingD2.KFactSeitzRankTwo)
    (hEight : TwE6EightA1A4) (hStr : TwE6LineStructure') {K : Type} [Field K] [Finite K]
    {σ : K ≃+* K} {q : ℕ} {E : Subgroup (MulAut (twistedE6RootGroup K σ))}
    (hcube : TwE6Cube K σ q E) {f : MulAut (twistedE6RootGroup K σ)} (hfE : f ∈ E) (hf1 : f ≠ 1)
    (hty : ∀ s : twistedE6RootGroup K σ, f = MulAut.conj s → twE6FixDim K σ s ≠ 24) :
    fixedPoints (Subgroup.zpowers f) ≤ seitzHyperGamma 3 E := by
  classical
  by_cases hex : q = 8 → ∀ h : twistedE6InndiagGL K σ, twistedE6InndiagConj K σ h = f →
      twE6MatFixDim K σ h ≠ 28
  · obtain ⟨hcomp, hgen⟩ := hStr K σ q E hcube f hfE hf1 hty hex
    have hJ : ∀ J : Subgroup (twistedE6RootGroup K σ),
        CFSG.Open.IsComponentOf J (fixedPoints (Subgroup.zpowers f)) →
          J ≤ seitzHyperGamma 3 E := by
      intro J hJ
      obtain ⟨hJE, hJT⟩ := hcomp J hJ
      exact component_le_hyperGamma_of_plane' hS E hcube.elemAbelian hcube.card_E f hfE hf1 J hJ
        hJT hJE
    have hhyp : (⨆ (F : Subgroup (MulAut (twistedE6RootGroup K σ)))
        (_ : F ≤ E ∧ F.relIndex E = 3 ∧ f ∈ F), fixedPoints F) ≤ seitzHyperGamma 3 E :=
      iSup₂_le fun F' hF' => KSNotAll24.fixedPoints_le_hyperGamma hF'.1 hF'.2.1
    exact hgen.trans (sup_le (sSup_le fun J hJ' => hJ J hJ') hhyp)
  · push Not at hex
    obtain ⟨hq8, h, hh, hd⟩ := hex
    exact hEight K σ q E hcube hq8 f hfE hf1 ⟨h, hh, hd⟩

theorem twE6NotAll24Plane_of_eight (hS : AGLEmbeddingD2.KFactSeitzRankTwo)
    (hEight : TwE6EightA1A4) (hStr : TwE6LineStructure') : TwE6NotAll24Plane := by
  intro K _ _ σ q hK3 hσ hKq h3 hq2 E hE hEc hED hEi hER hnot
  classical
  have hZ := exceptional_fixed_center_trivial TwistTag.E6 K σ
  have hconj : ∀ a b : twistedE6RootGroup K σ,
      (MulAut.conj a : MulAut (twistedE6RootGroup K σ)) = MulAut.conj b → a = b := by
    intro a b h
    have hc : b⁻¹ * a ∈ Subgroup.center (twistedE6RootGroup K σ) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have hx2 := congrArg (fun φ : MulAut (twistedE6RootGroup K σ) => φ x) h
      simp only [MulAut.conj_apply] at hx2
      calc x * (b⁻¹ * a) = b⁻¹ * (b * x * b⁻¹) * a := by group
        _ = b⁻¹ * a * x := by
          rw [← hx2]
          group
    rw [hZ] at hc
    exact (inv_mul_eq_one.1 (Subgroup.mem_bot.1 hc)).symm
  obtain ⟨s, hsE, hs1, hs24⟩ : ∃ s : twistedE6RootGroup K σ, MulAut.conj s ∈ E ∧ s ≠ 1 ∧
      twE6FixDim K σ s ≠ 24 := by
    unfold TwE6InnerAll24 at hnot
    push Not at hnot
    exact hnot
  have hc1 : (MulAut.conj s : MulAut (twistedE6RootGroup K σ)) ≠ 1 := fun h =>
    hs1 (hconj s 1 (by rw [h, map_one]))
  have hc3 : (MulAut.conj s : MulAut (twistedE6RootGroup K σ)) ^ 3 = 1 := hE.2 _ hsE
  obtain ⟨F, hFE, hFc, hsF, hFi⟩ := exists_plane_through_inner_outer E hE hEi s hsE hc1
  refine ⟨F, hFE, hFc, fun f hfF hf1 x hfx => ?_⟩
  have hfE : f ∈ E := hFE hfF
  have hty : ∀ s' : twistedE6RootGroup K σ, f = MulAut.conj s' → twE6FixDim K σ s' ≠ 24 := by
    intro s' hs'
    have hfI : f ∈ twistedE6Inn K σ := hs' ▸ ⟨s', rfl⟩
    have hmem : f ∈ Subgroup.zpowers (MulAut.conj s : MulAut (twistedE6RootGroup K σ)) :=
      KSNotAll24.mem_zpowers_of_mem_inf hFc hFi hsF ⟨s, rfl⟩ hc1 hc3 hfF hfI
    rcases KSNotAll24.eq_or_eq_inv_of_mem_zpowers hc3 hc1 hmem hf1 with h | h
    · rw [hconj s' s (hs'.symm.trans h)]
      exact hs24
    · rw [hconj s' s⁻¹ (hs'.symm.trans (h.trans (map_inv _ s).symm)), KSNotAll24.twE6FixDim_inv]
      exact hs24
  have hcube : TwE6Cube K σ q E :=
    ⟨hK3, hσ, hKq, h3, hq2, hE, hEc, hED, hEi, hER⟩
  have hxfix : x ∈ fixedPoints (Subgroup.zpowers f) := by
    have hle : Subgroup.zpowers f ≤ MulAction.stabilizer (MulAut (twistedE6RootGroup K σ)) x :=
      Subgroup.zpowers_le.2 hfx
    intro φ hφ
    exact hle hφ
  exact fixedPoints_le_hyperGamma_of_line hS hEight hStr hcube hfE hf1 hty hxfix

end Eight

section Closed

set_option linter.unusedSectionVars false


theorem twE6NotAll24Gen_of_eight (hEight : TwE6EightA1A4) (hStr : TwE6LineStructure') :
    TwE6NotAll24Gen :=
  twE6NotAll24Gen_of_plane CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
    (twE6NotAll24Plane_of_eight CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds hEight hStr)

end Closed

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
