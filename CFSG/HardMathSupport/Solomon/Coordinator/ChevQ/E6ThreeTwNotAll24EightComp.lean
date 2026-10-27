module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Eight
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24EightL28
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnClause

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.HardMathSupport.Timmesfeld.CrossChar

namespace KSEight

section Restrict

variable {X : Type} [Group X]

@[expose] noncomputable def restrictAut (E : Subgroup (MulAut X)) (J : Subgroup X)
    (hJE : ∀ g ∈ E, J.map g.toMonoidHom = J) : E →* MulAut J where
  toFun g := ((g : MulAut X).subgroupMap J).trans (MulEquiv.subgroupCongr (hJE g g.2))
  map_one' := by
    ext x
    rfl
  map_mul' := by
    intro a b
    ext x
    rfl

theorem restrictAut_apply (E : Subgroup (MulAut X)) (J : Subgroup X)
    (hJE : ∀ g ∈ E, J.map g.toMonoidHom = J) (g : E) (x : J) :
    ((restrictAut E J hJE g x : J) : X) = (g : MulAut X) x :=
  rfl

theorem component_le_hyperGamma_of_l2Eight [Finite X] (E : Subgroup (MulAut X))
    (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 3) {f : MulAut X} (hf : f ∈ E)
    (hf1 : f ≠ 1) (J : Subgroup X) (hJf : ∀ x ∈ J, f x = x)
    (hJE : ∀ g ∈ E, J.map g.toMonoidHom = J) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ 3) (eJ : J ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hnot : ∀ g ∈ E, ∀ s ∈ J, orderOf s = 9 → g s ≠ s ^ 4 ∧ g s ≠ s ^ 7) :
    J ≤ seitzHyperGamma 3 E := by
  classical
  haveI : Finite (MulAut X) := inferInstance
  set ρ := restrictAut E J hJE with hρ
  obtain ⟨H, hHE, hHrel, hHJ⟩ : ∃ H : Subgroup (MulAut X), H ≤ E ∧ H.relIndex E = 3 ∧
      ∀ g ∈ H, ∀ x ∈ J, g x = x := by
    have hfker : (⟨f, hf⟩ : E) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker]
      ext x
      exact hJf x x.2
    have hf1' : (⟨f, hf⟩ : E) ≠ 1 := fun h => hf1 (congrArg Subtype.val h)
    have hf3' : (⟨f, hf⟩ : E) ^ 3 = 1 := Subtype.ext (by simpa using hE.2 f hf)
    have hfo : orderOf (⟨f, hf⟩ : E) = 3 := orderOf_eq_prime hf3' hf1'
    have h3ker : 3 ∣ Nat.card ρ.ker := by
      rw [← hfo]
      exact Subgroup.orderOf_dvd_natCard _ hfker
    have hidx := Subgroup.card_ker_mul_card_range ρ
    rw [hEc] at hidx
    have hAel : IsElemAbelian 3 ρ.range := by
      have h := (hE.subgroupOf E).map ρ
      rwa [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map] at h
    obtain ⟨m, hm⟩ := h3ker
    by_cases hA9 : Nat.card ρ.range = 9
    · exfalso
      obtain ⟨ψ, hψ, s, hs9, hψs⟩ :=
        KSEight.exists_pow_four_or_seven_of_plane hF eJ ρ.range hAel hA9
      obtain ⟨g, rfl⟩ := hψ
      have hs9' : orderOf (s : X) = 9 := by rw [Subgroup.orderOf_coe]; exact hs9
      obtain ⟨h4, h7⟩ := hnot g g.2 s s.2 hs9'
      rcases hψs with h | h
      · apply h4
        have := congrArg Subtype.val h
        rw [restrictAut_apply] at this
        rw [this, Subgroup.coe_pow]
      · apply h7
        have := congrArg Subtype.val h
        rw [restrictAut_apply] at this
        rw [this, Subgroup.coe_pow]
    ·
      have hA : Nat.card ρ.range = 1 ∨ Nat.card ρ.range = 3 := by
        have hrm : Nat.card ρ.range * m = 9 := by
          rw [hm] at hidx
          nlinarith
        have hdvd : Nat.card ρ.range ∣ 9 := ⟨m, hrm.symm⟩
        have h9 : Nat.card ρ.range ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd
        set r := Nat.card ρ.range with hr
        interval_cases r <;> omega
      rcases hA with h1 | h3
      ·
        obtain ⟨e, heE, hne⟩ :=
          CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.exists_mem_not_mem_zpowers hEc
            (hE.2 f hf)
        refine ⟨Subgroup.zpowers f ⊔ Subgroup.zpowers e,
          sup_le (Subgroup.zpowers_le.2 hf) (Subgroup.zpowers_le.2 heE),
          CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.relIndex_zpowers_sup_zpowers hE hEc
            hf heE hf1 hne, fun g hg x hx => ?_⟩
        have hgE : g ∈ E := sup_le (Subgroup.zpowers_le.2 hf) (Subgroup.zpowers_le.2 heE) hg
        have hρ1 : ρ ⟨g, hgE⟩ = 1 := by
          have hsub : Subsingleton ρ.range := (Nat.card_eq_one_iff_unique.1 h1).1
          have := Subsingleton.elim (⟨ρ ⟨g, hgE⟩, ⟨_, rfl⟩⟩ : ρ.range) ⟨1, Subgroup.one_mem _⟩
          exact congrArg Subtype.val this
        have h2 := congrArg (fun φ : MulAut J => ((φ ⟨x, hx⟩ : J) : X)) hρ1
        simp only [hρ, restrictAut_apply, MulAut.one_apply] at h2
        exact h2
      ·
        have hker9 : Nat.card ρ.ker = 9 := by
          rw [h3] at hidx
          omega
        refine ⟨ρ.ker.map E.subtype, Subgroup.map_subtype_le _, ?_, fun g hg x hx => ?_⟩
        · refine KSNotAll24.relIndex_eq_three (Subgroup.map_subtype_le _) hEc ?_
          rw [Subgroup.card_map_of_injective E.subtype_injective, hker9]
          norm_num
        · obtain ⟨g', hg', rfl⟩ := hg
          have h2 := congrArg (fun φ : MulAut J => ((φ ⟨x, hx⟩ : J) : X)) (MonoidHom.mem_ker.1 hg')
          simp only [hρ, restrictAut_apply, MulAut.one_apply] at h2
          exact h2
  intro x hx
  exact KSNotAll24.fixedPoints_le_hyperGamma hHE hHrel (fun g hg => hHJ g hg x hx)

end Restrict

end KSEight

section Assembly

set_option linter.unusedSectionVars false


@[expose] def TwE6EightGen : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (E : Subgroup (MulAut (twistedE6RootGroup K σ))), TwE6Cube K σ q E → q = 8 →
      ∀ f ∈ E, f ≠ 1 → TwE6LineDim K σ f 28 → TwE6LineGenAt K σ E f

@[expose] def TwE6EightComps : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (E : Subgroup (MulAut (twistedE6RootGroup K σ))), TwE6Cube K σ q E → q = 8 →
      ∀ f ∈ E, f ≠ 1 → TwE6LineDim K σ f 28 →
        ∀ J : Subgroup (twistedE6RootGroup K σ),
          CFSG.Open.IsComponentOf J (fixedPoints (Subgroup.zpowers f)) →
            (∀ g ∈ E, J.map g.toMonoidHom = J) ∧
            (TwE6ComponentType J ∨
              ((∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ 3 ∧
                  Nonempty (J ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) ∧
                ∀ s ∈ J, orderOf s = 9 → ∀ h : twistedE6InndiagGL K σ,
                  twistedE6InndiagConj K σ h s ≠ s ^ 4 ∧ twistedE6InndiagConj K σ h s ≠ s ^ 7))

theorem twE6EightA1A4_of_comps (hS : AGLEmbeddingD2.KFactSeitzRankTwo) (hG : TwE6EightGen)
    (hC : TwE6EightComps) : TwE6EightA1A4 := by
  intro K _ _ σ q E hcube hq8 f hfE hf1 hdim
  have hgen := hG K σ q E hcube hq8 f hfE hf1 hdim
  have hhyp : (⨆ (F : Subgroup (MulAut (twistedE6RootGroup K σ)))
      (_ : F ≤ E ∧ F.relIndex E = 3 ∧ f ∈ F), fixedPoints F) ≤ seitzHyperGamma 3 E :=
    iSup₂_le fun F' hF' => KSNotAll24.fixedPoints_le_hyperGamma hF'.1 hF'.2.1
  refine hgen.trans (sup_le (sSup_le fun J hJ => ?_) hhyp)
  obtain ⟨hJE, hJT | ⟨⟨F, _, _, hF, ⟨eJ⟩⟩, hsim⟩⟩ := hC K σ q E hcube hq8 f hfE hf1 hdim J hJ
  · exact component_le_hyperGamma_of_plane' hS E hcube.elemAbelian hcube.card_E f hfE hf1 J hJ
      hJT hJE
  · refine KSEight.component_le_hyperGamma_of_l2Eight E hcube.elemAbelian hcube.card_E hfE hf1 J
      (fun x hx => hJ.1 hx f (Subgroup.mem_zpowers f)) hJE hF eJ ?_
    intro g hg s hs hs9
    have hgD : g ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ := hcube.le_inndiag hg
    rw [← range_twistedE6InndiagConj] at hgD
    obtain ⟨h, rfl⟩ := hgD
    exact hsim s hs hs9 h

end Assembly

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
