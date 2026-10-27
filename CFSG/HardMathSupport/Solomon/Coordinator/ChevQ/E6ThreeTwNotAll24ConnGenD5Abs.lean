module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenCore
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenUni
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenD5Perf
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreD5Class

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSGen

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn
  CFSG.HardMathSupport.Lang.TwE6Step3

set_option linter.unusedSectionVars false


@[expose] def D5TorusLang : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup Tag.E6 L p₀)
    (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) → S.D.Φ = twistHom TwistTag.E6 L Fr →
    ((3 : ℕ) : L) ≠ 0 → 3 ∣ S.D.q + 1 → S.D.q ≠ 2 →
    ∀ a : Fin Tag.E6.rank → Lˣ, rootDiagUnit Tag.E6 a ∈ S.D.torus → (∀ i, a i ^ 3 = 1) →
    (kernelRoots (rootCharHom a)).ncard = 40 →
    ∀ s ∈ torusGroup Tag.E6 L ⊓ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)),
      ∃ t ∈ torusGroup Tag.E6 L ⊓ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)),
        t⁻¹ * S.D.step t = s

@[expose] def D5FixedRational : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup Tag.E6 L p₀)
    (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) → S.D.Φ = twistHom TwistTag.E6 L Fr →
    ((3 : ℕ) : L) ≠ 0 → 3 ∣ S.D.q + 1 → S.D.q ≠ 2 →
    ∀ a : Fin Tag.E6.rank → Lˣ, rootDiagUnit Tag.E6 a ∈ S.D.torus → (∀ i, a i ^ 3 = 1) →
    (kernelRoots (rootCharHom a)).ncard = 40 →
    ∀ i : KernelComponent (rootCharHom a),
      ∀ g ∈ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)), S.D.step g = g →
        g ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i

theorem d5FixedRational_of_perfect (hP : D5FixedSpinPerfect) : D5FixedRational := by
  classical
  intro L _ _ p₀ S Fr hFr hΦ h3 h3q hq2 a hT hap hk i g hg hgF
  have hperf := hP L p₀ S Fr hFr hΦ h3 h3q hq2 a hT hap hk
  have hfin : (kernelRoots (rootCharHom a)).Finite :=
    (CFSG.Blueprint.Chevalley.finite_setOf_isRoot Tag.E6).subset fun γ hγ => hγ.1
  obtain ⟨-, -, -, -, hn, -⟩ := d5_class_data h3 hap hk i
  have hΨk : componentRoots (rootCharHom a) i = kernelRoots (rootCharHom a) :=
    Set.eq_of_subset_of_ncard_le (fun γ hγ => hγ.1) (by rw [hk, hn]) hfin
  have hrat : rationalRoots S.ρ (rootCharHom a) i = kernelRoots (rootCharHom a) := by
    refine Set.Subset.antisymm ?_ fun γ hγ => ⟨0, γ, by rw [hΨk]; exact hγ, rfl⟩
    rintro _ ⟨k, δ, hδ, rfl⟩
    rw [hΨk] at hδ
    induction k with
    | zero => exact hδ
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact rho_mem_kernelRoots_of_mem_torus S hT _ ih
  have hadj : rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) ≤ adjointGroup Tag.E6 L :=
    iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α
  have hgP : g ∈ rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) ⊓ S.D.model :=
    Subgroup.mem_inf.2 ⟨hg, S.D.mem_model.2 ⟨hadj hg, hgF⟩⟩
  have hle : rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) ⊓ S.D.model ≤
      rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) ⊓ S.Γ := by
    refine le_inf inf_le_left ?_
    calc rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) ⊓ S.D.model
        = ⁅rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) ⊓ S.D.model,
            rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) ⊓ S.D.model⁆ := hperf.symm
      _ ≤ ⁅S.D.model, S.D.model⁆ := Subgroup.commutator_mono inf_le_right inf_le_right
      _ = S.Γ := rfl
  have hg' : g ∈ ⁅rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) ⊓ S.D.model,
      rootSpan Tag.E6 L (kernelRoots (rootCharHom a)) ⊓ S.D.model⁆ := by
    rw [hperf]
    exact hgP
  have h2 := Subgroup.commutator_mono hle hle hg'
  rw [rationalComponent, rationalSpan, hrat]
  exact h2

theorem twE6ConnFixed_40_of (hLang : D5TorusLang) (hFix : D5FixedRational) :
    TwE6ConnFixed 40 := by
  classical
  intro L _ _ p₀ S Fr hFr hΦ h3 h3q hq2 a hT hap hk x hx hxF
  have hfin : (kernelRoots (rootCharHom a)).Finite :=
    (CFSG.Blueprint.Chevalley.finite_setOf_isRoot Tag.E6).subset fun γ hγ => hγ.1
  obtain ⟨α, hα⟩ : (kernelRoots (rootCharHom a)).Nonempty := by
    rw [← Set.ncard_pos hfin, hk]
    norm_num
  let i : KernelComponent (rootCharHom a) := ⟦⟨α, hα⟩⟧
  obtain ⟨_, _, -, -, hmodel⟩ := d5_class_strongModel S hFr hΦ h3 hT hap h3q hk i
  have hquasi : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := hmodel.2.1
  obtain ⟨r, e, hr, hchar, he, hq⟩ := S.exists_char_pow
  haveI : Fact r.Prime := ⟨hr⟩
  haveI := hchar
  obtain ⟨t, htH, htF, g, hgQ, hgF, rfl⟩ := exists_fixed_split S.D.step
    (H := torusGroup Tag.E6 L) (Q := rootSpan Tag.E6 L (kernelRoots (rootCharHom a)))
    (fun a ha b hb => torusGroup_comm ha hb)
    (CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan (fun γ hγ => hγ.1))
    (fun h hh => step_mem_torusGroup S hq hh)
    (fun g hg => step_mem_rootSpan S (fun γ hγ => hγ.1)
      (fun γ hγ => rho_mem_kernelRoots_of_mem_torus S hT γ hγ) hg)
    (hLang L p₀ S Fr hFr hΦ h3 h3q hq2 a hT hap hk) hx hxF
  refine ⟨t, htF, fun s hs => torusGroup_comm hs htH, g, ?_, rfl⟩
  have hgR : g ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    hFix L p₀ S Fr hFr hΦ h3 h3q hq2 a hT hap hk i g hgQ hgF
  exact Subgroup.mem_iSup_of_mem i (Subgroup.mem_iSup_of_mem hquasi hgR)

end KSGen

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
