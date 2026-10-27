module

public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.OddOrder.TypeIIntersectionInSupportingKernel

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup Prep06 Pointwise
open CFSG.FeitThompson.Prep05
  (IsMinimalSimpleOdd centralizerIn)
open CFSG.FeitThompson.Prep09
  (IsMinimalSimpleOddOrder coreFixedSet centIn sigmaSignalizerOn sigmaSignalizerOn_of_mem)

universe u

variable {G : Type u} [Group G]

theorem sigSignalizer_eq_sigmaSignalizer [Finite G] (x : G) :
    sigSignalizer x = _root_.CFSG.FeitThompson.sigmaSignalizer x := (rfl)

theorem inf_centralizer_hallCoreIn_eq_bot_of_notMem
    (h₁ : _root_.CFSG.FeitThompson.Statements.FPF_type_I_frobenius.{u})
    [Finite G] (hG : IsMinimalSimpleOdd G) {T : Subgroup G}
    (hT : IsCoatom T) (hTI : IsTypeI T) {y : G} (hyT : y ∈ T) (hyH : y ∉ hallCoreIn T) :
    hallCoreIn T ⊓ centralizer ({y} : Set G) = ⊥ := by
  obtain ⟨E, -, -, hsemi, hfree⟩ := h₁ G hG T hT hTI
  have hmul : ((hallCoreIn T : Subgroup G) : Set G) * (E : Set G) = (T : Set G) :=
    hsemi.coe_eq_mul.symm
  have hdisj : hallCoreIn T ⊓ E = ⊥ := hsemi.inf_eq_bot
  have : ((hallCoreIn T).subgroupOf T).Normal := hsemi.normal_subgroupOf
  have hCH : ∀ e ∈ E, e ≠ 1 → hallCoreIn T ⊓ centralizer ({e} : Set G) = ⊥ := by
    intro e he he1
    have h := hfree e he he1
    rwa [centralizerIn, centralizer_coe_zpowers] at h
  exact inf_centralizer_singleton_eq_bot_of_mem_of_notMem hmul hdisj hCH hyT hyH

theorem FTS_all_type_I_core_centralizer_control
    (h₁ : _root_.CFSG.FeitThompson.Statements.FPF_type_I_frobenius.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FTS_type_I_dade_support.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_all_type_I_core_centralizer_control.{u} := by
  intro G _ _ hG hallI M hM
  have hG5 : IsMinimalSimpleOdd G := ⟨hG.odd, hG.simple, hG.nonabelian, hG.solvable⟩
  have hG9 : IsMinimalSimpleOddOrder G := ⟨hG.odd, hG.simple, hG.nonabelian, hG.solvable⟩
  have hD := h₂ G hG9 M hM (hallI M hM)
  have hS : sigmaCore M = hallCoreIn M := hD.1
  have key : ∀ h ∈ (hallCoreIn M : Set G) \ {1},
      centralizer ({h} : Set G) ≤ M ∧ sigSignalizer h = ⊥ := by
    intro h hh
    obtain ⟨hhH, hh1⟩ := hh
    simp only [Set.mem_singleton_iff] at hh1
    have hmem : h ∈ coreFixedSet (hallCoreIn M) M := by
      refine ⟨hallCoreIn_le M hhH, hh1, ?_⟩
      intro hbot
      have hself : h ∈ centIn (hallCoreIn M) {h} :=
        ⟨hhH, by simp [Subgroup.mem_centralizer_singleton_iff]⟩
      rw [hbot] at hself
      exact hh1 (by simpa using hself)
    have hle : centralizer ({h} : Set G) ≤ M := by
      by_contra hnot
      obtain ⟨-, T, hTuniq, -, -, -, hTI', -⟩ := hD.2.2.2.2.2.2.2.2 h hmem hnot
      obtain ⟨⟨hhT, -, hcne⟩, hhnot⟩ := hTI' (hallI T hTuniq.isCoatom)
      exact hcne (inf_centralizer_hallCoreIn_eq_bot_of_notMem h₁ hG5 hTuniq.isCoatom
        (hallI T hTuniq.isCoatom) hhT (fun hc => hhnot ⟨hc, by simpa using hh1⟩))
    refine ⟨hle, ?_⟩
    obtain ⟨hRle, -, -, hRinf⟩ := hD.2.2.2.1 h hmem
    rw [sigmaSignalizerOn_of_mem (by rw [hS]; exact hhH) hh1] at hRle hRinf
    rw [sigSignalizer_eq_sigmaSignalizer, ← hRinf]
    exact (inf_eq_left.2 (le_inf (hRle.trans hle) hRle)).symm
  refine ⟨key, ?_⟩
  rw [sigDelta_eq, hS]
  ext z
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop]
  constructor
  · rintro ⟨x, hx, g, -, ⟨r, hr, rfl⟩, rfl⟩
    rw [(key x hx).2] at hr
    simp only [coe_bot, Set.mem_singleton_iff] at hr
    exact ⟨g, x, hx, by rw [hr, mul_one]⟩
  · rintro ⟨g, x, hx, rfl⟩
    refine ⟨x, hx, g, x, ⟨1, ?_, mul_one x⟩, rfl⟩
    rw [(key x hx).2]
    simp

end

end CFSG.FeitThompson.Proofs
