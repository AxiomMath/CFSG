module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.RatLayer
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsTwAux.ExcE6Layer

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KD4L
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KE6
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints)


section Lane


theorem ssTw_rho_stable_e6 {tau : Tag} [hτ : M27Ok tau] [E6Sub tau] {L : Type} [Field L]
    [IsAlgClosed L] {p0 : ℕ} (S : LangSetup tau L p0) {a : Fin tau.rank → Lˣ}
    (haT : rootDiagUnit tau a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (v : WeylGroup tau)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots tau (e6Nodes tau)) :
    ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i := by
  classical
  have h6 : 6 ≤ tau.rank := by rcases hτ.isE7E8 with rfl | rfl <;> decide
  rcases hτ.isE7E8 with rfl | rfl
  · refine S.rho_mem_componentRootsT haT i v hΨ (N := 0) (fun s hs => ?_)
      ⟨({Pi.single 0 1} : Finset (Fin Tag.E7.rank → ℤ)), fun α hα => ?_, by simp⟩
    · have := card_le_of_orth_e6 h6 [] (fun l hl h => absurd h (orth_e6_E7 l hl)) s hs
      simpa using this
    · rw [Finset.mem_singleton.1 hα]
      exact single_mem_parabolicRoots_e6 _ (by decide)
  · refine S.rho_mem_componentRootsT haT i v hΨ (N := 6) (fun s hs => ?_)
      ⟨({Pi.single 0 1, Pi.single 1 1, Pi.single 2 1, Pi.single 3 1, Pi.single 4 1,
        Pi.single 5 1, Pi.single 0 1 + Pi.single 2 1} : Finset (Fin Tag.E8.rank → ℤ)),
        fun α hα => ?_, by decide⟩
    · exact (card_le_of_orth_e6 h6 _ orth_e6_E8 s hs).trans (by decide)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hα
      rcases hα with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact single_mem_parabolicRoots_e6 _ (by decide)
      · exact single_mem_parabolicRoots_e6 _ (by decide)
      · exact single_mem_parabolicRoots_e6 _ (by decide)
      · exact single_mem_parabolicRoots_e6 _ (by decide)
      · exact single_mem_parabolicRoots_e6 _ (by decide)
      · exact single_mem_parabolicRoots_e6 _ (by decide)
      · refine ⟨isRoot_iff_mem_artifactRoots.2 (by decide), fun j hj => ?_⟩
        have key : ∀ j : Fin 8, ¬ (j.val ≤ 5) →
            ((Pi.single 0 1 + Pi.single 2 1 : Fin 8 → ℤ)) j = 0 := by decide
        exact key j hj

theorem ssTw_pgroup_e6 {tau : Tag} [M27Ok tau] [E6Sub tau] {L : Type} [Field L] [IsAlgClosed L]
    {p0 : ℕ} (S : LangSetup tau L p0) {a : Fin tau.rank → Lˣ}
    (haT : rootDiagUnit tau a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (v : WeylGroup tau)
    (hΨ : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots tau (e6Nodes tau))
    {l : ℕ} (hl : l.Prime) [CharP L l] (hl5 : 5 ≤ l) :
    ∃ V : Subgroup ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i), IsPGroup l V ∧
      8 ≤ Nat.card V := by
  classical
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨f, hf, hq⟩ := ssTw_exists_f S (ℓ := l)
  have hτ' : ∀ t : TwistTag, t.tag ≠ tau := by
    rcases M27Ok.isE7E8 (τ := tau) with rfl | rfl
    · exact twistTag_tag_ne_E7
    · exact twistTag_tag_ne_E8
  obtain ⟨w, hn⟩ := S.D.n_weyl
  have hρ := ssTw_rho_stable_e6 S haT i v hΨ
  have hw : ∀ γ ∈ componentRoots (rootCharHom a) i, w • γ ∈ componentRoots (rootCharHom a) i := by
    intro γ hγ
    rw [← S.rho_eq_smul hτ' hn hγ.1.1]
    exact hρ γ hγ
  obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted hτ'
  have hlayer : SsQB l (rootSpan tau L (componentRoots (rootCharHom a) i) ⊓ S.D.model) := by
    rw [hΨ]
    rw [hΨ] at hw
    refine ssTw_layer_untw S hq hFr hΦ hn v (e6Nodes tau) (SsQB l)
      (fun P g h => h.map_conj g) ?_
    intro n hn' hw'
    have hmaps : ∀ α ∈ parabolicRoots tau (e6Nodes tau),
        weylQuotientHom tau L ⟨n, hn'⟩ • α ∈ parabolicRoots tau (e6Nodes tau) := by
      intro α hα
      rw [hw']
      obtain ⟨β, hβ, hβe⟩ := hw (v • α) ⟨α, hα, rfl⟩
      rw [mul_smul, mul_smul, ← hβe, inv_smul_smul]
      exact hβ
    exact ⟨(e6Layer_finite_quasisimple tau (ℓ := l) hf hn' hmaps).2,
      ssBig_e6_layer hl5 hf hn' hmaps⟩
  exact ssTw_exists_pgroup_of_layer S i hρ hlayer

end Lane

end CFSG.HardMathSupport.Dickson.Sec6
