module

public import CFSG.Assembly.OddCoreElimination.TwoGroups

public section

namespace CFSG.Assembly.Dichotomy

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oddCoreSpan_ne_bot_of_mem {E : Subgroup G} {t : G} (htE : t ∈ E) (ht : orderOf t = 2)
    (hne : oddCore (Subgroup.centralizer ({t} : Set G)) ≠ ⊥) : oddCoreSpan E ≠ ⊥ := by
  intro hbot
  apply hne
  have hle := involutionOddCore_le_span E htE (by rintro rfl; simp at ht)
  rw [hbot, le_bot_iff, involutionOddCore,
    Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)] at hle
  exact hle

theorem oddCore_centralizer_eq_bot_of_steps (hcov : PerfectInvolutionCoverageStatement)
    (hprep : CompletedSpanPreparationStatement) (hcent : CentralInvolutionCentralizerStatement)
    (hfus : FusionControlStatement) (heq : FourSpanEqualizationStatement)
    (hemb : CommonSpanStrongEmbeddingStatement)
    (hperf : commutator G = ⊤) (hO : oddCore G = ⊥) (hrank : 3 ≤ twoRank G)
    (hcomp : ¬ IsComponentType G) (hse : ∀ M : Subgroup G, ¬ dichotomyStronglyEmbedded M)
    (hcompl : ∀ D : Subgroup G, IsElemAbelian 2 D → Nat.card D = 8 → OddCoreSpanCompleted D)
    (t : G) (ht : orderOf t = 2) : oddCore (Subgroup.centralizer ({t} : Set G)) = ⊥ := by
  by_contra hne
  obtain ⟨E, hE, hE8, htE⟩ := hcov G hperf hrank t ht
  have hEp : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x.1 x.2)⟩
  obtain ⟨S, hES⟩ := hEp.exists_le_sylow
  have hΩE := oddCoreSpan_ne_bot_of_mem htE ht hne
  have hS3 : 3 ≤ pRank 2 (S : Subgroup G) := (pRank_sylow_eq_twoRank S).symm ▸ hrank
  obtain ⟨U, hUS, hUn, hU, hU4, hpref⟩ : ∃ U : Subgroup G, U ≤ S ∧
      (S : Subgroup G) ≤ Subgroup.normalizer (U : Set G) ∧ IsElemAbelian 2 U ∧ Nat.card U = 4 ∧
      ((∃ V : Subgroup G, V ≤ subgroupCenter S ∧ IsElemAbelian 2 V ∧ Nat.card V = 4) →
        U ≤ subgroupCenter S) := by
    by_cases hc : ∃ V : Subgroup G, V ≤ subgroupCenter S ∧ IsElemAbelian 2 V ∧ Nat.card V = 4
    · obtain ⟨V, hVZ, hVe, hV4⟩ := hc
      refine ⟨V, hVZ.trans inf_le_left, fun s hs => Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.mpr fun v hv =>
          (Subgroup.mem_centralizer_iff.mp (hVZ hv).2 s hs).symm), hVe, hV4, fun _ => hVZ⟩
    · obtain ⟨V, hVS, hVn, hVe, hV4⟩ := exists_normal_four_of_three_le_pRank S.isPGroup' hS3
      exact ⟨V, hVS, hVn, hVe, hV4, fun h => absurd h hc⟩
  have hU1 : U ≠ ⊥ := by
    rintro rfl
    simp at hU4
  obtain ⟨z, hz, hz2⟩ := exists_involution_inf_subgroupCenter S.isPGroup' hUS hUn hU1
  obtain ⟨hWodd, hSW, hCW, hEW, hVW, hDW, hW1⟩ := hprep G hrank S U hUS hUn hU hU4 hcompl
  obtain ⟨-, hMG⟩ := hW1 ⟨E, hES, hE, hE8, hΩE⟩
  have hCz := hcent G hcomp S U hUS hUn hU hU4 hpref z hz hz2 (oddCoreSpan U) hWodd hSW
    (fun u hu hu1 => (hCW u hu hu1) ▸ inf_le_left)
  have hfc := hfus G S hS3 U hUS hUn hU hU4 z hz hz2 _ hSW hCz
    (fun V hVS hVe hV4 hV3 => (hVW V hVS hVe hV4 hV3).2) hDW
  have hV4 := heq G hperf hrank S (oddCoreSpan U) hSW
    (fun V hVS hVe hV4 hV3 => (hVW V hVS hVe hV4 hV3).1)
    (fun P hPS hP g hg => hfc P (hPS.trans hSW) hP g (hg.trans hSW))
  exact hse _ (hemb G hperf hrank hcomp S (oddCoreSpan U) hSW (hMG hO) hV4 hfc).2

end CFSG.Assembly.Dichotomy
