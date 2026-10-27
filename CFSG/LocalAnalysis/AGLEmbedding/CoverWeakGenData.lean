module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeSporAlt
import CFSG.LocalAnalysis.AGLEmbedding.CoverWeakGenDataAux
import CFSG.LocalAnalysis.AGLEmbedding.SporCaseThreeDataAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

theorem coverWeakGen_of_coverPointDatum {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hdat : CoverPointDatum X p) : CoverWeakGen X p := by
  intro K _ _ π hπ hker _ hZ1 hZp hZc T
  obtain ⟨D, k, b, l, hel, e, hn, hF, hb, hconj, hgen⟩ := hdat
  have hp : p.Prime := Fact.out
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  have hπZ : ∀ z ∈ Subgroup.center K, π z = 1 := fun z hz =>
    MonoidHom.mem_ker.mp (hker.symm ▸ hz)
  obtain ⟨T₀, hT₀⟩ := (D.isPGroup_comap π (hker ▸ hZp)).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K T₀ T
  refine glbWeakCore_eq_top_of_mulEquiv hp (MulAut.conj g)
    (by rw [← hg, Sylow.coe_subgroup_smul]; rfl) ?_
  have hn0 : 0 < D.n := by rcases hn with hn | hn <;> omega
  have ha : D.a ⟨0, hn0⟩ ≠ 1 := by
    intro h0
    have h1 := congrFun (D.elt_injective (show D.elt (Pi.single ⟨0, hn0⟩ 1) = D.elt 0 by
      rw [D.elt_single, D.elt_zero, h0])) ⟨0, hn0⟩
    simp at h1
  obtain ⟨E₀, -, hE₀, -, hE₀3⟩ :=
    D.exists_commutative_overgroup π hp hp2 hπ hker hZ1 hZp hZc hF hn (D.a_mem_span _) ha
  have hNA : Subgroup.normalizer ((D.span.comap π : Subgroup K) : Set K) ≤
      GLBWeakCore p (T₀ : Subgroup K) := by
    have h3 := hE₀3.trans (pRank_mono p hp hE₀)
    exact normalizer_le_weakCore p hT₀ (by omega) (h3.trans (pRank_mono p hp le_sup_left))
  have hNQ : ∀ j, Subgroup.normalizer (((Subgroup.zpowers (b j)).comap π : Subgroup K) : Set K) ≤
      GLBWeakCore p (T₀ : Subgroup K) := by
    intro j
    obtain ⟨E, hQE, hEA, hEc, hE3⟩ :=
      D.exists_commutative_overgroup π hp hp2 hπ hker hZ1 hZp hZc hF hn (hb j).1 (hb j).2
    exact normalizer_le_weakCore_of_commutative_overgroup p hp (hEA.trans hT₀) hQE hEc
      (D.two_le_pRank_comap_zpowers π hp hp2 hπ hker hZ1 hZp hZc hF (hb j).1 (hb j).2) hE3
  have hZ : Subgroup.center K ≤ GLBWeakCore p (T₀ : Subgroup K) := fun z hz =>
    hNA (Subgroup.le_normalizer_comap π (by rw [Subgroup.mem_comap, hπZ z hz]; exact one_mem _))
  have hmap : (GLBWeakCore p (T₀ : Subgroup K)).map π = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro u (⟨i, rfl⟩ | hu)
    · refine ⟨Function.surjInv hπ (D.g i), hNA (Subgroup.le_normalizer_comap π ?_),
        Function.surjInv_eq hπ _⟩
      rw [Subgroup.mem_comap, Function.surjInv_eq hπ]
      exact D.g_mem_normalizer i
    · obtain ⟨j, i, rfl⟩ := Set.mem_iUnion.mp hu
      refine ⟨Function.surjInv hπ (hel j i), hNQ j (Subgroup.le_normalizer_comap π ?_),
        Function.surjInv_eq hπ _⟩
      rw [Subgroup.mem_comap, Function.surjInv_eq hπ]
      exact mem_normalizer_zpowers_of_conj_eq_pow (hconj j i)
  rw [← Subgroup.comap_map_eq_self (H := GLBWeakCore p (T₀ : Subgroup K)) (hker ▸ hZ), hmap,
    Subgroup.comap_top]

end CFSG.AGLEmbedding
