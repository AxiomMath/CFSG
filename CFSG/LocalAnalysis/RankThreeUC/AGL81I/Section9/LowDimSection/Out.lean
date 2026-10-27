module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.LowDimSection.Inputs
import CFSG.Adapters.StatedPSLTwo
import CFSG.Open.StatedZModTwo

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.Assembly.LowTwoRank

private theorem not_mulEquiv_psl_two_three (T : Type) [Group T] [Finite T] [IsSimpleGroup T]
    (hT : ∃ a b : T, a * b ≠ b * a)
    (e : T ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 3)) :
    False := by
  have h60 := CFSG.GroupTheory.nonabelian_simple_order_at_least_sixty (G := T) inferInstance hT
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) = 24 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hle : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 3)) ≤ 24 :=
    hSL ▸ Nat.le_of_dvd (by rw [hSL]; norm_num) (Subgroup.card_quotient_dvd_card _)
  rw [Nat.card_congr e.toEquiv] at h60
  omega

private theorem statedClassicalModel_gl_three_two (T : Type) [Group T]
    (e : T ≃* GL (Fin 3) (ZMod 2)) : StatedClassicalModel T .PSL 3 2 1 := by
  have h := StatedAPI.statedSL_eq_top_of_card_two (K := ZMod 2) (by simp) 3
  exact StatedAPI.statedClassicalModel_psl_of_mulEquiv_statedSL_zmod_two le_rfl
    ((e.trans Subgroup.topEquiv.symm).trans (MulEquiv.subgroupCongr h.symm))

private theorem statedClassicalModel_psl_three (q : ℕ) [Fact q.Prime] (T : Type) [Group T]
    (e : T ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod q)) :
    StatedClassicalModel T .PSL 3 q 1 :=
  ⟨⟨Fact.out, le_rfl, by omega, fun h => absurd (congrArg Prod.fst h) (by omega),
      fun h => absurd (congrArg Prod.fst h) (by omega)⟩,
    ZMod q, inferInstance, inferInstance, by rw [Nat.card_zmod, pow_one],
    ⟨e.trans (projectiveSpecialLinearGroupEquivStatedProj 3 (ZMod q))⟩⟩

private theorem statedClassicalModel_psp_four (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (T : Type)
    [Group T] (e : T ≃* StatedProj (StatedSp 2 (ZMod q))) : StatedClassicalModel T .PSp 2 q 1 :=
  ⟨⟨Fact.out, le_rfl, le_rfl, fun h => hq2 (by simpa using congrArg Prod.snd h)⟩,
    ZMod q, inferInstance, inferInstance, by rw [Nat.card_zmod, pow_one], ⟨e⟩⟩

private theorem inCatalog_of_alternating (T : Type) [Group T] {k : ℕ} (hk : 5 ≤ k)
    (h : Nonempty (T ≃* alternatingGroup (Fin k))) : CFSG.Assembly.InCatalog T :=
  ⟨.alternating k hk, h⟩

private theorem inCatalog_of_isLowDimSimpleSection
    (hcat : ∀ (G : Type) [Group G] (t : StatedLieTag) (n p f : ℕ),
      StatedClassicalModel G t n p f → CFSG.Assembly.InCatalog G)
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (T : Type) [Group T] [Finite T] [IsSimpleGroup T]
    (hT : ∃ a b : T, a * b ≠ b * a) (hL : IsLowDimSimpleSection q T) :
    CFSG.Assembly.InCatalog T := by
  have hq : q.Prime := Fact.out
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  unfold IsLowDimSimpleSection at hL
  rcases hL with h | h | h | h | h | h | h | h
  · obtain ⟨e⟩ := h
    rcases (show q = 3 ∨ 5 ≤ q by
      rcases Nat.lt_or_ge q 5 with h | h
      · interval_cases q
        · exact Or.inl rfl
        · exact absurd hq (by norm_num)
      · exact Or.inr h) with rfl | h5
    · exact (not_mulEquiv_psl_two_three T hT e).elim
    · exact hcat T _ _ _ _ (StatedAPI.statedClassicalModel_psl_two_of_mulEquiv_zmod hq h5 e)
  · obtain ⟨e⟩ := h
    exact hcat T _ _ _ _ (statedClassicalModel_psl_three q T e)
  · obtain ⟨e⟩ := h
    exact hcat T _ _ _ _ (statedClassicalModel_psp_four q hq2 T e)
  · obtain ⟨e⟩ := h
    exact hcat T _ _ _ _ (statedClassicalModel_psl_two_of_mulEquiv T q 2 (by nlinarith) e)
  · exact inCatalog_of_alternating T le_rfl h
  · exact inCatalog_of_alternating T (by norm_num) h
  · exact inCatalog_of_alternating T (by norm_num) h
  · obtain ⟨e⟩ := h
    exact hcat T _ _ _ _ (statedClassicalModel_gl_three_two T e)

theorem lowDimOutSolvable_of
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    (hcat : ∀ (G : Type) [Group G] (t : CFSG.Open.StatedLieTag) (n p f : ℕ),
      CFSG.Open.StatedClassicalModel G t n p f → CFSG.Assembly.InCatalog G) :
    LowDimOutSolvable := by
  intro q _ hq2 T _ _ _ hT hL
  have hab : ∃ a b : T, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact hT ⟨⟨h⟩⟩
  exact hS T hab (inCatalog_of_isLowDimSimpleSection hcat q hq2 T hab hL)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
