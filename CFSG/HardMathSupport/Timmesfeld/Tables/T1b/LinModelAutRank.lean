module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.LinModelAut
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Tables112Lie

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.Assembly.LowTwoRank

@[expose] def diagGcd : StatedLieTag → ℕ → ℕ → ℕ → ℕ
  | .PSL, n, r, f => Nat.gcd n (r ^ f - 1)
  | .PSU, n, r, f => Nat.gcd n (r ^ f + 1)
  | _, _, _, _ => 1

theorem finite_mulAut_of_finite (X : Type) [Group X] [Finite X] : Finite (MulAut X) :=
  Finite.of_injective (fun α : MulAut X => (α : X → X)) fun _ _ h => MulEquiv.ext (congrFun h)

theorem pRank_mulAut_le_of_model {X : Type} [Group X] [Finite X] {t : StatedLieTag}
    {n r f p : ℕ} (hm : StatedClassicalModel X t n r f) (ht : t = .PSL ∨ t = .PSU)
    (hn : 3 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2) (hpg : p ∣ diagGcd t n r f) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤ n := by
  have := finite_mulAut_of_finite X
  refine CFSG.SectionRank.pRank_le hp.one_lt (fun E _ hE => ?_)
  rcases ht with rfl | rfl
  · exact card_le_pow_of_psl_model hm hn hp hp2 hpg E hE
  · exact card_le_pow_of_psu_model hm hp hp2 hpg E hE

theorem pRank_mulAut_le_succ_of_model {X : Type} [Group X] [Finite X] {t : StatedLieTag}
    {n r f p : ℕ} (hm : StatedClassicalModel X t n r f) (ht : t = .PSL ∨ t = .PSU)
    (hn : 3 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2) (hpg : p ∣ diagGcd t n r f)
    (hg : ¬ p ^ 2 ∣ diagGcd t n r f) (hcen : Subgroup.center X = ⊥) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤ CFSG.Open.pRank p (⊤ : Subgroup X) + 1 := by
  have := finite_mulAut_of_finite X
  refine CFSG.HardMathSupport.Timmesfeld.Coordinator.pRank_mulAut_le_of_meets hp hcen 1
    (fun D hD hc => ?_)
  have hc' : Nat.card D = p ^ 2 := hc
  rcases ht with rfl | rfl
  · exact meets_inner_of_psl_model hm hn hp hp2 hpg hg D hD hc'
  · exact meets_inner_of_psu_model hm hp hp2 hpg hg D hD hc'

theorem classicalModel_of_lieModel_psl {X : Type} [Group X] {n r f : ℕ}
    (hm : CFSG.Blueprint.LieModel X .PSL n r f) : StatedClassicalModel X .PSL n r f :=
  CFSG.Blueprint.LieModel.statedClassicalModel hm (by decide)

theorem classicalModel_of_lieModel_psu {X : Type} [Group X] {n r f : ℕ}
    (hm : CFSG.Blueprint.LieModel X .PSU n r f) : StatedClassicalModel X .PSU n r f :=
  CFSG.Blueprint.LieModel.statedClassicalModel hm (by decide)

theorem psl_facts_of_not_easy {n r f p : ℕ}
    (h : ¬ (3 ≤ n → ¬ p ∣ Nat.gcd n (r ^ f - 1))) : 3 ≤ n ∧ p ∣ Nat.gcd n (r ^ f - 1) := by
  by_cases hn : 3 ≤ n
  · exact ⟨hn, not_not.1 fun h' => h fun _ => h'⟩
  · exact absurd (fun h3 => absurd h3 hn) h

theorem psu_facts_of_lieModel_of_not_easy {X : Type} [Group X] {n r f p : ℕ}
    (hm : CFSG.Blueprint.LieModel X .PSU n r f) (h : ¬ ¬ p ∣ Nat.gcd n (r ^ f + 1)) :
    3 ≤ n ∧ ¬(n = 3 ∧ r ^ f = 2) ∧ p ∣ Nat.gcd n (r ^ f + 1) := by
  obtain ⟨⟨-, -, hn3, hne⟩, -⟩ := classicalModel_of_lieModel_psu hm
  exact ⟨hn3, fun ⟨h1, h2⟩ => hne (by rw [h1, h2]), not_not.1 h⟩

theorem psl_facts_of_lieModel_of_not_easy {X : Type} [Group X] {n r f p : ℕ}
    (hm : CFSG.Blueprint.LieModel X .PSL n r f)
    (h : ¬ (3 ≤ n → ¬ p ∣ Nat.gcd n (r ^ f - 1))) :
    StatedClassicalModel X .PSL n r f ∧ 3 ≤ n ∧ p ∣ Nat.gcd n (r ^ f - 1) :=
  ⟨classicalModel_of_lieModel_psl hm, psl_facts_of_not_easy h⟩

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
