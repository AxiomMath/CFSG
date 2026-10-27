module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18Thm3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18v

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

namespace S4B

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G}

theorem k18_Xi_class_not_conj (hc : Ctx13 t L S x₁ x₂ lam rho tau om) {w : G}
    (hw : w ∈ closure ({tau, om, lam} : Set G))
    (hH : ∀ {ξ : G}, ξ ∈ ctxXi t tau x₁ x₂ rho → (ξ * w) * (ξ * w) = 1 →
      ∃ η ∈ ctxXi t tau x₁ x₂ rho, ξ * w = η * w * η⁻¹)
    {g ξ : G} (hξ : ξ ∈ ctxXi t tau x₁ x₂ rho) (hg : g * t * g⁻¹ = ξ * w) : False := by
  have ht2 : t * t = 1 := by
    have h := (ctx13_relations hc).1
    rw [pow_two] at h; exact h
  have hsq : (ξ * w) * (ξ * w) = 1 := by
    rw [← hg]
    calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  obtain ⟨η, -, hη⟩ := hH hξ hsq
  apply k18_E32_not_conj hc hw (η⁻¹ * g)
  calc η⁻¹ * g * t * (η⁻¹ * g)⁻¹ = η⁻¹ * (g * t * g⁻¹) * η := by group
    _ = η⁻¹ * (ξ * w) * η := by rw [hg]
    _ = η⁻¹ * (η * w * η⁻¹) * η := by rw [hη]
    _ = w := by group

end S4B

@[expose] def Lemma418CaseAH1Stmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}
    (_hG : Sec4Glob G) (_hc : Ctx18A t L S x₁ x₂ lam rho tau om 𝒮) {ξ w : G},
    (w = lam ∨ w = lam * tau ∨ w = lam * om) → ξ ∈ ctxXi t tau x₁ x₂ rho →
      (ξ * w) * (ξ * w) = 1 → ∃ η ∈ ctxXi t tau x₁ x₂ rho, ξ * w = η * w * η⁻¹

theorem lemma418_FuA_of_H1 (h : Lemma418CaseAH1Stmt) : Lemma418CaseAFuAStmt := by
  intro G _ _ t L S x₁ x₂ lam rho tau om 𝒮 hG hc g ξ hξ hg
  refine S4B.k18_Xi_class_not_conj (w := lam) hc.toCtx13 ?_
    (fun hξ' hsq => h hG hc (Or.inl rfl) hξ' hsq) hξ hg
  exact Subgroup.subset_closure (by simp)

theorem lemma418_FuB_of_H1 (h : Lemma418CaseAH1Stmt) : Lemma418CaseAFuBStmt := by
  intro G _ _ t L S x₁ x₂ lam rho tau om 𝒮 hG hc g ξ hξ hg
  refine S4B.k18_Xi_class_not_conj (w := lam * tau) hc.toCtx13 ?_
    (fun hξ' hsq => h hG hc (Or.inr (Or.inl rfl)) hξ' hsq) hξ hg
  exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

theorem lemma418_FuD_of_H1 (h : Lemma418CaseAH1Stmt) : Lemma418CaseAFuDStmt := by
  intro G _ _ t L S x₁ x₂ lam rho tau om 𝒮 hG hc g ξ hξ hg
  refine S4B.k18_Xi_class_not_conj (w := lam * om) hc.toCtx13 ?_
    (fun hξ' hsq => h hG hc (Or.inr (Or.inr rfl)) hξ' hsq) hξ hg
  exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))


theorem harris1981_bound_reduced13E (h41 : Lemma4_1Stmt) (h41c : CtxOfLemma4_1Stmt)
    (h411 : Lemma4_11Stmt) (h413 : Lemma4_13Stmt) (hK : Ctx13KStmt)
    (hH1 : Lemma418CaseAH1Stmt) (hFC : Lemma418CaseAFuCStmt) (hI : Sec4Inputs)
    (hB : Sec4BInputs) : FritzII.Harris1981Bound :=
  harris1981_bound_reduced13D h41 h41c h411 h413 hK (lemma418_FuA_of_H1 hH1)
    (lemma418_FuB_of_H1 hH1) hFC (lemma418_FuD_of_H1 hH1) hI hB

end CFSG.OddStandard.SmallF3.HarrisU33
