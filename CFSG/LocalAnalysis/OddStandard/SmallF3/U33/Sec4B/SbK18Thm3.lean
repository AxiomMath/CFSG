module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18Thm2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18t

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

@[expose] def Lemma418CaseAFuAStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}
    (_hG : Sec4Glob G) (_hc : Ctx18A t L S x₁ x₂ lam rho tau om 𝒮) {g ξ : G},
    ξ ∈ ctxXi t tau x₁ x₂ rho → g * t * g⁻¹ = ξ * lam → False

@[expose] def Lemma418CaseAFuBStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}
    (_hG : Sec4Glob G) (_hc : Ctx18A t L S x₁ x₂ lam rho tau om 𝒮) {g ξ : G},
    ξ ∈ ctxXi t tau x₁ x₂ rho → g * t * g⁻¹ = ξ * (lam * tau) → False

@[expose] def Lemma418CaseAFuDStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}
    (_hG : Sec4Glob G) (_hc : Ctx18A t L S x₁ x₂ lam rho tau om 𝒮) {g ξ : G},
    ξ ∈ ctxXi t tau x₁ x₂ rho → g * t * g⁻¹ = ξ * (lam * om) → False

@[expose] def Lemma418CaseAFuCStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}
    (_hG : Sec4Glob G) (_hc : Ctx18A t L S x₁ x₂ lam rho tau om 𝒮) {g ξ : G},
    ξ ∈ ctxXi t tau x₁ x₂ rho → g * t * g⁻¹ = ξ * (lam * t) →
      ∃ η ∈ ctxXi t tau x₁ x₂ rho, ξ * (lam * t) = η * (lam * t) * η⁻¹

theorem lemma418_Fu_of_classes (hA : Lemma418CaseAFuAStmt) (hB : Lemma418CaseAFuBStmt)
    (hC : Lemma418CaseAFuCStmt) (hD : Lemma418CaseAFuDStmt) : Lemma418CaseAFuStmt := by
  intro G _ _ t L S x₁ x₂ lam rho tau om 𝒮 hG hc g e he hg
  exact S4B.k18_Fu_of_classes hc (fun hξ h => hA hG hc hξ h) (fun hξ h => hB hG hc hξ h)
    (fun hξ h => hD hG hc hξ h) (fun hξ h => hC hG hc hξ h) he hg


theorem harris1981_bound_reduced13D (h41 : Lemma4_1Stmt) (h41c : CtxOfLemma4_1Stmt)
    (h411 : Lemma4_11Stmt) (h413 : Lemma4_13Stmt) (hK : Ctx13KStmt)
    (hFA : Lemma418CaseAFuAStmt) (hFB : Lemma418CaseAFuBStmt) (hFC : Lemma418CaseAFuCStmt)
    (hFD : Lemma418CaseAFuDStmt) (hI : Sec4Inputs) (hB : Sec4BInputs) :
    FritzII.Harris1981Bound :=
  harris1981_bound_reduced13C h41 h41c h411 h413 hK (lemma418_Fu_of_classes hFA hFB hFC hFD) hI hB

end CFSG.OddStandard.SmallF3.HarrisU33
