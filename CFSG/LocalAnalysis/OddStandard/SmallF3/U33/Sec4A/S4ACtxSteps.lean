module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AStmt1

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

section Facts

variable {G : Type} [Group G] [Finite G]

structure CtxLModelFacts (L : Subgroup G) (x₁ x₂ lam rho : G) : Prop where
  cent_L_B : L ⊓ centralizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) = baseGrp x₁ x₂
  norm_L_B : L ⊓ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) = closure {x₁, x₂, rho, lam}

structure CtxIdxFacts (t : G) (L S : Subgroup G) (x₁ x₂ lam : G) : Prop where
  relIndex_two : (twoCore t ⊔ L).relIndex (invCent t) = 2
  index_PT : (twoCore t ⊔ wreathGrp x₁ x₂ lam).relIndex S = 2
  card_S : Nat.card S = 2 ^ 6 * Nat.card (twoCore t)

structure CtxTauFacts (t : G) (L S : Subgroup G) (x₁ x₂ lam rho tau : G) : Prop where
  S_eq : S = twoCore t ⊔ m12Grp x₁ x₂ lam tau
  tau_mem : tau ∈ S
  tau_not_mem : tau ∉ twoCore t ⊔ L
  tau_sq_mem : tau ^ 2 ∈ twoCore t
  tau_x₁ : tau * x₁ * tau⁻¹ = x₁⁻¹
  tau_x₂ : tau * x₂ * tau⁻¹ = x₂⁻¹
  tau_lam : tau * lam = lam * tau
  tau_rho : tau * rho = rho * tau
  cent_L_tau : L ⊓ centralizer ({tau} : Set G) = closure {x₁ ^ 2, (x₁ * x₂) ^ 2, rho, lam}
  perm_four : Nonempty (↥(L ⊓ centralizer ({tau} : Set G)) ≃* Equiv.Perm (Fin 4))
  cent_T_tau : wreathGrp x₁ x₂ lam ⊓ centralizer ({tau} : Set G) =
    closure {x₁ ^ 2, (x₁ * x₂) ^ 2, lam}
  dihedral : Nonempty (↥(closure {x₁ ^ 2, (x₁ * x₂) ^ 2, lam}) ≃* DihedralGroup 4)

@[expose] def CtxOuterFact (t : G) (L : Subgroup G) (tau : G) : Prop :=
  ∀ γ ∈ invCent t, γ ∉ twoCore t ⊔ L → γ ^ 2 ∈ twoCore t →
    ∃ h ∈ invCent t, ∃ p ∈ twoCore t, h * γ * h⁻¹ = p * tau

structure CtxCentreFacts (t : G) (S : Subgroup G) (x₁ x₂ lam : G) : Prop where
  normal_W : NormalIn (ctxW t x₁ x₂) S
  center_ge : closure {t, (x₁ * x₂) ^ 2} ≤ S ⊓ centralizer (S : Set G)
  center_le : S ⊓ centralizer (S : Set G) ≤ twoCore t ⊔ zpowers ((x₁ * x₂) ^ 2)
  center_omega : ∀ g ∈ S ⊓ centralizer (S : Set G), g ^ 2 = 1 → g ∈ closure {t, (x₁ * x₂) ^ 2}
  m2_PT : ∀ E : Subgroup G, E ≤ twoCore t ⊔ wreathGrp x₁ x₂ lam → CFSG.Open.IsElemAbelian 2 E →
    Nat.card E ≤ 8
  m2_PT_attained : CFSG.Open.IsElemAbelian 2 (closure {t, x₁ ^ 2, (x₁ * x₂) ^ 2}) ∧
    Nat.card (closure {t, x₁ ^ 2, (x₁ * x₂) ^ 2}) = 8
  E16_cases : ∀ E : Subgroup G, E ≤ S → CFSG.Open.IsElemAbelian 2 E → Nat.card E = 16 →
    E ⊓ (twoCore t ⊔ wreathGrp x₁ x₂ lam) = closure {t, x₁ ^ 2, (x₁ * x₂) ^ 2} ∨
    E ⊓ (twoCore t ⊔ wreathGrp x₁ x₂ lam) = closure {t, (x₁ * x₂) ^ 2, lam} ∨
    E ⊓ (twoCore t ⊔ wreathGrp x₁ x₂ lam) = closure {t, (x₁ * x₂) ^ 2, x₁⁻¹ * x₂ * lam}

structure CtxNormFacts (t : G) (x₁ x₂ lam rho tau : G) : Prop where
  cent_W : centralizer ((ctxW t x₁ x₂ : Subgroup G) : Set G) = ctxW t x₁ x₂
  cent_baseGrp : invCent t ⊓ centralizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) = ctxW t x₁ x₂
  norm_baseGrp : invCent t ⊓ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) =
    ctxW t x₁ x₂ ⊔ closure {rho, lam, tau}
  normal_norm : NormalIn (ctxW t x₁ x₂ ⊔ zpowers tau)
    (invCent t ⊓ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G))

end Facts

@[expose] def CtxLModelStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G},
    Ctx0 t L S x₁ x₂ lam rho → CtxLModelFacts L x₁ x₂ lam rho

@[expose] def CtxIdxStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G},
    Ctx0 t L S x₁ x₂ lam rho → Lemma4_1Concl t L → CtxIdxFacts t L S x₁ x₂ lam

@[expose] def CtxTauStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G},
    Ctx0 t L S x₁ x₂ lam rho → Lemma4_1Concl t L → CtxIdxFacts t L S x₁ x₂ lam →
      CtxLModelFacts L x₁ x₂ lam rho → ∃ tau : G, CtxTauFacts t L S x₁ x₂ lam rho tau

@[expose] def CtxOuterStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G},
    Ctx0 t L S x₁ x₂ lam rho → Lemma4_1Concl t L → CtxIdxFacts t L S x₁ x₂ lam →
      CtxTauFacts t L S x₁ x₂ lam rho tau → CtxOuterFact t L tau

@[expose] def CtxCentreStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G},
    Ctx0 t L S x₁ x₂ lam rho → Lemma4_1Concl t L → CtxIdxFacts t L S x₁ x₂ lam →
      CtxTauFacts t L S x₁ x₂ lam rho tau → CtxCentreFacts t S x₁ x₂ lam

@[expose] def CtxNormStmt : Prop :=
  ∀ {G : Type} [Group G] [Finite G]
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G},
    Ctx0 t L S x₁ x₂ lam rho → Lemma4_1Concl t L → CtxIdxFacts t L S x₁ x₂ lam →
      CtxTauFacts t L S x₁ x₂ lam rho tau → CtxLModelFacts L x₁ x₂ lam rho →
        CtxNormFacts t x₁ x₂ lam rho tau

theorem ctxOfLemma4_1_of_steps (m : CtxLModelStmt) (i : CtxIdxStmt) (ta : CtxTauStmt)
    (o : CtxOuterStmt) (c : CtxCentreStmt) (n : CtxNormStmt) : CtxOfLemma4_1Stmt := by
  intro G _ _ t L S x₁ x₂ lam rho h0 h1
  have hi := i h0 h1
  have hm := m h0
  obtain ⟨tau, ht⟩ := ta h0 h1 hi hm
  have ho := o h0 h1 hi ht
  have hc := c h0 h1 hi ht
  have hn := n h0 h1 hi ht hm
  exact ⟨tau,
    { toCtx0 := h0
      ne_fstar := h1
      relIndex_two := hi.relIndex_two
      index_PT := hi.index_PT
      card_S := hi.card_S
      S_eq := ht.S_eq
      tau_mem := ht.tau_mem
      tau_not_mem := ht.tau_not_mem
      tau_sq_mem := ht.tau_sq_mem
      tau_x₁ := ht.tau_x₁
      tau_x₂ := ht.tau_x₂
      tau_lam := ht.tau_lam
      tau_rho := ht.tau_rho
      cent_L_tau := ht.cent_L_tau
      perm_four := ht.perm_four
      cent_T_tau := ht.cent_T_tau
      dihedral := ht.dihedral
      normal_W := hc.normal_W
      cent_W := hn.cent_W
      invol_outer := ho
      center_ge := hc.center_ge
      center_le := hc.center_le
      center_omega := hc.center_omega
      m2_PT := hc.m2_PT
      m2_PT_attained := hc.m2_PT_attained
      E16_cases := hc.E16_cases
      cent_baseGrp := hn.cent_baseGrp
      norm_baseGrp := hn.norm_baseGrp
      normal_norm := hn.normal_norm }⟩

end CFSG.OddStandard.SmallF3.HarrisU33
