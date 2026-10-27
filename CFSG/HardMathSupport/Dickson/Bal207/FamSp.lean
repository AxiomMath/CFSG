module

public import CFSG.HardMathSupport.Dickson.Bal207.SpShape
public import CFSG.HardMathSupport.Dickson.Bal207.Glue

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux

open scoped commutatorElement

theorem bal207PlusFamClauses_of_compShape_b2 {G : ∀ (S : Type) [Group S], MulAut S → Prop}
    {X : Type} [Group X] [Finite X] {p : ℕ} {K B A : Subgroup X}
    (ctx : Bal207PlusCtx G p K B A) {T : ∀ (Q : Type) [Group Q], Prop} (hT : IsoInvariant T)
    {S : Type} [Group S] (e : (↥K ⧸ Subgroup.center ↥K) ≃* S)
    (hS : ∀ β : MulAut S, β ^ p = 1 → β ≠ 1 → CompShape T β)
    (hb2 : ∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup X,
      GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
      CFSG.Open.IsComponentOf J (K ⊓ Subgroup.centralizer ({a} : Set X)) →
      T (↥J ⧸ Subgroup.center ↥J) → ¬ IsBalSmall J → B ≤ Subgroup.normalizer (J : Set X) →
        IsStronglyLocallyOneBalanced p B a J) :
    Bal207PlusFamClauses p K B A := by
  have key : ∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup X,
      GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
        CFSG.Open.IsComponentOf J (K ⊓ Subgroup.centralizer ({a} : Set X)) ∧
          T (↥J ⧸ Subgroup.center ↥J) ∧
          ∀ g ∈ Subgroup.normalizer (K : Set X), ⁅g, a⁆ ∈ Subgroup.centralizer (K : Set X) →
            g ∈ Subgroup.normalizer (J : Set X) := by
    intro a haA ha1 J hJ
    have haB : a ∈ B := ctx.le haA
    have hap : a ^ p ∈ Subgroup.centralizer (K : Set X) := by
      rw [ctx.scp.2.1.2 a haB]
      exact one_mem _
    exact compShape_lift hT ctx.prime ctx.comp.2.2 e hS (ctx.norm haB) hap
      (not_mem_centralizer_of_inf_eq_bot ctx.disj haA ha1) hJ
  have hBJ : ∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup X,
      GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
        B ≤ Subgroup.normalizer (J : Set X) := by
    intro a haA ha1 J hJ b hb
    refine (key a haA ha1 J hJ).2.2 b (ctx.norm hb) ?_
    have hc := congrArg Subtype.val (ctx.scp.2.1.1.is_comm.comm ⟨b, hb⟩ ⟨a, ctx.le haA⟩)
    have h1 : ⁅b, a⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hc
    rw [h1]
    exact one_mem _
  refine ⟨hBJ, fun a haA ha1 J hJ hsmall => ?_, ?_⟩
  · obtain ⟨hcomp, hTJ, -⟩ := key a haA ha1 J hJ
    exact hb2 a haA ha1 J hJ hcomp hTJ hsmall (hBJ a haA ha1 J hJ)
  · have hbot : A ≠ ⊥ := by
      rintro rfl
      exact ctx.noncyc inferInstance
    obtain ⟨⟨a, haA⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hbot
    have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
    exact ⟨a, haA, ha1', fun w hw _ hwB J hJ =>
      (key a haA ha1' J hJ).2.2 w hw (hwB a (ctx.le haA))⟩

@[expose] def Bal207SpFirstClaim (G : ∀ (S : Type) [Group S], MulAut S → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (K B A : Subgroup X),
    Bal207PlusCtx G 3 K B A → IsLieQuot ↥K (FamSp 3) → Bal207PlusIH G A →
      ∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup X,
        GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
        CFSG.Open.IsComponentOf J (K ⊓ Subgroup.centralizer ({a} : Set X)) →
        B ≤ Subgroup.normalizer (J : Set X) → IsLieQuot ↥J IsSpFirstClaimIdx →
          IsStronglyLocallyOneBalanced 3 B a J

theorem bal207PlusFamSp_of_firstClaim {G : ∀ (S : Type) [Group S], MulAut S → Prop}
    (hFC : Bal207SpFirstClaim G) : Bal207PlusFamSp G := by
  intro X _ _ hKG p K B A ctx hK hIH
  have hp3 : p = 3 := by
    obtain ⟨⟨d, hv⟩, ⟨hi, hsp⟩, -⟩ := hK
    cases d with
    | B r q => exact hi.1
    | _ => exact hsp.elim
  subst hp3
  obtain ⟨F, _, _, f, r, hF, hf, hr, hne, ⟨e⟩⟩ := exists_psp_of_famSp hK
  refine bal207PlusFamClauses_of_compShape_b2 ctx isoInvariant_spCompType e
    (fun β hβ hβ1 => compShape_psp hF hf hr hne β hβ hβ1) ?_
  intro a haA ha1 J hJ hcomp hTJ hsmall hBJ
  rcases hTJ with hA6 | ⟨d, hd, hJd⟩
  · exact absurd (Or.inl hA6) hsmall
  · rcases spCompIdx_cases hd with hi | hi | hi | hi
    · exact Glue.stronglyLocallyOneBalanced_of_ih ctx hIH haA ha1 hJ hcomp.2.2 hBJ
        (Glue.bal207PlusHyp_of_isLieQuot
          (Glue.isLieQuot_subgroupOf (hJ.1.trans inf_le_right) ⟨d, hi, hJd⟩))
    · exact absurd (Or.inr (Or.inl ⟨d, hi, hJd⟩)) hsmall
    · exact absurd (Or.inr (Or.inr ⟨d, hi, hJd⟩)) hsmall
    · exact hFC X hKG K B A ctx hK hIH a haA ha1 J hJ hcomp hBJ ⟨d, hi, hJd⟩

end CFSG.HardMathSupport.Dickson.Bal207

end
