module

public import CFSG.HardMathSupport.Dickson.Bal207.CompShape
public import CFSG.HardMathSupport.Dickson.Bal207.Glue

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux

open scoped commutatorElement

theorem famShape_map_fixSubgroup_of_commute {S : Type} [Group S] (β ω : MulAut S)
    (hω : ω * β = β * ω) : (fixSubgroup β).map ω.toMonoidHom = fixSubgroup β := by
  have hcomm : ∀ x, ω (β x) = β (ω x) := fun x => congrArg (fun φ : MulAut S => φ x) hω
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : β x = x := hx
    show β (ω x) = ω x
    rw [← hcomm, hx']
  · intro hy
    have hy' : β y = y := hy
    refine ⟨ω.symm y, ?_, ω.apply_symm_apply y⟩
    show β (ω.symm y) = ω.symm y
    apply ω.injective
    rw [hcomm, ω.apply_symm_apply]
    exact hy'

theorem compShape_of_subsingleton {T : ∀ (Q : Type) [Group Q], Prop} {S : Type} [Group S]
    (β : MulAut S) (hlayer : PerfectInLayer β)
    (hall : ∀ L L' : Subgroup S, CFSG.Open.IsComponentOf L (fixSubgroup β) →
      CFSG.Open.IsComponentOf L' (fixSubgroup β) → L = L')
    (hT : ∀ L : Subgroup S, CFSG.Open.IsComponentOf L (fixSubgroup β) →
      T (↥L ⧸ Subgroup.center ↥L)) : CompShape T β where
  layer := hlayer
  type := hT
  norm := fun ω hω L hL => by
    have h1 : CFSG.Open.IsComponentOf (L.map ω.toMonoidHom) ((fixSubgroup β).map ω.toMonoidHom) :=
      CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map (ω : S ≃* S) hL
    rw [famShape_map_fixSubgroup_of_commute β ω hω] at h1
    exact hall _ _ h1 hL

theorem bal207PlusFamClauses_of_compShape {G : ∀ (S : Type) [Group S], MulAut S → Prop}
    {X : Type} [Group X] [Finite X] {p : ℕ} {K B A : Subgroup X}
    (ctx : Bal207PlusCtx G p K B A) (hIH : Bal207PlusIH G A)
    {T : ∀ (Q : Type) [Group Q], Prop} (hT : IsoInvariant T) {S : Type} [Group S]
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* S)
    (hS : ∀ β : MulAut S, β ^ p = 1 → β ≠ 1 → CompShape T β)
    (hTL : ∀ J : Subgroup X, T (↥J ⧸ Subgroup.center ↥J) → ¬ IsBalSmall J →
      IsLieQuot ↥J (fun d => Bal207Index p d ∧ ¬ IsG2EightIndex d)) :
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
    exact Glue.stronglyLocallyOneBalanced_of_ih ctx hIH haA ha1 hJ hcomp.2.2
      (hBJ a haA ha1 J hJ) (Glue.bal207PlusHyp_of_isLieQuot
        (Glue.isLieQuot_subgroupOf (hJ.1.trans inf_le_right) (hTL J hTJ hsmall)))
  · have hbot : A ≠ ⊥ := by
      rintro rfl
      exact ctx.noncyc inferInstance
    obtain ⟨⟨a, haA⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hbot
    have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
    exact ⟨a, haA, ha1', fun w hw _ hwB J hJ =>
      (key a haA ha1' J hJ).2.2 w hw (hwB a (ctx.le haA))⟩

end CFSG.HardMathSupport.Dickson.Bal207

end
