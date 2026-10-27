module

public import CFSG.HardMathSupport.Dickson.Bal207.G28Shape
public import CFSG.HardMathSupport.Dickson.Bal207.Restate

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux
open scoped commutatorElement

section G28


theorem excG28_model {Y : Type} [Group Y] (h : IsLieQuot Y IsG2EightIndex) :
    Nonempty ((Y ⧸ Subgroup.center Y) ≃* ↥(adjointGroup Tag.G2 (GaloisField 2 3))) := by
  obtain ⟨⟨d, hv⟩, hd, ⟨f⟩⟩ := h
  cases d with
  | G2 q =>
    have hK : Nat.card (GaloisField 2 3) = 8 := by
      rw [GaloisField.card 2 3 (by norm_num)]
      norm_num
    have hKq : Nat.card (GaloisField 2 3) = q.card := by
      rw [hK, TauCeti.PrimePower.card_def, hd.1, hd.2]
      norm_num
    obtain ⟨eB⟩ :=
      CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hd.1 (GaloisField 2 3) hKq
    have hZ : Subgroup.center ↥(adjointGroup Tag.G2 (GaloisField 2 3)) = ⊥ :=
      center_adjointGroup_eq_bot
    exact ⟨f.trans (eB.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot))⟩
  | _ => exact False.elim hd

theorem excG28_clauses
    {G : ∀ (S : Type) [Group S], MulAut S → Prop} {X : Type} [Group X] [Finite X]
    {K B A : Subgroup X} (ctx : Bal207PlusCtx G 3 K B A) (hq : IsLieQuot ↥K IsG2EightIndex) :
    Bal207PlusFamClauses 3 K B A := by
  obtain ⟨e⟩ := excG28_model hq
  have hK : Nat.card (GaloisField 2 3) = 8 := by
    rw [GaloisField.card 2 3 (by norm_num)]
    norm_num
  have key : ∀ a₀ ∈ A, a₀ ≠ 1 → ∀ J : Subgroup X,
      GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a₀} : Set X)) J →
        CFSG.Open.IsComponentOf J (K ⊓ Subgroup.centralizer ({a₀} : Set X)) ∧
        G28CompType (↥J ⧸ Subgroup.center ↥J) ∧
        ∀ g ∈ Subgroup.normalizer (K : Set X), ⁅g, a₀⁆ ∈ Subgroup.centralizer (K : Set X) →
          g ∈ Subgroup.normalizer (J : Set X) := by
    intro a₀ ha₀ ha₀1 J hJ
    have haB : a₀ ∈ B := ctx.le ha₀
    have hap : a₀ ^ 3 ∈ Subgroup.centralizer (K : Set X) := by
      rw [ctx.scp.2.1.2 a₀ haB]
      exact one_mem _
    have haK : a₀ ∉ Subgroup.centralizer (K : Set X) :=
      not_mem_centralizer_of_inf_eq_bot ctx.disj ha₀ ha₀1
    exact compShape_lift isoInvariant_g28CompType ctx.prime ctx.comp.2.2 e
      (fun β hβ hβ1 => g28_compShape hK hβ hβ1) (ctx.norm haB) hap haK hJ
  have hb1 : ∀ a₀ ∈ A, a₀ ≠ 1 → ∀ J : Subgroup X,
      GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a₀} : Set X)) J →
        B ≤ Subgroup.normalizer (J : Set X) := by
    intro a₀ ha₀ ha₀1 J hJ b hb
    refine (key a₀ ha₀ ha₀1 J hJ).2.2 b (ctx.norm hb) ?_
    have hcomm : b * a₀ = a₀ * b :=
      congrArg Subtype.val (ctx.scp.2.1.1.is_comm.comm ⟨b, hb⟩ ⟨a₀, ctx.le ha₀⟩)
    rw [commutatorElement_eq_one_iff_mul_comm.2 hcomm]
    exact one_mem _
  refine ⟨hb1, ?_, ?_⟩
  ·
    intro a₀ ha₀ ha₀1 J hJ hns
    exact absurd (isBalSmall_of_g28CompType (key a₀ ha₀ ha₀1 J hJ).2.1) hns
  ·
    have hbot : A ≠ ⊥ := by
      rintro rfl
      exact ctx.noncyc inferInstance
    obtain ⟨⟨a₀, ha₀A⟩, ha₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hbot
    have ha₀1' : a₀ ≠ 1 := fun h => ha₀1 (Subtype.ext h)
    exact ⟨a₀, ha₀A, ha₀1', fun w hw _ hwB J hJ =>
      (key a₀ ha₀A ha₀1' J hJ).2.2 w hw (hwB a₀ (ctx.le ha₀A))⟩

theorem bal207PlusFamG28
    (G : ∀ (S : Type) [Group S], MulAut S → Prop) : Bal207PlusFamG28 G := by
  intro X _ _ _ K B A ctx hq _ _
  exact excG28_clauses ctx hq

end G28

end CFSG.HardMathSupport.Dickson.Bal207

end
