module

public import CFSG.HardMathSupport.Dickson.Bal207.ExcReeShape
public import CFSG.HardMathSupport.Dickson.Bal207.Restate
import CFSG.HardMathSupport.Dickson.Bal207.Glue
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSRT
import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterTwisted
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux
open scoped commutatorElement

theorem excRee_index {d : TauCeti.ValidLieTypeIndex} (hd : IsExcRee32 d.1) :
    ∃ hv : (TauCeti.LieTypeIndex.reeF4 2).Valid, d = ⟨.reeF4 2, hv⟩ := by
  obtain ⟨dd, hv⟩ := d
  cases dd with
  | reeF4 m =>
    simp only [IsExcRee32] at hd
    subst hd
    exact ⟨hv, rfl⟩
  | _ => exact absurd hd (by simp [IsExcRee32])

theorem excRee_isLieQuot_of_type {X : Type} [Group X] {J : Subgroup X} {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ (2 * 2 + 1)) (h : ExcReeType K (↥J ⧸ Subgroup.center ↥J)) :
    IsLieQuot ↥J (fun d => Bal207Index 5 d ∧ ¬ IsG2EightIndex d) := by
  rcases h with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
  · obtain ⟨g⟩ := nonempty_suzukiGroup_equiv_cat (b := 2) (by norm_num) hK
    exact ⟨⟨.suzuki 2, suzuki_valid (by norm_num)⟩, ⟨⟨rfl, rfl⟩, fun h => h⟩, ⟨f.trans g⟩⟩
  · exact ⟨⟨.tits, tits_valid⟩, ⟨Or.inr rfl, fun h => h⟩, ⟨f⟩⟩

section Ree32

set_option linter.unusedSectionVars false


theorem excRee_clauses {G : ∀ (S : Type) [Group S], MulAut S → Prop} {X : Type} [Group X]
    [Finite X] {K B A : Subgroup X} (ctx : Bal207PlusCtx G 5 K B A)
    (hq : IsLieQuot ↥K IsExcRee32) (hIH : Bal207PlusIH G A) : Bal207PlusFamClauses 5 K B A := by
  obtain ⟨d, hd, ⟨f⟩⟩ := hq
  obtain ⟨hv, rfl⟩ := excRee_index hd
  have hR := CFSG.HardMathSupport.Timmesfeld.DefChar.lot_reeTitsModel_twistedF4_of_index 2 hv f
  obtain ⟨-, a, ha, hfa, K', _, _, _, hK', ⟨e⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.exists_mulEquiv_reeGamma hR
  have ha2 : a = 2 := by omega
  subst ha2
  have key : ∀ a₀ ∈ A, a₀ ≠ 1 → ∀ J : Subgroup X,
      GLAPComponent 5 (K ⊓ Subgroup.centralizer ({a₀} : Set X)) J →
        CFSG.Open.IsComponentOf J (K ⊓ Subgroup.centralizer ({a₀} : Set X)) ∧
        ExcReeType K' (↥J ⧸ Subgroup.center ↥J) ∧
        ∀ g ∈ Subgroup.normalizer (K : Set X), ⁅g, a₀⁆ ∈ Subgroup.centralizer (K : Set X) →
          g ∈ Subgroup.normalizer (J : Set X) := by
    intro a₀ ha₀ ha₀1 J hJ
    have haB : a₀ ∈ B := ctx.le ha₀
    have hap : a₀ ^ 5 ∈ Subgroup.centralizer (K : Set X) := by
      rw [ctx.scp.2.1.2 a₀ haB]
      exact one_mem _
    have haK : a₀ ∉ Subgroup.centralizer (K : Set X) :=
      not_mem_centralizer_of_inf_eq_bot ctx.disj ha₀ ha₀1
    exact compShape_lift (excReeType_isoInvariant K') ctx.prime ctx.comp.2.2 e
      (fun β hβ hβ1 => excRee_compShape hK' hβ hβ1) (ctx.norm haB) hap haK hJ
  have hb1 : ∀ a₀ ∈ A, a₀ ≠ 1 → ∀ J : Subgroup X,
      GLAPComponent 5 (K ⊓ Subgroup.centralizer ({a₀} : Set X)) J →
        B ≤ Subgroup.normalizer (J : Set X) := by
    intro a₀ ha₀ ha₀1 J hJ b hb
    refine (key a₀ ha₀ ha₀1 J hJ).2.2 b (ctx.norm hb) ?_
    have hcomm : b * a₀ = a₀ * b :=
      congrArg Subtype.val (ctx.scp.2.1.1.is_comm.comm ⟨b, hb⟩ ⟨a₀, ctx.le ha₀⟩)
    rw [commutatorElement_eq_one_iff_mul_comm.2 hcomm]
    exact one_mem _
  refine ⟨hb1, ?_, ?_⟩
  ·
    intro a₀ ha₀ ha₀1 J hJ _
    obtain ⟨hcomp, hty, -⟩ := key a₀ ha₀ ha₀1 J hJ
    have hJY : J ≤ Subgroup.centralizer ({a₀} : Set X) := hJ.1.trans inf_le_right
    exact Glue.stronglyLocallyOneBalanced_of_ih ctx hIH ha₀ ha₀1 hJ hcomp.2.2
      (hb1 a₀ ha₀ ha₀1 J hJ)
      (Glue.bal207PlusHyp_of_isLieQuot
        (Glue.isLieQuot_subgroupOf hJY (excRee_isLieQuot_of_type hK' hty)))
  ·
    have hbot : A ≠ ⊥ := by
      rintro rfl
      exact ctx.noncyc inferInstance
    obtain ⟨⟨a₀, ha₀A⟩, ha₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hbot
    have ha₀1' : a₀ ≠ 1 := fun h => ha₀1 (Subtype.ext h)
    exact ⟨a₀, ha₀A, ha₀1', fun w hw _ hwB J hJ =>
      (key a₀ ha₀A ha₀1' J hJ).2.2 w hw (hwB a₀ (ctx.le ha₀A))⟩

theorem bal207PlusFamRee32 (G : ∀ (S : Type) [Group S], MulAut S → Prop) :
    Bal207PlusFamRee32 G := by
  intro X _ _ _ p K B A ctx hq hIH
  obtain ⟨d, ⟨hp5, hd⟩, e⟩ := hq
  subst hp5
  exact excRee_clauses ctx ⟨d, hd, e⟩ hIH

end Ree32

end CFSG.HardMathSupport.Dickson.Bal207

end
