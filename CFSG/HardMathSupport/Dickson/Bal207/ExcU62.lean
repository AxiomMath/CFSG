module

public import CFSG.HardMathSupport.Dickson.Bal207.ExcU62Shape
public import CFSG.HardMathSupport.Dickson.Bal207.Restate
import CFSG.HardMathSupport.Dickson.Bal207.Glue

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
open scoped commutatorElement

theorem excU62_index {d : TauCeti.ValidLieTypeIndex} (hd : IsExcU62 d.1) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid),
      IsTwoPow q 1 ∧ d = ⟨.twistedA 5 q, hv⟩ := by
  obtain ⟨dd, hv⟩ := d
  cases dd with
  | twistedA r q =>
    obtain ⟨hr, hq⟩ := hd
    subst hr
    exact ⟨q, hv, hq, rfl⟩
  | _ => exact hd.elim

theorem excU62_compShape_of_data {ℓ f : ℕ} (hℓ : ℓ = 2) (hf : f = 1) {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (β : MulAut (primeFormP h (idGram K 6))) (hβ : β ^ 3 = 1)
    (hβ1 : β ≠ 1) : CompShape ExcU62Type β := by
  subst hℓ hf
  exact excU62_compShape_primeForm h β hβ hβ1

theorem excU62_clauses {G : ∀ (S : Type) [Group S], MulAut S → Prop} {X : Type} [Group X]
    [Finite X] {K B A : Subgroup X} (ctx : Bal207PlusCtx G 3 K B A)
    (hq : IsLieQuot ↥K IsExcU62) (hIH : Bal207PlusIH G A) : Bal207PlusFamClauses 3 K B A := by
  obtain ⟨d, hd, ⟨f⟩⟩ := hq
  obtain ⟨q, hv, hq1, rfl⟩ := excU62_index hd
  obtain ⟨⟨hℓ, hfe, hn3, hq'⟩, F, _, _, hF, ⟨eT⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 5 q hv f
  have h : UnitaryFieldData q.p q.exponent F := ⟨hℓ, hfe, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_idGram (n := 5 + 1) (K := F))
  let e' : (↥K ⧸ Subgroup.center ↥K) ≃* primeFormP h (idGram F 6) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  have key : ∀ a₀ ∈ A, a₀ ≠ 1 → ∀ J : Subgroup X,
      GLAPComponent 3 (K ⊓ Subgroup.centralizer ({a₀} : Set X)) J →
        CFSG.Open.IsComponentOf J (K ⊓ Subgroup.centralizer ({a₀} : Set X)) ∧
        ExcU62Type (↥J ⧸ Subgroup.center ↥J) ∧
        ∀ g ∈ Subgroup.normalizer (K : Set X), ⁅g, a₀⁆ ∈ Subgroup.centralizer (K : Set X) →
          g ∈ Subgroup.normalizer (J : Set X) := by
    intro a₀ ha₀ ha₀1 J hJ
    have haB : a₀ ∈ B := ctx.le ha₀
    have hap : a₀ ^ 3 ∈ Subgroup.centralizer (K : Set X) := by
      rw [ctx.scp.2.1.2 a₀ haB]
      exact one_mem _
    have haK : a₀ ∉ Subgroup.centralizer (K : Set X) :=
      not_mem_centralizer_of_inf_eq_bot ctx.disj ha₀ ha₀1
    exact compShape_lift excU62Type_isoInvariant ctx.prime ctx.comp.2.2 e'
      (fun β hβ hβ1 => excU62_compShape_of_data hq1.1 hq1.2 h β hβ hβ1) (ctx.norm haB) hap haK hJ
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
    obtain ⟨hcomp, hty, -⟩ := key a₀ ha₀ ha₀1 J hJ
    rcases excU62_lieQuot_or_small hty with hlq | hsmall
    · have hJY : J ≤ Subgroup.centralizer ({a₀} : Set X) := hJ.1.trans inf_le_right
      exact Glue.stronglyLocallyOneBalanced_of_ih ctx hIH ha₀ ha₀1 hJ hcomp.2.2
        (hb1 a₀ ha₀ ha₀1 J hJ)
        (Glue.bal207PlusHyp_of_isLieQuot (Glue.isLieQuot_subgroupOf hJY hlq))
    · exact absurd hsmall hns
  ·
    have hbot : A ≠ ⊥ := by
      rintro rfl
      exact ctx.noncyc inferInstance
    obtain ⟨⟨a₀, ha₀A⟩, ha₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hbot
    have ha₀1' : a₀ ≠ 1 := fun h => ha₀1 (Subtype.ext h)
    exact ⟨a₀, ha₀A, ha₀1', fun w hw _ hwB J hJ =>
      (key a₀ ha₀A ha₀1' J hJ).2.2 w hw (hwB a₀ (ctx.le ha₀A))⟩

theorem bal207PlusFamU62 (G : ∀ (S : Type) [Group S], MulAut S → Prop) :
    Bal207PlusFamU62 G := by
  intro X _ _ _ p K B A ctx hq hIH
  obtain ⟨d, ⟨hp3, hd⟩, e⟩ := hq
  subst hp3
  exact excU62_clauses ctx ⟨d, hd, e⟩ hIH

end CFSG.HardMathSupport.Dickson.Bal207

end
