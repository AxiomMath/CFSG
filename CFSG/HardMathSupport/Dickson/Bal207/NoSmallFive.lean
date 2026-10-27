module

public import CFSG.HardMathSupport.Dickson.Bal207.ExcRee32
public import CFSG.HardMathSupport.Dickson.Bal207.ExcSz32
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterTwisted
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTTits

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.Small

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux
  CFSG.HardMathSupport.Solomon.Coordinator.I1420 CFSG.HardMathSupport.Dickson.Bal207

theorem lieOrderFormula_ne_small {d : TauCeti.LieTypeIndex} (hd : Bal207Index 5 d) :
    lieOrderFormula d ≠ 360 ∧ lieOrderFormula d ≠ 6048 ∧ lieOrderFormula d ≠ 5515776 ∧
      lieOrderFormula d ≠ 504 := by
  cases d with
  | tits => exact ⟨by decide, by decide, by decide, by decide⟩
  | suzuki m =>
    obtain ⟨-, rfl⟩ := hd
    exact ⟨by decide, by decide, by decide, by decide⟩
  | reeF4 m =>
    obtain ⟨-, rfl⟩ := hd
    exact ⟨by decide, by decide, by decide, by decide⟩
  | _ => exact absurd hd (by simp [Bal207Index])

theorem not_isBalSmall_of_lieQuot {X : Type} [Group X] [Finite X] (hb : LieOrderBridge)
    {J : Subgroup X} (h : IsLieQuot ↥J (Bal207Index 5)) : ¬ IsBalSmall J := by
  obtain ⟨d, hd, ⟨f⟩⟩ := h
  have hcard : Nat.card (↥J ⧸ Subgroup.center ↥J) = lieOrderFormula d.1 := hb d _ ⟨f⟩
  obtain ⟨h360, h6048, h5515776, h504⟩ := lieOrderFormula_ne_small hd
  intro hsmall
  rcases hsmall with hA6 | hU | hL
  · obtain ⟨g⟩ := hA6
    have h := Nat.card_congr g.toEquiv
    rw [hcard, nat_card_alternatingGroup, Nat.card_fin] at h
    exact h360 (by rw [h]; norm_num [Nat.factorial])
  · obtain ⟨d', hd', ⟨f'⟩⟩ := hU
    have hcard' : Nat.card (↥J ⧸ Subgroup.center ↥J) = lieOrderFormula d'.1 := hb d' _ ⟨f'⟩
    rw [hcard] at hcard'
    obtain ⟨dd, hv'⟩ := d'
    cases dd with
    | twistedA r q =>
      obtain ⟨hr, h3 | h8⟩ := hd'
      · subst hr
        have hq : q.card = 3 := by
          rw [TauCeti.PrimePower.card_def, h3.1, h3.2]
          norm_num
        simp only [lieOrderFormula, hq] at hcard'
        exact h6048 (hcard'.trans (by decide))
      · subst hr
        have hq : q.card = 8 := by
          rw [TauCeti.PrimePower.card_def, h8.1, h8.2]
          norm_num
        simp only [lieOrderFormula, hq] at hcard'
        exact h5515776 (hcard'.trans (by decide))
    | _ => exact hd'.elim
  · obtain ⟨d', hd', ⟨f'⟩⟩ := hL
    have hcard' : Nat.card (↥J ⧸ Subgroup.center ↥J) = lieOrderFormula d'.1 := hb d' _ ⟨f'⟩
    rw [hcard] at hcard'
    obtain ⟨dd, hv'⟩ := d'
    cases dd with
    | A r q =>
      obtain ⟨hr, hq⟩ := hd'
      subst hr
      have hq8 : q.card = 8 := by
        rw [TauCeti.PrimePower.card_def, hq.1, hq.2]
        norm_num
      simp only [lieOrderFormula, hq8] at hcard'
      exact h504 (hcard'.trans (by decide))
    | _ => exact hd'.elim

section Holds

set_option linter.unusedSectionVars false


theorem excRee_isLieQuot_five {G : ∀ (S : Type) [Group S], MulAut S → Prop} {X : Type} [Group X]
    [Finite X] {K B A : Subgroup X} (ctx : Bal207PlusCtx G 5 K B A)
    (hq : IsLieQuot ↥K IsExcRee32) {a₀ : X} (ha₀ : a₀ ∈ A) (ha₀1 : a₀ ≠ 1) {J : Subgroup X}
    (hJ : GLAPComponent 5 (K ⊓ Subgroup.centralizer ({a₀} : Set X)) J) :
    IsLieQuot ↥J (Bal207Index 5) := by
  obtain ⟨d, hd, ⟨f⟩⟩ := hq
  obtain ⟨hv, rfl⟩ := excRee_index hd
  have hR := CFSG.HardMathSupport.Timmesfeld.DefChar.lot_reeTitsModel_twistedF4_of_index 2 hv f
  obtain ⟨-, a, ha, hfa, K', _, _, _, hK', ⟨e⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.exists_mulEquiv_reeGamma hR
  have ha2 : a = 2 := by omega
  subst ha2
  have haB : a₀ ∈ B := ctx.le ha₀
  have hap : a₀ ^ 5 ∈ Subgroup.centralizer (K : Set X) := by
    rw [ctx.scp.2.1.2 a₀ haB]
    exact one_mem _
  have haK : a₀ ∉ Subgroup.centralizer (K : Set X) :=
    not_mem_centralizer_of_inf_eq_bot ctx.disj ha₀ ha₀1
  obtain ⟨-, hty, -⟩ := compShape_lift (excReeType_isoInvariant K') ctx.prime ctx.comp.2.2 e
    (fun β hβ hβ1 => excRee_compShape hK' hβ hβ1) (ctx.norm haB) hap haK hJ
  obtain ⟨d', ⟨hd', -⟩, e'⟩ := excRee_isLieQuot_of_type hK' hty
  exact ⟨d', hd', e'⟩

theorem bal207PlusNoSmallFive (G : ∀ (S : Type) [Group S], MulAut S → Prop) :
    Bal207PlusNoSmallFive G := by
  intro X _ _ hX K B A ctx hIH a haA ha1 J hJ
  obtain ⟨d, ⟨e⟩, hd | ⟨h53, -⟩⟩ := ctx.hyp
  swap
  · exact absurd h53 (by norm_num)
  obtain ⟨hi, -⟩ := hd
  have haB : a ∈ B := ctx.le haA
  have haN : a ∈ Subgroup.normalizer (K : Set X) := ctx.norm haB
  have hap : a ^ 5 ∈ Subgroup.centralizer (K : Set X) := by
    rw [ctx.scp.2.1.2 a haB]
    exact one_mem _
  have haK : a ∉ Subgroup.centralizer (K : Set X) :=
    not_mem_centralizer_of_inf_eq_bot ctx.disj haA ha1
  obtain ⟨dd, hv⟩ := d
  cases dd with
  | tits =>
    haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := ctx.comp.2.2.2
    have hnc := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _
      ctx.comp.2.2
    exact (excVac_false_of_glaPComponent ctx.prime ctx.comp.2.2
      (fun β hβ hβ1 => isSolvable_fixSubgroup_tits hv hnc ⟨e⟩ ctx.prime ctx.odd hβ hβ1)
      haN hap haK hJ).elim
  | suzuki m =>
    obtain ⟨-, rfl⟩ := hi
    exact (excVac_false_of_glaPComponent ctx.prime ctx.comp.2.2
      (fun β hβ hβ1 => excSz_isSolvable_fixSubgroup e hβ hβ1) haN hap haK hJ).elim
  | reeF4 m =>
    obtain ⟨-, rfl⟩ := hi
    exact not_isBalSmall_of_lieQuot lieOrderBridge_holds
      (excRee_isLieQuot_five ctx ⟨⟨.reeF4 2, hv⟩, rfl, ⟨e⟩⟩ haA ha1 hJ)
  | _ => exact absurd hi (by simp [Bal207Index])

end Holds

end CFSG.HardMathSupport.Dickson.Bal207.Small

end
