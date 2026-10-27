module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Lemma65Rel
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Lemma65Adapt
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Cocode24Uniq
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Lemma65Defs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction.Balance

open Subgroup CFSG.Open CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Wong77
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.EvenSporadicStandard.Induction.Balance.Cocode24 (SylowFacts)
open scoped IsMulCommutative

section


theorem uniq_of_setting (hSyl : SylowFacts) {Γ : Type} [Group Γ] [Finite Γ]
    {E H₁ : Subgroup Γ} {e : Γ} [(E.subgroupOf H₁).Normal] (hS : Setting65 Γ E H₁ e)
    (φ : ↥H₁ ⧸ E.subgroupOf H₁ ≃* Carrier .M23) {A : Subgroup Γ} (hA : IsElemAbelian 2 A)
    (hAcard : Nat.card A = 2 ^ 12) : A = E := by
  have : E.Normal := hS.normal
  have : IsMulCommutative ↥E := hS.elemAb.1
  have : IsMulCommutative ↥(E.subgroupOf H₁) := hS.isMulCommutative_N
  let _ : Module (ZMod 2) (Additive ↥E) := vecModule hS.elemAb.2
  let _ : Module (ZMod 2) (Additive ↥(E.subgroupOf H₁)) := vecModule hS.sq_N
  obtain ⟨pE, hconj, hrel⟩ := exists_points hS φ
  obtain ⟨ψ, hact⟩ := Cocode24.exists_psi_of_points pE hconj hrel hS.card
  have hcent : ∀ g : Γ, (∀ x ∈ E, g * x = x * g) → g ∈ E := by
    intro g hg
    have : g ∈ centralizer (E : Set Γ) := mem_centralizer_iff.2 fun x hx => (hg x hx).symm
    rwa [hS.cent] at this
  refine Cocode24.eq_of_elemAb hSyl ψ hact hcent hS.card_quot A ?_ ?_ hAcard
  · intro a ha
    have := hA.2 a ha
    rwa [pow_two] at this
  · intro a ha b hb
    exact congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

end

theorem isElemAbelian_subgroupOf {G : Type*} [Group G] {H A : Subgroup G}
    (h : IsElemAbelian 2 A) : IsElemAbelian 2 (A.subgroupOf H) :=
  CFSG.Open.IsElemAbelian.subgroupOf h H

theorem sol78Lemma65Uniq_of_facts
    (hM23 : M23Facts) (hSyl : SylowFacts) : Sol78Lemma65Uniq := by
  intro G _ _ H E H₁ e hEH hEN hab hcard hcent he hord horb hC hH₁ hdisj hN hiso _ A hAH hAab
    hAcard
  obtain ⟨φ⟩ := hiso
  have := hM23.1
  have hsimple : IsSimpleGroup (H₁ ⧸ E.subgroupOf H₁) := φ.isSimpleGroup
  have hcard₁ : Nat.card (H₁ ⧸ E.subgroupOf H₁) = 10200960 :=
    (Nat.card_congr φ.toEquiv).trans hM23.2
  have hS := setting65_of_subgroup hEH hH₁ hEN hN hab hcard hcent he hord horb hC hdisj hsimple
    hcard₁
  obtain ⟨ψ⟩ := nonempty_subgroupQuotEquiv hH₁ hEN hN
  have hN' := hS.normal₁
  have h1 := uniq_of_setting hSyl hS (ψ.trans φ) (isElemAbelian_subgroupOf hAab)
    ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv).trans hAcard)
  have h2 := Subgroup.subgroupOf_inj.1 h1
  rwa [inf_eq_left.2 hAH, inf_eq_left.2 hEH] at h2

end CFSG.EvenSporadicStandard.Induction.Balance
