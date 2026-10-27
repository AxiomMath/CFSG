module

public import CFSG.CGT.Timmesfeld75.JLemma

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

section Main

variable {G : Type} [Group G] [Finite G]

theorem jLemma35 (h215 : Lemma215Stmt) (h26 : Lemma26Input)
    (hind : SimpleCaseUpTo (Nat.card G)) {T : Subgroup G} (hT : IsWC T) (hglob : Sec3Global T)
    {r : ℕ} {Ts : Fin r → Subgroup G} (hTi : ∃ i, Ts i = T) {R : Subgroup G}
    (hR : ⨆ i, Ts i = R) (hRconj : ∀ i, ∃ g ∈ R, Ts i = conjSubgroup g T) {Q : Subgroup G}
    (hQR : Q ≤ R) (hQ2 : IsPGroup 2 Q) (hQn : ∀ x ∈ R, conjSubgroup x Q = Q) (hQT : ⁅Q, T⁆ ≠ ⊥)
    (hq : ∃ j, 2 * Nat.card (normIn T (Ts j)) < Nat.card T) :
    IsSimpleGroup (jQuot ↥R) ∧ ListGroup (jQuot ↥R) ∧
      Lemma26Hyp (jQuot ↥R) ((T.subgroupOf R).map (jMap ↥R)) ∧
      Lemma26Concl (jQuot ↥R) ((T.subgroupOf R).map (jMap ↥R)) ∧
      (∀ x ∈ (T.subgroupOf R).map (jMap ↥R), x ≠ 1 → ∀ y ∈ (T.subgroupOf R).map (jMap ↥R), y ≠ 1 →
        ∃ g ∈ Subgroup.normalizer (((T.subgroupOf R).map (jMap ↥R) : Subgroup (jQuot ↥R)) :
          Set (jQuot ↥R)), g * x * g⁻¹ = y) ∧
      (∀ w : ↥R, w ∈ (jMap ↥R).ker → ∀ i, conjSubgroup (w : G) (Ts i) = Ts i) := by
  obtain ⟨i₀, hi₀⟩ := hTi
  have hTR : T ≤ R := hR ▸ hi₀ ▸ le_iSup Ts i₀
  have hgen : R ≤ ⨆ g : R, conjSubgroup (g : G) T := by
    refine hR.symm.le.trans (iSup_le fun i => ?_)
    obtain ⟨g, hg, e⟩ := hRconj i
    exact e ▸ le_iSup (fun g : R => conjSubgroup (g : G) T) ⟨g, hg⟩
  have hcl := normalClosure_subgroupOf_eq_top_of_le hTR hgen
  have hRQ : R ≤ Subgroup.normalizer (Q : Set G) := fun x hx =>
    mem_normalizer_of_conjSubgroup_eq (hQn x hx)
  have hQle : Q ≤ pCoreOf 2 R := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQR hRQ hQ2
  have hroot := isRootInvolutionSet_classDIn_of_not_commute_of_global hglob hT hTR fun h =>
    hQT (le_bot_iff.1 ((Subgroup.commutator_mono hQle le_rfl).trans h.le))
  have hroot' := isRootInvolutionSet_classD_subgroupOf hroot
  obtain ⟨j, hj⟩ := hq
  obtain ⟨g, hg, hgj⟩ := hRconj j
  have h4 : 4 ≤ Nat.card ((T.subgroupOf R).map (QuotientGroup.mk' (CFSG.pCore 2 ↥R))) :=
    four_le_card_map_pCore hT hTR hg (hgj ▸ hj)
  have hQne : Q ≠ ⊥ := fun h => hQT (by rw [h]; exact Subgroup.commutator_bot_left _)
  have hO : CFSG.pCore 2 ↥R ≠ ⊥ := pCore_ne_bot_of_normalizes hQR hQ2 hQn hQne
  obtain ⟨hsimple, hlist, hhyp, htrans, -⟩ := jCore hind h215 (isWC_subgroupOf hT R hTR) hcl hroot'
    h4 (card_quot_pCore_lt hO)
  refine ⟨hsimple, hlist, hhyp, h26.apply hhyp, htrans, fun w hw i => ?_⟩
  obtain ⟨g', hg', hg'i⟩ := hRconj i
  rw [hg'i]
  exact conjSubgroup_coe_eq_of_mem_ker_jMap hTR hT hw hg'

end Main

end CFSG.CGT.Timmesfeld75
