module

public import CFSG.CGT.Timmesfeld75.JLemmaFam
public import CFSG.CGT.Timmesfeld75.Sec3Results
public import CFSG.CGT.Timmesfeld75.JLemmaQuot

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

section Ker

variable {G : Type} [Group G] [Finite G] {R T : Subgroup G}

theorem conjSubgroup_coe_eq_of_mem_ker_jMap (hTR : T ≤ R) (hT : IsWC T) {w : ↥R}
    (hw : w ∈ (jMap ↥R).ker) {g : G} (hg : g ∈ R) :
    conjSubgroup (w : G) (conjSubgroup g T) = conjSubgroup g T := by
  have h := conj_conjSubgroup_eq_of_mem_ker_jMap (isWC_subgroupOf hT R hTR) hw ⟨g, hg⟩
  rw [conjSubgroup_subgroupOf R T ⟨g, hg⟩, conjSubgroup_subgroupOf R (conjSubgroup g T) w] at h
  have h1 : conjSubgroup g T ≤ R := conjSubgroup_le_of_le_of_mem hTR hg
  have h2 : conjSubgroup (w : G) (conjSubgroup g T) ≤ R :=
    conjSubgroup_le_of_le_of_mem h1 w.2
  have h3 := Subgroup.subgroupOf_inj.1 h
  rwa [inf_eq_left.2 h2, inf_eq_left.2 h1] at h3

end Ker

section Main

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem jLemma (h215 : Lemma215Stmt) (h26 : Lemma26Input) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hind : SimpleCaseUpTo (Nat.card G)) {T : Subgroup G} (hT : IsWC T) (hglob : Sec3Global T)
    (hiso : Sec3IsoGlobal T) (h16 : Nat.card T ≠ 16) {r : ℕ} {Ts : Fin r → Subgroup G}
    (hr : 0 < r) (hinj : Function.Injective Ts) (hconj : ∀ i, ∃ g : G, Ts i = conjSubgroup g T)
    (hTi : ∃ i, Ts i = T) (hne : ∀ j, (⨅ i, normIn (Ts j) (Ts i)) ≠ ⊥) {R : Subgroup G}
    (hR : ⨆ i, Ts i = R) (hRconj : ∀ i, ∃ g ∈ R, Ts i = conjSubgroup g T)
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
  obtain ⟨hQ, hQn, hroot⟩ := lemma313 G hnab T hT hglob hiso h16 r Ts hr hinj hconj ⟨i₀, hi₀⟩ hne
  rw [hR] at hroot
  have hroot' := isRootInvolutionSet_classD_subgroupOf hroot
  obtain ⟨j, hj⟩ := hq
  obtain ⟨g, hg, hgj⟩ := hRconj j
  have h4 : 4 ≤ Nat.card ((T.subgroupOf R).map (QuotientGroup.mk' (CFSG.pCore 2 ↥R))) :=
    four_le_card_map_pCore hT hTR hg (hgj ▸ hj)
  have hQR : (⨆ j, ⨅ i, normIn (Ts j) (Ts i)) ≤ R :=
    hR ▸ iSup_le fun j => (iInf_le _ j).trans ((normIn_le _ _).trans (le_iSup Ts j))
  have hQne : (⨆ j, ⨅ i, normIn (Ts j) (Ts i)) ≠ ⊥ := fun h =>
    hne i₀ (le_bot_iff.1 (h ▸ le_iSup (fun j => ⨅ i, normIn (Ts j) (Ts i)) i₀))
  have hO : CFSG.pCore 2 ↥R ≠ ⊥ :=
    pCore_ne_bot_of_normalizes hQR (isPGroup_two_of_isElemAbelian hQ) (hR ▸ hQn) hQne
  obtain ⟨hsimple, hlist, hhyp, htrans, -⟩ := jCore hind h215 (isWC_subgroupOf hT R hTR) hcl hroot'
    h4 (card_quot_pCore_lt hO)
  refine ⟨hsimple, hlist, hhyp, h26.apply hhyp, htrans, fun w hw i => ?_⟩
  obtain ⟨g', hg', hg'i⟩ := hRconj i
  rw [hg'i]
  exact conjSubgroup_coe_eq_of_mem_ker_jMap hTR hT hw hg'

end Main

end CFSG.CGT.Timmesfeld75
