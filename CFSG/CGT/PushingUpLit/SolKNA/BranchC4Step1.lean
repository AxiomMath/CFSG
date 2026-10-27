module

public import CFSG.CGT.PushingUpLit.SolKNA.Thm3

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G]


theorem exists_aData_of_caseII5 {K R T H : Subgroup G} {g : G} (cfg : NAConfig G K R T g)
    (h5 : CaseII5 K R T H) : ∃ W : Subgroup G, AData R T W ∧ W ⊓ R = H := by
  obtain ⟨-, -, hcard, -, -, hcomm, -, -, -⟩ := cfg.basic
  have hcardR : Nat.card ↥R = 2 * Nat.card ↥T ^ 2 := by
    have := Subgroup.relIndex_mul_card H R
    rw [h5.relIndex_two, inf_of_le_left h5.H_le, h5.card_H] at this
    exact this.symm
  rcases cfg.four_or_five with hnorm | ⟨W, hKW, hTW, hWS, hcardW, hZW, hZF, hiso, hΩ, hrel⟩
  · exfalso
    have h4 := cfg.caseII4_of h5.elem_T hnorm
    have h1 := Subgroup.relIndex_mul_card (R ⊓ Subgroup.normalizer (T : Set G)) R
    rw [inf_of_le_left (inf_le_left : R ⊓ Subgroup.normalizer (T : Set G) ≤ R)] at h1
    have hle : Nat.card ↥R ≤ Nat.card ↥T ^ 2 :=
      calc Nat.card ↥R = (R ⊓ Subgroup.normalizer (T : Set G)).relIndex R *
            Nat.card ↥(R ⊓ Subgroup.normalizer (T : Set G)) := h1.symm
        _ ≤ Nat.card ↥(R ⊓ Subgroup.normalizer (T : Set G)) *
            Nat.card ↥(R ⊓ Subgroup.normalizer (T : Set G)) :=
          Nat.mul_le_mul_right _ h4.relIndex_le
        _ = Nat.card ↥T ^ 2 := by rw [hcard, sq]
    have hpos : 0 < Nat.card ↥T ^ 2 := pow_pos Nat.card_pos 2
    omega
  · have hA : AData R T W := aData_of_alt5 (cfg.tiPair hcomm) hTW hWS
      (le_trans (sup_le_sup_right cfg.R_le_K T) hKW) hcardW hZW hZF hiso hΩ hrel hcard.le
    refine ⟨W, hA, ?_⟩
    obtain ⟨⟨t, ht⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp cfg.T_ne
    have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
    have hle : W ⊓ R ≤ H := by
      intro x hx
      by_contra hxH
      have h1 : t * x * t⁻¹ * x⁻¹ ∈ R ⊓ Subgroup.normalizer (T : Set G) := by
        have := hA.Z_comm t (hA.T_le ht) x hx.1
        rwa [hA.center_eq] at this
      exact h5.comm_not_mem x hx.2 hxH t ht ht1' h1
    exact Subgroup.eq_of_le_of_card_ge hle (h5.card_H.trans hA.card_H.symm).le

end CFSG.CGT.PushingUpLit.SolKNA
