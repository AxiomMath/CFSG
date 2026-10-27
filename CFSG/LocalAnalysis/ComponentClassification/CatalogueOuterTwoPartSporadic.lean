module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueOuterTwoPart
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27ComponentLayer

public section

namespace CFSG.ComponentClassification.CatalogueOuterTwoPart

open CFSG.Blueprint

theorem four_le_ordProj_two_of_simple (T : Type) [Group T] [Finite T] [IsSimpleGroup T]
    (hnonab : ∃ a b : T, a * b ≠ b * a) : 4 ≤ ordProj[2] (Nat.card T) := by
  obtain ⟨a, b, hab⟩ := hnonab
  have hcenter : Subgroup.center T = ⊥ := by
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T)).resolve_right
      fun h => hab ?_
    exact (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  have hcomm : commutator T = ⊤ := by
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator T)).resolve_left fun h => hab ?_
    have hmem : a * b * a⁻¹ * b⁻¹ ∈ commutator T :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot] at hmem
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [hmem, one_mul]
  have hquot : IsSimpleGroup (T ⧸ Subgroup.center T) :=
    ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).isSimpleGroup
  have h4 : 4 ∣ Nat.card T :=
    GorensteinWalter.isQuasisimple_four_dvd_card ⟨inferInstance, hcomm, hquot⟩
  have hpos : Nat.card T ≠ 0 := Nat.card_pos.ne'
  have h4' : 2 ^ 2 ∣ ordProj[2] (Nat.card T) :=
    (Nat.Prime.pow_dvd_iff_dvd_ordProj Nat.prime_two hpos).mp h4
  exact Nat.le_of_dvd (Nat.ordProj_pos _ _) h4'

theorem outerTwoPartBound_of_mulEquiv {T T' : Type} [Group T] [Group T'] (e : T ≃* T')
    (h : OuterTwoPartBound T') : OuterTwoPartBound T := by
  obtain ⟨⟨eo, -⟩, -⟩ := LocalAnalysis.ComponentInitial.outer_isomorphism e
  rw [OuterTwoPartBound, Nat.card_congr e.toEquiv, Nat.card_congr eo.toEquiv]
  exact h

theorem outerTwoPartBound_of_card_outer_le_two (T : Type) [Group T] [Finite T] [IsSimpleGroup T]
    (hnonab : ∃ a b : T, a * b ≠ b * a) (hout : Nat.card (OuterAutomorphisms.Outer T) ≤ 2) :
    OuterTwoPartBound T := by
  have h4 := four_le_ordProj_two_of_simple T hnonab
  refine ⟨h4, lt_of_le_of_lt ?_ (lt_of_lt_of_le (by norm_num : 2 < 4) h4)⟩
  have hpos : Nat.card (OuterAutomorphisms.Outer T) ≠ 0 := Nat.card_pos.ne'
  exact (Nat.ordProj_le 2 hpos).trans hout

@[expose] def SporadicOuterTwoPart (s : TauCeti.SporadicName) : Prop :=
  OuterTwoPartBound (NativeSporadic.Carrier s)

theorem sporadic_outer_two_part_bound_of_cases (h : ∀ s, SporadicOuterTwoPart s) {T : Type}
    [Group T] (hT : NativeSporadic.SporadicRep T) : OuterTwoPartBound T := by
  obtain ⟨s, ⟨e⟩⟩ := hT
  exact outerTwoPartBound_of_mulEquiv e (h s)

end CFSG.ComponentClassification.CatalogueOuterTwoPart
