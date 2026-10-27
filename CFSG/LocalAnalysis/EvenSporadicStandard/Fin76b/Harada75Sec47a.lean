module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75V

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Open

theorem sec47_card_le_four {d : ℕ} (hd : d ∣ 8) (hne : d ≠ 8) : d ≤ 4 := by
  have hbound : d ≤ 8 := Nat.le_of_dvd (by norm_num) hd
  interval_cases d <;> omega

theorem sec47_E_le {S : Type} [Group S] [Finite S] (hS : IsPGroup 2 S) {E : Subgroup S} [E.Normal]
    (hE8 : Nat.card E = 8)
    (hP2 : ∀ U : Subgroup (S ⧸ E), Group.rank U ≤ 2) (T : Subgroup S) (hT : 4 < Group.rank T) :
    E ≤ T ∧ (∀ x ∈ E, x ∈ phi T → x = 1) ∧ ¬ IsCyclic (T.map (QuotientGroup.mk' E)) := by
  have hker : (QuotientGroup.mk' E).ker = E := QuotientGroup.ker_mk' E
  have hrank2 : Group.rank (T.map (QuotientGroup.mk' E)) ≤ 2 := hP2 _
  have hET : E ≤ T := by
    by_contra hne
    have hdvd : Nat.card (T ⊓ E : Subgroup S) ∣ Nat.card E :=
      Subgroup.card_dvd_of_le inf_le_right
    rw [hE8] at hdvd
    have hne8 : Nat.card (T ⊓ E : Subgroup S) ≠ 8 := by
      intro h8
      apply hne
      have heq : T ⊓ E = E := Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
      exact (le_of_eq heq.symm).trans inf_le_left
    have hle4 : Nat.card (T ⊓ E : Subgroup S) ≤ 4 := sec47_card_le_four hdvd hne8
    have h := rank_le_add_of_frattini hS (QuotientGroup.mk' E) T ⊥ (m := 2) (k := 2) hrank2
      bot_le bot_le (by
        rw [hker, Subgroup.card_bot]
        omega)
    omega
  have hEphi : ∀ x ∈ E, x ∈ phi T → x = 1 := by
    intro x hxE hxphi
    by_contra hx1
    have hMle : Subgroup.zpowers x ≤ T ⊓ (QuotientGroup.mk' E).ker := by
      rw [hker]
      exact (Subgroup.zpowers_le).mpr ⟨hET hxE, hxE⟩
    have hMphi : Subgroup.zpowers x ≤ phi T := (Subgroup.zpowers_le).mpr hxphi
    have hMcard : 2 ≤ Nat.card (Subgroup.zpowers x) := by
      rw [Nat.card_zpowers]
      have hpos : 0 < orderOf x := orderOf_pos x
      have hne : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
      omega
    have h := rank_le_add_of_frattini hS (QuotientGroup.mk' E) T (Subgroup.zpowers x)
      (m := 2) (k := 2) hrank2 hMle hMphi (by
        rw [hker, inf_eq_right.mpr hET, hE8]
        omega)
    omega
  refine ⟨hET, hEphi, ?_⟩
  intro hcyc
  have hm : Group.rank (T.map (QuotientGroup.mk' E)) ≤ 1 := rank_le_one_of_isCyclic hcyc
  have h := rank_le_add_of_frattini hS (QuotientGroup.mk' E) T ⊥ (m := 1) (k := 3) hm
    bot_le bot_le (by
      rw [hker, Subgroup.card_bot]
      have := Subgroup.card_le_of_le (inf_le_right : T ⊓ E ≤ E)
      omega)
  omega

end CFSG.EvenSporadicStandard.Fin76b
