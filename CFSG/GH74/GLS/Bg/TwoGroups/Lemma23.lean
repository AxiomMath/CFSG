module

public import CFSG.GH74.GLS.Bg.TwoGroups.L23Main
public import CFSG.GH74.GLS.Bg.TwoGroups.Statements

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

open L23

@[expose] def invsInc {T : Type} [Group T] (A : Subgroup T) :
    {a : A // a * a = 1 ∧ a ≠ 1} → {t : T // t * t = 1 ∧ t ≠ 1} := fun a =>
  ⟨a.1.1, congrArg Subtype.val a.2.1, fun h => a.2.2 (Subtype.ext h)⟩

theorem invsInc_injective {T : Type} [Group T] (A : Subgroup T) :
    Function.Injective (invsInc A) := by
  intro a b h
  have h' : a.1.1 = b.1.1 :=
    congrArg (fun s : {t : T // t * t = 1 ∧ t ≠ 1} => s.1) h
  exact Subtype.ext (Subtype.ext h')

theorem om1_ne_of_card_lt {T : Type} [Group T] [Finite T] (A : Subgroup T)
    (h : Nat.card {a : A // a * a = 1 ∧ a ≠ 1} < Nat.card {t : T // t * t = 1 ∧ t ≠ 1}) :
    Om1 A ≠ Om1 (⊤ : Subgroup T) := by
  intro heq
  have hsurj : Function.Surjective (invsInc A) := by
    intro t
    have h1 : t.1 ∈ Om1 (⊤ : Subgroup T) :=
      Subgroup.subset_closure ⟨Subgroup.mem_top _, by rw [pow_two]; exact t.2.1⟩
    rw [← heq] at h1
    have h2 : Om1 A ≤ A := (Subgroup.closure_le _).mpr (fun h hh => hh.1)
    exact ⟨⟨⟨t.1, h2 h1⟩, Subtype.ext t.2.1, fun h => t.2.2 (congrArg Subtype.val h)⟩, rfl⟩
  exact absurd (Nat.card_le_card_of_surjective _ hsurj) (not_le.mpr h)

theorem om1_eq_of_card_eq {T : Type} [Group T] [Finite T] (A : Subgroup T)
    (h : Nat.card {a : A // a * a = 1 ∧ a ≠ 1} = Nat.card {t : T // t * t = 1 ∧ t ≠ 1}) :
    Om1 A = Om1 (⊤ : Subgroup T) := by
  have hbij : Function.Bijective (invsInc A) :=
    (invsInc_injective A).bijective_of_nat_card_le (le_of_eq h.symm)
  apply le_antisymm
  · exact Subgroup.closure_mono (fun h hh => ⟨Subgroup.mem_top _, hh.2⟩)
  · refine (Subgroup.closure_le _).mpr (fun t ht => ?_)
    by_cases h1 : t = 1
    · rw [h1]; exact (Om1 A).one_mem
    · have hinv : t * t = 1 ∧ t ≠ 1 := ⟨by rw [← pow_two]; exact ht.2, h1⟩
      obtain ⟨a, ha⟩ := hbij.2 ⟨t, hinv⟩
      have hta : t ∈ A := by
        have h3 : a.1.1 = t := congrArg (fun s : {t : T // t * t = 1 ∧ t ≠ 1} => s.1) ha
        rw [← h3]
        exact a.1.2
      exact Subgroup.subset_closure ⟨hta, ht.2⟩

theorem card_Z4Z4 : Nat.card Z4Z4 = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem iv2_2_3 : IV2_2_3 := by
  intro T _ _ hT x hx3 hfix A hAn hAx hθ hCA
  obtain ⟨θ⟩ := hθ
  have := hAn
  have hx3' : x ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx3] at this
  have hA16 : Nat.card A = 16 := (Nat.card_congr θ.toEquiv).trans card_Z4Z4
  have hA3 : Nat.card {a : A // a * a = 1 ∧ a ≠ 1} = 3 :=
    (card_invs_congr θ).trans card_invs_Z4Z4
  rcases classify_T A θ x hAx hx3' hfix hCA hT hA16 with ⟨he, h27⟩ | ⟨he, h3⟩
  · refine ⟨fun hom => ?_, fun _ => he⟩
    exact absurd hom (om1_ne_of_card_lt A (by rw [hA3]; exact lt_of_lt_of_eq (by norm_num) h27.symm))
  · refine ⟨fun _ => he, fun hne => ?_⟩
    exact absurd (om1_eq_of_card_eq A (by rw [hA3]; exact h3.symm)) hne

end CFSG.GH74.GLS.Bg.TwoGroups
