module

public import CFSG.HardMathSupport.Lang.E6Descent.MaxClassMeta

public section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.Walter.W67

theorem card_le_nine_of_maxClass {P : Type*} [Group P] [Finite P] (hP : IsPGroup 3 P)
    {m : ℕ} (hm : 5 ≤ m) (hcard : Nat.card P = 3 ^ m)
    (hne : (⊤ : Subgroup P).lowerCentralSeries (m - 2) ≠ ⊥) (E : Subgroup P)
    (hE : CFSG.Open.IsElemAbelian 3 E) : Nat.card E ≤ 9 := by
  let d : MC P :=
    { m := m, hm := hm, hP := hP, hcard := hcard, hne := hne,
      abel := derived_abelian m (by omega) P hP hcard hne }
  exact d.card_le_nine E (fun a ha b hb => hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩ |> congrArg Subtype.val)
    hE.2

theorem card_eq_81_of_maxClass_of_elemAbelian27 {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 3 P) (hmax : CFSG.Walter.W67.IsMaximalClass 3 P) (E : Subgroup P)
    (hE : CFSG.Open.IsElemAbelian 3 E) (h27 : 27 ≤ Nat.card E) : Nat.card P = 81 := by
  obtain ⟨m, hm2, hcard, hne⟩ := hmax
  have hEP : Nat.card E ≤ Nat.card P := Subgroup.card_le_card_group E
  rw [hcard] at hEP
  have hm3 : 3 ≤ m := by
    by_contra h
    push Not at h
    have : 3 ^ m ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rcases (show m = 3 ∨ m = 4 ∨ 5 ≤ m by omega) with h3 | h4 | h5
  · exfalso
    subst h3
    have hEtop : E = ⊤ := Subgroup.eq_top_of_card_eq _ (by
      rw [hcard]; norm_num at hEP ⊢; omega)
    apply hne
    rw [show (3 : ℕ) - 2 = 1 by norm_num, Subgroup.top_lowerCentralSeries_one, eq_bot_iff]
    rw [commutator_def, Subgroup.commutator_le]
    intro g _ h _
    have := hE.1.is_comm.comm (⟨g, by rw [hEtop]; trivial⟩ : E) ⟨h, by rw [hEtop]; trivial⟩
    have h' : g * h = h * g := congrArg Subtype.val this
    rw [commutatorElement_def, Subgroup.mem_bot, h']
    group
  · subst h4; rw [hcard]; norm_num
  · exfalso
    have := card_le_nine_of_maxClass hP h5 hcard hne E hE
    omega

end CFSG.HardMathSupport.Lang.E6Descent
