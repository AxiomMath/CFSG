module

public import CFSG.LargeExtraspecial.S12InspP4Ord

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Open CFSG.Fischer.Classification

namespace S12Insp4P

theorem four_dvd_card_of_commute {X : Type*} [Group X] [Finite X] {a b : X} (ha : a * a = 1)
    (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hc : a * b = b * a) :
    4 ∣ Nat.card X := by
  have h1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have h2 : b * (a * b) = a := by rw [← mul_assoc, ← hc, mul_assoc, hb, mul_one]
  have h3 : a * b * a = b := by rw [mul_assoc, ← hc, h1]
  have h4 : a * b * b = a := by rw [mul_assoc, hb, mul_one]
  have h5 : a * b * (a * b) = 1 := by rw [← mul_assoc, h3, hb]
  have hia : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hib : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hiab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right h5
  let V : Subgroup X :=
    { carrier := {1, a, b, a * b}
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
        rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
          simp only [one_mul, mul_one, ha, hb, h1, h2, h3, h4, h5, ← hc, true_or, or_true]
      one_mem' := Set.mem_insert _ _
      inv_mem' := by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
        rcases hx with rfl | rfl | rfl | rfl
        · simp
        · simp [hia]
        · simp [hib]
        · simp [hiab] }
  have hab1 : a * b ≠ 1 := fun h => hab (by rw [← hib, ← mul_eq_one_iff_eq_inv.mp h])
  have haab : a ≠ a * b := fun h => hb1 (by
    have := congrArg (a⁻¹ * ·) h
    simpa using this.symm)
  have hbab : b ≠ a * b := fun h => ha1 (by
    have := congrArg (· * b⁻¹) h
    simpa using this.symm)
  have hV : Nat.card V = 4 := by
    show Nat.card ↥({1, a, b, a * b} : Set X) = 4
    rw [Nat.card_coe_set_eq, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
      Set.ncard_pair hbab]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hab, haab⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨ha1.symm, hb1.symm, hab1.symm⟩
  rw [← hV]
  exact card_subgroup_dvd_card V

theorem not_seven_dvd_card_GL_five_three : ¬ 7 ∣ Nat.card (GL (Fin 5) (ZMod 3)) := by
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_five]
  decide

end S12Insp4P

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem false_of_reflGroup_five {g : G}
    (hP : ∀ P : Subgroup S.Mbar, IsPGroup 2 P → Nat.card P ≤ 2 ^ 7)
    (hsec : ∀ N : Subgroup S.Mbar, N.Normal → 20160 ∣ Nat.card N ∨ 20160 ∣ N.index)
    {f : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3)} (hsymm : ∀ x y, f x y = f y x)
    (hnd : ∀ x, (∀ y, f x y = 0) → x = 0)
    (hmod : fischerCentralQuotientModel (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g))
      (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
      (fischerTransvections (fun x y => f x y) fun v => f v v = 1)) : False := by
  have hf : IsF3Form f := ⟨hsymm, hnd⟩
  obtain ⟨ψ, -⟩ := (fischerCentralQuotientModel_iff _).1 hmod
  have hcX : Nat.card (S.Xbar12 g) = Nat.card (R3 f) := Nat.card_congr ψ.toEquiv
  obtain ⟨v, hv⟩ := F3.exists_norm_eq hf (by norm_num) (one_ne_zero (α := ZMod 3))
  obtain ⟨w, hw, hwv⟩ := F3.exists_norm_eq_perp hf (by norm_num) hv (one_ne_zero (α := ZMod 3))
  have hvw : f v w = 0 := by rw [hsymm]; exact hwv
  have hne : reflBar f v ≠ reflBar f w := by
    rw [Ne, reflBar_eq_reflBar_iff hf (by norm_num) hv hw]
    rintro (rfl | rfl)
    · rw [hv] at hwv
      exact one_ne_zero hwv
    · rw [LinearMap.BilinForm.neg_left, hv] at hwv
      exact absurd hwv (by decide)
  have h4 : 4 ∣ Nat.card (R3 f) :=
    S12Insp4P.four_dvd_card_of_commute (reflBar_mul_self v) (reflBar_mul_self w)
      (reflBar_ne_one hf (by norm_num) hv) (reflBar_ne_one hf (by norm_num) hw) hne
      ((reflBar_commute_iff hf (by norm_num) hv hw).2 (Or.inl hvw))
  have h7 : ¬ 7 ∣ Nat.card (R3 f) := fun h =>
    S12Insp4P.not_seven_dvd_card_GL_five_three
      ((h.trans (card_quotient_dvd_card _)).trans (card_subgroup_dvd_card _))
  refine false_of_section (g := g) hP hsec (hcX ▸ h4) fun h => h7 ?_
  rw [← hcX]
  exact (by norm_num : 7 ∣ 20160).trans h

end Setting

end CFSG.LargeExtraspecial
