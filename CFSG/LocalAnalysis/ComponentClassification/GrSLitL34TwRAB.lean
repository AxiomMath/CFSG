module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwRA

public section

namespace CFSG.ComponentClassification.GrSLit.L34Tw

open CFSG Subgroup CFSG.ComponentClassification.PSL3Four

theorem mem_wrR_iff {x : WrE} : x ∈ wrR ↔ x.a ∈ R ∧ x.b ∈ R := Iff.rfl

theorem mem_ssS_iff {x : WrE} : x ∈ ssS ↔ x.e = false ∧ x.a ∈ S ∧ x.b ∈ S := Iff.rfl

theorem mem_Pw_iff {x : WrE} : x ∈ Pw ↔ x.a ∈ RA ∧ x.b ∈ RA := Iff.rfl

theorem mem_N0w_iff {x : WrE} :
    x ∈ N0w ↔ x.e = false ∧ x.a ∈ L34Facts.T0 ∧ x.b ∈ L34Facts.T0 := Iff.rfl

private def wreathEquiv (A : Subgroup (Equiv.Perm (Fin 42))) (P : Subgroup WrE)
    (hP : ∀ x, x ∈ P ↔ x.a ∈ A ∧ x.b ∈ A) : P ≃ A × A × Bool where
  toFun x := (⟨x.1.a, ((hP _).1 x.2).1⟩, ⟨x.1.b, ((hP _).1 x.2).2⟩, x.1.e)
  invFun p := ⟨⟨p.1.1, p.2.1.1, p.2.2⟩, (hP _).2 ⟨p.1.2, p.2.1.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def noSwapEquiv (A : Subgroup (Equiv.Perm (Fin 42))) (P : Subgroup WrE)
    (hP : ∀ x, x ∈ P ↔ x.e = false ∧ x.a ∈ A ∧ x.b ∈ A) : P ≃ A × A where
  toFun x := (⟨x.1.a, ((hP _).1 x.2).2.1⟩, ⟨x.1.b, ((hP _).1 x.2).2.2⟩)
  invFun p := ⟨⟨p.1.1, p.2.1, false⟩, (hP _).2 ⟨rfl, p.1.2, p.2.2⟩⟩
  left_inv x := Subtype.ext (WrE.ext rfl rfl ((hP _).1 x.2).1.symm)
  right_inv _ := rfl

private theorem card_wreath (A : Subgroup (Equiv.Perm (Fin 42))) (P : Subgroup WrE)
    (hP : ∀ x, x ∈ P ↔ x.a ∈ A ∧ x.b ∈ A) : Nat.card P = 2 * Nat.card A ^ 2 := by
  rw [Nat.card_congr (wreathEquiv A P hP), Nat.card_prod, Nat.card_prod,
    Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
  ring

private theorem card_noSwap (A : Subgroup (Equiv.Perm (Fin 42))) (P : Subgroup WrE)
    (hP : ∀ x, x ∈ P ↔ x.e = false ∧ x.a ∈ A ∧ x.b ∈ A) : Nat.card P = Nat.card A ^ 2 := by
  rw [Nat.card_congr (noSwapEquiv A P hP), Nat.card_prod]
  ring

theorem card_wrR : Nat.card wrR = 2 * Nat.card R ^ 2 := card_wreath R wrR fun _ => Iff.rfl

theorem card_Pw : Nat.card Pw = 2 * Nat.card RA ^ 2 := card_wreath RA Pw fun _ => Iff.rfl

theorem Pw_le_wrR : Pw ≤ wrR := fun _ hx =>
  mem_wrR_iff.2 ⟨RA_le_R (mem_Pw_iff.1 hx).1, RA_le_R (mem_Pw_iff.1 hx).2⟩

theorem Pw_inf_ssS :
    Pw ⊓ ssS = N0w := by
  ext x
  rw [Subgroup.mem_inf, mem_Pw_iff, mem_ssS_iff, mem_N0w_iff]
  have key : ∀ y : Equiv.Perm (Fin 42), (y ∈ RA ∧ y ∈ S) ↔ y ∈ L34Facts.T0 := fun y => by
    rw [← Subgroup.mem_inf, RA_inf_S]
  constructor
  · rintro ⟨⟨ha, hb⟩, he, haS, hbS⟩
    exact ⟨he, (key _).1 ⟨ha, haS⟩, (key _).1 ⟨hb, hbS⟩⟩
  · rintro ⟨he, ha, hb⟩
    exact ⟨⟨T0_le_RA ha, T0_le_RA hb⟩, he, L34Facts.T0_le_S ha, L34Facts.T0_le_S hb⟩

theorem card_N0w : Nat.card N0w = 2 ^ 12 := by
  rw [card_noSwap L34Facts.T0 N0w fun _ => Iff.rfl, card_T0_ra]
  norm_num

end CFSG.ComponentClassification.GrSLit.L34Tw
