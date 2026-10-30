module

public import CFSG.HardMathSupport.Dickson.BMRows.Types
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporRows

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.BMRows.M11

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def GoodM12 (T : Type) [Group T] : Prop :=
  Nonempty (T ≃* (TauCeti.CFSGIndex.sporadic .M12).Group)

@[expose] def TrivRk (_T : Type) [Group _T] : Prop := True

theorem GoodM12.of_equiv {T T' : Type} [Group T] [Group T'] (f : T ≃* T') (h : GoodM12 T) :
    GoodM12 T' := by
  obtain ⟨g⟩ := h
  exact ⟨f.symm.trans g⟩

theorem kLevel_goodM12 : ∀ (T : Type) [Group T], GoodM12 T → kLevel 11 T ≤ 2 := by
  intro T _ ⟨e⟩
  exact kLevel_le_two_of_catalogIs (P := k2 11) ⟨.sporadic .M12, rfl, ⟨e⟩⟩ fun _ h => h

section M12


theorem card_of_goodM12 {T : Type} [Group T] (h : GoodM12 T) : Nat.card T = 95040 := by
  obtain ⟨e⟩ := h
  obtain ⟨f⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
  rw [Nat.card_congr (e.trans f.symm).toEquiv, CFSG.Sporadic.Mathieu.card_M12]

theorem finite_of_goodM12 {T : Type} [Group T] (h : GoodM12 T) : Finite T :=
  Nat.finite_of_card_ne_zero (by rw [card_of_goodM12 h]; norm_num)

theorem isSimpleGroup_of_goodM12 {T : Type} [Group T] (h : GoodM12 T) : IsSimpleGroup T := by
  obtain ⟨e⟩ := h
  obtain ⟨f⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
  have := CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
  exact (e.trans f.symm).isSimpleGroup

theorem noncomm_of_goodM12 {T : Type} [Group T] (h : GoodM12 T) : ∃ a b : T, a * b ≠ b * a := by
  have := isSimpleGroup_of_goodM12 h
  by_contra hc
  push Not at hc
  letI : CommGroup T := { (inferInstance : Group T) with mul_comm := hc }
  have hp := IsSimpleGroup.prime_card (α := T)
  rw [card_of_goodM12 h] at hp
  norm_num at hp

theorem not_sq_dvd_card_mulAut_goodM12
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) {T : Type} [Group T]
    (h : GoodM12 T) : ¬ 11 ^ 2 ∣ Nat.card (MulAut T) := by
  haveI := finite_of_goodM12 h
  haveI := isSimpleGroup_of_goodM12 h
  have hnc := noncomm_of_goodM12 h
  have hZ : Subgroup.center T = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hnc
  have hO : Nat.card (Outer T) ≤ 2 := hOut T inferInstance hnc .M12 h
  have hinj : Function.Injective (MulAut.conj : T →* MulAut T) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hmem : a ∈ Subgroup.center T := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut T => φ g) ha
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      exact (mul_inv_eq_iff_eq_mul.mp this).symm
    rw [hZ] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hI : Nat.card (inner T) = Nat.card T := by
    have : inner T = (MulAut.conj : T →* MulAut T).range := rfl
    rw [this]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hA : Nat.card (MulAut T) = Nat.card (Outer T) * Nat.card T := by
    rw [← hI]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup (inner T)
  haveI : Finite (MulAut T) := MulEquiv.finite_left
  have hpos : 0 < Nat.card (MulAut T) := Nat.card_pos
  rw [hA, card_of_goodM12 h] at hpos ⊢
  rcases (by omega : Nat.card (Outer T) = 1 ∨ Nat.card (Outer T) = 2) with h1 | h1 <;>
    rw [h1] <;> norm_num

theorem typeOK_goodM12 (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) :
    ∀ (T : Type) [Group T], GoodM12 T → I1416Rows.TypeOK 11 T := by
  intro T _ h _ ha _
  exact absurd ha (not_sq_dvd_card_mulAut_goodM12 hOut h)

theorem qtypeOK_goodM12 (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) :
    ∀ (T : Type) [Group T], GoodM12 T → I1416QRows.QTypeOK 11 T := by
  intro T _ h
  haveI := finite_of_goodM12 h
  exact I1416QRows.qtypeOK_of_not_sq_dvd_aut (by norm_num) (not_sq_dvd_card_mulAut_goodM12 hOut h)

theorem ctypeOK_goodM12 (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    ∀ (T : Type) [Group T], GoodM12 T → Chev2Rows.CTypeOK 11 T := by
  intro T _ h
  haveI := finite_of_goodM12 h
  exact Chev2Rows.ctypeOK_of_card_eq hb (card_of_goodM12 h)

end M12

end CFSG.HardMathSupport.Dickson.BMRows.M11
