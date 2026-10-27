module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Irred

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family

abbrev V3 : Type := Fin 3 → ZMod 2

@[expose] def act (g : GL32) (x : V3) : V3 := (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec x

theorem act_one (x : V3) : act 1 x = x := by simp [act]

theorem act_mul (g h : GL32) (x : V3) : act (g * h) x = act g (act h x) := by
  simp [act, Matrix.mulVec_mulVec]

theorem act_add (g : GL32) (x y : V3) : act g (x + y) = act g x + act g y := by
  simp [act, Matrix.mulVec_add]

theorem act_zero (g : GL32) : act g 0 = 0 := by simp [act]

theorem act_inv_act (g : GL32) (x : V3) : act g⁻¹ (act g x) = x := by
  rw [← act_mul, inv_mul_cancel, act_one]

theorem act_act_inv (g : GL32) (x : V3) : act g (act g⁻¹ x) = x := by
  rw [← act_mul, mul_inv_cancel, act_one]

theorem act_eq_zero_iff (g : GL32) (x : V3) : act g x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have := congrArg (act g⁻¹) h
    rwa [act_inv_act, act_zero] at this
  · rintro rfl
    exact act_zero g

theorem add_self_V3 (p : V3) : p + p = 0 := by
  ext i
  have h : ∀ a : ZMod 2, a + a = 0 := by decide
  simpa using h (p i)

theorem act_fixes_of_forall {g : GL32} {p : V3}
    (hg : ∀ x : V3, act g x = x ∨ act g x = x + p) : act g p = p := by
  rcases hg p with h | h
  · exact h
  · rw [add_self_V3] at h
    have : p = 0 := (act_eq_zero_iff g p).1 h
    rw [this, act_zero]

@[expose] def Spt (p : V3) : Subgroup GL32 where
  carrier := {g | ∀ x : V3, act g x = x ∨ act g x = x + p}
  one_mem' := fun x => Or.inl (act_one x)
  mul_mem' := by
    intro g h hg hh x
    have hgp : act g p = p := act_fixes_of_forall hg
    show act (g * h) x = x ∨ act (g * h) x = x + p
    rw [act_mul]
    rcases hh x with h1 | h1
    · rw [h1]
      exact hg x
    · rw [h1, act_add, hgp]
      rcases hg x with h2 | h2
      · right
        rw [h2]
      · left
        rw [h2, add_assoc, add_self_V3, add_zero]
  inv_mem' := by
    intro g hg x
    have h := hg (act g⁻¹ x)
    rw [act_act_inv] at h
    show act g⁻¹ x = x ∨ act g⁻¹ x = x + p
    generalize act g⁻¹ x = y at h ⊢
    rcases h with h | h
    · left
      exact h.symm
    · right
      rw [h, add_assoc, add_self_V3, add_zero]

theorem mem_Spt {g : GL32} {p : V3} : g ∈ Spt p ↔ ∀ x : V3, act g x = x ∨ act g x = x + p :=
  Iff.rfl

@[expose] def Pstab (p : V3) : Subgroup GL32 where
  carrier := {g | act g p = p}
  one_mem' := act_one p
  mul_mem' := by
    intro g h hg hh
    show act (g * h) p = p
    rw [act_mul]
    change act h p = p at hh
    change act g p = p at hg
    rw [hh, hg]
  inv_mem' := by
    intro g hg
    change act g p = p at hg
    show act g⁻¹ p = p
    have := congrArg (act g⁻¹) hg
    rw [act_inv_act] at this
    exact this.symm

theorem mem_Pstab {g : GL32} {p : V3} : g ∈ Pstab p ↔ act g p = p := Iff.rfl

section Module

variable (M : Type*) [AddCommGroup M] [DistribMulAction GL32 M]

@[expose] def fixSub (H : Subgroup GL32) : AddSubgroup M where
  carrier := {m | ∀ g ∈ H, g • m = m}
  zero_mem' := fun g _ => smul_zero g
  add_mem' := by
    intro a b ha hb g hg
    rw [smul_add, ha g hg, hb g hg]
  neg_mem' := by
    intro a ha g hg
    rw [smul_neg, ha g hg]

variable {M}

theorem mem_fixSub {H : Subgroup GL32} {m : M} : m ∈ fixSub M H ↔ ∀ g ∈ H, g • m = m := Iff.rfl

@[expose] def commSub (M : Type*) [AddCommGroup M] [DistribMulAction GL32 M] (H : Subgroup GL32) :
    AddSubgroup M :=
  AddSubgroup.closure {x | ∃ g ∈ H, ∃ m : M, x = g • m - m}

end Module

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813
