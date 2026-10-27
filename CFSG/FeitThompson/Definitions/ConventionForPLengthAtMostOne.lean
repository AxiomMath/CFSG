module

public import CFSG.FeitThompson.Local.PiCoreLargestNormalSubgroup
public import Mathlib.GroupTheory.Sylow

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {p : ℕ} {X : Type*} [Group X] [Finite X]

def HasPLengthLeOne (p : ℕ) (X : Type*) [Group X] [Finite X] : Prop :=
  ∃ P : Sylow p (X ⧸ pComplCore p X),
    (P : Subgroup (X ⧸ pComplCore p X)) = pCore p (X ⧸ pComplCore p X)

theorem hasPLengthLeOne_iff :
    HasPLengthLeOne p X ↔ ∃ P : Sylow p (X ⧸ pComplCore p X),
      (P : Subgroup (X ⧸ pComplCore p X)) = pCore p (X ⧸ pComplCore p X) := Iff.rfl

theorem HasPLengthLeOne.exists_sylow_eq (h : HasPLengthLeOne p X) :
    ∃ P : Sylow p (X ⧸ pComplCore p X),
      (P : Subgroup (X ⧸ pComplCore p X)) = pCore p (X ⧸ pComplCore p X) := h

theorem hasPLengthLeOne_of_sylow_eq (P : Sylow p (X ⧸ pComplCore p X))
    (hP : (P : Subgroup (X ⧸ pComplCore p X)) = pCore p (X ⧸ pComplCore p X)) :
    HasPLengthLeOne p X := ⟨P, hP⟩

variable [Fact p.Prime]

theorem hasPLengthLeOne_iff_not_dvd_index :
    HasPLengthLeOne p X ↔ ¬ p ∣ (pCore p (X ⧸ pComplCore p X)).index := by
  constructor
  · rintro ⟨P, hP⟩
    rw [← hP]
    exact P.not_dvd_index
  · exact fun h => ⟨(isPGroup_pCore Fact.out _).toSylow h, IsPGroup.toSylow_coe _ _⟩

theorem HasPLengthLeOne.not_dvd_index (h : HasPLengthLeOne p X) :
    ¬ p ∣ (pCore p (X ⧸ pComplCore p X)).index :=
  hasPLengthLeOne_iff_not_dvd_index.1 h

def HasPLengthLeOne.sylow (h : HasPLengthLeOne p X) : Sylow p (X ⧸ pComplCore p X) :=
  (isPGroup_pCore Fact.out _).toSylow h.not_dvd_index

@[simp]
theorem HasPLengthLeOne.coe_sylow (h : HasPLengthLeOne p X) :
    (h.sylow : Subgroup (X ⧸ pComplCore p X)) = pCore p (X ⧸ pComplCore p X) :=
  IsPGroup.toSylow_coe _ _

theorem HasPLengthLeOne.normal_sylow (h : HasPLengthLeOne p X) :
    (h.sylow : Subgroup (X ⧸ pComplCore p X)).Normal := by
  rw [h.coe_sylow, pCore_eq_piCore]
  exact piCore_normal _ _

theorem HasPLengthLeOne.subsingleton_sylow (h : HasPLengthLeOne p X) :
    Subsingleton (Sylow p (X ⧸ pComplCore p X)) :=
  have := h.sylow.unique_of_normal h.normal_sylow
  inferInstance

theorem HasPLengthLeOne.coe_eq_pCore (h : HasPLengthLeOne p X)
    (P : Sylow p (X ⧸ pComplCore p X)) :
    (P : Subgroup (X ⧸ pComplCore p X)) = pCore p (X ⧸ pComplCore p X) := by
  have := h.subsingleton_sylow
  rw [Subsingleton.elim P h.sylow, h.coe_sylow]

theorem hasPLengthLeOne_iff_forall_sylow :
    HasPLengthLeOne p X ↔ ∀ P : Sylow p (X ⧸ pComplCore p X),
      (P : Subgroup (X ⧸ pComplCore p X)) = pCore p (X ⧸ pComplCore p X) :=
  ⟨fun h => h.coe_eq_pCore, fun h => ⟨Classical.arbitrary _, h _⟩⟩

theorem hasPLengthLeOne_iff_card :
    HasPLengthLeOne p X ↔ Nat.card (pCore p (X ⧸ pComplCore p X))
      = p ^ (Nat.card (X ⧸ pComplCore p X)).factorization p := by
  constructor
  · rintro ⟨P, hP⟩
    exact hP ▸ P.card_eq_multiplicity
  · exact fun h => ⟨Sylow.ofCard _ h, Sylow.coe_ofCard _ h⟩

theorem hasPLengthLeOne_iff_normal_sylow :
    HasPLengthLeOne p X ↔ ∀ P : Sylow p (X ⧸ pComplCore p X),
      (P : Subgroup (X ⧸ pComplCore p X)).Normal := by
  refine ⟨fun h P => ?_, fun h => ?_⟩
  · rw [h.coe_eq_pCore P, pCore_eq_piCore]
    exact piCore_normal _ _
  · refine ⟨Classical.arbitrary _, ?_⟩
    set P := Classical.arbitrary (Sylow p (X ⧸ pComplCore p X))
    exact (P.is_maximal' (isPGroup_pCore Fact.out _)
      (le_pCore Fact.out (h P) P.isPGroup')).symm

theorem hasPLengthLeOne_of_not_dvd_card (h : ¬ p ∣ Nat.card X) : HasPLengthLeOne p X := by
  rw [hasPLengthLeOne_iff_not_dvd_index]
  exact fun hdvd => h (hdvd.trans
    ((Subgroup.index_dvd_card _).trans (Subgroup.card_quotient_dvd_card _)))

end

end CFSG.FeitThompson
