module

public import Mathlib.GroupTheory.Complement
public import Mathlib.Algebra.BigOperators.Finprod

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {G : Type*} [Group G] {P : Subgroup G} {T : Set G} {Q : Type*} [CommGroup Q]

noncomputable def transversalAct (hT : IsComplement (P : Set G) T) (t : T) (g : G) : T :=
  (hT.equiv ((t : G) * g)).2

noncomputable def transversalCocycle (hT : IsComplement (P : Set G) T) (t : T) (g : G) : P :=
  (hT.equiv ((t : G) * g)).1

variable (hT : IsComplement (P : Set G) T)

theorem transversalAct_eq (t : T) (g : G) : transversalAct hT t g = (hT.equiv ((t : G) * g)).2 :=
  (rfl)

theorem transversalCocycle_eq (t : T) (g : G) :
    transversalCocycle hT t g = (hT.equiv ((t : G) * g)).1 :=
  (rfl)

theorem transversalCocycle_mul_transversalAct (t : T) (g : G) :
    (transversalCocycle hT t g : G) * (transversalAct hT t g : G) = (t : G) * g := by
  rw [transversalCocycle_eq, transversalAct_eq]
  exact hT.equiv_fst_mul_equiv_snd _

theorem coe_transversalCocycle (t : T) (g : G) :
    (transversalCocycle hT t g : G) = (t : G) * g * (transversalAct hT t g : G)⁻¹ := by
  rw [transversalCocycle_eq, transversalAct_eq]
  exact hT.equiv_fst_eq_mul_inv _

theorem mul_mul_transversalAct_inv_mem (t : T) (g : G) :
    (t : G) * g * (transversalAct hT t g : G)⁻¹ ∈ P :=
  coe_transversalCocycle hT t g ▸ (transversalCocycle hT t g).2

theorem rightCosetEquivalence_transversalAct (t : T) (g : G) :
    RightCosetEquivalence (P : Set G) ((t : G) * g) (transversalAct hT t g) := by
  rw [transversalAct_eq]
  exact hT.rightCosetEquivalence_equiv_snd _

theorem eq_transversalAct_iff (t : T) (g : G) (s : T) :
    s = transversalAct hT t g ↔ RightCosetEquivalence (P : Set G) ((t : G) * g) (s : G) := by
  rw [transversalAct_eq, ← hT.equiv_snd_eq_iff_rightCosetEquivalence,
    hT.equiv_snd_eq_self_of_mem_of_one_mem P.one_mem s.2]
  exact ⟨fun h => by rw [h], fun h => by simpa using h.symm⟩

@[simp]
theorem transversalAct_one (t : T) : transversalAct hT t 1 = t := by
  rw [transversalAct_eq, mul_one, hT.equiv_snd_eq_self_of_mem_of_one_mem P.one_mem t.2]

@[simp]
theorem transversalCocycle_one (t : T) : transversalCocycle hT t 1 = 1 := by
  apply Subtype.ext
  rw [coe_transversalCocycle, transversalAct_one, mul_one, mul_inv_cancel, OneMemClass.coe_one]

private theorem equiv_mul_mul (t : T) (g h : G) :
    hT.equiv ((t : G) * (g * h)) =
      (transversalCocycle hT t g * transversalCocycle hT (transversalAct hT t g) h,
        transversalAct hT (transversalAct hT t g) h) := by
  have key : (t : G) * (g * h)
      = (transversalCocycle hT t g : G) * ((transversalAct hT t g : G) * h) :=
    calc (t : G) * (g * h) = (t : G) * g * h := (mul_assoc _ _ _).symm
      _ = (transversalCocycle hT t g : G) * (transversalAct hT t g : G) * h := by
          rw [transversalCocycle_mul_transversalAct]
      _ = (transversalCocycle hT t g : G) * ((transversalAct hT t g : G) * h) := mul_assoc _ _ _
  rw [key, hT.equiv_mul_left, transversalCocycle_eq hT (transversalAct hT t g) h,
    transversalAct_eq hT (transversalAct hT t g) h]

theorem transversalAct_mul (t : T) (g h : G) :
    transversalAct hT (transversalAct hT t g) h = transversalAct hT t (g * h) := by
  rw [transversalAct_eq hT t (g * h), equiv_mul_mul]

theorem transversalCocycle_mul (t : T) (g h : G) :
    transversalCocycle hT t (g * h)
      = transversalCocycle hT t g * transversalCocycle hT (transversalAct hT t g) h := by
  rw [transversalCocycle_eq hT t (g * h), equiv_mul_mul]

noncomputable def transversalPerm (g : G) : Equiv.Perm T where
  toFun t := transversalAct hT t g
  invFun t := transversalAct hT t g⁻¹
  left_inv t := by simp only [transversalAct_mul, mul_inv_cancel, transversalAct_one]
  right_inv t := by simp only [transversalAct_mul, inv_mul_cancel, transversalAct_one]

@[simp]
theorem transversalPerm_apply (g : G) (t : T) : transversalPerm hT g t = transversalAct hT t g :=
  (rfl)

@[simp]
theorem transversalPerm_symm_apply (g : G) (t : T) :
    (transversalPerm hT g).symm t = transversalAct hT t g⁻¹ :=
  (rfl)

theorem transversalAct_bijective (g : G) :
    Function.Bijective (fun t : T => transversalAct hT t g) :=
  (transversalPerm hT g).bijective

noncomputable def transversalTransfer (f : P →* Q) (g : G) : Q :=
  ∏ᶠ t : T, f (transversalCocycle hT t g)

theorem transversalTransfer_eq_finprod (f : P →* Q) (g : G) :
    transversalTransfer hT f g = ∏ᶠ t : T, f (transversalCocycle hT t g) :=
  (rfl)

theorem transversalTransfer_eq_prod [Fintype T] (f : P →* Q) (g : G) :
    transversalTransfer hT f g = ∏ t : T, f (transversalCocycle hT t g) :=
  finprod_eq_prod_of_fintype _

@[simp]
theorem transversalTransfer_one (f : P →* Q) : transversalTransfer hT f 1 = 1 := by
  simp [transversalTransfer]

theorem transversalTransfer_mul [Finite T] (f : P →* Q) (g h : G) :
    transversalTransfer hT f (g * h)
      = transversalTransfer hT f g * transversalTransfer hT f h := by
  simp only [transversalTransfer, transversalCocycle_mul, map_mul]
  rw [finprod_mul_distrib (Set.toFinite _) (Set.toFinite _)]
  congr 1
  have := finprod_comp_equiv (transversalPerm hT g)
    (f := fun t : T => f (transversalCocycle hT t h))
  simpa using this

noncomputable def transversalTransferHom [Finite T] (f : P →* Q) : G →* Q where
  toFun := transversalTransfer hT f
  map_one' := transversalTransfer_one hT f
  map_mul' := transversalTransfer_mul hT f

@[simp]
theorem transversalTransferHom_apply [Finite T] (f : P →* Q) (g : G) :
    transversalTransferHom hT f g = transversalTransfer hT f g :=
  (rfl)

end CFSG.FeitThompson
