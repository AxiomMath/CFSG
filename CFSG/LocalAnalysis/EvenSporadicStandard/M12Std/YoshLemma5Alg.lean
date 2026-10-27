module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshWord

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

section Alg

variable {H : Type*} [Group H]

theorem conj_lift_substW {m : ℕ} (z : H) (g : Fin m → H) (W : Fin m → List (Fin m × Bool))
    (hW : ∀ i, z⁻¹ * g i * z = FreeGroup.lift g (FreeGroup.mk (W i)))
    (w : List (Fin m × Bool)) :
    z⁻¹ * FreeGroup.lift g (FreeGroup.mk w) * z =
      FreeGroup.lift g (FreeGroup.mk (substW W w)) := by
  induction w with
  | nil => simp [substW]
  | cons l w ih =>
    obtain ⟨i, b⟩ := l
    have h1 : substW W ((i, b) :: w) = (if b then W i else invW (W i)) ++ substW W w := by
      simp [substW]
    rw [h1, show FreeGroup.mk ((i, b) :: w) = FreeGroup.mk [(i, b)] * FreeGroup.mk w from rfl,
      map_mul, lift_mk_append, ← ih]
    have h2 : z⁻¹ * FreeGroup.lift g (FreeGroup.mk [(i, b)]) * z =
        FreeGroup.lift g (FreeGroup.mk (if b then W i else invW (W i))) := by
      cases b
      · simp only [Bool.false_eq_true, if_false, lift_mk_invW]
        rw [← hW i]
        simp [mul_assoc]
      · simp only [if_true]
        rw [← hW i]
        simp
    calc z⁻¹ * (FreeGroup.lift g (FreeGroup.mk [(i, b)]) * FreeGroup.lift g (FreeGroup.mk w)) * z
        = (z⁻¹ * FreeGroup.lift g (FreeGroup.mk [(i, b)]) * z) *
          (z⁻¹ * FreeGroup.lift g (FreeGroup.mk w) * z) := by group
      _ = _ := by rw [h2]

theorem lift_mk_map {m k : ℕ} (f : Fin m → Fin k) (g : Fin k → H) (w : List (Fin m × Bool)) :
    FreeGroup.lift (g ∘ f) (FreeGroup.mk w) =
      FreeGroup.lift g (FreeGroup.mk (w.map fun l => (f l.1, l.2))) := by
  induction w with
  | nil => simp
  | cons l w ih =>
    obtain ⟨i, b⟩ := l
    rw [show FreeGroup.mk ((i, b) :: w) = FreeGroup.mk [(i, b)] * FreeGroup.mk w from rfl,
      map_mul, ih, List.map_cons,
      show FreeGroup.mk ((f i, b) :: List.map (fun l => (f l.1, l.2)) w) =
        FreeGroup.mk [(f i, b)] * FreeGroup.mk (List.map (fun l => (f l.1, l.2)) w) from rfl,
      map_mul]
    congr 1

end Alg

end CFSG.EvenSporadicStandard.M12Std.Yosh
