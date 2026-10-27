module

public import CFSG.CGT.PushingUpLit.CGT6.TwoEightData

public section

namespace CFSG.CGT.PushingUpLit.CGT6X

open CFSG.CGT.PushingUpLit.CGT6.TwoEight

section Polar

variable {F L : Type} [Field F] [AddCommGroup L] [Module F L] (D : Data F L)

@[expose] def polarD (w w' : Wd F L) : F := w.1 * w'.2.2 + w'.1 * w.2.2 + D.B w.2.1 w'.2.1

theorem polarD_add_left (w w₁ w' : Wd F L) :
    polarD D (w + w₁) w' = polarD D w w' + polarD D w₁ w' := by
  simp only [polarD, Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]
  ring

theorem polarD_add_right (w w' w₁ : Wd F L) :
    polarD D w (w' + w₁) = polarD D w w' + polarD D w w₁ := by
  simp only [polarD, Prod.fst_add, Prod.snd_add, map_add]
  ring

theorem polarD_smul_right (c : F) (w w' : Wd F L) : polarD D w (c • w') = c * polarD D w w' := by
  simp only [polarD, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, B_smul_right]
  ring

variable [CharP F 2]

theorem wd_add_self_gen (w : Wd F L) : w + w = 0 :=
  Prod.ext (CharTwo.add_self_eq_zero _)
    (Prod.ext (add_self_L F _) (CharTwo.add_self_eq_zero _))

theorem polarD_eq (w w' : Wd F L) : polarD D w w' = Qt D (w + w') + Qt D w + Qt D w' := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  simp only [polarD, Qt, Prod.fst_add, Prod.snd_add]
  rw [D.Q_add]
  linear_combination (-(w.1 * w.2.2 + w'.1 * w'.2.2 + D.Q w.2.1 + D.Q w'.2.1)) * h2

theorem polarD_self (w : Wd F L) : polarD D w w = 0 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  simp only [polarD, D.alt]
  linear_combination (w.1 * w.2.2) * h2

omit [CharP F 2] in
theorem polarD_nondeg (w : Wd F L) (hw : w ≠ 0) : ∃ w' : Wd F L, polarD D w w' ≠ 0 := by
  obtain ⟨p, y, s⟩ := w
  by_cases hs : s = 0
  · by_cases hp : p = 0
    · have hy : y ≠ 0 := by
        rintro rfl
        exact hw (by rw [hs, hp]; rfl)
      obtain ⟨y', hy'⟩ := B_eq_zero_of_ne D hy
      refine ⟨(0, y', 0), ?_⟩
      simpa [polarD, hs, hp] using hy'
    · exact ⟨(0, 0, 1), by simpa [polarD, hs] using hp⟩
  · exact ⟨(1, 0, 0), by simpa [polarD] using hs⟩

theorem polarD_perm {α : Equiv.Perm (Wd F L)} (hadd : IsAddPerm α)
    (hQ : ∀ w, Qt D (α w) = Qt D w) (w w' : Wd F L) :
    polarD D (α w) (α w') = polarD D w w' := by
  rw [polarD_eq, polarD_eq, ← hadd, hQ, hQ, hQ]

end Polar

section Line

variable {F L : Type} [Field F] [AddCommGroup L] [Module F L] [CharP F 2] (D : Data F L)

theorem four_lt_ncard_range [Finite F] [Finite L] (hF : 4 ≤ Nat.card F)
    {α : Equiv.Perm (Wd F L)} (hadd : IsAddPerm α) (hQ : ∀ w, Qt D (α w) = Qt D w)
    (hsmul : ∀ (c : F) (w : Wd F L), α (c • w) = c • α w) (h3 : ∀ w, α (α (α w)) = w)
    (h1 : ∃ w, α w ≠ w) : 4 < Set.ncard {z : Wd F L | ∃ w, z = α w + w} := by
  by_contra hle
  rw [not_lt] at hle
  obtain ⟨u₀, hu₀⟩ := h1
  set R : Set (Wd F L) := {z | ∃ w, z = α w + w} with hR
  have hRfin : R.Finite := Set.toFinite R
  set w₀ : Wd F L := α u₀ + u₀ with hw₀def
  have hw₀ : w₀ ≠ 0 := by
    intro h
    have h' : α u₀ + u₀ = 0 := h
    apply hu₀
    calc α u₀ = α u₀ + (u₀ + u₀) := by rw [wd_add_self_gen, add_zero]
      _ = (α u₀ + u₀) + u₀ := by rw [add_assoc]
      _ = u₀ := by rw [h', zero_add]
  have hline : ∀ c : F, c • w₀ ∈ R := fun c => ⟨c • u₀, by rw [hsmul, smul_add]⟩
  have hinj : Function.Injective fun c : F => c • w₀ := smul_left_injective F hw₀
  have hsub : Set.range (fun c : F => c • w₀) ⊆ R := by
    rintro _ ⟨c, rfl⟩
    exact hline c
  have hcard : Set.ncard (Set.range fun c : F => c • w₀) = Nat.card F := by
    rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective hinj]
  have hReq : Set.range (fun c : F => c • w₀) = R :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hcard]; omega) hRfin
  have hmult : ∀ m : Wd F L, ∃ c : F, α m + m = c • w₀ := fun m => by
    have hm : α m + m ∈ R := ⟨m, rfl⟩
    rw [← hReq] at hm
    obtain ⟨c, hc⟩ := hm
    exact ⟨c, hc.symm⟩
  have hperp_fix : ∀ f : Wd F L, α f = f → polarD D w₀ f = 0 := by
    intro f hf
    have h := polarD_perm D hadd hQ u₀ f
    rw [hf] at h
    show polarD D (α u₀ + u₀) f = 0
    rw [polarD_add_left, h]
    exact CharTwo.add_self_eq_zero _
  have hperp_R : ∀ m : Wd F L, polarD D w₀ (α m + m) = 0 := by
    intro m
    obtain ⟨c, hc⟩ := hmult m
    rw [hc, polarD_smul_right, polarD_self, mul_zero]
  have hall : ∀ m : Wd F L, polarD D w₀ m = 0 := by
    intro m
    set f : Wd F L := α (α m) + α m + m with hf
    have hfix : α f = f := by
      rw [hf, hadd, hadd, h3]
      abel
    have hdecomp : m = f + α (α m + m) := by
      calc m = m + ((α (α m) + α m) + (α (α m) + α m)) := by rw [wd_add_self_gen, add_zero]
        _ = (α (α m) + α m + m) + (α (α m) + α m) := by abel
        _ = f + α (α m + m) := by rw [hadd]
    calc polarD D w₀ m = polarD D w₀ (f + α (α m + m)) := by rw [← hdecomp]
      _ = polarD D w₀ f + polarD D w₀ (α (α m + m)) := polarD_add_right D _ _ _
      _ = 0 := by
        rw [hperp_fix f hfix, zero_add, hadd]
        exact hperp_R (α m)
  obtain ⟨w', hw'⟩ := polarD_nondeg D w₀ hw₀
  exact hw' (hall w')

end Line

end CFSG.CGT.PushingUpLit.CGT6X
