
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshModelBase

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Subgroup

@[expose] def extEquiv : Fin 12 ≃ {x : Fin 14 // x.val < 12} where
  toFun i := ⟨⟨i.val, by omega⟩, i.2⟩
  invFun x := ⟨x.1.val, x.2⟩
  left_inv i := by simp
  right_inv x := by simp

@[expose] noncomputable def extHom : Equiv.Perm (Fin 12) →* Equiv.Perm (Fin 14) :=
  Equiv.Perm.extendDomainHom extEquiv

theorem extHom_injective : Function.Injective extHom :=
  Equiv.Perm.extendDomainHom_injective extEquiv

theorem extHom_apply_lt (σ : Equiv.Perm (Fin 12)) (i : Fin 14) (h : i.val < 12) :
    (extHom σ i).val = (σ ⟨i.val, h⟩).val := by
  have := Equiv.Perm.extendDomain_apply_image σ extEquiv ⟨i.val, h⟩
  have hi : ((extEquiv ⟨i.val, h⟩ : {x : Fin 14 // x.val < 12}) : Fin 14) = i := by
    simp [extEquiv]
  rw [hi] at this
  simp only [extHom, Equiv.Perm.extendDomainHom_apply]
  rw [this]
  simp [extEquiv]

theorem extHom_apply_ge (σ : Equiv.Perm (Fin 12)) (i : Fin 14) (h : ¬ i.val < 12) :
    extHom σ i = i := by
  simp only [extHom, Equiv.Perm.extendDomainHom_apply]
  exact Equiv.Perm.extendDomain_apply_not_subtype σ extEquiv h

@[expose] def tauP : Equiv.Perm (Fin 14) := Equiv.swap ⟨12, by omega⟩ ⟨13, by omega⟩

theorem tauP_sq : tauP * tauP = 1 := by
  simp [tauP, Equiv.swap_mul_self]

theorem tauP_apply_lt (i : Fin 14) (h : i.val < 12) : tauP i = i := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h'
    have := congrArg Fin.val h'
    simp at this
    omega
  · intro h'
    have := congrArg Fin.val h'
    simp at this
    omega

theorem tauP_apply_ge (i : Fin 14) (h : ¬ i.val < 12) : ¬ (tauP i).val < 12 := by
  have hi : i.val = 12 ∨ i.val = 13 := by omega
  rcases hi with hi | hi
  · have : i = ⟨12, by omega⟩ := Fin.ext hi
    rw [this]
    simp [tauP]
  · have : i = ⟨13, by omega⟩ := Fin.ext hi
    rw [this]
    simp [tauP]

theorem extHom_comm_tauP (σ : Equiv.Perm (Fin 12)) : extHom σ * tauP = tauP * extHom σ := by
  ext i
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  by_cases h : i.val < 12
  · rw [tauP_apply_lt i h]
    have hlt : (extHom σ i).val < 12 := by rw [extHom_apply_lt σ i h]; exact (σ _).2
    rw [tauP_apply_lt _ hlt]
  · rw [extHom_apply_ge σ i h, extHom_apply_ge σ _ (tauP_apply_ge i h)]

theorem zmod_two_cases (v : ZMod 2) : v = 0 ∨ v = 1 := by
  revert v; decide

@[expose] noncomputable def tauPow (a : Multiplicative (ZMod 2)) : Equiv.Perm (Fin 14) :=
  tauP ^ (Multiplicative.toAdd a).val

theorem tauPow_mul (a b : Multiplicative (ZMod 2)) : tauPow (a * b) = tauPow a * tauPow b := by
  unfold tauPow
  rw [toAdd_mul, ZMod.val_add, ← pow_add]
  have h2 : tauP ^ 2 = 1 := by rw [pow_two]; exact tauP_sq
  rw [pow_eq_pow_mod (a := tauP) ((Multiplicative.toAdd a).val + (Multiplicative.toAdd b).val) h2]

theorem tauPow_one : tauPow 1 = 1 := by simp [tauPow]

theorem tauPow_apply_lt (a : Multiplicative (ZMod 2)) (i : Fin 14) (h : i.val < 12) :
    tauPow a i = i := by
  unfold tauPow
  induction (Multiplicative.toAdd a).val with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Equiv.Perm.coe_mul, Function.comp_apply, tauP_apply_lt i h, ih]

theorem tauPow_apply_twelve (a : Multiplicative (ZMod 2)) :
    (tauPow a ⟨12, by omega⟩).val = 12 + (Multiplicative.toAdd a).val := by
  have hv : (Multiplicative.toAdd a).val = 0 ∨ (Multiplicative.toAdd a).val = 1 := by
    rcases zmod_two_cases (Multiplicative.toAdd a) with h | h
    · left; rw [h]; rfl
    · right; rw [h]; rfl
  unfold tauPow
  rcases hv with hv | hv <;> rw [hv]
  · simp
  · simp [tauP]

theorem tauPow_comm (a : Multiplicative (ZMod 2)) (σ : Equiv.Perm (Fin 12)) :
    Commute (tauPow a) (extHom σ) := by
  unfold tauPow
  have hc : Commute tauP (extHom σ) := (extHom_comm_tauP σ).symm
  exact hc.pow_left _

@[expose] noncomputable def kapP : Multiplicative (ZMod 2) × Equiv.Perm (Fin 12) →*
    Equiv.Perm (Fin 14) where
  toFun p := tauPow p.1 * extHom p.2
  map_one' := by simp [tauPow_one]
  map_mul' p q := by
    show tauPow (p.1 * q.1) * extHom (p.2 * q.2) =
      (tauPow p.1 * extHom p.2) * (tauPow q.1 * extHom q.2)
    rw [tauPow_mul, map_mul]
    have h := (tauPow_comm q.1 p.2).eq
    calc tauPow p.1 * tauPow q.1 * (extHom p.2 * extHom q.2)
        = tauPow p.1 * (tauPow q.1 * extHom p.2) * extHom q.2 := by simp only [mul_assoc]
      _ = tauPow p.1 * (extHom p.2 * tauPow q.1) * extHom q.2 := by rw [h]
      _ = _ := by simp only [mul_assoc]

theorem kapP_apply (a : Multiplicative (ZMod 2)) (σ : Equiv.Perm (Fin 12)) :
    kapP (a, σ) = tauPow a * extHom σ := rfl

theorem rep_tbl14 (σ : Equiv.Perm (Fin 12)) : Rep 14 (tbl14 σ) (extHom σ) := by
  intro i hi
  rw [idx_of_lt _ hi]
  have hget : (tbl14 σ)[i]! =
      if h : i < 12 then ((σ ⟨i, h⟩ : Fin 12).val.toUInt32) else i.toUInt32 := by
    simp [tbl14, hi]
  simp only [ap, hget]
  by_cases h : i < 12
  · rw [dif_pos h]
    have := extHom_apply_lt σ ⟨i, hi⟩ h
    simp only [Equiv.Perm.smul_def]
    rw [this]
    simp
    have := (σ ⟨i, h⟩).2
    omega
  · rw [dif_neg h]
    have := extHom_apply_ge σ ⟨i, hi⟩ h
    simp only [Equiv.Perm.smul_def]
    rw [this]
    simp
    omega

theorem rep_tauT : Rep 14 tauT tauP := by
  intro i hi
  rw [idx_of_lt _ hi]
  have hget : tauT[i]! = if i = 12 then (13 : UInt32) else if i = 13 then 12 else i.toUInt32 := by
    simp [tauT, hi]
  simp only [ap, hget, Equiv.Perm.smul_def]
  by_cases h12 : i = 12
  · subst h12
    simp [tauP]
  · by_cases h13 : i = 13
    · subst h13
      simp [tauP]
    · have hne1 : (⟨i, hi⟩ : Fin 14) ≠ ⟨12, by omega⟩ := fun h =>
        h12 (by simpa using congrArg Fin.val h)
      have hne2 : (⟨i, hi⟩ : Fin 14) ≠ ⟨13, by omega⟩ := fun h =>
        h13 (by simpa using congrArg Fin.val h)
      rw [tauP, Equiv.swap_apply_of_ne_of_ne hne1 hne2]
      simp [h12, h13]
      omega

end CFSG.EvenSporadicStandard.M12Std.Yosh
