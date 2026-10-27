module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapLift

public section

namespace CFSG.OddStandard.AltStdSec.SwapPattern

open Subgroup Equiv Equiv.Perm

section Pair

variable {α : Type*} [DecidableEq α]

theorem commute_swap_preserves_pair {w : Perm α} {x y : α} (hxy : x ≠ y)
    (hw : w * swap x y = swap x y * w) :
    (w x = x ∧ w y = y) ∨ (w x = y ∧ w y = x) := by
  have h1 : swap (w x) (w y) = swap x y := by
    rw [swap_apply_apply, hw, mul_inv_cancel_right]
  have hwxy : w x ≠ w y := fun h => hxy (w.injective h)
  have hx : w x = x ∨ w x = y := by
    by_contra hne
    push Not at hne
    have h2 := congrArg (fun f : Perm α => f (w x)) h1
    simp only [swap_apply_left] at h2
    rw [swap_apply_of_ne_of_ne hne.1 hne.2] at h2
    exact hwxy h2.symm
  have hy : w y = x ∨ w y = y := by
    by_contra hne
    push Not at hne
    have h2 := congrArg (fun f : Perm α => f (w y)) h1
    simp only [swap_apply_right] at h2
    rw [swap_apply_of_ne_of_ne hne.1 hne.2] at h2
    exact hwxy h2
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact absurd (hx.trans hy.symm) hwxy
  · exact Or.inl ⟨hx, hy⟩
  · exact Or.inr ⟨hx, hy⟩
  · exact absurd (hx.trans hy.symm) hwxy

end Pair

theorem apply_eight_mem_pair_of_mem_centralizer {σ : Perm (Fin 10)}
    (hσ : σ ∈ centralizer ({τ₀} : Set (Perm (Fin 10)))) :
    (σ 8 = 8 ∧ σ 9 = 9) ∨ (σ 8 = 9 ∧ σ 9 = 8) :=
  commute_swap_preserves_pair (by decide) (mem_centralizer_singleton_iff.1 hσ)

theorem tau0_mul_self : τ₀ * τ₀ = 1 := by
  rw [τ₀]; exact swap_mul_self 8 9

def restrFix (σ : ↥(centralizer ({τ₀} : Set (Perm (Fin 10))))) : Perm (Fin 10) :=
  if (σ : Perm (Fin 10)) 8 = 8 then (σ : Perm (Fin 10)) else τ₀ * (σ : Perm (Fin 10))

theorem restrFix_mem (σ : ↥(centralizer ({τ₀} : Set (Perm (Fin 10))))) :
    restrFix σ ∈ stab2 8 9 := by
  have hpair := apply_eight_mem_pair_of_mem_centralizer σ.2
  rw [restrFix]
  split_ifs with h8
  · rw [mem_stab2]
    rcases hpair with ⟨h88, h99⟩ | ⟨h89, -⟩
    · exact ⟨h88, h99⟩
    · exact absurd (h89.symm.trans h8) (by decide)
  · rw [mem_stab2]
    rcases hpair with ⟨h88, -⟩ | ⟨h89, h98⟩
    · exact absurd h88 h8
    · exact ⟨by simp [Perm.mul_apply, h89, τ₀], by simp [Perm.mul_apply, h98, τ₀]⟩

theorem tau_mul_mul {a b : Perm (Fin 10)} (ha : a * τ₀ = τ₀ * a) :
    τ₀ * (a * b) = a * (τ₀ * b) := by
  calc τ₀ * (a * b) = τ₀ * a * b := by group
    _ = a * τ₀ * b := by rw [ha]
    _ = a * (τ₀ * b) := by group

theorem tau_mul_tau_mul {a b : Perm (Fin 10)} (ha : a * τ₀ = τ₀ * a)
    (hb : b * τ₀ = τ₀ * b) (hτ : τ₀ * τ₀ = 1) :
    τ₀ * (a * (τ₀ * b)) = a * b := by
  rw [show τ₀ * (a * (τ₀ * b)) = (τ₀ * a) * (τ₀ * b) by group]
  calc (τ₀ * a) * (τ₀ * b) = τ₀ * (a * τ₀) * b := by group
    _ = τ₀ * (τ₀ * a) * b := by rw [ha]
    _ = τ₀ * τ₀ * (a * b) := by group
    _ = a * b := by rw [hτ, one_mul]

theorem restrFix_mul (σ σ' : ↥(centralizer ({τ₀} : Set (Perm (Fin 10))))) :
    restrFix (σ * σ') = restrFix σ * restrFix σ' := by
  have hpairσ := apply_eight_mem_pair_of_mem_centralizer σ.2
  have hpairσ' := apply_eight_mem_pair_of_mem_centralizer σ'.2
  have hcommσ := mem_centralizer_singleton_iff.1 σ.2
  have hcommσ' := mem_centralizer_singleton_iff.1 σ'.2
  rcases hpairσ with ⟨hσ8, hσ9⟩ | ⟨hσ8, hσ9⟩ <;>
    rcases hpairσ' with ⟨hσ'8, hσ'9⟩ | ⟨hσ'8, hσ'9⟩ <;>
    simp [restrFix, hσ8, hσ9, hσ'8, hσ'9, hcommσ, hcommσ', tau0_mul_self, mul_assoc]
  · exact tau_mul_mul hcommσ
  · exact (tau_mul_tau_mul hcommσ hcommσ' tau0_mul_self).symm

noncomputable def restr (σ : ↥(centralizer ({τ₀} : Set (Perm (Fin 10))))) : Perm (Fin 8) :=
  Classical.choose (mem_stab2_iff_exists_liftS8.1 (restrFix_mem σ))

theorem liftS8_restr (σ : ↥(centralizer ({τ₀} : Set (Perm (Fin 10))))) :
    liftS8 (restr σ) = restrFix σ :=
  Classical.choose_spec (mem_stab2_iff_exists_liftS8.1 (restrFix_mem σ))

theorem restr_mul (σ σ' : ↥(centralizer ({τ₀} : Set (Perm (Fin 10))))) :
    restr (σ * σ') = restr σ * restr σ' := by
  apply liftS8_injective
  rw [liftS8_restr, map_mul, liftS8_restr, liftS8_restr, restrFix_mul]

@[expose] noncomputable def restrHom :
    ↥(centralizer ({τ₀} : Set (Perm (Fin 10)))) →* Perm (Fin 8) :=
  MonoidHom.mk' restr restr_mul

theorem restrHom_apply (σ : ↥(centralizer ({τ₀} : Set (Perm (Fin 10))))) :
    restrHom σ = restr σ := rfl

theorem exists_restr :
    ∃ r : ↥(centralizer ({τ₀} : Set (Perm (Fin 10)))) →* Perm (Fin 8),
      ∀ σ : ↥(centralizer ({τ₀} : Set (Perm (Fin 10)))),
        (((σ : Perm (Fin 10)) = liftS8 (r σ)) ∧ (σ : Perm (Fin 10)) 8 = 8) ∨
        (((σ : Perm (Fin 10)) = τ₀ * liftS8 (r σ)) ∧ (σ : Perm (Fin 10)) 8 = 9) := by
  refine ⟨restrHom, fun σ => ?_⟩
  have hlift := liftS8_restr σ
  rw [restrFix] at hlift
  split_ifs at hlift with h8
  · exact Or.inl ⟨hlift.symm, h8⟩
  · refine Or.inr ⟨?_, ?_⟩
    · rw [restrHom_apply, hlift, ← mul_assoc, tau0_mul_self, one_mul]
    · rcases apply_eight_mem_pair_of_mem_centralizer σ.2 with ⟨h88, -⟩ | ⟨h89, -⟩
      · exact absurd h88 h8
      · exact h89

theorem card_cycleType_τ₀_mul_liftS8 (ρ : Perm (Fin 8)) :
    Multiset.card (τ₀ * liftS8 ρ).cycleType = Multiset.card ρ.cycleType + 1 := by
  have hdisj : Disjoint τ₀ (liftS8 ρ) := by
    intro x
    by_cases h8 : x = 8
    · right; rw [h8]; exact liftS8_apply_eight ρ
    by_cases h9 : x = 9
    · right; rw [h9]; exact liftS8_apply_nine ρ
    · left; exact swap_apply_of_ne_of_ne h8 h9
  have hτ : τ₀.cycleType = {2} :=
    isSwap_iff_cycleType.mp ⟨8, 9, by decide, rfl⟩
  rw [hdisj.cycleType_mul, cycleType_liftS8, Multiset.card_add, hτ, Multiset.card_singleton]
  omega

theorem card_cycleType_le_four {ρ : Perm (Fin 8)} (hρ : ρ * ρ = 1) :
    Multiset.card ρ.cycleType ≤ 4 := by
  have h1 := card_support_eq_two_mul_card_cycleType hρ
  have h2 : ρ.support.card ≤ Fintype.card (Fin 8) := Finset.card_le_univ _
  rw [Fintype.card_fin] at h2
  omega

theorem factorial_two_pow_factorial_injective {k k' : ℕ} (hk : k ≤ 4) (hk' : k' ≤ 4)
    (h : (8 - 2 * k).factorial * 2 ^ k * k.factorial =
      (8 - 2 * k').factorial * 2 ^ k' * k'.factorial) : k = k' := by
  interval_cases k <;> interval_cases k' <;> first | rfl | (norm_num at h)

theorem card_cycleType_of_injective_endo {γ : Perm (Fin 8) →* Perm (Fin 8)}
    (hγ : Function.Injective γ) {ρ : Perm (Fin 8)} (hρ : ρ * ρ = 1) :
    Multiset.card (γ ρ).cycleType = Multiset.card ρ.cycleType := by
  have hγρ : γ ρ * γ ρ = 1 := by rw [← map_mul, hρ, map_one]
  have hmap : (centralizer ({ρ} : Set (Perm (Fin 8)))).map γ =
      centralizer ({γ ρ} : Set (Perm (Fin 8))) := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [mem_centralizer_singleton_iff] at hy
      rw [mem_centralizer_singleton_iff]
      rw [← map_mul, ← map_mul, hy]
    · intro hx
      rw [mem_centralizer_singleton_iff] at hx
      obtain ⟨y, rfl⟩ := hγ.bijective_of_finite.2 x
      refine ⟨y, ?_, rfl⟩
      rw [mem_centralizer_singleton_iff]
      apply hγ
      rw [map_mul, map_mul, hx]
  have hcard : Nat.card (centralizer ({γ ρ} : Set (Perm (Fin 8)))) =
      Nat.card (centralizer ({ρ} : Set (Perm (Fin 8)))) := by
    rw [← hmap]
    exact Subgroup.card_map_of_injective hγ
  have hγcard := nat_card_centralizer_of_mul_self hγρ
  have hρcard := nat_card_centralizer_of_mul_self hρ
  rw [Fintype.card_fin] at hγcard hρcard
  refine factorial_two_pow_factorial_injective (card_cycleType_le_four hγρ)
    (card_cycleType_le_four hρ) ?_
  rw [← hγcard, hcard, hρcard]

theorem card_cycleType_of_commute_swap (β : Perm (Fin 8) →* Perm (Fin 10))
    (hinj : Function.Injective β) (hcomm : ∀ ρ, β ρ * τ₀ = τ₀ * β ρ) (hne : ∀ ρ, β ρ ≠ τ₀)
    {ρ : Perm (Fin 8)} (hρ : ρ * ρ = 1) :
    Multiset.card (β ρ).cycleType =
        Multiset.card ρ.cycleType + (if β ρ 8 = 9 then 1 else 0) ∧
      Multiset.card (τ₀ * β ρ).cycleType =
        Multiset.card ρ.cycleType + (if β ρ 8 = 9 then 0 else 1) := by
  classical
  obtain ⟨r, hr⟩ := exists_restr
  let β'' : Perm (Fin 8) →* Perm (Fin 8) :=
    r.comp (β.codRestrict (centralizer ({τ₀} : Set (Perm (Fin 10))))
      (fun ρ => mem_centralizer_singleton_iff.2 (hcomm ρ)))
  have hβ''_apply : ∀ ρ,
      β'' ρ = r ⟨β ρ, mem_centralizer_singleton_iff.2 (hcomm ρ)⟩ := fun ρ => rfl
  have dich : ∀ ρ : Perm (Fin 8),
      (β ρ = liftS8 (r ⟨β ρ, mem_centralizer_singleton_iff.2 (hcomm ρ)⟩) ∧ (β ρ) 8 = 8) ∨
      (β ρ = τ₀ * liftS8 (r ⟨β ρ, mem_centralizer_singleton_iff.2 (hcomm ρ)⟩) ∧
        (β ρ) 8 = 9) :=
    fun ρ => by
      simpa only [Subtype.coe_mk] using hr ⟨β ρ, mem_centralizer_singleton_iff.2 (hcomm ρ)⟩
  have hβ''_one : ∀ ρ, β'' ρ = 1 → ρ = 1 := by
    intro ρ h
    have hlift : liftS8 (β'' ρ) = 1 := by rw [h, map_one]
    rcases dich ρ with ⟨h1, -⟩ | ⟨h1, -⟩
    · have hβ1 : β ρ = 1 := by rw [h1, ← hβ''_apply ρ, hlift]
      exact hinj (by rw [hβ1, map_one])
    · have hβτ : β ρ = τ₀ := by rw [h1, ← hβ''_apply ρ, hlift, mul_one]
      exact absurd hβτ (hne ρ)
  have hβ''_inj : Function.Injective β'' := by
    intro a b hab
    have h1 : β'' (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : a * b⁻¹ = 1 := hβ''_one (a * b⁻¹) h1
    calc a = a * (b⁻¹ * b) := by rw [inv_mul_cancel, mul_one]
      _ = a * b⁻¹ * b := by rw [mul_assoc]
      _ = 1 * b := by rw [h2]
      _ = b := by rw [one_mul]
  have hendo : Multiset.card (β'' ρ).cycleType = Multiset.card ρ.cycleType :=
    card_cycleType_of_injective_endo hβ''_inj hρ
  rcases dich ρ with ⟨hβ, -⟩ | ⟨hβ, -⟩
  · rw [hβ, ← hβ''_apply ρ]
    constructor
    · rw [cycleType_liftS8, hendo]
      simp [liftS8_apply_eight]
    · rw [card_cycleType_τ₀_mul_liftS8, hendo]
      simp [liftS8_apply_eight]
  · rw [hβ, ← hβ''_apply ρ]
    constructor
    · rw [card_cycleType_τ₀_mul_liftS8, hendo]
      simp [Perm.mul_apply, τ₀, liftS8_apply_eight]
    · rw [← mul_assoc, tau0_mul_self, one_mul, cycleType_liftS8, hendo]
      simp [Perm.mul_apply, τ₀, liftS8_apply_eight]

theorem exists_swapIndicator (β : Perm (Fin 8) →* Perm (Fin 10))
    (hcomm : ∀ ρ, β ρ * τ₀ = τ₀ * β ρ) :
    ∃ ε : Perm (Fin 8) →* ℤˣ, ∀ ρ, ε ρ = if β ρ 8 = 9 then -1 else 1 := by
  refine ⟨MonoidHom.mk' (fun ρ => if β ρ 8 = 9 then (-1 : ℤˣ) else 1) ?_, fun ρ => rfl⟩
  intro a b
  have ha := commute_swap_preserves_pair (by decide : (8 : Fin 10) ≠ 9) (hcomm a)
  have hb := commute_swap_preserves_pair (by decide : (8 : Fin 10) ≠ 9) (hcomm b)
  have hmul : β (a * b) 8 = β a (β b 8) := by rw [map_mul]; rfl
  rcases ha with ⟨ha8, ha9⟩ | ⟨ha8, ha9⟩ <;>
    rcases hb with ⟨hb8, hb9⟩ | ⟨hb8, hb9⟩ <;>
    simp [hmul, ha8, ha9, hb8, hb9]

end CFSG.OddStandard.AltStdSec.SwapPattern
