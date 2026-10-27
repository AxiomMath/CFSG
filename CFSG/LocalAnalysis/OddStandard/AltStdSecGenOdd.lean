module

public import CFSG.Sporadic.SchreierLemmas.MoorePresentation
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.OddStandard.AltStdSec

open Equiv Subgroup CFSG.Sporadic.SchreierLemmas

section OddAlg

variable {Γ : Type*} [Group Γ]

theorem pow_card_eq_one_of_mem {Z : Subgroup Γ} [Finite Z] {w : Γ} (hw : w ∈ Z) :
    w ^ Nat.card Z = 1 := by
  have h := congrArg Subtype.val (pow_card_eq_one' (x := (⟨w, hw⟩ : Z)))
  rw [Subgroup.coe_pow] at h
  exact h

theorem eq_one_of_self_inv_odd {Z : Subgroup Γ} [Finite Z] (hodd : Odd (Nat.card Z)) {w : Γ}
    (hw : w ∈ Z) (h : w = w⁻¹) : w = 1 := by
  obtain ⟨k, hk⟩ := hodd
  have hc : w ^ (2 * k + 1) = 1 := hk ▸ pow_card_eq_one_of_mem hw
  have h2 : w ^ 2 = 1 := by
    have : w * w = 1 := by
      calc w * w = w⁻¹ * w := by rw [← h]
        _ = 1 := inv_mul_cancel w
    simpa [pow_two] using this
  calc w = (w ^ 2) ^ k * w := by rw [h2, one_pow, one_mul]
    _ = w ^ (2 * k) * w := by rw [pow_mul]
    _ = w ^ (2 * k + 1) := by rw [pow_succ]
    _ = 1 := hc

theorem invol_pow_eq_one {Z : Subgroup Γ} [Finite Z] (hZc : Z ≤ Subgroup.center Γ)
    (hodd : Odd (Nat.card Z)) {u v : Γ} (hu : u * u = 1) (hv : v * v = 1) {k : ℕ}
    (hk : (u * v) ^ k ∈ Z) : (u * v) ^ k = 1 := by
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have h1 : (u * v)⁻¹ = v * u := by rw [mul_inv_rev, hui, hvi]
  have h2 : v * (u * v) ^ k * v⁻¹ = (v * u) ^ k := by
    rw [← conj_pow]
    congr 1
    group
  have h3 : v * (u * v) ^ k * v⁻¹ = (u * v) ^ k := by
    rw [Subgroup.mem_center_iff.1 (hZc hk) v]; group
  have h4 : (v * u) ^ k = ((u * v) ^ k)⁻¹ := by rw [← h1, inv_pow]
  refine eq_one_of_self_inv_odd hodd hk ?_
  calc (u * v) ^ k = v * (u * v) ^ k * v⁻¹ := h3.symm
    _ = (v * u) ^ k := h2
    _ = ((u * v) ^ k)⁻¹ := h4

section Defects

variable {Z : Subgroup Γ}

theorem conj_of_sq_eq {x y ω : Γ} (h : (x * y) ^ 2 = ω) : y * x * y = x⁻¹ * ω := by
  rw [← h, pow_two]
  group

theorem omega_cube_eq (hZc : Z ≤ Subgroup.center Γ) {x y : Γ} (hy : y * y = 1)
    (hω : (x * y) ^ 2 ∈ Z) (hτ : x ^ 3 ∈ Z) : ((x * y) ^ 2) ^ 3 = (x ^ 3) ^ 2 := by
  set ω := (x * y) ^ 2 with hωdef
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have e1 : y * x * y⁻¹ = x⁻¹ * ω := by rw [hyi]; exact conj_of_sq_eq rfl
  have e2 : y * x ^ 3 * y⁻¹ = (x⁻¹ * ω) ^ 3 := by rw [← conj_pow, e1]
  have hc : Commute x⁻¹ ω := Subgroup.mem_center_iff.1 (hZc hω) x⁻¹
  rw [hc.mul_pow] at e2
  have e3 : y * x ^ 3 * y⁻¹ = x ^ 3 := by
    rw [Subgroup.mem_center_iff.1 (hZc hτ) y]; group
  have e4 : (x⁻¹) ^ 3 = (x ^ 3)⁻¹ := by rw [inv_pow]
  rw [e3, e4] at e2
  calc ω ^ 3 = x ^ 3 * ((x ^ 3)⁻¹ * ω ^ 3) := by group
    _ = x ^ 3 * x ^ 3 := by rw [← e2]
    _ = (x ^ 3) ^ 2 := by rw [pow_two]

theorem nu_sq_eq (hZc : Z ≤ Subgroup.center Γ) {x y w : Γ} (hy : y * y = 1) (hw : w * w = 1)
    (hyw : y * w = w * y) (hω : (x * y) ^ 2 ∈ Z) (hν : (x * w) ^ 3 ∈ Z) :
    ((x * w) ^ 3) ^ 2 = ((x * y) ^ 2) ^ 3 := by
  set ω := (x * y) ^ 2 with hωdef
  set ν := (x * w) ^ 3 with hνdef
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  have e1 : y * x * y⁻¹ = x⁻¹ * ω := by rw [hyi]; exact conj_of_sq_eq rfl
  have e1' : y * w * y⁻¹ = w := by rw [hyw]; group
  have e2 : y * (x * w) ^ 3 * y⁻¹ = (x⁻¹ * ω * w) ^ 3 := by
    rw [← conj_pow]
    congr 1
    calc y * (x * w) * y⁻¹ = (y * x * y⁻¹) * (y * w * y⁻¹) := by group
      _ = x⁻¹ * ω * w := by rw [e1, e1']
  have hc : Commute ω (x⁻¹ * w) := by
    have := Subgroup.mem_center_iff.1 (hZc hω) (x⁻¹ * w)
    exact this.symm
  have e3 : x⁻¹ * ω * w = ω * (x⁻¹ * w) := by
    have := Subgroup.mem_center_iff.1 (hZc hω) x⁻¹
    calc x⁻¹ * ω * w = (ω * x⁻¹) * w := by rw [this]
      _ = ω * (x⁻¹ * w) := by group
  rw [e3, hc.mul_pow] at e2
  have e4 : (x⁻¹ * w) ^ 3 = ν⁻¹ := by
    have h1 : (x⁻¹ * w)⁻¹ = w * x := by rw [mul_inv_rev, inv_inv, hwi]
    have h2 : (w * x) ^ 3 = ν := by
      calc (w * x) ^ 3 = w * (x * w) ^ 3 * w⁻¹ := by
            rw [← conj_pow]; congr 1; group
        _ = ν := by rw [Subgroup.mem_center_iff.1 (hZc hν) w]; group
    rw [← inv_inv ((x⁻¹ * w) ^ 3), ← inv_pow, h1, h2]
  have e5 : y * (x * w) ^ 3 * y⁻¹ = ν := by
    rw [Subgroup.mem_center_iff.1 (hZc hν) y]; group
  rw [e5, e4] at e2
  calc ν ^ 2 = ν * ν := by rw [pow_two]
    _ = ν * (ω ^ 3 * ν⁻¹) := by rw [← e2]
    _ = ω ^ 3 := by
        have hc2 : Commute ν (ω ^ 3) := (Subgroup.mem_center_iff.1 (hZc hν) _).symm
        rw [← mul_assoc, hc2.eq, mul_assoc, mul_inv_cancel, mul_one]

theorem omega_eq_of_commute [Finite Z] (hZc : Z ≤ Subgroup.center Γ) (hodd : Odd (Nat.card Z))
    {x y y' : Γ} (hy : y * y = 1) (hy' : y' * y' = 1) (hcomm : y * y' = y' * y)
    (hω : (x * y) ^ 2 ∈ Z) (hω' : (x * y') ^ 2 ∈ Z) : (x * y) ^ 2 = (x * y') ^ 2 := by
  set ω := (x * y) ^ 2 with hωdef
  set ω' := (x * y') ^ 2 with hω'def
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hyi' : y'⁻¹ = y' := inv_eq_of_mul_eq_one_right hy'
  have e1 : y' * x * y'⁻¹ = x⁻¹ * ω' := by rw [hyi']; exact conj_of_sq_eq rfl
  have e1' : y' * y * y'⁻¹ = y := by rw [← hcomm]; group
  have e2 : y' * (x * y) ^ 2 * y'⁻¹ = (x⁻¹ * ω' * y) ^ 2 := by
    rw [← conj_pow]
    congr 1
    calc y' * (x * y) * y'⁻¹ = (y' * x * y'⁻¹) * (y' * y * y'⁻¹) := by group
      _ = x⁻¹ * ω' * y := by rw [e1, e1']
  have e3 : x⁻¹ * ω' * y = ω' * (x⁻¹ * y) := by
    have := Subgroup.mem_center_iff.1 (hZc hω') x⁻¹
    calc x⁻¹ * ω' * y = (ω' * x⁻¹) * y := by rw [this]
      _ = ω' * (x⁻¹ * y) := by group
  have hc : Commute ω' (x⁻¹ * y) := (Subgroup.mem_center_iff.1 (hZc hω') _).symm
  rw [e3, hc.mul_pow] at e2
  have e4 : (x⁻¹ * y) ^ 2 = ω⁻¹ := by
    have h1 : (x⁻¹ * y)⁻¹ = y * x := by rw [mul_inv_rev, inv_inv, hyi]
    have h2 : (y * x) ^ 2 = ω := by
      calc (y * x) ^ 2 = y * (x * y) ^ 2 * y⁻¹ := by
            rw [← conj_pow]; congr 1; group
        _ = ω := by rw [Subgroup.mem_center_iff.1 (hZc hω) y]; group
    rw [← inv_inv ((x⁻¹ * y) ^ 2), ← inv_pow, h1, h2]
  have e5 : y' * (x * y) ^ 2 * y'⁻¹ = ω := by
    rw [Subgroup.mem_center_iff.1 (hZc hω) y']; group
  rw [e5, e4] at e2
  have hcω : Commute ω ω' := (Subgroup.mem_center_iff.1 (hZc hω) ω').symm
  have e6 : ω * ω = ω' ^ 2 := by
    calc ω * ω = (ω' ^ 2 * ω⁻¹) * ω := by rw [← e2]
      _ = ω' ^ 2 := by group
  have hmem : ω * ω'⁻¹ ∈ Z := Z.mul_mem hω (Z.inv_mem hω')
  have hsq : (ω * ω'⁻¹) * (ω * ω'⁻¹) = 1 := by
    calc (ω * ω'⁻¹) * (ω * ω'⁻¹) = (ω * ω) * (ω'⁻¹ * ω'⁻¹) :=
          Commute.mul_mul_mul_comm hcω.symm.inv_left ω ω'⁻¹
      _ = 1 := by rw [e6, pow_two]; group
  have h1 : ω * ω'⁻¹ = 1 := eq_one_of_self_inv_odd hodd hmem (eq_inv_of_mul_eq_one_left hsq)
  exact (mul_inv_eq_one.1 h1)

end Defects

section Main

variable {Z : Subgroup Γ}

theorem commute_of_invol_sq {u v : Γ} (hu : u * u = 1) (hv : v * v = 1) (h : (u * v) ^ 2 = 1) :
    u * v = v * u := by
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have h1 : (u * v) * (u * v) = 1 := by rw [← pow_two]; exact h
  have h2 : (u * v)⁻¹ = u * v := (eq_inv_of_mul_eq_one_left h1).symm
  calc u * v = (u * v)⁻¹ := h2.symm
    _ = v * u := by rw [mul_inv_rev, hui, hvi]

theorem eq_of_sq_eq_odd [Finite Z] (hZc : Z ≤ Subgroup.center Γ) (hodd : Odd (Nat.card Z))
    {a b : Γ} (ha : a ∈ Z) (hb : b ∈ Z) (h : a ^ 2 = b ^ 2) : a = b := by
  have hcab : Commute a b⁻¹ := (Subgroup.mem_center_iff.1 (hZc ha) b⁻¹).symm
  have hsq : (a * b⁻¹) * (a * b⁻¹) = 1 := by
    calc (a * b⁻¹) * (a * b⁻¹) = a ^ 2 * (b⁻¹) ^ 2 := by
          rw [← pow_two, hcab.mul_pow]
      _ = 1 := by rw [h, inv_pow]; group
  have h1 : a * b⁻¹ = 1 :=
    eq_one_of_self_inv_odd hodd (Z.mul_mem ha (Z.inv_mem hb)) (eq_inv_of_mul_eq_one_left hsq)
  exact mul_inv_eq_one.1 h1

end Main

end OddAlg

section Split

variable {m : ℕ} {Γ : Type*} [Group Γ]

theorem exists_section_of_odd_central_cover (hm : 8 ≤ m)
    (π : Γ →* alternatingGroup (Fin m)) (hπ : Function.Surjective π) [Finite π.ker]
    (hZc : π.ker ≤ Subgroup.center Γ) (hodd : Odd (Nat.card π.ker)) :
    ∃ s : alternatingGroup (Fin m) →* Γ, ∀ a, π (s a) = a := by
  classical
  have hm3 : 3 ≤ m := by omega
  have hM := isMooreFamily_mooreCycle hm3
  choose g hg using fun i : ℕ => hπ (mooreCycle m i)
  set Z := π.ker with hZ
  have hmemZ : ∀ w : Γ, π w = 1 → w ∈ Z := fun w h => h
  set c := Nat.card Z with hc
  let e : ℕ → Γ := fun j => if j = 1 then g 1 else g j ^ c
  have he1 : e 1 = g 1 := by simp [e]
  have hej : ∀ j, j ≠ 1 → e j = g j ^ c := fun j hj => by simp [e, hj]
  have hπe : ∀ j ∈ Set.Icc 1 (m - 2), π (e j) = mooreCycle m j := by
    intro j hj
    by_cases h1 : j = 1
    · subst h1; rw [he1]; exact hg 1
    · rw [hej j h1, map_pow, hg j]
      obtain ⟨k, hk⟩ := hodd
      have h2 : mooreCycle m j ^ 2 = 1 := hM.sq_eq_one j (by have := hj.1; omega) hj.2
      rw [hk]
      calc mooreCycle m j ^ (2 * k + 1) = (mooreCycle m j ^ 2) ^ k * mooreCycle m j := by
            rw [pow_succ, pow_mul]
        _ = mooreCycle m j := by rw [h2, one_pow, one_mul]
  have hee : ∀ j ∈ Set.Icc 2 (m - 2), e j * e j = 1 := by
    intro j hj
    have hj1 : j ≠ 1 := by have := hj.1; omega
    have hmem : g j ^ 2 ∈ Z := hmemZ _ (by
      rw [map_pow, hg j]; exact hM.sq_eq_one j hj.1 hj.2)
    rw [hej j hj1, ← pow_add, ← two_mul, pow_mul]
    exact pow_card_eq_one_of_mem hmem
  have hsq_dist : ∀ i j, 2 ≤ i → i + 2 ≤ j → j ≤ m - 2 → (e i * e j) ^ 2 = 1 := by
    intro i j hi hij hj
    have hmem : (e i * e j) ^ 2 ∈ Z := hmemZ _ (by
      rw [map_pow, map_mul, hπe i ⟨by omega, by omega⟩, hπe j ⟨by omega, hj⟩]
      exact hM.sq_distant i j (by omega) hij hj)
    exact invol_pow_eq_one hZc hodd (hee i ⟨hi, by omega⟩) (hee j ⟨by omega, hj⟩) hmem
  have hcube_adj : ∀ j, 3 ≤ j → j ≤ m - 2 → (e (j - 1) * e j) ^ 3 = 1 := by
    intro j hj3 hj
    have hmem : (e (j - 1) * e j) ^ 3 ∈ Z := hmemZ _ (by
      rw [map_pow, map_mul, hπe (j - 1) ⟨by omega, by omega⟩, hπe j ⟨by omega, hj⟩]
      exact hM.cube_adjacent j (by omega) hj)
    exact invol_pow_eq_one hZc hodd (hee (j - 1) ⟨by omega, by omega⟩) (hee j ⟨by omega, hj⟩) hmem
  set x := g 1 with hx
  have hτ : x ^ 3 ∈ Z := hmemZ _ (by rw [map_pow, hg 1]; exact hM.cube_one)
  have hν : (x * e 2) ^ 3 ∈ Z := hmemZ _ (by
    rw [map_pow, map_mul, hg 1, hπe 2 ⟨by omega, by omega⟩]
    exact hM.cube_adjacent 2 le_rfl (by omega))
  have hω : ∀ j, 3 ≤ j → j ≤ m - 2 → (x * e j) ^ 2 ∈ Z := by
    intro j hj3 hj
    exact hmemZ _ (by
      rw [map_pow, map_mul, hg 1, hπe j ⟨by omega, hj⟩]
      exact hM.sq_distant 1 j le_rfl (by omega) hj)
  have hωcube : ∀ j, 3 ≤ j → j ≤ m - 2 → ((x * e j) ^ 2) ^ 3 = (x ^ 3) ^ 2 := fun j hj3 hj =>
    omega_cube_eq hZc (hee j ⟨by omega, hj⟩) (hω j hj3 hj) hτ
  have hντ : (x * e 2) ^ 3 = x ^ 3 := by
    have h4 : e 4 * e 2 = e 2 * e 4 := (commute_of_invol_sq (hee 2 ⟨le_rfl, by omega⟩)
      (hee 4 ⟨by omega, by omega⟩) (hsq_dist 2 4 le_rfl (by omega) (by omega))).symm
    have h5 := nu_sq_eq hZc (hee 4 ⟨by omega, by omega⟩) (hee 2 ⟨le_rfl, by omega⟩) h4
      (hω 4 (by omega) (by omega)) hν
    rw [hωcube 4 (by omega) (by omega)] at h5
    exact eq_of_sq_eq_odd hZc hodd hν hτ h5
  have hωeq : ∀ j, 3 ≤ j → j ≤ m - 2 → (x * e j) ^ 2 = (x * e 3) ^ 2 := by
    have key : ∀ j j', 3 ≤ j → j + 2 ≤ j' → j' ≤ m - 2 → (x * e j) ^ 2 = (x * e j') ^ 2 := by
      intro j j' hj hjj' hj'
      exact omega_eq_of_commute hZc hodd (hee j ⟨by omega, by omega⟩) (hee j' ⟨by omega, hj'⟩)
        (commute_of_invol_sq (hee j ⟨by omega, by omega⟩) (hee j' ⟨by omega, hj'⟩)
          (hsq_dist j j' (by omega) hjj' hj')) (hω j hj (by omega)) (hω j' (by omega) hj')
    intro j hj3 hj
    rcases (show j = 3 ∨ j = 4 ∨ 5 ≤ j by omega) with h | h | h
    · subst h; rfl
    · subst h
      rw [key 4 6 (by omega) (by omega) (by omega), ← key 3 6 (by omega) (by omega) (by omega)]
    · exact (key 3 j le_rfl (by omega) hj).symm
  set ω₀ := (x * e 3) ^ 2 with hω₀def
  have hω₀ : ω₀ ∈ Z := hω 3 le_rfl (by omega)
  obtain ⟨k, hk⟩ := hodd
  set ρ := ω₀⁻¹ with hρ
  have hρZ : ρ ∈ Z := Z.inv_mem hω₀
  set ζ := ρ ^ (k + 1) with hζdef
  have hζZ : ζ ∈ Z := Subgroup.pow_mem _ hρZ _
  have hρc : ρ ^ c = 1 := pow_card_eq_one_of_mem hρZ
  have hζ2 : ζ ^ 2 = ρ := by
    have h1 : (k + 1) * 2 = c + 1 := by omega
    rw [hζdef, ← pow_mul, h1, pow_succ, hρc, one_mul]
  have hτc : ((x ^ 3)⁻¹) ^ c = 1 := pow_card_eq_one_of_mem (Z.inv_mem hτ)
  have hρ3 : ρ ^ 3 = ((x ^ 3)⁻¹) ^ 2 := by
    rw [hρ, inv_pow, hω₀def, hωcube 3 le_rfl (by omega), inv_pow]
  have hζ3 : ζ ^ 3 = (x ^ 3)⁻¹ := by
    calc ζ ^ 3 = (ρ ^ 3) ^ (k + 1) := by rw [hζdef, ← pow_mul, ← pow_mul, mul_comm]
      _ = (((x ^ 3)⁻¹) ^ 2) ^ (k + 1) := by rw [hρ3]
      _ = ((x ^ 3)⁻¹) ^ (c + 1) := by rw [← pow_mul]; congr 1; omega
      _ = (x ^ 3)⁻¹ := by rw [pow_succ, hτc, one_mul]
  have hcz : ∀ g : Γ, g * ζ = ζ * g := fun g => Subgroup.mem_center_iff.1 (hZc hζZ) g
  let y : ℕ → Γ := Function.update e 1 (x * ζ)
  have hy1 : y 1 = x * ζ := Function.update_self _ _ _
  have hyj : ∀ j, j ≠ 1 → y j = e j := fun j hj => Function.update_of_ne hj _ _
  have hMy : IsMooreFamily (m - 2) y := by
    refine ⟨?_, fun j h2 hj => ?_, fun j h2 hj => ?_, fun i j hi hij hj => ?_⟩
    · rw [hy1, Commute.mul_pow (hcz x) 3, hζ3]
      exact mul_inv_cancel _
    · rw [hyj j (by omega), pow_two]
      exact hee j ⟨h2, hj⟩
    · by_cases hj2 : j = 2
      · subst hj2
        show (y 1 * y 2) ^ 3 = 1
        rw [hy1, hyj 2 (by omega)]
        have h1 : x * ζ * e 2 = (x * e 2) * ζ := by
          calc x * ζ * e 2 = x * (ζ * e 2) := by rw [mul_assoc]
            _ = x * (e 2 * ζ) := by rw [(hcz (e 2)).symm]
            _ = (x * e 2) * ζ := by rw [mul_assoc]
        rw [h1, Commute.mul_pow (hcz (x * e 2)), hντ, hζ3]
        exact mul_inv_cancel _
      · rw [hyj (j - 1) (by omega), hyj j (by omega)]
        exact hcube_adj j (by omega) hj
    · by_cases hi1 : i = 1
      · subst hi1
        rw [hy1, hyj j (by omega)]
        have h1 : x * ζ * e j = (x * e j) * ζ := by
          calc x * ζ * e j = x * (ζ * e j) := by rw [mul_assoc]
            _ = x * (e j * ζ) := by rw [(hcz (e j)).symm]
            _ = (x * e j) * ζ := by rw [mul_assoc]
        rw [h1, Commute.mul_pow (hcz (x * e j)), hωeq j (by omega) hj, hζ2, hρ]
        exact mul_inv_cancel _
      · rw [hyj i hi1, hyj j (by omega)]
        exact hsq_dist i j (by omega) hij hj
  obtain ⟨s, hs⟩ := exists_hom_mooreCycle hm3 y hMy
  refine ⟨s, fun a => ?_⟩
  have hid : π.comp s = MonoidHom.id _ := hom_ext_mooreCycle hm3 (fun i hi => by
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, hs i hi]
    by_cases h1 : i = 1
    · subst h1
      rw [hy1, map_mul, hg 1, MonoidHom.mem_ker.1 hζZ, mul_one]
    · rw [hyj i h1]
      exact hπe i hi)
  exact DFunLike.congr_fun hid a

theorem comm_mul_central_left {w : Γ} (hw : w ∈ Subgroup.center Γ) (a b : Γ) :
    (w * a) * b * (w * a)⁻¹ * b⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have h1 : ∀ g : Γ, g * w = w * g := fun g => Subgroup.mem_center_iff.1 hw g
  have h2 : ∀ g : Γ, g * w⁻¹ = w⁻¹ * g := fun g => Subgroup.mem_center_iff.1 (inv_mem hw) g
  calc (w * a) * b * (w * a)⁻¹ * b⁻¹ = w * a * b * a⁻¹ * (w⁻¹ * b⁻¹) := by group
    _ = w * a * b * a⁻¹ * (b⁻¹ * w⁻¹) := by rw [← h2 b⁻¹]
    _ = (w * (a * b * a⁻¹ * b⁻¹)) * w⁻¹ := by group
    _ = ((a * b * a⁻¹ * b⁻¹) * w) * w⁻¹ := by rw [← h1]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem comm_mul_central_right {w : Γ} (hw : w ∈ Subgroup.center Γ) (a b : Γ) :
    a * (w * b) * a⁻¹ * (w * b)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have h1 : ∀ g : Γ, g * w = w * g := fun g => Subgroup.mem_center_iff.1 hw g
  have h2 : ∀ g : Γ, g * w⁻¹ = w⁻¹ * g := fun g => Subgroup.mem_center_iff.1 (inv_mem hw) g
  calc a * (w * b) * a⁻¹ * (w * b)⁻¹ = a * w * b * a⁻¹ * (b⁻¹ * w⁻¹) := by group
    _ = w * a * b * a⁻¹ * b⁻¹ * w⁻¹ := by rw [h1 a]; group
    _ = (w * (a * b * a⁻¹ * b⁻¹)) * w⁻¹ := by group
    _ = ((a * b * a⁻¹ * b⁻¹) * w) * w⁻¹ := by rw [← h1]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem ker_eq_bot_of_perfect_odd_central_cover (hm : 8 ≤ m) [Group.IsPerfect Γ]
    (π : Γ →* alternatingGroup (Fin m)) (hπ : Function.Surjective π) [Finite π.ker]
    (hZc : π.ker ≤ Subgroup.center Γ) (hodd : Odd (Nat.card π.ker)) : π.ker = ⊥ := by
  obtain ⟨s, hs⟩ := exists_section_of_odd_central_cover hm π hπ hZc hodd
  set S := s.range with hS
  have hdec : ∀ g : Γ, ∃ w ∈ π.ker, ∃ t ∈ S, g = w * t := fun g =>
    ⟨g * (s (π g))⁻¹, by simp [MonoidHom.mem_ker, hs], s (π g), ⟨π g, rfl⟩, by group⟩
  have hcomm : commutator Γ ≤ S := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    obtain ⟨w₁, hw₁, t₁, ht₁, rfl⟩ := hdec g₁
    obtain ⟨w₂, hw₂, t₂, ht₂, rfl⟩ := hdec g₂
    rw [commutatorElement_def, comm_mul_central_left (hZc hw₁),
      comm_mul_central_right (hZc hw₂)]
    exact S.mul_mem (S.mul_mem (S.mul_mem ht₁ ht₂) (S.inv_mem ht₁)) (S.inv_mem ht₂)
  rw [eq_bot_iff]
  intro w hw
  have hwS : w ∈ S := hcomm Group.IsPerfect.mem_commutator
  obtain ⟨a, rfl⟩ := hwS
  have h1 : a = 1 := by
    have := hs a
    rw [MonoidHom.mem_ker.1 hw] at this
    exact this.symm
  rw [h1, map_one]
  exact Subgroup.one_mem _

end Split

end CFSG.OddStandard.AltStdSec
