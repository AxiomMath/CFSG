module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4S47RCyc

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
  {φ : (Fin 7 → ZMod 2) → G}

theorem sec4S47RCoord_ind (h : Sec4FSetup t L S z A B φ) :
    sec4S47RCoord t φ sec4S47RInd = sec4MPt t φ (some 0) * sec4MPt t φ (some 1) := by
  have hδ : sec4S47RInd = Pi.single (some 0) (1 : ZMod 2) + Pi.single (some 1) 1 := by
    funext r
    rw [Pi.add_apply]
    unfold sec4S47RInd
    by_cases h0 : r = some 0
    · subst h0
      rw [if_pos (Or.inl rfl), Pi.single_eq_same,
        Pi.single_eq_of_ne (by decide : (some 0 : Option (Fin 7)) ≠ some 1), add_zero]
    · by_cases h1 : r = some 1
      · subst h1
        rw [if_pos (Or.inr rfl),
          Pi.single_eq_of_ne (by decide : (some 1 : Option (Fin 7)) ≠ some 0),
          Pi.single_eq_same, zero_add]
      · rw [if_neg (by tauto), Pi.single_eq_of_ne h0, Pi.single_eq_of_ne h1, add_zero]
  rw [hδ, sec4S47RCoord_add h, sec4S47RCoord_single h, sec4S47RCoord_single h]

theorem sec4S47R_exists_involution (h : Sec4FSetup t L S z A B φ) {y : G}
    (hyN : y ∈ normalizer (A : Set G)) (hρ : h.actHom ⟨y, hyN⟩ = sec4S47RTau)
    (h2 : ∃ n : ℕ, y ^ (2 ^ n) = 1) : ∃ a ∈ A, (y * a) * (y * a) = 1 := by
  have hyR : Sec4MRealizes t φ y sec4S47RTau := by
    have hspec := h.actHom_spec ⟨y, hyN⟩
    rw [hρ] at hspec
    simpa using hspec
  have hyyN : y * y ∈ normalizer (A : Set G) := mul_mem hyN hyN
  have hφ1 : h.actHom ⟨y * y, hyyN⟩ = 1 := by
    have hmul : h.actHom (⟨y * y, hyyN⟩ : ↥(normalizer (A : Set G))) =
        sec4S47RTau * sec4S47RTau := by
      calc h.actHom (⟨y * y, hyyN⟩ : ↥(normalizer (A : Set G)))
          = h.actHom (⟨y, hyN⟩ * ⟨y, hyN⟩) := rfl
        _ = h.actHom ⟨y, hyN⟩ * h.actHom ⟨y, hyN⟩ := map_mul h.actHom _ _
        _ = sec4S47RTau * sec4S47RTau := by rw [hρ]
    rw [hmul, sec4S47RTau, Equiv.swap_mul_self]
  have hyyC : y * y ∈ centralizer (A : Set G) :=
    (h.actHom_eq_one_iff ⟨y * y, hyyN⟩).mp hφ1
  obtain ⟨n, hn⟩ := h2
  have hcy : (y * y) ^ (2 ^ n) = 1 := by
    rw [show y * y = y ^ 2 by rw [pow_two], ← pow_mul,
      show 2 * 2 ^ n = 2 ^ n * 2 by ring, pow_mul, hn, one_pow]
  have hyyA : y * y ∈ A := h.cent_two_elt hyyC ⟨n, hcy⟩
  obtain ⟨v, hv⟩ := sec4S47R_exists_coord h hyyA
  have hτ : ∃ ε : ZMod 2, ∀ r, v (sec4S47RTau.symm r) + v r = ε :=
    sec4S47R_inv_tau h hyN hρ hv
  have h₁ := sec4S47R_inv_cycle h hyN hρ hv (a := none) (b := some 2) (c := some 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have h₂ := sec4S47R_inv_cycle h hyN hρ hv (a := some 3) (b := some 4) (c := some 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have h₃ := sec4S47R_inv_cycle h hyN hρ hv (a := some 5) (b := some 6) (c := none)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  obtain ⟨e, ε, hvε⟩ := sec4S47R_comb v hτ h₁ h₂ h₃
  have hcoorde : sec4S47RCoord t φ v = sec4S47RCoord t φ (fun r => e * sec4S47RInd r) := by
    rw [sec4S47RCoord_eq_iff h]
    refine ⟨ε, fun r => ?_⟩
    rw [hvε r]
    exact (by decide : ∀ x y : ZMod 2, (x + y) + x = y) _ _
  have he : e = 0 ∨ e = 1 := (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) e
  rcases he with rfl | rfl
  ·
    have hw0 : (fun r : Option (Fin 7) => (0 : ZMod 2) * sec4S47RInd r) = 0 := by
      funext r
      simp
    have hyy : y * y = 1 := by
      rw [← hv, hcoorde, hw0, sec4S47RCoord_zero h]
    exact ⟨1, A.one_mem, by rw [mul_one, hyy]⟩
  ·
    have hw1 : (fun r : Option (Fin 7) => (1 : ZMod 2) * sec4S47RInd r) = sec4S47RInd := by
      funext r
      simp
    have hyy : y * y = sec4MPt t φ (some 0) * sec4MPt t φ (some 1) := by
      rw [← hv, hcoorde, hw1, sec4S47RCoord_ind h]
    have hτinv : sec4S47RTau.symm (some 0) = some 1 := by
      rw [sec4S47RTau, Equiv.symm_apply_eq, Equiv.swap_apply_right]
    have hconj : y⁻¹ * sec4MPt t φ (some 0) * y = sec4MPt t φ (some 1) := by
      have h1 := hyR.inv (some 0)
      simpa [Equiv.Perm.inv_def, hτinv] using h1
    refine ⟨sec4MPt t φ (some 0), sec4MPt_mem_A h.data (some 0), ?_⟩
    have hkey : (y * sec4MPt t φ (some 0)) * (y * sec4MPt t φ (some 0))
        = (y * y) * ((y⁻¹ * sec4MPt t φ (some 0) * y) * sec4MPt t φ (some 0)) := by
      group
    rw [hkey, hyy, hconj]
    calc (sec4MPt t φ (some 0) * sec4MPt t φ (some 1)) *
          (sec4MPt t φ (some 1) * sec4MPt t φ (some 0))
        = sec4MPt t φ (some 0) *
            (sec4MPt t φ (some 1) * sec4MPt t φ (some 1)) *
            sec4MPt t φ (some 0) := by group
      _ = sec4MPt t φ (some 0) * 1 * sec4MPt t φ (some 0) := by
            rw [sec4MPt_mul_self h.data (some 1)]
      _ = sec4MPt t φ (some 0) * sec4MPt t φ (some 0) := by rw [mul_one]
      _ = 1 := sec4MPt_mul_self h.data (some 0)

end CFSG.OddStandard.SmallF3.Omega
