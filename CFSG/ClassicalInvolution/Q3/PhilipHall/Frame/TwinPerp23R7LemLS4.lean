module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

open Equiv

@[expose] def dtp (i : Fin 3) : Equiv.Perm (Fin 4) :=
  if i = 0 then Equiv.swap 0 1 * Equiv.swap 2 3
  else if i = 1 then Equiv.swap 0 2 * Equiv.swap 1 3
  else Equiv.swap 0 3 * Equiv.swap 1 2

@[expose] def pairAct (g : Equiv.Perm (Fin 4)) (i : Fin 3) : Fin 3 :=
  if g * dtp i * g⁻¹ = dtp 0 then 0 else if g * dtp i * g⁻¹ = dtp 1 then 1 else 2

theorem pairAct_one : ∀ i : Fin 3, pairAct 1 i = i := by decide +kernel

theorem pairAct_mul : ∀ (g h : Equiv.Perm (Fin 4)) (i : Fin 3),
    pairAct (g * h) i = pairAct g (pairAct h i) := by decide +kernel

theorem pairAct_inv : ∀ (g : Equiv.Perm (Fin 4)) (i : Fin 3), pairAct g⁻¹ (pairAct g i) = i := by
  decide +kernel

theorem pairAct_inv' : ∀ (g : Equiv.Perm (Fin 4)) (i : Fin 3), pairAct g (pairAct g⁻¹ i) = i := by
  decide +kernel

@[expose] def s4ToS3 : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 3) where
  toFun g :=
    { toFun := pairAct g
      invFun := pairAct g⁻¹
      left_inv := fun i => pairAct_inv g i
      right_inv := fun i => pairAct_inv' g i }
  map_one' := Equiv.ext pairAct_one
  map_mul' := fun g h => Equiv.ext fun i => pairAct_mul g h i

theorem s4ToS3_apply (g : Equiv.Perm (Fin 4)) (i : Fin 3) : s4ToS3 g i = pairAct g i := rfl

theorem s4ToS3_surjective : Function.Surjective s4ToS3 := by
  have h : ∀ s : Equiv.Perm (Fin 3), ∃ g : Equiv.Perm (Fin 4), ∀ i : Fin 3, pairAct g i = s i := by
    decide +kernel
  intro s
  obtain ⟨g, hg⟩ := h s
  exact ⟨g, Equiv.ext fun i => hg i⟩

theorem s4ToS3_ker_sq {g : Equiv.Perm (Fin 4)} (hg : s4ToS3 g = 1) : g * g = 1 := by
  have h : ∀ g : Equiv.Perm (Fin 4), (∀ i : Fin 3, pairAct g i = i) → g * g = 1 := by
    decide +kernel
  exact h g fun i => by
    have := congrArg (fun s : Equiv.Perm (Fin 3) => s i) hg
    simpa [s4ToS3_apply] using this

theorem perm4_oddNormal_trivial (N : Subgroup (Equiv.Perm (Fin 4))) [N.Normal]
    (hodd : Odd (Nat.card N)) : N = ⊥ := by
  have key : ∀ x : Equiv.Perm (Fin 4), x ^ 3 = 1 → x ≠ 1 →
      ∃ y : Equiv.Perm (Fin 4), y * x * y⁻¹ * x⁻¹ ≠ 1 ∧ (y * x * y⁻¹ * x⁻¹) ^ 2 = 1 := by
    decide +kernel
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  have hord : orderOf x ∣ 3 := by
    have h1 : orderOf x ∣ Nat.card N := by
      have := orderOf_dvd_natCard (⟨x, hx⟩ : N)
      rwa [Subgroup.orderOf_mk] at this
    have h24 : orderOf x ∣ 24 := by
      have := orderOf_dvd_natCard x
      simpa [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] using this
    have hcop : Nat.Coprime (orderOf x) (2 ^ 3) :=
      Nat.Coprime.pow_right 3 (Odd.coprime_two_right (hodd.of_dvd_nat h1))
    have h24' : orderOf x ∣ 2 ^ 3 * 3 := by norm_num; exact h24
    exact Nat.Coprime.dvd_of_dvd_mul_left hcop h24'
  have hx3 : x ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp hord
  obtain ⟨y, hc1, hc2⟩ := key x hx3 hx1
  have hcN : y * x * y⁻¹ * x⁻¹ ∈ N :=
    N.mul_mem (Subgroup.Normal.conj_mem inferInstance x hx y) (N.inv_mem hx)
  have hord2 : orderOf (y * x * y⁻¹ * x⁻¹) = 2 := orderOf_eq_prime hc2 hc1
  have h2dvd : 2 ∣ Nat.card N := by
    have := orderOf_dvd_natCard (⟨y * x * y⁻¹ * x⁻¹, hcN⟩ : N)
    rwa [Subgroup.orderOf_mk, hord2] at this
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2dvd)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
