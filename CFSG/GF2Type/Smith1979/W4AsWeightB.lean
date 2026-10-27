module

public import CFSG.GF2Type.Smith1979.W4AsWeight
public import CFSG.GF2Type.Smith1979.W4O83Plane

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4As

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.GF2Type.Smith1979.W4O83

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem exists_ne_zero_mem_plane (C : Omega83Pre S) (i : Fin 4) : ∃ v ∈ C.plane i, v ≠ 0 := by
  by_contra h
  push Not at h
  have hbot : C.plane i = ⊥ := (Submodule.eq_bot_iff _).mpr h
  have h2 := C.finrank_plane i
  rw [hbot, finrank_bot] at h2
  omega

theorem q_sum_eq (C : Omega83Pre S) {w : Fin 4 → S.Qt} (hw : ∀ i, w i ∈ C.plane i) :
    S.q (∑ i, w i) = ∑ i, S.q (w i) := by
  have h : ∀ i j, i ≠ j → polar S.q (w i) (w j) = 0 := fun i j hij =>
    C.polar_eq_zero i j hij _ (hw i) _ (hw j)
  simp only [Fin.sum_univ_four, QuadraticMap.map_add, polar_add_left, h 0 1 (by decide),
    h 0 2 (by decide), h 1 2 (by decide), h 0 3 (by decide), h 1 3 (by decide),
    h 2 3 (by decide), add_zero]

theorem false_of_two_prL_eq_zero {E : Subgroup S.O} (C : Omega83Pre S) (hEM : E ≤ S.Mbar)
    (hE3 : ∀ x ∈ E, x ^ 3 = 1) (hE81 : Nat.card E ∣ 3 ^ 4) (hθ : ∀ i, C.theta i ∈ E)
    (hw : S.width = 4) {g : G} (H : S4.Hyp4 S g) (Cn : S4.Cons311 S g) {i j : Fin 4}
    (hij : i ≠ j) (hi : C.prL i (S.cl (g * S.z * g⁻¹)) = 0)
    (hj : C.prL j (S.cl (g * S.z * g⁻¹)) = 0) : False := by
  set b := S.cl (g * S.z * g⁻¹)
  let X : Subgroup S.O :=
    { carrier := {x | x ∈ E ∧ (x : S.Qt ≃ₗ[ZMod 2] S.Qt) b = b}
      mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, by
        rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hy.2, hx.2]⟩
      one_mem' := ⟨one_mem _, rfl⟩
      inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by
        conv_lhs => rw [← hx.2]
        exact LinearEquiv.symm_apply_apply _ b⟩ }
  have hXE : X ≤ E := fun x hx => hx.1
  have hX3 : Nat.card X ∣ 3 :=
    card_dvd_three H Cn hw (X := X) (fun x hx => hEM hx.1) (fun x hx => hE3 x hx.1)
      ((Subgroup.card_dvd_of_le hXE).trans hE81) (fun x hx => hx.2)
  have hθX : ∀ l, C.prL l b = 0 → C.theta l ∈ X := fun l hl => ⟨hθ l, (C.th_eq_iff l b).mpr hl⟩
  have hθ1 : ∀ l, C.theta l ≠ 1 := by
    intro l h
    obtain ⟨v, hv, hv0⟩ := exists_ne_zero_mem_plane C l
    refine hv0 (C.eq_zero_of_th_eq hv ?_)
    change ((C.theta l : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v
    rw [h]
    rfl
  have hcard : Nat.card X = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hX3 with h | h
    · exfalso
      have hX1 : X = ⊥ := (Subgroup.card_eq_one).mp h
      have := hθX i hi
      rw [hX1, Subgroup.mem_bot] at this
      exact hθ1 i this
    · exact h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne : (⟨C.theta i, hθX i hi⟩ : X) ≠ 1 := fun h => hθ1 i (congrArg Subtype.val h)
  obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.mp
    (mem_powers_of_prime_card (g' := (⟨C.theta j, hθX j hj⟩ : X)) hcard hne)
  have hpow : C.theta i ^ n = C.theta j := congrArg Subtype.val hn
  obtain ⟨v, hv, hv0⟩ := exists_ne_zero_mem_plane C j
  have hθv : ((C.theta i : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := C.th_eq_of_ne hij hv
  have hfix : ∀ m : ℕ, ((C.theta i ^ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [pow_succ, Subgroup.coe_mul, LinearEquiv.mul_apply, hθv, ih]
  refine hv0 (C.eq_zero_of_th_eq hv ?_)
  change ((C.theta j : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v
  rw [← hpow]
  exact hfix n

theorem prL_ne_zero_of_conj_z (C : Omega83Pre S) {E : Subgroup S.O} (hEM : E ≤ S.Mbar)
    (hE3 : ∀ x ∈ E, x ^ 3 = 1) (hE81 : Nat.card E ∣ 3 ^ 4) (hθ : ∀ i, C.theta i ∈ E)
    (hw : S.width = 4) {g : G} (H : S4.Hyp4 S g) (Cn : S4.Cons311 S g) (k : Fin 4) :
    C.prL k (S.cl (g * S.z * g⁻¹)) ≠ 0 := by
  set b := S.cl (g * S.z * g⁻¹)
  intro hk
  have hothers : ∀ j, j ≠ k → C.prL j b ≠ 0 := fun j hj h =>
    false_of_two_prL_eq_zero C hEM hE3 hE81 hθ hw H Cn hj.symm hk h
  have hsum : S.q b = ∑ i, S.q (C.prL i b) := by
    conv_lhs => rw [← C.sum_prL b]
    exact q_sum_eq C fun i => C.prL_mem_plane i b
  have hval : ∀ i, S.q (C.prL i b) = if i = k then 0 else 1 := by
    intro i
    by_cases hik : i = k
    · subst hik
      rw [hk, map_zero, ite_eq_left rfl]
    · rw [ite_eq_right hik]
      exact C.q_eq_one i _ (C.prL_mem_plane i b) (hothers i hik)
  have hq : S.q b = 0 := S4.q_cl_conj_z S H.conj_mem
  rw [hsum] at hq
  simp only [hval] at hq
  revert hq
  fin_cases k <;> decide

end CFSG.GF2Type.Smith1979.W4As
