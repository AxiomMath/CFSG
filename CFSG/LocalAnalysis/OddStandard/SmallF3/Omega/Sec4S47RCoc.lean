module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4S47Odd

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
  {φ : (Fin 7 → ZMod 2) → G}

theorem sec4S47R_mem_A_oddCore (h : Sec4FSetup t L S z A B φ) {x : G} (hxA : x ∈ A)
    (hxO : x ∈ oddCoreIn (centralizer (A : Set G))) : x = 1 := by
  have hx2 : x * x = 1 := h.A_sq hxA
  have hodd : Odd (orderOf x) := odd_orderOf_of_mem_oddCoreIn hxO
  have hdvd : orderOf x ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_two]
    exact hx2
  have h1 : orderOf x = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr hodd) hdvd dvd_rfl
  exact orderOf_eq_one_iff.mp h1

theorem sec4S47R_sq_conj (h : Sec4FSetup t L S z A B φ) {y y' : G}
    (hyN : y ∈ normalizer (A : Set G)) (hc : y * y ∈ A) (hc' : y' * y' ∈ A)
    (hd : y⁻¹ * y' ∈ centralizer (A : Set G)) :
    ∃ a ∈ A, y' * y' = (y * y) * ((y⁻¹ * a * y) * a) := by
  have hcomm : ∀ a ∈ A, ∀ o ∈ oddCoreIn (centralizer (A : Set G)), a * o = o * a :=
    fun a ha o ho =>
      Subgroup.mem_centralizer_iff.mp ((oddCoreIn_normal (centralizer (A : Set G))).1 ho) a ha
  have hdO : y⁻¹ * y' ∈ A ⊔ oddCoreIn (centralizer (A : Set G)) := by
    rw [h.sup_oddCore]
    exact hd
  obtain ⟨a, ha, o, ho, hdo⟩ := sec4F_mem_sup_comm hcomm hdO
  refine ⟨a, ha, ?_⟩
  have hya : y⁻¹ * a * y ∈ A := (Subgroup.mem_set_normalizer_iff''.mp hyN a).mp ha
  have hyo : y⁻¹ * o * y ∈ oddCoreIn (centralizer (A : Set G)) := by
    have h1 := h.conj_mem_oddCore (inv_mem hyN) ho
    simpa using h1
  have hy' : y' = y * (a * o) := by
    rw [← hdo]
    group
  have hcalc : y' * y' =
      (y * y) * (((y⁻¹ * a * y) * (y⁻¹ * o * y)) * (a * o)) := by
    rw [hy']
    group
  have hkey : ((y⁻¹ * a * y) * (y⁻¹ * o * y)) * (a * o) =
      ((y⁻¹ * a * y) * a) * ((y⁻¹ * o * y) * o) := by
    have h1 : (y⁻¹ * o * y) * a = a * (y⁻¹ * o * y) :=
      (hcomm a ha (y⁻¹ * o * y) hyo).symm
    calc ((y⁻¹ * a * y) * (y⁻¹ * o * y)) * (a * o)
        = (y⁻¹ * a * y) * ((y⁻¹ * o * y) * (a * o)) := by group
      _ = (y⁻¹ * a * y) * (((y⁻¹ * o * y) * a) * o) := by group
      _ = (y⁻¹ * a * y) * ((a * (y⁻¹ * o * y)) * o) := by rw [h1]
      _ = ((y⁻¹ * a * y) * a) * ((y⁻¹ * o * y) * o) := by group
  have hsq : y' * y' =
      ((y * y) * ((y⁻¹ * a * y) * a)) * ((y⁻¹ * o * y) * o) := by
    rw [hcalc, hkey]
    group
  have hc0 : (y * y) * ((y⁻¹ * a * y) * a) ∈ A := A.mul_mem hc (A.mul_mem hya ha)
  have hxO : (y⁻¹ * o * y) * o ∈ oddCoreIn (centralizer (A : Set G)) :=
    (oddCoreIn (centralizer (A : Set G))).mul_mem hyo ho
  have hx_eq : ((y * y) * ((y⁻¹ * a * y) * a))⁻¹ * (y' * y') =
      (y⁻¹ * o * y) * o := by
    rw [hsq]
    group
  have hxA : (y⁻¹ * o * y) * o ∈ A := by
    rw [← hx_eq]
    exact A.mul_mem (A.inv_mem hc0) hc'
  have hx1 : (y⁻¹ * o * y) * o = 1 := sec4S47R_mem_A_oddCore h hxA hxO
  rw [hsq, hx1, mul_one]

end CFSG.OddStandard.SmallF3.Omega
