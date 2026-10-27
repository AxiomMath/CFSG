module

public import CFSG.Quasithin.Background.G6Natural
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Quasithin

namespace Coho5

def cA : Equiv.Perm (Fin 5) := Equiv.swap 1 2 * Equiv.swap 3 4

def cB : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 1 3

theorem cA_alt : cA ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

theorem cB_alt : cB ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

theorem cA_sq : cA ^ 2 = 1 := by decide +kernel

theorem cB_cube : cB ^ 3 = 1 := by decide +kernel

theorem cAB_five : (cA * cB) ^ 5 = 1 := by decide +kernel

theorem alt_le_of_mem {K : Subgroup (Equiv.Perm (Fin 5))} (ha : cA ∈ K) (hb : cB ∈ K) :
    alternatingGroup (Fin 5) ≤ K := by
  classical
  let a' : alternatingGroup (Fin 5) := ⟨cA, cA_alt⟩
  let b' : alternatingGroup (Fin 5) := ⟨cB, cB_alt⟩
  let H : Subgroup (alternatingGroup (Fin 5)) := K.subgroupOf (alternatingGroup (Fin 5))
  have ha' : a' ∈ H := Subgroup.mem_subgroupOf.2 ha
  have hb' : b' ∈ H := Subgroup.mem_subgroupOf.2 hb
  have h2 : a' ^ 2 = 1 := by decide +kernel
  have h3 : b' ^ 3 = 1 := by decide +kernel
  have h5 : (a' * b') ^ 5 = 1 := by decide +kernel
  have n2 : a' ≠ 1 := by decide +kernel
  have n3 : b' ≠ 1 := by decide +kernel
  have n5 : a' * b' ≠ 1 := by decide +kernel
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have d2 : 2 ∣ Nat.card H := by
    simpa [orderOf_eq_prime h2 n2] using Subgroup.orderOf_dvd_natCard H ha'
  have d3 : 3 ∣ Nat.card H := by
    simpa [orderOf_eq_prime h3 n3] using Subgroup.orderOf_dvd_natCard H hb'
  have d5 : 5 ∣ Nat.card H := by
    simpa [orderOf_eq_prime h5 n5] using Subgroup.orderOf_dvd_natCard H (mul_mem ha' hb')
  have hcardA : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hdvd : Nat.card H ∣ 60 := hcardA ▸ Subgroup.card_subgroup_dvd_card H
  have hle : Nat.card H ≤ 60 := Nat.le_of_dvd (by norm_num) hdvd
  have h30 : Nat.card H = 30 ∨ Nat.card H = 60 := by
    interval_cases h : Nat.card H <;> omega
  have hHtop : H = ⊤ := by
    rcases h30 with h | h
    · exfalso
      have hidx : H.index = 2 := by
        have := Subgroup.card_mul_index H
        rw [h, hcardA] at this
        omega
      have := Subgroup.normal_of_index_eq_two hidx
      have := alternatingGroup.isSimpleGroup (α := Fin 5) (by simp)
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with h' | h'
      · rw [h', Subgroup.index_bot, hcardA] at hidx
        omega
      · rw [h', Subgroup.index_top] at hidx
        omega
    · exact Subgroup.eq_top_of_card_eq H (h.trans hcardA.symm)
  intro σ hσ
  have : (⟨σ, hσ⟩ : alternatingGroup (Fin 5)) ∈ H := by rw [hHtop]; trivial
  exact Subgroup.mem_subgroupOf.1 this

theorem core_mul_comm (x y : G6.coreMod 5) : x * y = y * x :=
  Subtype.ext (mul_comm (x : G6.PermMod 5) y)

theorem comm_aux {G : Type*} [Group G] (hcomm : ∀ x y : G, x * y = y * x) (A X w : G) :
    A * w⁻¹ * (X * A⁻¹) = X * w⁻¹ := by
  let _ : CommGroup G := { (inferInstance : Group G) with mul_comm := hcomm }
  rw [show A * w⁻¹ * (X * A⁻¹) = (A * A⁻¹) * (X * w⁻¹) by ac_rfl, mul_inv_cancel, one_mul]

def nrm (σ : Equiv.Perm (Fin 5)) : ℕ → G6.coreMod 5 → G6.coreMod 5
  | 0, _ => 1
  | n + 1, u => u * (G6.coreAct 5 σ) (nrm σ n u)

section Cocycle

variable {E : Type*} [Group E] (η : E →* Equiv.Perm (Fin 5)) (c : E → G6.coreMod 5)

theorem c_pow (hc : ∀ e e', c (e * e') = c e * (G6.coreAct 5 (η e)) (c e')) (h1 : c 1 = 1)
    (x : E) (n : ℕ) : c (x ^ n) = nrm (η x) n (c x) := by
  induction n with
  | zero => simpa [nrm] using h1
  | succ n ih => rw [pow_succ', hc, ih]; rfl

theorem good_mul (hc : ∀ e e', c (e * e') = c e * (G6.coreAct 5 (η e)) (c e'))
    (w : G6.coreMod 5) {x y : E} (hx : c x = (G6.coreAct 5 (η x)) w * w⁻¹)
    (hy : c y = (G6.coreAct 5 (η y)) w * w⁻¹) :
    c (x * y) = (G6.coreAct 5 (η (x * y))) w * w⁻¹ := by
  rw [hc, hx, hy, map_mul η, map_mul (G6.coreAct 5), MulAut.mul_apply, map_mul, map_inv]
  exact comm_aux core_mul_comm _ _ _

theorem act_inv_act (x : E) (u : G6.coreMod 5) :
    (G6.coreAct 5 (η x⁻¹)) ((G6.coreAct 5 (η x)) u) = u := by
  rw [← MulAut.mul_apply, ← map_mul, ← map_mul η, inv_mul_cancel, map_one, map_one]
  rfl

theorem good_inv (hc : ∀ e e', c (e * e') = c e * (G6.coreAct 5 (η e)) (c e')) (h1 : c 1 = 1)
    (w : G6.coreMod 5) {x : E} (hx : c x = (G6.coreAct 5 (η x)) w * w⁻¹) :
    c x⁻¹ = (G6.coreAct 5 (η x⁻¹)) w * w⁻¹ := by
  have h := hc x x⁻¹
  rw [mul_inv_cancel, h1] at h
  have h2 : (G6.coreAct 5 (η x)) (c x⁻¹) = (c x)⁻¹ := eq_inv_of_mul_eq_one_right h.symm
  have h3 : c x⁻¹ = (G6.coreAct 5 (η x⁻¹)) ((c x)⁻¹) := by
    rw [← h2, act_inv_act]
  rw [h3, hx, mul_inv_rev, inv_inv, map_mul, map_inv (G6.coreAct 5 (η x⁻¹)), act_inv_act]

end Cocycle

section Key

local instance instDecidablePredMemCore : DecidablePred (· ∈ G6.coreMod 5) :=
  fun x => decidable_of_iff (∑ i, Multiplicative.toAdd x i = 0) G6.mem_coreMod.symm

set_option synthInstance.maxSize 2000 in
theorem key : ∀ u v : G6.coreMod 5,
    nrm cA 2 u = 1 → nrm cB 3 v = 1 → nrm (cA * cB) 5 (u * (G6.coreAct 5 cA) v) = 1 →
    ∃ w : G6.coreMod 5, u = (G6.coreAct 5 cA) w * w⁻¹ ∧ v = (G6.coreAct 5 cB) w * w⁻¹ := by
  decide +kernel

end Key

end Coho5

theorem coho_A5 {E : Type*} [Group E] [Finite E] (η : E →* Equiv.Perm (Fin 5))
    (hA : ∀ e, η e ∈ alternatingGroup (Fin 5))
    (hs : ∀ σ ∈ alternatingGroup (Fin 5), ∃ e, η e = σ)
    (c : E → G6.coreMod 5)
    (hc : ∀ e e', c (e * e') = c e * (G6.coreAct 5 (η e)) (c e'))
    (hker : ∀ e, η e = 1 → c e = 1) :
    ∃ w : G6.coreMod 5, ∀ e, c e = (G6.coreAct 5 (η e)) w * w⁻¹ := by
  obtain ⟨ea, hea⟩ := hs _ Coho5.cA_alt
  obtain ⟨eb, heb⟩ := hs _ Coho5.cB_alt
  have h1 : c 1 = 1 := hker 1 (map_one η)
  have R1 : Coho5.nrm Coho5.cA 2 (c ea) = 1 := by
    rw [← hea, ← Coho5.c_pow η c hc h1 ea 2]
    exact hker _ (by rw [map_pow, hea]; exact Coho5.cA_sq)
  have R2 : Coho5.nrm Coho5.cB 3 (c eb) = 1 := by
    rw [← heb, ← Coho5.c_pow η c hc h1 eb 3]
    exact hker _ (by rw [map_pow, heb]; exact Coho5.cB_cube)
  have R3 : Coho5.nrm (Coho5.cA * Coho5.cB) 5 (c ea * (G6.coreAct 5 Coho5.cA) (c eb)) = 1 := by
    have e1 : η (ea * eb) = Coho5.cA * Coho5.cB := by rw [map_mul, hea, heb]
    have e2 : c (ea * eb) = c ea * (G6.coreAct 5 Coho5.cA) (c eb) := by rw [hc, hea]
    rw [← e1, ← e2, ← Coho5.c_pow η c hc h1]
    exact hker _ (by rw [map_pow, e1]; exact Coho5.cAB_five)
  obtain ⟨w, hwa, hwb⟩ := Coho5.key _ _ R1 R2 R3
  let Gd : Subgroup E :=
    { carrier := {e | c e = (G6.coreAct 5 (η e)) w * w⁻¹}
      mul_mem' := fun {x y} hx hy => Coho5.good_mul η c hc w hx hy
      one_mem' := by
        show c 1 = (G6.coreAct 5 (η 1)) w * w⁻¹
        rw [h1, map_one, map_one]
        simp
      inv_mem' := fun {x} hx => Coho5.good_inv η c hc h1 w hx }
  have hker_le : ∀ e, η e = 1 → e ∈ Gd := by
    intro e he
    show c e = (G6.coreAct 5 (η e)) w * w⁻¹
    rw [hker e he, he, map_one]
    simp
  have hea_mem : ea ∈ Gd := by
    show c ea = (G6.coreAct 5 (η ea)) w * w⁻¹
    rw [hea]
    exact hwa
  have heb_mem : eb ∈ Gd := by
    show c eb = (G6.coreAct 5 (η eb)) w * w⁻¹
    rw [heb]
    exact hwb
  have hK : alternatingGroup (Fin 5) ≤ Gd.map η :=
    Coho5.alt_le_of_mem (Subgroup.mem_map.2 ⟨ea, hea_mem, hea⟩)
      (Subgroup.mem_map.2 ⟨eb, heb_mem, heb⟩)
  refine ⟨w, fun e => ?_⟩
  obtain ⟨g, hg, hge⟩ := Subgroup.mem_map.1 (hK (hA e))
  have hk : e * g⁻¹ ∈ Gd := hker_le _ (by rw [map_mul, map_inv, hge, mul_inv_cancel])
  have := mul_mem hk hg
  rw [inv_mul_cancel_right] at this
  exact this

end CFSG.CGT.PushingUpLit.SYMB
