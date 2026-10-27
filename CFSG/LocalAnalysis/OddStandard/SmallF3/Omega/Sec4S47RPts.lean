module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FSetup
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def sec4S47RCoord (t : G) (φ : (Fin 7 → ZMod 2) → G) (v : Option (Fin 7) → ZMod 2) : G :=
  t ^ (v none + ∑ k, v (some k)).val * φ (fun k => (∑ l, v (some l)) + v (some k))

variable [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
  {φ : (Fin 7 → ZMod 2) → G}

private def sec4S47RS (v : Option (Fin 7) → ZMod 2) : ZMod 2 := ∑ k, v (some k)

private def sec4S47RA (v : Option (Fin 7) → ZMod 2) : ZMod 2 := v none + sec4S47RS v

private def sec4S47RW (v : Option (Fin 7) → ZMod 2) : Fin 7 → ZMod 2 :=
  fun k => sec4S47RS v + v (some k)

private def sec4S47RTw (t : G) (a : ZMod 2) : G := t ^ a.val

private lemma sec4S47RCoord_eq (v : Option (Fin 7) → ZMod 2) :
    sec4S47RCoord t φ v = sec4S47RTw t (sec4S47RA v) * φ (sec4S47RW v) := rfl

private lemma sec4S47RS_add (v w : Option (Fin 7) → ZMod 2) :
    sec4S47RS (v + w) = sec4S47RS v + sec4S47RS w := by
  simp only [sec4S47RS, Pi.add_apply]
  rw [Finset.sum_add_distrib]

private lemma sec4S47RA_add (v w : Option (Fin 7) → ZMod 2) :
    sec4S47RA (v + w) = sec4S47RA v + sec4S47RA w := by
  simp only [sec4S47RA, Pi.add_apply, sec4S47RS_add]
  ring

private lemma sec4S47RW_add (v w : Option (Fin 7) → ZMod 2) :
    sec4S47RW (v + w) = sec4S47RW v + sec4S47RW w := by
  funext k
  simp only [sec4S47RW, Pi.add_apply, sec4S47RS_add]
  ring

private lemma sec4S47RW_even (v : Option (Fin 7) → ZMod 2) : IsEvenVec (sec4S47RW v) := by
  simp only [IsEvenVec, sec4S47RW, sec4S47RS]
  rw [Finset.sum_add_distrib, Fin.sum_const, nsmul_eq_mul]
  rw [show ((7 : ℕ) : ZMod 2) = 1 by decide, one_mul]
  exact CharTwo.add_self_eq_zero _

private lemma sec4S47RTw_zero (t : G) : sec4S47RTw t 0 = 1 := by
  unfold sec4S47RTw
  rw [show (0 : ZMod 2).val = 0 by decide, pow_zero]

private lemma sec4S47RTw_one (t : G) : sec4S47RTw t 1 = t := by
  unfold sec4S47RTw
  rw [show (1 : ZMod 2).val = 1 by decide, pow_one]

private lemma sec4S47RTw_add {t : G} (ht : t * t = 1) (a b : ZMod 2) :
    sec4S47RTw t (a + b) = sec4S47RTw t a * sec4S47RTw t b := by
  have h2 : t ^ 2 = 1 := by rw [pow_two]; exact ht
  unfold sec4S47RTw
  rw [ZMod.val_add, ← pow_add, pow_eq_pow_mod (a.val + b.val) h2]

private lemma sec4S47RA_single (s : Option (Fin 7)) :
    sec4S47RA (Pi.single s (1 : ZMod 2)) = 1 := by
  revert s
  decide +kernel

private lemma sec4S47RA_ones :
    sec4S47RA (fun _ : Option (Fin 7) => (1 : ZMod 2)) = 0 := by
  decide +kernel

private lemma sec4S47RW_none :
    sec4S47RW (Pi.single (none : Option (Fin 7)) (1 : ZMod 2)) = 0 := by
  decide +kernel

private lemma sec4S47RW_some (i : Fin 7) :
    sec4S47RW (Pi.single (some i : Option (Fin 7)) (1 : ZMod 2)) = sec4MW i := by
  revert i
  decide +kernel

private lemma sec4S47RW_ones :
    sec4S47RW (fun _ : Option (Fin 7) => (1 : ZMod 2)) = 0 := by
  decide +kernel

private lemma sec4S47RCoord_mem_A (h : Sec4FSetup t L S z A B φ)
    (v : Option (Fin 7) → ZMod 2) : sec4S47RCoord t φ v ∈ A := by
  rw [sec4S47RCoord_eq]
  exact A.mul_mem (A.pow_mem h.t_mem_A (sec4S47RA v).val)
    (h.B_le_A (h.data.bdata.perm.mem (sec4S47RW_even v)))

theorem sec4S47RCoord_zero (h : Sec4FSetup t L S z A B φ) : sec4S47RCoord t φ 0 = 1 := by
  rw [sec4S47RCoord_eq]
  have hA : sec4S47RA (0 : Option (Fin 7) → ZMod 2) = 0 := by decide +kernel
  have hW : sec4S47RW (0 : Option (Fin 7) → ZMod 2) = 0 := by decide +kernel
  rw [hA, hW, sec4S47RTw_zero, one_mul]
  exact IsPermModuleVia.map_zero h.data.bdata.perm

theorem sec4S47RCoord_add (h : Sec4FSetup t L S z A B φ) (v w : Option (Fin 7) → ZMod 2) :
    sec4S47RCoord t φ (v + w) = sec4S47RCoord t φ v * sec4S47RCoord t φ w := by
  have hwv : IsEvenVec (sec4S47RW v) := sec4S47RW_even v
  have hww : IsEvenVec (sec4S47RW w) := sec4S47RW_even w
  have hphiA : φ (sec4S47RW v) ∈ A := h.B_le_A (h.data.bdata.perm.mem hwv)
  have htwA : sec4S47RTw t (sec4S47RA w) ∈ A := A.pow_mem h.t_mem_A (sec4S47RA w).val
  have hcomm : φ (sec4S47RW v) * sec4S47RTw t (sec4S47RA w)
      = sec4S47RTw t (sec4S47RA w) * φ (sec4S47RW v) := h.A_comm hphiA htwA
  rw [sec4S47RCoord_eq (v + w), sec4S47RCoord_eq v, sec4S47RCoord_eq w,
    sec4S47RA_add, sec4S47RW_add, sec4S47RTw_add h.t_sq,
    h.data.bdata.perm.1 (sec4S47RW v) (sec4S47RW w) hwv hww]
  rw [mul_assoc (sec4S47RTw t (sec4S47RA v)) (sec4S47RTw t (sec4S47RA w))
    (φ (sec4S47RW v) * φ (sec4S47RW w))]
  rw [← mul_assoc (sec4S47RTw t (sec4S47RA w)) (φ (sec4S47RW v))
    (φ (sec4S47RW w))]
  rw [hcomm.symm]
  rw [mul_assoc (φ (sec4S47RW v)) (sec4S47RTw t (sec4S47RA w)) (φ (sec4S47RW w))]
  rw [← mul_assoc (sec4S47RTw t (sec4S47RA v)) (φ (sec4S47RW v))
    (sec4S47RTw t (sec4S47RA w) * φ (sec4S47RW w))]

theorem sec4S47RCoord_single (h : Sec4FSetup t L S z A B φ) (s : Option (Fin 7)) :
    sec4S47RCoord t φ (Pi.single s 1) = sec4MPt t φ s := by
  cases s with
  | none =>
    have hA : sec4S47RA (Pi.single (none : Option (Fin 7)) (1 : ZMod 2)) = 1 :=
      sec4S47RA_single none
    have hW : sec4S47RW (Pi.single (none : Option (Fin 7)) (1 : ZMod 2)) = 0 :=
      sec4S47RW_none
    rw [sec4S47RCoord_eq, hA, hW, sec4S47RTw_one,
      IsPermModuleVia.map_zero h.data.bdata.perm, mul_one]
    dsimp only [sec4MPt, sec4MV]
    rw [IsPermModuleVia.map_zero h.data.bdata.perm, mul_one]
  | some i =>
    have hA : sec4S47RA (Pi.single (some i : Option (Fin 7)) (1 : ZMod 2)) = 1 :=
      sec4S47RA_single (some i)
    have hW : sec4S47RW (Pi.single (some i : Option (Fin 7)) (1 : ZMod 2)) = sec4MW i :=
      sec4S47RW_some i
    rw [sec4S47RCoord_eq, hA, hW, sec4S47RTw_one]
    rfl

theorem sec4S47RCoord_mem (h : Sec4FSetup t L S z A B φ) (v : Option (Fin 7) → ZMod 2) :
    sec4S47RCoord t φ v ∈ A :=
  sec4S47RCoord_mem_A h v

theorem sec4S47R_exists_coord (h : Sec4FSetup t L S z A B φ) {a : G} (ha : a ∈ A) :
    ∃ v : Option (Fin 7) → ZMod 2, sec4S47RCoord t φ v = a := by
  obtain ⟨b, hb, hcases⟩ := h.mem_A_cases ha
  obtain ⟨w, hw_even, hw_eq⟩ := (h.data.bdata.perm.2.2.1 b).mp hb
  rcases hcases with rfl | rfl
  · refine ⟨fun s : Option (Fin 7) => Option.elim s 0 w, ?_⟩
    have hS : sec4S47RS (fun s : Option (Fin 7) => Option.elim s 0 w) = 0 := by
      simpa [sec4S47RS, IsEvenVec] using hw_even
    have hA : sec4S47RA (fun s : Option (Fin 7) => Option.elim s 0 w) = 0 := by
      simp [sec4S47RA, hS]
    have hW : sec4S47RW (fun s : Option (Fin 7) => Option.elim s 0 w) = w := by
      funext k; simp [sec4S47RW, hS]
    rw [sec4S47RCoord_eq, hA, hW, sec4S47RTw_zero, one_mul, hw_eq]
  · refine ⟨fun s : Option (Fin 7) => Option.elim s 1 w, ?_⟩
    have hS : sec4S47RS (fun s : Option (Fin 7) => Option.elim s 1 w) = 0 := by
      simpa [sec4S47RS, IsEvenVec] using hw_even
    have hA : sec4S47RA (fun s : Option (Fin 7) => Option.elim s 1 w) = 1 := by
      simp [sec4S47RA, hS]
    have hW : sec4S47RW (fun s : Option (Fin 7) => Option.elim s 1 w) = w := by
      funext k; simp [sec4S47RW, hS]
    rw [sec4S47RCoord_eq, hA, hW, sec4S47RTw_one, hw_eq, h.t_cent_L (h.B_le_L hb)]

theorem sec4S47RCoord_eq_one_iff (h : Sec4FSetup t L S z A B φ) (v : Option (Fin 7) → ZMod 2) :
    sec4S47RCoord t φ v = 1 ↔ v = 0 ∨ v = fun _ => 1 := by
  constructor
  · intro hv
    by_cases ha0 : sec4S47RA v = 0
    · have hphi : φ (sec4S47RW v) = 1 := by
        have h := hv
        rw [sec4S47RCoord_eq, ha0, sec4S47RTw_zero, one_mul] at h
        exact h
      have hw0 : sec4S47RW v = 0 :=
        h.data.bdata.perm.2.1 (sec4S47RW v) 0 (sec4S47RW_even v)
          (by unfold IsEvenVec; simp)
          (by rw [hphi, IsPermModuleVia.map_zero h.data.bdata.perm])
      have hsome : ∀ k : Fin 7, v (some k) = sec4S47RS v := by
        intro k
        have hk := congr_fun hw0 k
        simp only [sec4S47RW, Pi.zero_apply] at hk
        exact (CharTwo.add_eq_zero.mp hk).symm
      have hnone : v none = sec4S47RS v := by
        have h0 := ha0
        simp only [sec4S47RA] at h0
        exact CharTwo.add_eq_zero.mp h0
      have hvS : v = fun _ => sec4S47RS v := by
        funext r
        cases r with
        | none => exact hnone
        | some k => exact hsome k
      by_cases hS : sec4S47RS v = 0
      · left; rw [hvS, hS]; rfl
      · right; rw [hvS, zmod2_eq_one_of_ne_zero hS]
    · exfalso
      have ha1 : sec4S47RA v = 1 := zmod2_eq_one_of_ne_zero ha0
      have ht : t = (φ (sec4S47RW v))⁻¹ := by
        have h := hv
        rw [sec4S47RCoord_eq, ha1, sec4S47RTw_one] at h
        exact mul_eq_one_iff_eq_inv.mp h
      have hb : φ (sec4S47RW v) ∈ B := h.data.bdata.perm.mem (sec4S47RW_even v)
      have htL : t ∈ L := by
        rw [ht]
        exact h.B_le_L (B.inv_mem hb)
      exact sec4_t_not_mem h.ctx.toSec4Setting htL
  · rintro (rfl | rfl)
    · exact sec4S47RCoord_zero h
    · rw [sec4S47RCoord_eq, sec4S47RA_ones, sec4S47RW_ones, sec4S47RTw_zero, one_mul,
        IsPermModuleVia.map_zero h.data.bdata.perm]

theorem sec4S47RCoord_eq_iff (h : Sec4FSetup t L S z A B φ) (v w : Option (Fin 7) → ZMod 2) :
    sec4S47RCoord t φ v = sec4S47RCoord t φ w ↔ ∃ ε : ZMod 2, ∀ r, v r + w r = ε := by
  constructor
  · intro hvw
    have h1 : sec4S47RCoord t φ (v + w) = 1 := by
      rw [sec4S47RCoord_add h v w, hvw, h.A_sq (sec4S47RCoord_mem h w)]
    rcases (sec4S47RCoord_eq_one_iff h (v + w)).mp h1 with h0 | h1'
    · refine ⟨0, fun r => ?_⟩
      have hr := congr_fun h0 r
      simpa using hr
    · refine ⟨1, fun r => ?_⟩
      have hr := congr_fun h1' r
      simpa using hr
  · rintro ⟨ε, hε⟩
    have hvw : v + w = fun _ => ε := by
      funext r; exact hε r
    have h1 : sec4S47RCoord t φ (v + w) = 1 := by
      rw [hvw]
      exact (sec4S47RCoord_eq_one_iff h (fun _ => ε)).mpr (by
        by_cases hε0 : ε = 0
        · left; funext r; simp [hε0]
        · right; funext r; simp [zmod2_eq_one_of_ne_zero hε0])
    have hmul : sec4S47RCoord t φ v * sec4S47RCoord t φ w = 1 := by
      rw [← sec4S47RCoord_add h v w, h1]
    have hww : sec4S47RCoord t φ w * sec4S47RCoord t φ w = 1 :=
      h.A_sq (sec4S47RCoord_mem h w)
    rw [mul_eq_one_iff_eq_inv] at hmul
    rw [hmul, (mul_eq_one_iff_eq_inv.mp hww).symm]

theorem sec4S47RCoord_conj (h : Sec4FSetup t L S z A B φ) {m : G}
    {σ : Equiv.Perm (Option (Fin 7))} (hm : Sec4MRealizes t φ m σ)
    (v : Option (Fin 7) → ZMod 2) :
    m * sec4S47RCoord t φ v * m⁻¹ = sec4S47RCoord t φ (v ∘ σ.symm) := by
  let P : (Option (Fin 7) → ZMod 2) → Prop :=
    fun u => m * sec4S47RCoord t φ u * m⁻¹ = sec4S47RCoord t φ (u ∘ σ.symm)
  have hzero : P 0 := by
    dsimp only [P]
    have hz : (0 : Option (Fin 7) → ZMod 2) ∘ σ.symm = 0 := rfl
    rw [sec4S47RCoord_zero h, hz, sec4S47RCoord_zero h]
    group
  have hsingle : ∀ s : Option (Fin 7), P (Pi.single s (1 : ZMod 2)) := by
    intro s
    dsimp only [P]
    have hcomp : (Pi.single s (1 : ZMod 2)) ∘ σ.symm = Pi.single (σ s) 1 := by
      funext r
      rw [Function.comp_apply, Pi.single_apply, Pi.single_apply]
      by_cases hs : σ.symm r = s
      · rw [if_pos hs, if_pos ((Equiv.symm_apply_eq σ).mp hs)]
      · rw [if_neg hs, if_neg (fun hh => hs ((Equiv.symm_apply_eq σ).mpr hh))]
    rw [sec4S47RCoord_single h s, hcomp, sec4S47RCoord_single h (σ s)]
    exact hm s
  have hadd : ∀ u w, P u → P w → P (u + w) := by
    intro u w hu hw
    dsimp only [P] at hu hw ⊢
    rw [sec4S47RCoord_add h u w]
    have hcomp : (u + w) ∘ σ.symm = u ∘ σ.symm + w ∘ σ.symm := rfl
    rw [hcomp, sec4S47RCoord_add h (u ∘ σ.symm) (w ∘ σ.symm)]
    calc m * (sec4S47RCoord t φ u * sec4S47RCoord t φ w) * m⁻¹
        = (m * sec4S47RCoord t φ u * m⁻¹) * (m * sec4S47RCoord t φ w * m⁻¹) := by
          group
      _ = sec4S47RCoord t φ (u ∘ σ.symm) * sec4S47RCoord t φ (w ∘ σ.symm) := by
          rw [hu, hw]
  have hP : ∀ u : Option (Fin 7) → ZMod 2, P u := by
    intro u
    let f : Option (Fin 7) → (Option (Fin 7) → ZMod 2) := fun i => Pi.single i (u i)
    have hsum : u = ∑ i, f i := (Finset.univ_sum_single u).symm
    rw [hsum]
    refine Finset.sum_induction (s := Finset.univ) f P hadd hzero ?_
    intro x _
    change P (Pi.single x (u x))
    by_cases hx : u x = 0
    · rw [hx, Pi.single_zero]
      exact hzero
    · rw [zmod2_eq_one_of_ne_zero hx]
      exact hsingle x
  exact hP v

end CFSG.OddStandard.SmallF3.Omega
