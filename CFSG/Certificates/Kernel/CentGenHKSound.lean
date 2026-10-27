module

public import Certificates.Data.Kernel.CentGenHK
public import CFSG.Certificates.Kernel.CentGenKSound

public section

namespace CFSG.KC.CentGenK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.SporSch
open scoped commutatorElement

section Nielsen

variable {G : Type*} [Group G]

theorem closure_mul_right (x y : G) :
    Subgroup.closure ({x * y, y} : Set G) = Subgroup.closure {x, y} := by
  refine le_antisymm (Subgroup.closure_le _ |>.2 ?_) (Subgroup.closure_le _ |>.2 ?_)
  · rintro g (rfl | rfl)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · exact Subgroup.subset_closure (by simp)
  · rintro g (rfl | rfl)
    · have e : g = g * y * y⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
    · exact Subgroup.subset_closure (by simp)

theorem closure_mul_left (x y : G) :
    Subgroup.closure ({y * x, y} : Set G) = Subgroup.closure {x, y} := by
  refine le_antisymm (Subgroup.closure_le _ |>.2 ?_) (Subgroup.closure_le _ |>.2 ?_)
  · rintro g (rfl | rfl)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · exact Subgroup.subset_closure (by simp)
  · rintro g (rfl | rfl)
    · have e : g = y⁻¹ * (y * g) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
        (Subgroup.subset_closure (by simp))
    · exact Subgroup.subset_closure (by simp)

theorem nielOK_cons (r : Nat) (prog : List Nat) :
    nielOK (r :: prog) = (Nat.beq (opC r) 0 && (Nat.blt (opK r) 2 &&
      (Nat.beq (opA r + opB r) 1 && nielOK prog))) := by
  simp only [nielOK, bA]
  rfl

theorem closure_niel : ∀ (prog : List ℕ) (R : ℕ → G), nielOK prog = true →
    Subgroup.closure ({runA R prog 0, runA R prog 1} : Set G) = Subgroup.closure {R 0, R 1}
  | [], _, _ => rfl
  | r :: prog, R, h => by
    rw [nielOK_cons, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨hc, hk, hab, h⟩ := h
    have hrun : runA R (r :: prog) = runA (stepA R r) prog := rfl
    rw [hrun, closure_niel prog _ h]
    have hc' : opC r = 0 := Nat.eq_of_beq_eq_true hc
    have hab' : opA r + opB r = 1 := Nat.eq_of_beq_eq_true hab
    unfold stepA
    rw [if_pos hc']
    rcases (by omega : opK r = 0 ∨ opK r = 1) with hk0 | hk0 <;>
    rcases (by omega : opA r = 0 ∧ opB r = 1 ∨ opA r = 1 ∧ opB r = 0) with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
    simp only [Function.update_apply, hk0, ha, hb, if_true, one_ne_zero, zero_ne_one, if_false]
    · exact closure_mul_right _ _
    · exact closure_mul_left _ _
    · rw [Set.pair_comm, closure_mul_left, Set.pair_comm]
    · rw [Set.pair_comm, closure_mul_right, Set.pair_comm]

end Nielsen

variable {n w : Nat}

theorem hpK_spec {A B : Nat} {a b : Equiv.Perm (Fin n)} (hA : PRep n w A a) (hB : PRep n w B b)
    {D : HPK} (h : hpK n w A B D = true) :
    ∃ s₁ s₂ : Equiv.Perm (Fin n),
      Subgroup.closure {s₁, s₂} = Subgroup.closure {a, b} ∧ 0 < D.p ∧
      (s₁ ^ D.ke) ^ D.p = 1 ∧ (s₂ ^ D.kf) ^ D.p = 1 ∧
      Commute ⁅s₁ ^ D.ke, s₂ ^ D.kf⁆ (s₁ ^ D.ke) ∧ Commute ⁅s₁ ^ D.ke, s₂ ^ D.kf⁆ (s₂ ^ D.kf) ∧
      (∀ k < D.p, ⁅s₁ ^ D.ke, s₂ ^ D.kf⁆ ≠ (s₁ ^ D.ke) ^ k) ∧
      (∀ k < D.p, ⁅s₁ ^ D.ke, s₂ ^ D.kf⁆ ≠ (s₂ ^ D.kf) ^ k) := by
  unfold hpK at h
  simp only [sB, bA, Bool.and_eq_true] at h
  obtain ⟨hsz, hA0, hB0, hn, h⟩ := h
  have psA : PS n w A a := ⟨hA, Nat.eq_of_beq_eq_true hA0⟩
  have psB : PS n w B b := ⟨hB, Nat.eq_of_beq_eq_true hB0⟩
  obtain ⟨R, -, hR, hfin⟩ := runK_sim hsz 2 [] _ D.prog _ (initA a b)
    (by simp [initR, repR_eq]) (ps_init hsz psA psB) h
  unfold finHK at hfin
  simp only [sB, bA, Bool.and_eq_true, Nat.sub_eq] at hfin
  obtain ⟨hp, hx, hy, hzx, hzy, hnx, hny⟩ := hfin
  have hp' : 0 < D.p := by simpa [Nat.blt_eq] using hp
  set S1 := runA (initA a b) D.prog 0 with hS1
  set S2 := runA (initA a b) D.prog 1 with hS2
  have px := ps_pow hsz (hR 0) D.ke
  have py := ps_pow hsz (hR 1) D.kf
  rw [ps_beq hsz (ps_pow hsz px D.p) (ps_one hsz), decide_eq_true_iff] at hx
  rw [ps_beq hsz (ps_pow hsz py D.p) (ps_one hsz), decide_eq_true_iff] at hy
  have hxi : (S1 ^ D.ke) ^ (D.p - 1) = (S1 ^ D.ke)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← pow_succ, Nat.sub_add_cancel hp', hx])
  have hyi : (S2 ^ D.kf) ^ (D.p - 1) = (S2 ^ D.kf)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← pow_succ, Nat.sub_add_cancel hp', hy])
  have pz := ps_mul hsz (ps_mul hsz (ps_mul hsz px py) (ps_pow hsz px (D.p - 1)))
    (ps_pow hsz py (D.p - 1))
  rw [hxi, hyi, ← commutatorElement_def] at pz
  rw [ps_beq hsz (ps_mul hsz pz px) (ps_mul hsz px pz), decide_eq_true_iff] at hzx
  rw [ps_beq hsz (ps_mul hsz pz py) (ps_mul hsz py pz), decide_eq_true_iff] at hzy
  refine ⟨S1, S2, by simpa [initA] using closure_niel D.prog (initA a b) hn, hp', hx, hy, hzx,
    hzy, fun k hk => ?_, fun k hk => ?_⟩
  · simpa using neAll_sound hsz pz px D.p _ 1 (ps_one hsz) hnx k hk
  · simpa using neAll_sound hsz pz py D.p _ 1 (ps_one hsz) hny k hk

end CFSG.KC.CentGenK

end
