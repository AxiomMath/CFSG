module

public import Certificates.Data.Kernel.Co1Three.Cen
public import CFSG.Certificates.Kernel.Co1Three.SlpSound
public import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.Co1Cl

open CFSG.KC.Enum CFSG.KC.Co1F2

theorem fixFreeK_sound {R B : List Nat} (h : fixFreeK R B = true) {a : Nat} (h0 : 0 < a)
    (ha : a < 3 ^ B.length) : actK 3 6 R (actK 3 6 B a 0) 0 ≠ actK 3 6 B a 0 := by
  unfold fixFreeK at h
  have h' := CFSG.KS.Raw.Orb.allN_iff.1 h (a - 1) (by
    change a - 1 < Nat.pow 3 (lenL B) - 1
    rw [lenL_eq]
    change a - 1 < 3 ^ B.length - 1
    omega)
  rw [strictB_eq, Nat.succ_eq_add_one, Nat.sub_add_cancel h0] at h'
  intro he
  rw [he, Nat.beq_refl] at h'
  exact Bool.false_ne_true h'

theorem addVK_sub_three : ∀ a < 27, ∀ a' < 27,
    addVK 3 3 a (addVK 3 3 a' (addVK 3 3 a a)) = a' ∧
      (addVK 3 3 a' (addVK 3 3 a a) = 0 → a = a') := by decide +kernel

theorem addVK_sub_four : ∀ a < 81, ∀ a' < 81,
    addVK 3 4 a (addVK 3 4 a' (addVK 3 4 a a)) = a' ∧
      (addVK 3 4 a' (addVK 3 4 a a) = 0 → a = a') := by decide +kernel

theorem card_inf_centralizer_mul_le {M : Type*} [Group M] {T : Subgroup M} [Finite T]
    (hT : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (t : M) {m : Nat} (w : Nat → M)
    (hw : ∀ a < m, w a ∈ T)
    (hsub : ∀ a < m, ∀ a' < m, ∃ x < m, w a' = w a * w x ∧ (x = 0 → a = a'))
    (hfree : ∀ x < m, 0 < x → w x * t ≠ t * w x) :
    Nat.card ↥(T ⊓ Subgroup.centralizer ({t} : Set M)) * m ≤ Nat.card T := by
  set S := T ⊓ Subgroup.centralizer ({t} : Set M)
  let F : ↥S × Fin m → ↥T := fun p => ⟨p.1 * w p.2, T.mul_mem (Subgroup.mem_inf.1 p.1.2).1
    (hw _ p.2.2)⟩
  have hF : Function.Injective F := by
    rintro ⟨s, a⟩ ⟨s', a'⟩ he
    have e : (s : M) * w a = s' * w a' := congrArg Subtype.val he
    obtain ⟨x, hx, hwx, hx0⟩ := hsub a a.2 a' a'.2
    have hsT := (Subgroup.mem_inf.1 s.2).1
    have hs'T := (Subgroup.mem_inf.1 s'.2).1
    have hc : (s : M) = s' * w x := by
      rw [hwx, hT _ (hw _ a.2) _ (hw _ hx), ← mul_assoc] at e
      exact mul_right_cancel e
    have hxC : w x ∈ Subgroup.centralizer ({t} : Set M) := by
      have : w x = (s' : M)⁻¹ * s := by rw [hc, inv_mul_cancel_left]
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_inf.1 s'.2).2)
        (Subgroup.mem_inf.1 s.2).2
    have hx0' : x = 0 := by
      by_contra hne
      exact hfree x hx (Nat.pos_of_ne_zero hne)
        (Subgroup.mem_centralizer_singleton_iff.1 hxC)
    have haa := hx0 hx0'
    have hw0 : w x = 1 := by
      have e2 := hwx
      rw [← haa] at e2
      exact (mul_eq_left.1 e2.symm)
    have hss : s = s' := Subtype.ext (by rw [hc, hw0, mul_one])
    rw [hss, Fin.ext haa]
  have h := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin] at h

end CFSG.KC.Co1Cl

end
