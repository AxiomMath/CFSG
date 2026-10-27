module

public import Certificates.Data.Kernel.E81IK
public import CFSG.Certificates.Kernel.BfsPinAlg

public section

namespace CFSG.KC.E81IK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin

variable {n w : ℕ}

theorem eq_of_beq {a b : ℕ} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem pidn_comm (hsz : szOK n w = true) {s : ℕ} (hs : PP n w s) :
    pcomp n w (mask w) (pidn n w) s = pcomp n w (mask w) s (pidn n w) := by
  obtain ⟨hn, hw⟩ := szOK_facts' hsz
  have h32 : n < 2 ^ 32 := hs.lt32
  refine PF.eq_of_fields (PF.w_pos hw) (PF.pcomp_shr _ _ h32 (PF.w_pos hw))
    (PF.pcomp_shr _ _ h32 (PF.w_pos hw)) fun i hi => ?_
  rw [PF.pg_pcomp h32 hi, PF.pg_pcomp h32 hi, PF.pg_pidn hn hw (hs.2.1 i hi), PF.pg_pidn hn hw hi]

theorem covI_of {nd nh : ℕ} {ND : ℕ → ℕ} {DT : ℕ → ℕ → ℕ} {Z Z2 : ℕ} {ZW H : ℕ → ℕ}
    (hsz : szOK n w = true) (hnh : 0 < nh) (hH : H 0 = pidn n w)
    (hZ2 : pcomp n w (mask w) Z Z = Z2) {c s : ℕ} (hs : PP n w s) (hZ : PP n w Z)
    (h : covIK n w nd ND DT Z Z2 ZW c s = true) :
    (pcomp n w (mask w) s (pcomp n w (mask w) s s) ≠ pidn n w ∨ s = pidn n w ∨ s = Z ∨
        s = pcomp n w (mask w) Z Z) ∨
      ∃ i < nh, ∃ t < nd, ∃ j < ND t, ∃ j' < ND t,
        pcomp n w (mask w) (H i) s = pcomp n w (mask w) (DT t j) (H i) ∧
          pcomp n w (mask w) (H i) Z = pcomp n w (mask w) (DT t j') (H i) := by
  obtain ⟨hn, hw⟩ := szOK_facts' hsz
  have h32 : n < 2 ^ 32 := hs.lt32
  unfold covIK at h
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with (⟨-, (h | h) | h⟩ | ⟨⟨hc0, hcn⟩, hx⟩) | ⟨-, h⟩
  · exact Or.inl (Or.inr (Or.inr (Or.inl (eq_of_beq h))))
  · rw [hZ2]
    exact Or.inl (Or.inr (Or.inr (Or.inr (eq_of_beq h))))
  · exact Or.inl (Or.inr (Or.inl (eq_of_beq h)))
  · left
    left
    intro e
    have hx' : c - 1 < n := by
      have := Nat.le_of_ble_eq_true hcn
      have := Nat.blt_eq.mp hc0
      omega
    have e2 := congrArg (fun p => pg w (mask w) p (c - 1)) e
    rw [PF.pg_pcomp h32 hx', PF.pg_pcomp h32 hx', PF.pg_pidn hn hw hx'] at e2
    rw [e2, Nat.beq_refl] at hx
    exact absurd hx (by decide)
  · right
    unfold covIW at h
    simp only [Bool.and_eq_true] at h
    generalize (c - 1 - n) % nd = t at h
    generalize (c - 1 - n) / nd = j at h
    obtain ⟨⟨⟨⟨⟨ht, hj⟩, hz0⟩, hzl⟩, hsd⟩, hzd⟩ := h
    have hz0' := Nat.blt_eq.mp hz0
    have hzl' := Nat.le_of_ble_eq_true hzl
    refine ⟨0, hnh, t, Nat.blt_eq.mp ht, j, Nat.blt_eq.mp hj, ZW t - 1, by omega, ?_, ?_⟩
    · rw [hH, ← eq_of_beq hsd]
      exact pidn_comm hsz hs
    · rw [hH, ← eq_of_beq hzd]
      exact pidn_comm hsz hZ

end CFSG.KC.E81IK

end
