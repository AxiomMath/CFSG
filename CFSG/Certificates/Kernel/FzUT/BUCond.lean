module

public import CFSG.Certificates.Kernel.FzUT.BUTransport

public section

namespace CFSG.KC.FzUT

open CFSG.OddStandard.SmallF3.FritzII CFSG.GH74.GLS.Bg.TwoGroups

variable {aq as ay : MulAut FzUT}

theorem hq_of (A : FzbAdm (fzRho0 * fzRho0) aq as ay) (x : FzUT) :
    enc (aq x) = cfP (enc (aq fzE1)) (enc (aq fzF1)) (enc x) :=
  cfP_of_comm aq (fun y => A.q_r y) x

theorem hs_of (A : FzbAdm (fzRho0 * fzRho0) aq as ay) (x : FzUT) :
    enc (as x) = cfP (enc (as fzE1)) (enc (as fzF1)) (enc x) :=
  cfP_of_comm as (fun y => A.s_r y) x

theorem hy_of (A : FzbAdm (fzRho0 * fzRho0) aq as ay) (x : FzUT) :
    enc (ay x) = yfP (enc (ay fzE1)) (enc (ay fzF1)) (enc x) :=
  yfP_of_inv ay (fun y => A.y_r y) x

theorem cfP_comp (A : FzbAdm (fzRho0 * fzRho0) aq as ay) :
    (∀ x, enc ((aq * aq) x) = cfP (enc ((aq * aq) fzE1)) (enc ((aq * aq) fzF1)) (enc x)) := by
  apply cfP_of_comm
  intro y
  change aq (aq (fzRho0 (fzRho0 y))) = fzRho0 (fzRho0 (aq (aq y)))
  have hq' : ∀ x, aq (fzRho0 (fzRho0 x)) = fzRho0 (fzRho0 (aq x)) := A.q_r
  rw [hq', hq']

theorem qOK_of_adm (A : FzbAdm (fzRho0 * fzRho0) aq as ay) :
    qOK (enc (aq fzE1)) (enc (aq fzF1)) = true := by
  have hq := hq_of A
  have h2 := cfP_comp A
  have hu : cfP (enc (aq fzE1)) (enc (aq fzF1)) (enc (aq fzE1)) = enc ((aq * aq) fzE1) :=
    (hq _).symm
  have hv : cfP (enc (aq fzE1)) (enc (aq fzF1)) (enc (aq fzF1)) = enc ((aq * aq) fzF1) :=
    (hq _).symm
  simp only [qOK, andB_true, Nat.beq_eq]
  refine ⟨?_, ?_, ?_⟩
  · rw [hu, hv, ← h2]
    change enc (aq (aq (aq (aq fzE1)))) = 1
    rw [A.q4, enc_e1]
  · rw [hu, hv, ← h2]
    change enc (aq (aq (aq (aq fzF1)))) = 4
    rw [A.q4, enc_f1]
  · rw [← card_eq_cntB (fun x => aq (aq x))
      (fun n => cfP (enc (aq fzE1)) (enc (aq fzF1)) (cfP (enc (aq fzE1)) (enc (aq fzF1)) n))
      (fun x => by rw [hq (aq x), hq x]), A.q_fix]

theorem enc_e1Z : ∀ x : FzUT, FzInZ (x * fzE1⁻¹) →
    enc x = Nat.add 1 (Nat.mul 16 (enc x / 16)) ∧ enc x / 16 < 4 := by
  unfold FzInZ
  decide +kernel

theorem enc_f1Z : ∀ x : FzUT, FzInZ (x * fzF1⁻¹) →
    enc x = Nat.add 4 (Nat.mul 16 (enc x / 16)) ∧ enc x / 16 < 4 := by
  unfold FzInZ
  decide +kernel

theorem enc_eq_iff {x y : FzUT} : enc x = enc y ↔ x = y := enc_injective.eq_iff

theorem sOK_of_adm (A : FzbAdm (fzRho0 * fzRho0) aq as ay) :
    sOK (enc (aq fzE1)) (enc (aq fzF1)) (enc (as fzE1)) (enc (as fzF1)) = true := by
  have hq : ∀ x, cfP (enc (aq fzE1)) (enc (aq fzF1)) (enc x) = enc (aq x) :=
    fun x => (hq_of A x).symm
  have hs : ∀ x, cfP (enc (as fzE1)) (enc (as fzF1)) (enc x) = enc (as x) :=
    fun x => (hs_of A x).symm
  simp only [sOK, it3, andB_true, orB_true, Nat.beq_eq, allB_iff, impB_true]
  refine ⟨?_, ?_, ?_⟩
  · rw [← enc_e1, ← enc_f1]
    simp only [hq, hs, enc_eq_iff]
    obtain ⟨k, hk⟩ := A.s_sq
    fin_cases k
    · left
      exact ⟨hk fzE1, hk fzF1⟩
    · right; left
      simp only [hk]
      simp
    · right; right; left
      simp only [hk]
      simp [pow_two]
    · right; right; right
      simp only [hk]
      simp [pow_succ, pow_two]
  · rw [← enc_e1, ← enc_f1]
    simp only [hq, hs, enc_eq_iff]
    rcases A.s_q with h | h
    · exact Or.inl ⟨h fzE1, h fzF1⟩
    · exact Or.inr ⟨h fzE1, h fzF1⟩
  · intro x hx e
    rw [← enc_dec_lt hx] at e ⊢
    rw [hq, hq, enc_eq_iff] at e
    rw [hs, pmulP_eq, A.s_inv _ e, enc_one]

theorem sZ_codes (A : FzbAdm (fzRho0 * fzRho0) aq as ay) :
    (enc (as fzE1) = Nat.add 1 (Nat.mul 16 (enc (as fzE1) / 16)) ∧ enc (as fzE1) / 16 < 4) ∧
      (enc (as fzF1) = Nat.add 4 (Nat.mul 16 (enc (as fzF1) / 16)) ∧ enc (as fzF1) / 16 < 4) :=
  ⟨enc_e1Z _ (A.s_Z fzE1), enc_f1Z _ (A.s_Z fzF1)⟩

theorem yOK_of_adm (A : FzbAdm (fzRho0 * fzRho0) aq as ay) (hq1 : enc (aq fzE1) = 4)
    (hq4 : enc (aq fzF1) = 17) :
    yOK (enc (as fzE1)) (enc (as fzF1)) (enc (ay fzE1)) (enc (ay fzF1)) = true := by
  have hq : ∀ x, cfP 4 17 (enc x) = enc (aq x) := fun x => by rw [hq_of A x, hq1, hq4]
  have hs : ∀ x, cfP (enc (as fzE1)) (enc (as fzF1)) (enc x) = enc (as x) :=
    fun x => (hs_of A x).symm
  have hy : ∀ x, yfP (enc (ay fzE1)) (enc (ay fzF1)) (enc x) = enc (ay x) :=
    fun x => (hy_of A x).symm
  have t := hy (aq fzF1)
  rw [hq4] at t
  simp only [yOK, andB_true, Nat.beq_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hy (ay fzE1), A.y_sq, enc_e1]
  · rw [hy (ay fzF1), A.y_sq, enc_f1]
  · rw [t, A.y_q, ← hq (ay fzF1)]
  · rw [hy (as fzE1), hs (ay fzE1), A.y_s]
  · rw [hy (as fzF1), hs (ay fzF1), A.y_s]

end CFSG.KC.FzUT
