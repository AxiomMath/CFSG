module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC16F

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] noncomputable def c16Beta (z u fz fu q : G) : C16H0 :=
  (c16cK z u ⁅q, fz⁆, c16cK z u ⁅q, fu⁆)

variable {K Y Q : Subgroup G} {t rho z u fz fu : G}

private lemma c16_conj_eq_of_comm {q k : G} (h : q * k = k * q) : q * k * q⁻¹ = k := by
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

theorem c16_comm_mul (H : C16Ab K Y Q t rho z u fz fu) {q q' f : G} (hq : q ∈ Q) (hq' : q' ∈ Q)
    (hf : f ∈ Y) : ⁅q * q', f⁆ = ⁅q', f⁆ * ⁅q, f⁆ := by
  have hk : ⁅q', f⁆ ∈ K := H.Q_comm_Y q' hq' f hf
  have hcomm : q * ⁅q', f⁆ = ⁅q', f⁆ * q := H.Q_cent_K q hq ⁅q', f⁆ hk
  rw [commutatorElement_mul_left_eq_conj_mul, c16_conj_eq_of_comm hcomm]

theorem c16_comm_mul_right (H : C16Ab K Y Q t rho z u fz fu) {q f f' : G} (hq : q ∈ Q)
    (hf : f ∈ Y) (hf' : f' ∈ Y) : ⁅q, f * f'⁆ = ⁅q, f⁆ * ⁅q, f'⁆ := by
  have hk : ⁅q, f'⁆ ∈ K := H.Q_comm_Y q hq f' hf'
  have hkY : ⁅q, f'⁆ ∈ Y := H.K_le_Y hk
  have hcomm : f * ⁅q, f'⁆ = ⁅q, f'⁆ * f := H.Y_comm f hf ⁅q, f'⁆ hkY
  rw [commutatorElement_mul_right_eq_mul_conj, mul_assoc ⁅q, f⁆ f ⁅q, f'⁆, hcomm]
  simp only [mul_assoc, mul_inv_cancel, mul_one]

theorem c16_beta_add (H : C16Ab K Y Q t rho z u fz fu) {q q' : G} (hq : q ∈ Q) (hq' : q' ∈ Q) :
    c16Beta z u fz fu (q * q') = c16Beta z u fz fu q + c16Beta z u fz fu q' := by
  have h1 := c16_comm_mul H hq hq' H.fz_mem
  have h2 := c16_comm_mul H hq hq' H.fu_mem
  have hk1 : ⁅q', fz⁆ ∈ K := H.Q_comm_Y q' hq' fz H.fz_mem
  have hk2 : ⁅q, fz⁆ ∈ K := H.Q_comm_Y q hq fz H.fz_mem
  have hk1' : ⁅q', fu⁆ ∈ K := H.Q_comm_Y q' hq' fu H.fu_mem
  have hk2' : ⁅q, fu⁆ ∈ K := H.Q_comm_Y q hq fu H.fu_mem
  apply Prod.ext
  · show c16cK z u ⁅q * q', fz⁆ = c16cK z u ⁅q, fz⁆ + c16cK z u ⁅q', fz⁆
    rw [h1, c16cK_mul H.kb hk1 hk2, add_comm]
  · show c16cK z u ⁅q * q', fu⁆ = c16cK z u ⁅q, fu⁆ + c16cK z u ⁅q', fu⁆
    rw [h2, c16cK_mul H.kb hk1' hk2', add_comm]

theorem c16_beta_one (z u fz fu : G) : c16Beta z u fz fu 1 = 0 := by
  show (c16cK z u ⁅(1 : G), fz⁆, c16cK z u ⁅(1 : G), fu⁆) = 0
  simp [c16cK_one]

theorem c16_beta_inv (H : C16Ab K Y Q t rho z u fz fu) {q : G} (hq : q ∈ Q) :
    c16Beta z u fz fu q⁻¹ = c16Beta z u fz fu q := by
  have hqinv : q⁻¹ ∈ Q := Q.inv_mem hq
  have hsum : c16Beta z u fz fu q + c16Beta z u fz fu q⁻¹ = 0 := by
    rw [← c16_beta_add H hq hqinv, mul_inv_cancel, c16_beta_one]
  have hself : c16Beta z u fz fu q + c16Beta z u fz fu q = 0 := c16_add_self _
  apply add_left_cancel (a := c16Beta z u fz fu q)
  rw [hsum, hself]

theorem c16_beta_eq_zero_iff (H : C16Ab K Y Q t rho z u fz fu) {q : G} (hq : q ∈ Q) :
    c16Beta z u fz fu q = 0 ↔ ∀ f ∈ Y, q * f = f * q := by
  constructor
  · intro hbeta f hf
    have h1 : c16cK z u ⁅q, fz⁆ = 0 := by
      simpa [c16Beta] using congrArg Prod.fst hbeta
    have h2 : c16cK z u ⁅q, fu⁆ = 0 := by
      simpa [c16Beta] using congrArg Prod.snd hbeta
    have hkz : ⁅q, fz⁆ ∈ K := H.Q_comm_Y q hq fz H.fz_mem
    have hku : ⁅q, fu⁆ ∈ K := H.Q_comm_Y q hq fu H.fu_mem
    have hzf : q * fz = fz * q :=
      commutatorElement_eq_one_iff_mul_comm.mp ((c16cK_eq_zero H.kb hkz).mp h1)
    have huf : q * fu = fu * q :=
      commutatorElement_eq_one_iff_mul_comm.mp ((c16cK_eq_zero H.kb hku).mp h2)
    have hqκ : ∀ κ ∈ K, Commute q κ :=
      fun κ hκ => (commute_iff_eq q κ).mpr (H.Q_cent_K q hq κ hκ)
    have hqz : Commute q fz := (commute_iff_eq q fz).mpr hzf
    have hqu : Commute q fu := (commute_iff_eq q fu).mpr huf
    rcases c16_Y_cases H hf with ⟨κ, hκ, hf' | hf' | hf' | hf'⟩
    · rw [hf']; exact (hqκ κ hκ).eq
    · rw [hf']; exact ((hqκ κ hκ).mul_right hqz).eq
    · rw [hf']; exact ((hqκ κ hκ).mul_right hqu).eq
    · rw [hf']; exact ((hqκ κ hκ).mul_right (hqz.mul_right hqu)).eq
  · intro hcomm
    have hzf : q * fz = fz * q := hcomm fz H.fz_mem
    have huf : q * fu = fu * q := hcomm fu H.fu_mem
    have h1 : ⁅q, fz⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hzf
    have h2 : ⁅q, fu⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr huf
    simp [c16Beta, h1, h2, c16cK_one]

theorem c16_beta_t (H : C16Ab K Y Q t rho z u fz fu) : c16Beta z u fz fu t = c16T0 := by
  have hzt : ⁅t, fz⁆ = z := by
    rw [← commutatorElement_inv, H.fz_t]
    exact inv_eq_of_mul_eq_one_right H.kb.z_sq
  have hut : ⁅t, fu⁆ = u := by
    rw [← commutatorElement_inv, H.fu_t]
    exact inv_eq_of_mul_eq_one_right H.kb.u_sq
  show (c16cK z u ⁅t, fz⁆, c16cK z u ⁅t, fu⁆) = c16T0
  rw [hzt, hut, c16cK_z H.kb, c16cK_u H.kb]
  rfl

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
