module

public import CFSG.Certificates.Kernel.DceSPPerm
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Certificates.DSP

open CFSG.KC.HNA.DceS CFSG.Certificates.DceLoop

abbrev Pt : Type := Finset (Fin 55)

@[expose] def fP (i : ℕ) : Fin 55 := ⟨i % 55, Nat.mod_lt _ (by norm_num)⟩

@[expose] noncomputable def ptS (P : ℕ) : Pt := {fP (p0 P), fP (p1 P)}

@[expose] noncomputable def actP (p : Pt) (y : Equiv.Perm (Fin 55)) : Pt := p.image (y⁻¹ : Equiv.Perm (Fin 55))

theorem actP_one (p : Pt) : actP p 1 = p := by
  unfold actP
  rw [inv_one]
  exact Finset.image_id

theorem actP_mul (p : Pt) (a b : Equiv.Perm (Fin 55)) : actP (actP p a) b = actP p (a * b) := by
  unfold actP
  rw [Finset.image_image, mul_inv_rev]
  rfl

theorem p0_eq (P : ℕ) : p0 P = P % 64 := by
  unfold p0
  change P &&& (2 ^ 6 - 1) = _
  rw [land_low]
  rfl

theorem p1_eq (P : ℕ) : p1 P = P / 64 := by
  unfold p1
  change P >>> 6 = _
  rw [Nat.shiftRight_eq_div_pow]

theorem canonP_spec {P : ℕ} (h : canonP P = true) : P < 4096 ∧ p0 P < p1 P ∧ p1 P < 55 := by
  unfold canonP at h
  obtain ⟨h1, h⟩ := andL_iff.1 h
  obtain ⟨h2, h3⟩ := andL_iff.1 h
  exact ⟨Nat.blt_eq.mp h1, Nat.blt_eq.mp h2, Nat.blt_eq.mp h3⟩

theorem lor_six {a b : ℕ} (ha : a < 64) : Nat.lor a (Nat.shiftLeft b 6) = a + 64 * b := by
  change a ||| b <<< 6 = _
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (show a < 2 ^ 6 from ha), Nat.shiftLeft_eq]
  ring

theorem p01_mk {a b : ℕ} (ha : a < 64) : p0 (a + 64 * b) = a ∧ p1 (a + 64 * b) = b := by
  rw [p0_eq, p1_eq]
  refine ⟨?_, ?_⟩
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  · rw [Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt ha, Nat.zero_add]

theorem fP_val {i : ℕ} (h : i < 55) : (fP i : ℕ) = i := Nat.mod_eq_of_lt h

theorem pm_fP {M i : ℕ} (hM : PV M) (hi : i < 55) : pm M (fP i) = fP (fld M i) := by
  apply Fin.ext
  rw [pm_val hM, fP_val (hM.2.1 i hi), fP_val hi]

theorem actOK_sound {P M Q : ℕ} (hok : actOK P M Q = true) (hP : canonP P = true)
    (hQ : canonP Q = true) (hM : PV M) : actP (ptS P) (mP M) = ptS Q := by
  obtain ⟨-, hP01, hP1⟩ := canonP_spec hP
  unfold actP ptS mP
  rw [inv_inv, Finset.image_insert, Finset.image_singleton, pm_fP hM (by omega), pm_fP hM hP1]
  unfold actOK at hok
  beta_reduce at hok
  have hx := fld_lt M (p0 P)
  have hy := fld_lt M (p1 P)
  have e := Nat.eq_of_beq_eq_true hok
  cases hxy : Nat.blt (fld M (p0 P)) (fld M (p1 P))
  · rw [hxy] at e
    dsimp only at e
    rw [lor_six hy] at e
    obtain ⟨e0, e1⟩ := p01_mk (b := fld M (p0 P)) hy
    rw [e, e0, e1]
    exact Finset.pair_comm _ _
  · rw [hxy] at e
    dsimp only at e
    rw [lor_six hx] at e
    obtain ⟨e0, e1⟩ := p01_mk (b := fld M (p1 P)) hx
    rw [e, e0, e1]

theorem p01_eq (P : ℕ) : P = p0 P + 64 * p1 P := by
  rw [p0_eq, p1_eq]
  omega

theorem ptS_inj {P Q : ℕ} (hP : canonP P = true) (hQ : canonP Q = true) (h : ptS P = ptS Q) :
    P = Q := by
  obtain ⟨-, aP, bP⟩ := canonP_spec hP
  obtain ⟨-, aQ, bQ⟩ := canonP_spec hQ
  have h' : ((ptS P : Finset (Fin 55)) : Set (Fin 55)) = ((ptS Q : Finset (Fin 55)) : Set (Fin 55)) := by
    rw [h]
  unfold ptS at h'
  rw [Finset.coe_pair, Finset.coe_pair] at h'
  have v : ∀ {a b : ℕ}, a < 55 → b < 55 → fP a = fP b → a = b := fun ha hb e => by
    have := congrArg Fin.val e
    rwa [fP_val ha, fP_val hb] at this
  rcases Set.pair_eq_pair_iff.1 h' with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [p01_eq P, p01_eq Q, v (by omega) (by omega) e1, v bP bQ e2]
  · have := v (by omega) bQ e1
    have := v bP (by omega) e2
    omega

end CFSG.Certificates.DSP

end
