module

public import CFSG.ClassicalGroups.Unitary.Form

public section

namespace CFSG.ClassicalGroups.Unitary

open Matrix CFSG.LieType.Universal.Unitary

variable {K : Type*} [Field K]

structure WittData (σ : K ≃+* K) where
  u : K
  ω : K
  hu : σ u * u = -1
  hω : σ ω * ω = 1
  hω1 : ω ≠ 1

variable {σ : K ≃+* K}

theorem IsUnitaryInvolution.nonempty_wittData (hσ : IsUnitaryInvolution σ) :
    Nonempty (WittData σ) := by
  obtain ⟨u, hu⟩ := hσ.exists_norm_neg_one
  obtain ⟨ω, hω, hω1⟩ := hσ.exists_norm_one_ne_one
  exact ⟨⟨u, ω, hu, hω, hω1⟩⟩

namespace WittData

variable (W : WittData σ) {m : ℕ}

theorem u_ne_zero : W.u ≠ 0 := by
  intro h
  have := W.hu
  rw [h, mul_zero] at this
  exact one_ne_zero (neg_eq_zero.mp this.symm)

theorem σu_ne_zero : σ W.u ≠ 0 := (map_ne_zero σ).mpr W.u_ne_zero

theorem one_sub_ω_ne_zero : 1 - W.ω ≠ 0 := sub_ne_zero.mpr (Ne.symm W.hω1)

theorem σω_ne_one : σ W.ω ≠ 1 := by
  intro h
  apply W.hω1
  apply σ.injective
  rw [h, map_one]

@[expose] def hypA (m : ℕ) : Fin (m + 2) → K := Pi.single 0 1 + Pi.single 1 W.u

@[expose] noncomputable def hypB (m : ℕ) : Fin (m + 2) → K :=
  (1 - W.ω)⁻¹ • (Pi.single 0 1 + Pi.single 1 (W.u * W.ω))

theorem herm_hypA_left (y : Fin (m + 2) → K) : herm σ (W.hypA m) y = y 0 + σ W.u * y 1 := by
  rw [hypA, herm_add_left, herm_single_left, herm_single_left, map_one, one_mul]

theorem herm_hypB_left (y : Fin (m + 2) → K) :
    herm σ (W.hypB m) y = σ (1 - W.ω)⁻¹ * (y 0 + σ (W.u * W.ω) * y 1) := by
  rw [hypB, herm_smul_left, herm_add_left, herm_single_left, herm_single_left, map_one, one_mul,
    map_inv₀]

@[simp] theorem hypA_zero : W.hypA m 0 = 1 := by simp [hypA]
@[simp] theorem hypA_one : W.hypA m 1 = W.u := by simp [hypA]
@[simp] theorem hypB_zero : W.hypB m 0 = (1 - W.ω)⁻¹ := by simp [hypB]
@[simp] theorem hypB_one : W.hypB m 1 = (1 - W.ω)⁻¹ * (W.u * W.ω) := by simp [hypB]

theorem succ_succ_ne_one (i : Fin m) : (i.succ.succ : Fin (m + 2)) ≠ 1 := by
  intro h
  rw [← Fin.succ_zero_eq_one] at h
  exact Fin.succ_ne_zero i (Fin.succ_injective _ h)

theorem hypA_succ_succ (i : Fin m) : W.hypA m i.succ.succ = 0 := by
  simp [hypA, Fin.succ_ne_zero, succ_succ_ne_one]

theorem hypB_succ_succ (i : Fin m) : W.hypB m i.succ.succ = 0 := by
  simp [hypB, Fin.succ_ne_zero, succ_succ_ne_one]

theorem herm_hypA_hypA : herm σ (W.hypA m) (W.hypA m) = 0 := by
  rw [herm_hypA_left, hypA_zero, hypA_one, W.hu]
  ring

theorem herm_hypB_hypB : herm σ (W.hypB m) (W.hypB m) = 0 := by
  rw [herm_hypB_left, hypB_zero, hypB_one, map_mul]
  have : σ W.u * σ W.ω * ((1 - W.ω)⁻¹ * (W.u * W.ω)) =
      (σ W.u * W.u) * (σ W.ω * W.ω) * (1 - W.ω)⁻¹ := by ring
  rw [this, W.hu, W.hω]
  ring

theorem herm_hypA_hypB : herm σ (W.hypA m) (W.hypB m) = 1 := by
  rw [herm_hypA_left, hypB_zero, hypB_one]
  have : (1 - W.ω)⁻¹ + σ W.u * ((1 - W.ω)⁻¹ * (W.u * W.ω)) =
      (1 + (σ W.u * W.u) * W.ω) * (1 - W.ω)⁻¹ := by ring
  rw [this, W.hu, show 1 + -1 * W.ω = 1 - W.ω by ring, mul_inv_cancel₀ W.one_sub_ω_ne_zero]

theorem herm_hypB_hypA (hσ : ∀ c, σ (σ c) = c) : herm σ (W.hypB m) (W.hypA m) = 1 := by
  rw [herm_conj σ hσ, W.herm_hypA_hypB, map_one]

theorem hypA_ne_zero : W.hypA m ≠ 0 := by
  intro h
  have := congrFun h 0
  rw [hypA_zero] at this
  exact one_ne_zero this

theorem coord_eq_zero_of_perp {y : Fin (m + 2) → K} (ha : herm σ (W.hypA m) y = 0)
    (hb : herm σ (W.hypB m) y = 0) : y 0 = 0 ∧ y 1 = 0 := by
  rw [herm_hypA_left] at ha
  rw [herm_hypB_left] at hb
  have hs : σ (1 - W.ω)⁻¹ ≠ 0 := (map_ne_zero σ).mpr (inv_ne_zero W.one_sub_ω_ne_zero)
  have hb' : y 0 + σ (W.u * W.ω) * y 1 = 0 := (mul_eq_zero.mp hb).resolve_left hs
  rw [map_mul] at hb'
  have h1 : σ W.u * (1 - σ W.ω) * y 1 = 0 := by linear_combination ha - hb'
  have h2 : σ W.u * (1 - σ W.ω) ≠ 0 :=
    mul_ne_zero W.σu_ne_zero (sub_ne_zero.mpr (Ne.symm W.σω_ne_one))
  have hy1 : y 1 = 0 := (mul_eq_zero.mp h1).resolve_left h2
  refine ⟨?_, hy1⟩
  rw [hy1, mul_zero, add_zero] at ha
  exact ha

theorem single_one_eq :
    (Pi.single 1 1 : Fin (m + 2) → K) =
      (W.u * (1 - W.ω))⁻¹ • (W.hypA m - (1 - W.ω) • W.hypB m) := by
  have h1 : W.hypA m - (1 - W.ω) • W.hypB m =
      (W.u * (1 - W.ω)) • (Pi.single 1 1 : Fin (m + 2) → K) := by
    rw [hypA, hypB, smul_smul, mul_inv_cancel₀ W.one_sub_ω_ne_zero, one_smul]
    funext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs <;> ring
  rw [h1, smul_smul, inv_mul_cancel₀ (mul_ne_zero W.u_ne_zero W.one_sub_ω_ne_zero), one_smul]

theorem single_zero_eq :
    (Pi.single 0 1 : Fin (m + 2) → K) = W.hypA m - W.u • (Pi.single 1 1 : Fin (m + 2) → K) := by
  rw [hypA, ← Pi.single_smul, smul_eq_mul, mul_one, add_sub_cancel_right]

theorem fix_singles_of_fix {n : ℕ} {g : SUid σ (n + 2)} (ha : g • W.hypA n = W.hypA n)
    (hb : g • W.hypB n = W.hypB n) :
    g • (Pi.single 1 1 : Fin (n + 2) → K) = Pi.single 1 1 ∧
      g • (Pi.single 0 1 : Fin (n + 2) → K) = Pi.single 0 1 := by
  have h1 : g • (Pi.single 1 1 : Fin (n + 2) → K) = Pi.single 1 1 := by
    rw [W.single_one_eq, smul_comm, smul_sub, smul_comm, ha, hb]
  refine ⟨h1, ?_⟩
  rw [W.single_zero_eq, smul_sub, smul_comm, ha, h1]

end WittData

theorem herm_single_add_single {n : ℕ} {i j : Fin n} (hij : i ≠ j) (t : K) :
    herm σ (Pi.single i 1 + Pi.single j t) (Pi.single i 1 + Pi.single j t) = 1 + σ t * t := by
  simp [herm_single_right, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij.symm]

end CFSG.ClassicalGroups.Unitary
