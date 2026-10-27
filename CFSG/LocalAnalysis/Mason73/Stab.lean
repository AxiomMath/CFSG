module

public import CFSG.LocalAnalysis.Mason73.Rank

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.GH74.GLS.Stage1.Thm3.Sec8 Equiv Subgroup

variable {n : ℕ}

theorem patFix_one (χ : Fin 4 → ℕ) : PatFix 1 χ := fun i j => by
  simp only [inv_one, Perm.one_apply]
  omega

theorem patFix_mul {π σ : Perm (Fin 4)} {χ : Fin 4 → ℕ} (hπ : PatFix π χ) (hσ : PatFix σ χ) :
    PatFix (π * σ) χ := by
  intro i j
  have h1 := hσ (π⁻¹ i) (π⁻¹ j)
  have h2 := hπ i j
  rw [mul_inv_rev, Perm.mul_apply, Perm.mul_apply]
  omega

theorem patFix_inv {π : Perm (Fin 4)} {χ : Fin 4 → ℕ} (hπ : PatFix π χ) : PatFix π⁻¹ χ := by
  intro i j
  have h := hπ (π i) (π j)
  rw [show π⁻¹ (π i) = i by simp, show π⁻¹ (π j) = j by simp] at h
  rw [inv_inv]
  omega

@[expose] def stabP (p : Fin 2 × Fin 2 × Fin 2) : Subgroup Fin81.R0 where
  carrier := {π | PatFix (π : Perm (Fin 4)) (pat p)}
  mul_mem' ha hb := patFix_mul ha hb
  one_mem' := patFix_one _
  inv_mem' ha := patFix_inv ha

instance (p : Fin 2 × Fin 2 × Fin 2) : DecidablePred (· ∈ stabP p) := fun π =>
  inferInstanceAs (Decidable (PatFix (π : Perm (Fin 4)) (pat p)))

theorem mem_stabP {p : Fin 2 × Fin 2 × Fin 2} {π : Fin81.R0} :
    π ∈ stabP p ↔ PatFix (π : Perm (Fin 4)) (pat p) := Iff.rfl

theorem comm_omegaEl_iff (hn : 3 ≤ n) {s : L4Model n} {p : Fin 2 × Fin 2 × Fin 2} :
    s * omegaEl hn p = omegaEl hn p * s ↔ PatFix (piT s : Perm (Fin 4)) (pat p) := by
  refine ⟨patFix_of_comm hn, fun hp => ?_⟩
  obtain ⟨d, π, hd, rfl⟩ := exists_eq_el s
  rw [piT_el] at hp
  have hc : IsConst (pv (π : Perm (Fin 4)) (hv n (pat p)) - hv n (pat p)) := by
    rw [pv_hv, hv_sub_hv_isConst_iff (by omega)]
    exact hp
  unfold omegaEl
  split_ifs with hpar
  · exact (el_comm_diag_iff (by omega) hd _).2 hc
  · refine (el_comm_diag_iff (by omega) hd _).2 ?_
    have : pv (π : Perm (Fin 4)) (wv n (pat p)) - wv n (pat p) =
        pv (π : Perm (Fin 4)) (hv n (pat p)) - hv n (pat p) := by
      funext i
      simp only [Pi.sub_apply, pv, wv]
      ring
    rw [this]
    exact hc

theorem centralizer_omegaEl (hn : 3 ≤ n) (p : Fin 2 × Fin 2 × Fin 2) :
    centralizer {omegaEl hn p} = (stabP p).comap piT := by
  ext s
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_comap, comm_omegaEl_iff hn]
  rfl

theorem card_centralizer_omegaEl (hn : 3 ≤ n) (p : Fin 2 × Fin 2 × Fin 2) :
    Nat.card (centralizer {omegaEl hn p}) = 2 ^ (3 * n - 2) * Nat.card (stabP p) := by
  rw [centralizer_omegaEl hn, card_comap_of_surjective' piT_surjective]
  change Nat.card (A n) * _ = _
  rw [card_A (by omega)]

theorem card_stabP_of_odd (p : Fin 2 × Fin 2 × Fin 2)
    (hp : (pat p 0 + pat p 1 + pat p 2 + pat p 3) % 2 = 1) : Nat.card (stabP p) = 2 := by
  rw [Nat.card_eq_fintype_card]
  revert hp
  revert p
  decide

end CFSG.LocalAnalysis.Mason73
