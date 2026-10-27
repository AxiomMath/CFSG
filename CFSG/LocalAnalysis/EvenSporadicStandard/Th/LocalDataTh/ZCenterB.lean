module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.ZCenterA

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd.LocalDataTh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3
open scoped Matrix commutatorElement

section Z


theorem uVec_indep3 {a b c : ZMod 2} (h : a • uVec 0 + b • uVec 1 + c • uVec 2 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have := ptFacts.2.2.2.2.2.2.2.2.2.2 ![a, b, c] (by
    rw [Fin.sum_univ_three]
    simpa [uVec] using h)
  exact ⟨by simpa using congrFun this 0, by simpa using congrFun this 1,
    by simpa using congrFun this 2⟩

theorem rho_coords {σ : J} (hσ : σ ∈ S) (k : Fin 3) :
    ∃ e : Vec4, cA e = σ * nf 0 (uVec k) * σ⁻¹ ∧
      rho σ *ᵥ uVec k = e 1 • uVec 0 + e 2 • uVec 1 + e 3 • uVec 2 := by
  obtain ⟨e, he⟩ := exists_cA (conj_mem_A_of_mem_S hσ (nf_zero_uVec_mem k))
  refine ⟨e, he, ?_⟩
  obtain ⟨t, ht⟩ := conj_nf hσ.1 0 (uVec k)
  obtain ⟨s', hs'⟩ := cA_eq_nf e
  rw [he, ht] at hs'
  exact congrArg Prod.snd (nf_injective (a₁ := (t, rho σ *ᵥ uVec k)) (a₂ := (s', _)) hs')

theorem lam_invariant (hZ : HZFacts) {s : J} (hKt : s ∈ Kt) (hSB : ∀ x ∈ S, ⁅s, x⁆ ∈ B)
    (lam : Fin 3 → ZMod 2) (hlam : ∀ j, ⁅s, nf 0 (uVec j)⁆ = z ^ (lam j).val) :
    lam = 0 ∨ lam = psi0 := by
  refine hZ.2.1 lam ?_
  intro a ha P hP k
  obtain ⟨σ, hσS, hσ⟩ := mem_Pt_iff_exists_S.1 (mem_Pt_iff.2 ⟨a, ha, rfl⟩)
  obtain ⟨e, he, hrho⟩ := rho_coords hσS k
  have h1 : rho σ *ᵥ uVec k = ∑ i, P i k • uVec i := by rw [hσ]; exact hP k
  rw [Fin.sum_univ_three] at h1
  have hXY : (P 0 k • uVec 0 + P 1 k • uVec 1 + P 2 k • uVec 2) =
      e 1 • uVec 0 + e 2 • uVec 1 + e 3 • uVec 2 := h1.symm.trans hrho
  have h2 : (P 0 k + e 1) • uVec 0 + (P 1 k + e 2) • uVec 1 + (P 2 k + e 3) • uVec 2 = 0 := by
    have : (P 0 k + e 1) • uVec 0 + (P 1 k + e 2) • uVec 1 + (P 2 k + e 3) • uVec 2 =
        (P 0 k • uVec 0 + P 1 k • uVec 1 + P 2 k • uVec 2) +
          (e 1 • uVec 0 + e 2 • uVec 1 + e 3 • uVec 2) := by
      simp only [add_smul]
      abel
    rw [this, ← hXY, vec_add_self]
  obtain ⟨h3, h4, h5⟩ := uVec_indep3 h2
  have hc : ∀ a b : ZMod 2, a + b = 0 → b = a := by decide
  have e1 := hc _ _ h3
  have e2 := hc _ _ h4
  have e3 := hc _ _ h5
  have hc1 : ⁅s, cA e⁆ = z ^ (e 1 * lam 0 + e 2 * lam 1 + e 3 * lam 2).val :=
    comm_cA hKt lam hlam e
  have hc2 : ⁅s, cA e⁆ = z ^ (lam k).val := by
    have := comm_conj_A hKt hSB (S.inv_mem hσS) (nf_zero_uVec_mem k)
    rw [inv_inv] at this
    rw [he, this]
    exact hlam k
  have hlk := zpow_val_inj (hc1.symm.trans hc2)
  rw [Fin.sum_univ_three, ← e1, ← e2, ← e3]
  exact hlk

theorem center_mod_B (hZ : HZFacts) {s : J} (hs : s ∈ S) (hSB : ∀ x ∈ S, ⁅s, x⁆ ∈ B) :
    s ∈ B ∨ (nf 0 vZ)⁻¹ * s ∈ B := by
  have hfix := rho_fix_of_comm_B hZ hs hSB
  have hKt : s ∈ Kt := ⟨hs.1, hfix⟩
  have hlam' : ∀ j : Fin 3, ∃ b : ZMod 2, z ^ b.val = ⁅s, nf 0 (uVec j)⁆ := fun j =>
    (CFSG.Certificates.ExtraspecialNF.mem_zpowers_iff_exists symplectic_rel).1
      (comm_mem_zpowers_of_fix hs.1 (hfix j))
  choose lam hlam using hlam'
  have hlam2 : ∀ j, ⁅s, nf 0 (uVec j)⁆ = z ^ (lam j).val := fun j => (hlam j).symm
  rcases lam_invariant hZ hKt hSB lam hlam2 with h0 | h0
  · left
    refine mem_B_of_comm hKt (fun j => ?_)
    have : ⁅s, nf 0 (uVec j)⁆ = 1 := by rw [hlam2 j, h0]; simp
    exact comm_eq_one_iff.1 this
  · right
    have hc : nf 0 vZ ∈ Kt := Q_le_Kt (nf_mem_Q 0 vZ)
    have hcz : ∀ j : Fin 3, ⁅nf 0 vZ, nf 0 (uVec j)⁆ = z ^ (psi0 j).val := fun j => by
      rw [comm_nf_nf, hZ.2.2.1 j]
    rw [h0] at hlam2
    let cK : ↥Kt := ⟨nf 0 vZ, hc⟩
    let sK : ↥Kt := ⟨s, hKt⟩
    have hθ : theta (cK⁻¹ * sK) = 1 := by
      rw [map_mul, map_inv]
      funext j
      apply Subtype.ext
      simp only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply, Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.coe_one]
      rw [theta_apply, theta_apply]
      show (⁅nf 0 vZ, nf 0 (uVec j)⁆)⁻¹ * ⁅s, nf 0 (uVec j)⁆ = 1
      rw [hcz j, hlam2 j, inv_mul_cancel]
    have hker : cK⁻¹ * sK ∈ theta.ker := hθ
    rw [ker_theta, Subgroup.mem_subgroupOf] at hker
    simpa [cK, sK] using hker

end Z

end CFSG.EvenSporadicStandard.ThStd.LocalDataTh
