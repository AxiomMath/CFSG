module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.KappaLemmaAForm
import CFSG.LocalAnalysis.EvenBN.Tits.S56N7
import CFSG.LocalAnalysis.EvenBN.Tits.S56N4
public import CFSG.Yardstones.M41b0c98b3153.Definitions

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.KappaA

open Matrix Subgroup CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.EvenBN.Tits
  CFSG.LocalAnalysis.EvenBN.Tits.Model

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}

theorem ecoord_pv (hd : d.Hyp) (j : Fin 5) : ecoord d (d.pv (basisV j)) = Pi.single j 1 := by
  rw [← crdE_single j, ecoord_crdE hd]

theorem U10_coord (hd : d.Hyp) {u : G} (hu : u ∈ d.s56U10) :
    u ∈ d.E ∧ ecoord d u 3 = 0 ∧ ecoord d u 4 = 0 := by
  let S : Subgroup G :=
    { carrier := {u | u ∈ d.E ∧ ecoord d u 3 = 0 ∧ ecoord d u 4 = 0}
      one_mem' := ⟨one_mem _, by simp [ecoord_one hd], by simp [ecoord_one hd]⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        rw [ecoord_mul hd ha.1 hb.1]; simp [ha.2.1, hb.2.1], by
        rw [ecoord_mul hd ha.1 hb.1]; simp [ha.2.2, hb.2.2]⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [ecoord_inv hd ha.1]; exact ha.2.1, by
        rw [ecoord_inv hd ha.1]; exact ha.2.2⟩ }
  have hmem : ∀ j : Fin 5, j ≠ 3 → j ≠ 4 → d.pv (basisV j) ∈ S := fun j h3 h4 => by
    refine ⟨?_, ?_, ?_⟩
    · rw [← crdE_single j]; exact crdE_mem hd _
    · rw [ecoord_pv hd]; simp [Ne.symm h3]
    · rw [ecoord_pv hd]; simp [Ne.symm h4]
  have h10 : d.s56U10 ≤ S := by
    rw [Data.s56U10_def, Data.s56U11_def]
    refine sup_le ((closure_le S).2 ?_) (zpowers_le.2 (hmem 2 (by decide) (by decide)))
    rintro _ (rfl | rfl)
    · exact hmem 1 (by decide) (by decide)
    · exact hmem 0 (by decide) (by decide)
  exact h10 hu

theorem pv9_mem_F (d : Data G) : d.pv 9 ∈ d.F :=
  Data.mem_liftSub.2 ⟨Model.parrottV 9, Model.parrottV_mem_parrottF (by simp),
    Model.parrottF_le_titsD (Model.parrottV_mem_parrottF (by simp)), rfl⟩

theorem z0_sq_eq_one (h49 : d.Thm49Statement) (hd : d.Hyp)
    (hz : d.S56Z0 z₀) : z₀ * z₀ = 1 := by
  by_contra hne
  have hs1 : zc (z₀ * z₀) = 1 := by
    rcases hd.s56_Z0_sq_cases hz with h | h
    · exact absurd h hne
    · rw [h]; exact zc_z hd
  obtain ⟨μ, hμ⟩ := exists_mu h49 hd hz
  rw [hs1] at hμ
  obtain ⟨x, hx, hxa⟩ := eb_surj h49 hd hz ![0, 0, 1, 0]
  have hεE := hd.s56_V_eps_mem_E hx
  have hεF : d.s56Eps x ∈ d.F := by
    have hc1 := congrFun hxa 0
    have hc2 := congrFun hxa 1
    have hc3 := congrFun hxa 2
    have hc4 := congrFun hxa 3
    simp only [eb, wcoord, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hc1 hc2 hc3 hc4
    have hcrd := crdE_ecoord hd hεE
    rw [← hcrd]
    have e1 : ecoord d (d.s56Eps x) 1 = 0 := hc1
    have e2 : ecoord d (d.s56Eps x) 2 = 0 := hc2
    have e3 : ecoord d (d.s56Eps x) 3 = 1 := hc3
    have e4 : ecoord d (d.s56Eps x) 4 = 0 := hc4
    unfold crdE
    rw [e1, e2, e3, e4, Data.s56_pv12]
    simp only [ZMod.val_zero, ZMod.val_one, pow_zero, pow_one, mul_one]
    exact mul_mem (pow_mem hd.s56_z_mem_F _) (pv9_mem_F d)
  have hxQ0 : x ∈ d.s56Q0 := hd.s56_Q_le_Q0 hx.1
  have hxN : x ∈ d.N := (hd.s56_mem_N_iff_eps h49 hxQ0).2 hεF
  have hxP0 := hd.s56_Q2_inf_N_le_P0 h49 hx.2 hxN
  have hδ := hd.s56_P0_comm_F_le_U10 h49 hxP0 hd.s56_pv7_mem_F
  obtain ⟨-, h3, -⟩ := U10_coord hd hδ
  have hq7 : d.pv 7 ∈ d.s56J := Data.s56_pv_mem_J d (by simp)
  have hB := hμ x hx (d.pv 7) hq7
  rw [fb_pv7 hd, hxa] at hB
  have hκ : kk d x (d.pv 7) = 0 := by
    unfold kk
    rw [hxa, fb_pv7 hd]
    simp [b0, dotProduct, Fin.sum_univ_four]
  have hep : ep d z₀ x (d.pv 7) = x * d.pv 7 * x⁻¹ * (d.pv 7)⁻¹ := by
    unfold ep
    rw [hκ]
    simp
  have h2 := congrFun hB 2
  unfold Bf at h2
  rw [hep] at h2
  have h0 : wcoord d (x * d.pv 7 * x⁻¹ * (d.pv 7)⁻¹) 2 = 0 := h3
  rw [h0, kapA_table1 μ] at h2
  exact absurd h2 (by decide)

end CFSG.LocalAnalysis.EvenBN.Tits.N.KappaA

