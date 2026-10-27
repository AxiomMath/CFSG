module

public import CFSG.ClassicalInvolution.Q3.Q3T6D9Out
public import CFSG.ClassicalInvolution.Q3.Q3T6DR10bStd
public import CFSG.ClassicalInvolution.Q3.Q3T6D9B
public import CFSG.ClassicalInvolution.Q3.Q3T6DC3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.ClassicalInvolution.Asc77.T3CII.T3R
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Uniform
open scoped MatrixGroups commutatorElement

section Sq

variable {G : Type} [Group G] [Finite G]

theorem sq_mem_of_order_eight {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {L R : Subgroup G}
    {w : G} (hL : L ∈ Ω) (hw : IsUniqueInvolution L w) (hR : IsSylow2In R L)
    (h8 : Nat.card R = 8) {r : G} (hr : r ∈ R) : r * r = 1 ∨ r * r = w := by
  have hq : IsQuatSub R := Sec6Gen.isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hL hR)
  have h4 : r ^ 4 = 1 := by simpa [h8] using Sec6Gen.IsQuatSub.pow_half_eq_one hq hr
  have hsq : (r * r) * (r * r) = 1 := by
    rw [show (r * r) * (r * r) = r ^ 4 by simp only [pow_succ, pow_zero, one_mul, mul_assoc]]
    exact h4
  exact hw.unique (r * r) (L.mul_mem (hR.1 hr) (hR.1 hr)) hsq

end Sq

section TX


variable {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem Std20Three.r10b_TX (d : Std20Three K K' J S R R' W V z t) (c8 : Concl20_8 S K' R)
    (h8 : Nat.card R = 8) : ∀ g ∈ (S : Subgroup G), conjSub g K = K →
      g ∈ sec20X (CoreAssembly.conjClass K) z K K' := by
  classical
  intro g hg hgK
  have hΩ : HypOmegaGen (CoreAssembly.conjClass K) := d.late_hΩ
  have hKΩ : K ∈ CoreAssembly.conjClass K := d.late_mem_K
  have hK'Ω : K' ∈ CoreAssembly.conjClass K := d.late_mem_K'
  obtain ⟨z₀, hz₀⟩ := d.hyp.classical K hKΩ
  obtain ⟨hfact, ⟨eK⟩⟩ := hz₀.witness
  have hF3 : Nat.card (GaloisField 3 1) = 3 := by
    rw [natCard_galoisField_eq (p := 3) (f := 1) Nat.one_pos]
    norm_num
  have hFodd : Odd (Nat.card (GaloisField 3 1)) := by rw [hF3]; exact ⟨1, rfl⟩
  have hR8' : Nat.card R' = 8 :=
    Q3T6.natCard_rSet_of_classical (fun J hJ => by
      obtain ⟨w, hw⟩ := d.hyp.classical J hJ
      exact ⟨w, hw⟩) (mem_RSet_of_isSylow2In hK'Ω d.hR')
  obtain ⟨u, hu, huK⟩ := d.late_exists_swap
  obtain ⟨v, hv, hord, hvN⟩ := d.r9_vdata
  have hvV : v ∈ V := hv ▸ Subgroup.mem_zpowers v
  have hV2 : IsPGroup 2 V := Sec6Gen.isPGroup_of_mem_USet hΩ d.hV
  have tw : Twin20 (CoreAssembly.conjClass K) K K' z (S : Subgroup G) V :=
    ⟨hΩ.conjInvariant, d.viol.hzK, d.twins, d.ne, d.hSz, d.hV, d.hVS, hV2⟩
  set T : Subgroup G := (S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G) with hT
  have hT2 : IsPGroup 2 ↥T := S.isPGroup'.to_le inf_le_left
  have hTN : T ≤ Subgroup.normalizer (K : Set G) := inf_le_right
  have hRT : R ≤ T := le_inf d.hRS (d.hR.1.trans Subgroup.le_normalizer)
  have hVT : V ≤ T := le_inf d.hVS (d.hVW.trans d.late_W_le_N_K)
  have hvT : v ∈ T := hVT hvV
  have hRp : ∀ y ∈ T, phiG K eK y = 1 → y ∈ R' := fun y hyT hy1 =>
    d.r9_cStar_S c8 hu huK hyT.1 ((phiG_eq_one_iff hyT.2).mp hy1)
  have hvout : phiG K eK v ∉
      (MulAut.conj : SL(2, GaloisField 3 1) →* MulAut SL(2, GaloisField 3 1)).range := by
    intro hin
    obtain ⟨r, hr, hrv⟩ := exists_mem_of_phiG_inner hFodd hT2 hTN hRT d.hR hvT hin
    have hrN : r ∈ Subgroup.normalizer (K : Set G) := hTN (hRT hr)
    have hvN' : v ∈ Subgroup.normalizer (K : Set G) := hTN hvT
    have hcT : r⁻¹ * v ∈ T := T.mul_mem (T.inv_mem (hRT hr)) hvT
    have hc : r⁻¹ * v ∈ R' :=
      hRp _ hcT (by rw [phiG_mul (Subgroup.inv_mem _ hrN) hvN', phiG_inv hrN, hrv, inv_mul_cancel])
    have hcomm : r * (r⁻¹ * v) = (r⁻¹ * v) * r := d.late_R_R'_comm hr hc
    have hvv : v * v = (r * r) * ((r⁻¹ * v) * (r⁻¹ * v)) := by
      calc v * v = (r * (r⁻¹ * v)) * (r * (r⁻¹ * v)) := by group
        _ = r * ((r⁻¹ * v) * r) * (r⁻¹ * v) := by group
        _ = r * (r * (r⁻¹ * v)) * (r⁻¹ * v) := by rw [hcomm]
        _ = (r * r) * ((r⁻¹ * v) * (r⁻¹ * v)) := by group
    have hz2 : z * z = 1 := d.viol.hzK.sq
    have hsq : v * v = 1 ∨ v * v = z := by
      rcases sq_mem_of_order_eight hΩ hKΩ d.viol.hzK d.hR h8 hr with h1 | h1 <;>
        rcases sq_mem_of_order_eight hΩ hK'Ω d.late_hzK' d.hR' hR8' hc with h2 | h2 <;>
        rw [hvv, h1, h2] <;> simp [hz2]
    have hv4 : orderOf v = 4 := by omega
    have hvv1 : v * v ≠ 1 := by
      intro h
      have h2 : orderOf v ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
      have := Nat.le_of_dvd (by norm_num) h2
      omega
    have hvv4 : (v * v) * (v * v) = 1 := by
      have h4 : v ^ 4 = 1 := by rw [← hv4]; exact pow_orderOf_eq_one v
      rw [show (v * v) * (v * v) = v ^ 4 by simp only [pow_succ, pow_zero, one_mul, mul_assoc]]
      exact h4
    have hvt : v * v = t := d.eq_t_of_invol_mem_V (V.mul_mem hvV hvV) hvv4 hvv1
    rcases hsq with h | h
    · exact hvv1 h
    · exact d.late_ne_inv (hvt.symm.trans h)
  have hRR'V_le_X : R ⊔ R' ⊔ V ≤ sec20X (CoreAssembly.conjClass K) z K K' :=
    sup_le (sup_le (d.hR.1.trans le_sec20X_left) (d.hR'.1.trans le_sec20X_right)) tw.hVX
  have hgT : g ∈ T := ⟨hg, mem_normalizer_iff_conjSub_eq.mpr hgK⟩
  exact hRR'V_le_X (mem_sup_of_not_inner hF3 hT2 hTN hRT d.hR hRp hvV hvT hvout hgT)

end TX

end CFSG.ClassicalInvolution.Q3.Q3T6D
