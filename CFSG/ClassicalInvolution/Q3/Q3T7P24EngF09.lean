module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24EngF08
public import CFSG.ClassicalInvolution.Q3.Q3T7P24EngF07x

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

namespace Asc77
namespace S24B
namespace Ctx8Frame

section
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight (HypOmegaGen)
open CFSG.ClassicalInvolution.Asc77.S24
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8Frame Ω K K' W S R R' z u)

include C in
theorem exists_caseI {c : G} (hcS : c ∈ (S : Subgroup G)) (hc2 : c * c = 1)
    (hinv : ∀ w ∈ W, c * w * c⁻¹ = w⁻¹) (hcr : c * C.D.F.ρ.r = C.D.F.ρ.r * c)
    (hin : InnerOn c R') :
    ∃ e ∈ (S : Subgroup G), e ∉ sZero Ω W S ∧ e * e = 1 ∧
      (∀ x ∈ (S : Subgroup G), x ∉ sZero Ω W S → e⁻¹ * x ∈ sZero Ω W S) ∧
      (∀ v ∈ R, v * e = e * v) ∧ (∀ v ∈ R', v * e = e * v) := by
  obtain ⟨q, hq, hqv⟩ := hin
  have hrS : C.D.F.ρ.r ∈ (S : Subgroup G) := C.hd.hR.2.2 C.r_mem_R
  have hqS : q ∈ (S : Subgroup G) := C.hd.hR'.2.2 hq
  have hqrP : q * C.D.F.ρ.r ∈ sZero Ω W S :=
    inf_le_sZero ⟨S.mul_mem hqS hrS, (MGrp Ω W).mul_mem
      (Thompson.le_MGrp_of_mem_D C.D.F.ρ'.hR (by rw [C.hR']; exact hq))
      (Thompson.le_MGrp_of_mem_D C.D.F.ρ.hR C.D.F.ρ.hr)⟩
  have hcR : ∀ v ∈ R, c * v * c⁻¹ = C.D.F.ρ.r * v * C.D.F.ρ.r⁻¹ := by
    refine conj_eq_of_gens (Subgroup.zpowers_le.mpr C.x₁_mem_R) C.card_R C.r_mem_R
      C.r_not_mem_zpowers ?_ ?_
    · rw [hinv _ C.D.x₁_mem, C.D.r₁]
    · rw [hcr, mul_inv_cancel_right]
      group
  have hqR : ∀ v ∈ R, q * v = v * q := fun v hv => (C.commutes_R_R' v hv q hq).symm
  have hrR' : ∀ v ∈ R', C.D.F.ρ.r * v = v * C.D.F.ρ.r := fun v hv =>
    C.commutes_R_R' _ C.r_mem_R v hv
  have hcq : c * q = q * c := by
    have e := hqv q hq
    calc c * q = c * q * c⁻¹ * c := by group
      _ = q * c := by rw [e]; group
  have hqr : q * C.D.F.ρ.r = C.D.F.ρ.r * q := (hrR' q hq).symm
  have hqU : q ∉ Subgroup.zpowers C.D.x₂ := by
    intro h
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
    have e := hqv _ C.x₂_mem_R'
    rw [hinv _ C.D.x₂_mem, (Commute.zpow_self C.D.x₂ i).eq, mul_inv_cancel_right] at e
    have e3 : C.D.x₂ ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [← e]
      exact inv_mul_cancel _
    have := orderOf_dvd_of_pow_eq_one e3
    rw [C.orderOf_x₂] at this
    omega
  have hqq : q * q = z := by
    have hquat := C.hyp.isQuatSub_of_mem_RSet C.hd.hR'.1
    have hzR' : z ∈ R' := T7C.mem_of_isSylow2In C.hyp C.hK'tw.1 (hR'syl C) C.hzK'
    exact AscL62.sq_eq_of_not_mem hquat (AscL62.isUniqueInvolution_of_le C.hzK' C.hd.hR'.2.1 hzR')
      (Subgroup.zpowers_le.mpr C.x₂_mem_R') inferInstance C.card_R' hq hqU
  have hcqr : c * (q * C.D.F.ρ.r) = (q * C.D.F.ρ.r) * c := by
    rw [← mul_assoc, hcq, mul_assoc, hcr, ← mul_assoc]
  have hqr2 : (q * C.D.F.ρ.r) * (q * C.D.F.ρ.r) = 1 := by
    calc (q * C.D.F.ρ.r) * (q * C.D.F.ρ.r) = q * (C.D.F.ρ.r * q) * C.D.F.ρ.r := by group
      _ = q * (q * C.D.F.ρ.r) * C.D.F.ρ.r := by rw [hqr]
      _ = (q * q) * (C.D.F.ρ.r * C.D.F.ρ.r) := by group
      _ = 1 := by rw [hqq, C.r_mul_self, C.hzK.sq]
  have hcqr' : c * (q * C.D.F.ρ.r)⁻¹ = (q * C.D.F.ρ.r)⁻¹ * c := by
    calc c * (q * C.D.F.ρ.r)⁻¹ = (q * C.D.F.ρ.r)⁻¹ * ((q * C.D.F.ρ.r) * c) *
          (q * C.D.F.ρ.r)⁻¹ := by group
      _ = (q * C.D.F.ρ.r)⁻¹ * (c * (q * C.D.F.ρ.r)) * (q * C.D.F.ρ.r)⁻¹ := by rw [hcqr]
      _ = (q * C.D.F.ρ.r)⁻¹ * c := by group
  refine ⟨c * (q * C.D.F.ρ.r)⁻¹, S.mul_mem hcS (S.inv_mem (S.mul_mem hqS hrS)), ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h2 := Subgroup.mul_mem _ h hqrP
    rw [inv_mul_cancel_right] at h2
    exact not_mem_sZero C hinv h2
  · calc c * (q * C.D.F.ρ.r)⁻¹ * (c * (q * C.D.F.ρ.r)⁻¹)
        = c * ((q * C.D.F.ρ.r)⁻¹ * c) * (q * C.D.F.ρ.r)⁻¹ := by group
      _ = c * (c * (q * C.D.F.ρ.r)⁻¹) * (q * C.D.F.ρ.r)⁻¹ := by rw [hcqr']
      _ = (c * c) * ((q * C.D.F.ρ.r) * (q * C.D.F.ρ.r))⁻¹ := by group
      _ = 1 := by rw [hc2, hqr2]; group
  · intro x hx hxN
    have h := (mem_or_inv_mul_mem_sZero C hcS hinv hx).resolve_left hxN
    have e : (c * (q * C.D.F.ρ.r)⁻¹)⁻¹ * x = (q * C.D.F.ρ.r) * (c⁻¹ * x) := by group
    rw [e]
    exact Subgroup.mul_mem _ hqrP h
  · intro v hv
    have hv' : C.D.F.ρ.r⁻¹ * v * C.D.F.ρ.r ∈ R :=
      R.mul_mem (R.mul_mem (R.inv_mem C.r_mem_R) hv) C.r_mem_R
    have hqv' : q⁻¹ * v * q = v := by
      calc q⁻¹ * v * q = q⁻¹ * (v * q) := by group
        _ = q⁻¹ * (q * v) := by rw [hqR v hv]
        _ = v := by group
    have key : c * (q * C.D.F.ρ.r)⁻¹ * v * (c * (q * C.D.F.ρ.r)⁻¹)⁻¹ = v := by
      calc c * (q * C.D.F.ρ.r)⁻¹ * v * (c * (q * C.D.F.ρ.r)⁻¹)⁻¹
          = c * (C.D.F.ρ.r⁻¹ * (q⁻¹ * v * q) * C.D.F.ρ.r) * c⁻¹ := by group
        _ = c * (C.D.F.ρ.r⁻¹ * v * C.D.F.ρ.r) * c⁻¹ := by rw [hqv']
        _ = C.D.F.ρ.r * (C.D.F.ρ.r⁻¹ * v * C.D.F.ρ.r) * C.D.F.ρ.r⁻¹ := hcR _ hv'
        _ = v := by group
    calc v * (c * (q * C.D.F.ρ.r)⁻¹)
        = c * (q * C.D.F.ρ.r)⁻¹ * v * (c * (q * C.D.F.ρ.r)⁻¹)⁻¹ * (c * (q * C.D.F.ρ.r)⁻¹) := by
          rw [key]
      _ = c * (q * C.D.F.ρ.r)⁻¹ * v := by group
  · intro v hv
    have hv' : q⁻¹ * v * q ∈ R' := R'.mul_mem (R'.mul_mem (R'.inv_mem hq) hv) hq
    have key : c * (q * C.D.F.ρ.r)⁻¹ * v * (c * (q * C.D.F.ρ.r)⁻¹)⁻¹ = v := by
      calc c * (q * C.D.F.ρ.r)⁻¹ * v * (c * (q * C.D.F.ρ.r)⁻¹)⁻¹
          = c * (C.D.F.ρ.r⁻¹ * (q⁻¹ * v * q) * C.D.F.ρ.r) * c⁻¹ := by group
        _ = c * ((q⁻¹ * v * q) * C.D.F.ρ.r⁻¹ * C.D.F.ρ.r) * c⁻¹ := by
            rw [show C.D.F.ρ.r⁻¹ * (q⁻¹ * v * q) = (q⁻¹ * v * q) * C.D.F.ρ.r⁻¹ by
              calc C.D.F.ρ.r⁻¹ * (q⁻¹ * v * q)
                  = C.D.F.ρ.r⁻¹ * ((q⁻¹ * v * q) * C.D.F.ρ.r) * C.D.F.ρ.r⁻¹ := by group
                _ = C.D.F.ρ.r⁻¹ * (C.D.F.ρ.r * (q⁻¹ * v * q)) * C.D.F.ρ.r⁻¹ := by
                    rw [hrR' _ hv']
                _ = (q⁻¹ * v * q) * C.D.F.ρ.r⁻¹ := by group]
        _ = c * (q⁻¹ * v * q) * c⁻¹ := by group
        _ = q * (q⁻¹ * v * q) * q⁻¹ := hqv _ hv'
        _ = v := by group
    calc v * (c * (q * C.D.F.ρ.r)⁻¹)
        = c * (q * C.D.F.ρ.r)⁻¹ * v * (c * (q * C.D.F.ρ.r)⁻¹)⁻¹ * (c * (q * C.D.F.ρ.r)⁻¹) := by
          rw [key]
      _ = c * (q * C.D.F.ρ.r)⁻¹ * v := by group

end
end Ctx8Frame
end S24B
end Asc77

end CFSG.ClassicalInvolution.Q3.Q3T8
