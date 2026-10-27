module

public import CFSG.LargeExtraspecial.S10FourF
public import CFSG.LargeExtraspecial.S10FlagB
public import CFSG.LargeExtraspecial.S10FourE

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem conj_mem_Mbar (X : Hyp10 S g t) (m : S.M) : S.ρ m * t * (S.ρ m)⁻¹ ∈ S.Mbar :=
  mul_mem (mul_mem (MonoidHom.mem_range.mpr ⟨m, rfl⟩) (S.Lbar_le_Mbar g X.ht))
    (inv_mem (MonoidHom.mem_range.mpr ⟨m, rfl⟩))

theorem finrank_commSpace_conj_t (X : Hyp10 S g t) (m : S.M) :
    finrank (ZMod 2) (commSpace ((S.ρ m * t * (S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 4 := by
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [finrank_commSpace_conj, finrank_commSpace_t X]

theorem StronglyClosedL.fix_Vt_of_conj (hSC : StronglyClosedL S g t) (hCE : CentralExtInput.{u})
    (X : Hyp10 S g t) (F : Frame X) (h7 : 7 ≤ S.width) {m : S.M}
    (hne : S.ρ m * t * (S.ρ m)⁻¹ ≠ t)
    (hcomm : (S.ρ m * t * (S.ρ m)⁻¹) * t = t * (S.ρ m * t * (S.ρ m)⁻¹)) :
    ∀ v ∈ Vt S g t, ((S.ρ m * t * (S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  obtain ⟨t', ht'⟩ : ∃ t' : S.O, t' = S.ρ m * t * (S.ρ m)⁻¹ := ⟨_, rfl⟩
  rw [← ht'] at hne hcomm ⊢
  have hTt : (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) * (t : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      (t : S.Qt ≃ₗ[ZMod 2] S.Qt) * (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hcomm]
  obtain ⟨hTV, hTW⟩ := apply_mem_Vt_Wt_of_commute X hTt
  have ht'M : t' ∈ S.Mbar := ht' ▸ conj_mem_Mbar X m
  have hD1 : ∀ v ∈ Vt S g t, (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∉ orbit S g t := by
    intro v hv hdo
    obtain ⟨k, hk, hdk⟩ := exists_of_mem_orbit hdo X.haQ
    have htk := mem_Lbar_mul_of_mem_Rbar X.H X.ht hk
    have hcs : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈
        commSpace ((S.ρ m * t * (S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      rw [← ht', ← hdk]
      exact sub_mem_commSpace _ v
    have ht'k := hSC.mem_Lbar_of_mem_commSpace_conj X F hcs
    have h1 : S.ρ 1 * t * (S.ρ 1)⁻¹ ∈ S.Lbar ((k : G) * g) := by
      rw [map_one, one_mul, inv_one, mul_one]
      exact htk
    have := hSC.conj_eq_conj ht'k h1
    rw [map_one, one_mul, inv_one, mul_one, ← ht'] at this
    exact hne this
  by_contra hcon
  push Not at hcon
  obtain ⟨v₀, hv₀, hv₀m⟩ := hcon
  obtain ⟨p, hp, hpm⟩ : ∃ p ∈ orbit S g t, (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) p ≠ p := by
    by_contra h
    push Not at h
    apply hv₀m
    have hle : Vt S g t ≤ fixSpace (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      rw [Vt_eq_span_orbit X.H X.ht, Submodule.span_le]
      intro q hq
      exact mem_fixSpace.mpr (h q hq)
    exact mem_fixSpace.mp (hle hv₀)
  have hpV : p ∈ Vt S g t := orbit_subset_Vt X.ht X.haQ hp
  have hTp := apply_mem_orbit_of_commute X ht'M hcomm hp
  obtain ⟨k₁, hk₁, e₁⟩ := exists_orbV_eq X (v := ⟨p, hpV⟩) hp
  obtain ⟨k₂, hk₂, e₂⟩ := exists_orbV_eq X (v := ⟨_, hTV p hpV⟩) hTp
  have hβ : beta X.H X.C X.ht X.ht1 X.hVQ (orbV X.haQ X.ht hk₁) (orbV X.haQ X.ht hk₂) = 1 := by
    set d : Vt S g t := ⟨_, sub_mem (hTV p hpV) hpV⟩ with hd
    have hd0 : d ≠ 0 := fun h => hpm (sub_eq_zero.mp (congrArg Subtype.val h))
    have hQd := F.qf_eq_one hd0 (hD1 p hpV)
    have hsum : orbV X.haQ X.ht hk₂ = orbV X.haQ X.ht hk₁ + d := by
      rw [e₁, e₂]
      exact Subtype.ext (by simp [hd])
    have hQ1 : qf (F.φ (orbV X.haQ X.ht hk₁)) = 0 := by
      rw [← F.mem_orbit_iff (orbV_ne_zero' X hk₁)]
      exact ⟨S.ρ k₁, hk₁, coe_orbV X.haQ X.ht hk₁⟩
    have hQ2 : qf (F.φ (orbV X.haQ X.ht hk₂)) = 0 := by
      rw [← F.mem_orbit_iff (orbV_ne_zero' X hk₂)]
      exact ⟨S.ρ k₂, hk₂, coe_orbV X.haQ X.ht hk₂⟩
    have h3 := F.qf_add' (orbV X.haQ X.ht hk₁) d
    rw [← hsum, hQ2, hQ1, hQd, zero_add] at h3
    have hβd : beta X.H X.C X.ht X.ht1 X.hVQ (orbV X.haQ X.ht hk₁) d = 1 := by
      rcases CFSG.RankThree.Literature.FSmith.zmod2_cases
        (beta X.H X.C X.ht X.ht1 X.hVQ (orbV X.haQ X.ht hk₁) d) with h | h
      · rw [h] at h3
        exact absurd h3 (by decide)
      · exact h
    rw [hsum, map_add, (beta_isAlt X.H X.C X.ht X.ht1 X.hVQ) _, zero_add, hβd]
  obtain ⟨y₀, hy₀⟩ := MonoidHom.mem_range.mp ht'M
  have hcl : S.cl (((y₀ * k₁ : S.M) : G) * g * S.z * (((y₀ * k₁ : S.M) : G) * g)⁻¹) =
      S.cl ((k₂ : G) * g * S.z * ((k₂ : G) * g)⁻¹) := by
    rw [← ρ_cl_conj_mul X, hy₀, ← coe_orbV' X hk₁, e₁, ← coe_orbV' X hk₂, e₂]
  have hyP : ∀ w ∈ S.clSub (S.QG ⊓ S.Qa ((k₁ : G) * g)) ⊓ Wt S g t,
      (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ S.clSub (S.QG ⊓ S.Qa ((k₂ : G) * g)) ⊓ Wt S g t := by
    intro w hw
    refine ⟨?_, hTW w hw.2⟩
    have h1 := apply_mem_clSub_Qa_mul (g := (k₁ : G) * g) y₀ hw.1
    rw [hy₀] at h1
    rwa [show (y₀ : G) * ((k₁ : G) * g) = ((y₀ * k₁ : S.M) : G) * g by
        rw [Subgroup.coe_mul, mul_assoc],
      clSub_eq_of_cl_eq (conj_mem_QG' S (y₀ * k₁).2 X.haQ)
        (conj_ne_z' S (y₀ * k₁).2 X.H.conj_ne) (conj_mem_QG' S k₂.2 X.haQ) hcl] at h1
  have hsw := width_le_of_swap hCE X hk₁ hk₂ hβ hTV hyP
  have hflag := flag_of_commute X hTt
  rw [ht', finrank_commSpace_conj_t X m, ← ht'] at hflag
  have hzero : finrank (ZMod 2) ((Vt S g t).map
      (((t' : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1)) = 0 := by omega
  rw [Submodule.finrank_eq_zero] at hzero
  have hmem : (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p ∈ (Vt S g t).map
      (((t' : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1) :=
    ⟨p, hpV, rfl⟩
  rw [hzero, Submodule.mem_bot, sub_eq_zero] at hmem
  exact hpm hmem

end CFSG.LargeExtraspecial.S10
