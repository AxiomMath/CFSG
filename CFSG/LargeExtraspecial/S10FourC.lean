module

public import CFSG.LargeExtraspecial.S10Frame
public import CFSG.LargeExtraspecial.S10ModelB
public import CFSG.LargeExtraspecial.S4EightF3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

theorem qf_add (m m' : M2) : qf (m + m') = qf m + qf m' + pf m m' := by
  simp only [qf, pf, Matrix.add_apply]
  ring

theorem exists_pair_perp_M2 : ∀ v : M2, qf v = 1 → ∃ p p' : M2, p ≠ 0 ∧ qf p = 0 ∧ p' ≠ 0 ∧
    qf p' = 0 ∧ pf p p' = 1 ∧ pf p v = 0 ∧ pf p' v = 0 := by
  decide +kernel

theorem exists_comm_comm_ne_zero : ∃ m : M2, act τ₂ (act τ₁ m - m) - (act τ₁ m - m) ≠ 0 := by
  decide +kernel

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem exists_orbV_eq (X : Hyp10 S g t) {v : Vt S g t} (hv : (v : S.Qt) ∈ orbit S g t) :
    ∃ k : S.M, ∃ hk : S.ρ k ∈ Rbar S g t, orbV X.haQ X.ht hk = v := by
  obtain ⟨k, hk, hvk⟩ := exists_of_mem_orbit hv X.haQ
  refine ⟨k, hk, Subtype.ext ?_⟩
  rw [coe_orbV, ρ_cl_conj_z S k X.haQ, hvk]

namespace Frame

variable {X : Hyp10 S g t} (F : Frame X)
include F

theorem qf_add' (x y : Vt S g t) : qf (F.φ (x + y)) =
    qf (F.φ x) + qf (F.φ y) + beta X.H X.C X.ht X.ht1 X.hVQ x y := by
  rw [map_add, F.beta_eq, qf_add]

theorem mem_orbit_iff {v : Vt S g t} (hv : v ≠ 0) :
    (v : S.Qt) ∈ orbit S g t ↔ qf (F.φ v) = 0 := by
  rw [← mem_orbitOf_RmodN_iff X.haQ X.ht]
  exact F.sing v hv

theorem qf_eq_one {v : Vt S g t} (hv : v ≠ 0) (hvo : (v : S.Qt) ∉ orbit S g t) :
    qf (F.φ v) = 1 := by
  rcases CFSG.RankThree.Literature.FSmith.zmod2_cases (qf (F.φ v)) with h | h
  · exact absurd ((F.mem_orbit_iff hv).mpr h) hvo
  · exact h

theorem exists_pair_perp {v : Vt S g t} (hv0 : v ≠ 0) (hvo : (v : S.Qt) ∉ orbit S g t) :
    ∃ k₁ k₂ : S.M, ∃ hk₁ : S.ρ k₁ ∈ Rbar S g t, ∃ hk₂ : S.ρ k₂ ∈ Rbar S g t,
      beta X.H X.C X.ht X.ht1 X.hVQ (orbV X.haQ X.ht hk₁) (orbV X.haQ X.ht hk₂) = 1 ∧
      beta X.H X.C X.ht X.ht1 X.hVQ (orbV X.haQ X.ht hk₁) v = 0 ∧
      beta X.H X.C X.ht X.ht1 X.hVQ (orbV X.haQ X.ht hk₂) v = 0 := by
  obtain ⟨p, p', hp0, hp, hp'0, hp', hpp', hpv, hp'v⟩ :=
    exists_pair_perp_M2 (F.φ v) (F.qf_eq_one hv0 hvo)
  have hu : ∀ {p : M2}, p ≠ 0 → qf p = 0 → ((F.φ.symm p : Vt S g t) : S.Qt) ∈ orbit S g t :=
    fun {p} hp0 hp => (F.mem_orbit_iff (fun h => hp0 (by
      rw [← F.φ.apply_symm_apply p, h, map_zero]))).mpr (by rw [F.φ.apply_symm_apply]; exact hp)
  obtain ⟨k₁, hk₁, e₁⟩ := exists_orbV_eq X (hu hp0 hp)
  obtain ⟨k₂, hk₂, e₂⟩ := exists_orbV_eq X (hu hp'0 hp')
  refine ⟨k₁, k₂, hk₁, hk₂, ?_, ?_, ?_⟩
  · rw [e₁, e₂, F.beta_eq, F.φ.apply_symm_apply, F.φ.apply_symm_apply]
    exact hpp'
  · rw [e₁, F.beta_eq, F.φ.apply_symm_apply]
    exact hpv
  · rw [e₂, F.beta_eq, F.φ.apply_symm_apply]
    exact hp'v

end Frame

end CFSG.LargeExtraspecial.S10
