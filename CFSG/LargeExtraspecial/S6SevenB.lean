module

public import CFSG.LargeExtraspecial.S6Seven
public import CFSG.LargeExtraspecial.S6Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

omit [Finite G] in
theorem mem_Qa_of_cl_mem {g' x : G} (hx : x ∈ S.QG) (hz : S.z ∈ S.Qa g')
    (h : S.cl x ∈ S.clSub (S.QG ⊓ S.Qa g')) : x ∈ S.Qa g' := by
  obtain ⟨y, hy, hyQ, hyx⟩ := S.mem_clSub_iff.mp h
  rcases (S.cl_eq_cl_iff hyQ hx).mp hyx with rfl | rfl
  · exact hy.2
  · exact mul_mem hy.2 hz

section Omega

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g) {Qf : QuadraticForm (ZMod 2) (Vt S g t)}
  (hpol : Qf.polarBilin = beta H C ht ht1 hVQ)
  (horb : ∀ v : Vt S g t, v ≠ 0 → (Qf v = 0 ↔ (v : S.Qt) ∈ orbit S g t))
include H C ht ht1 hVQ hpol horb

omit hpol in
theorem mem_clSub_of_singular {k₃ : G} {d : Vt S g t}
    (hd : (d : S.Qt) = S.cl (k₃ * S.z * k₃⁻¹)) (hk₃Q : k₃ * S.z * k₃⁻¹ ∈ S.QG)
    (hQd : Qf d = 1) {v : Vt S g t} (hv0 : v ≠ 0) (hQv : Qf v = 0)
    (hvd : beta H C ht ht1 hVQ v d = 0) : (v : S.Qt) ∈ S.clSub (S.QG ⊓ S.Qa k₃) := by
  obtain ⟨k₄, hk₄, hv⟩ := exists_of_mem_orbit ((horb v hv0).mp hQv) H.conj_mem
  have htk₄ := mem_Lbar_mul_of_mem_Rbar H ht hk₄
  have hb : bV htk₄ = v := Subtype.ext hv.symm
  have h2 := (beta_bV_eq_zero_iff H C ht ht1 hVQ hk₄ htk₄ d).mp (by rw [hb]; exact hvd)
  rw [hd] at h2
  have h3 : k₃ * S.z * k₃⁻¹ ∈ S.Qa ((k₄ : G) * g) :=
    mem_Qa_of_cl_mem hk₃Q (S.z_mem_Qa (H.mul k₄).conj_mem (H.mul k₄).conj_ne) h2
  have hne : k₃ * S.z * k₃⁻¹ ≠ (k₄ : G) * g * S.z * ((k₄ : G) * g)⁻¹ := by
    intro he
    have hdv : d = v := Subtype.ext (by rw [hd, he, hv])
    rw [hdv, hQv] at hQd
    exact zero_ne_one hQd
  have h4 := S.mem_Qa_symm hne h3
  rw [hv]
  exact S.cl_mem_clSub ⟨(H.mul k₄).conj_mem, h4⟩ (H.mul k₄).conj_mem

theorem mem_clSub_of_beta_eq_zero {k₃ : G} {d : Vt S g t}
    (hd : (d : S.Qt) = S.cl (k₃ * S.z * k₃⁻¹)) (hk₃Q : k₃ * S.z * k₃⁻¹ ∈ S.QG)
    (hQd : Qf d = 1) {v : Vt S g t} (hvd : beta H C ht ht1 hVQ v d = 0) :
    (v : S.Qt) ∈ S.clSub (S.QG ⊓ S.Qa k₃) := by
  have hpolar : ∀ x y : Vt S g t, polar Qf x y = beta H C ht ht1 hVQ x y := fun x y => by
    rw [← polarBilin_apply_apply, hpol]
  have hdP : (d : S.Qt) ∈ S.clSub (S.QG ⊓ S.Qa k₃) := by
    rw [hd]
    exact S.cl_mem_clSub ⟨hk₃Q, S.conj_z_mem_Qa k₃⟩ hk₃Q
  by_cases hv0 : v = 0
  · rw [hv0]
    exact zero_mem _
  rcases zmod2_eq_zero_or_eq_one (Qf v) with hQv | hQv
  · exact mem_clSub_of_singular H C ht ht1 hVQ horb hd hk₃Q hQd hv0 hQv hvd
  · have hQvd : Qf (v + d) = 0 := by
      rw [map_add_eq, hQv, hQd, hpolar, hvd]
      decide
    have hvd' : beta H C ht ht1 hVQ (v + d) d = 0 := by
      rw [map_add, LinearMap.add_apply, hvd, beta_isAlt H C ht ht1 hVQ d, add_zero]
    by_cases hvd0 : v + d = 0
    · have : v = d := (eq_of_add_eq_zero' (show d + v = 0 by rw [add_comm]; exact hvd0))
      rw [this]
      exact hdP
    · have h1 := mem_clSub_of_singular H C ht ht1 hVQ horb hd hk₃Q hQd hvd0 hQvd hvd'
      have h2 := add_mem h1 hdP
      rwa [Submodule.coe_add, add_assoc, vec_add_self, add_zero] at h2

end Omega

end CFSG.LargeExtraspecial.S6
