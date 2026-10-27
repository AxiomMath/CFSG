module

public import CFSG.LargeExtraspecial.S111ABasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G} {A : Subgroup G}

omit [Finite G] in
theorem IncClosed.commutator_mem (hA : IncClosed S A) {k y x : G} (hk : k * S.z * k⁻¹ ∈ A)
    (hy : y ∈ S.Qa k) (hx : x ∈ A) :
    y * x * y⁻¹ * x⁻¹ = 1 ∨ y * x * y⁻¹ * x⁻¹ = k * S.z * k⁻¹ :=
  (S.conjBy k).commutator_eq_one_or_z hy (hA.le_Qa k hk hx)

theorem IncClosed.apply_sub_mem_span (hA : IncClosed S A) {k : G} (hk : k * S.z * k⁻¹ ∈ A)
    {s : S.O} (hs : s ∈ S.Lbar k) {v : S.Qt} (hv : v ∈ S.clSub A) :
    (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ (ZMod 2) ∙ S.cl (k * S.z * k⁻¹) := by
  obtain ⟨y, hyL, rfl⟩ := (mem_Lbar S).mp hs
  obtain ⟨x, hx, hxQ, rfl⟩ := S.mem_clSub_iff.mp hv
  rw [S.ρ_cl y hxQ]
  have e : (y : G) * x * (y : G)⁻¹ = ((y : G) * x * (y : G)⁻¹ * x⁻¹) * x := by group
  rcases hA.commutator_mem hk hyL.1 hx with h | h
  · rw [e, h, one_mul, sub_self]
    exact zero_mem _
  · rw [e, h, S.cl_mul (hA.le_QG hk) hxQ, add_sub_cancel_right]
    exact Submodule.mem_span_singleton_self _

theorem IncClosed.exists_transvection (hA : IncClosed S A) {k : G} (hk : k * S.z * k⁻¹ ∈ A)
    (_hkz : k * S.z * k⁻¹ ≠ S.z) (f : S.Qt →ₗ[ZMod 2] ZMod 2) (hf : f (S.cl (k * S.z * k⁻¹)) = 0) :
    ∃ y : S.M, (y : G) ∈ S.L0 k ∧ ∀ v ∈ S.clSub A,
      (S.ρ y : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v + f v • S.cl (k * S.z * k⁻¹) := by
  classical
  set T := S.conjBy k with hT
  have hAT : A ≤ T.QG := hA.le_Qa k hk
  have hlift : ∀ u : T.clSub A, ∃ x ∈ A, T.cl x = u := fun u => by
    obtain ⟨x, hx, -, hxu⟩ := T.mem_clSub_iff.mp u.2
    exact ⟨x, hx, hxu⟩
  choose lift hliftA hliftcl using hlift
  have key : ∀ x ∈ A, ∀ y ∈ A, T.cl x = T.cl y → f (S.cl x) = f (S.cl y) := by
    intro x hx y hy hxy
    rcases (T.cl_eq_cl_iff (hAT hx) (hAT hy)).mp hxy with e | e
    · rw [e]
    · rw [e]
      change f (S.cl x) = f (S.cl (x * (k * S.z * k⁻¹)))
      rw [S.cl_mul (hA.le_QG hx) (hA.le_QG hk), map_add, hf, add_zero]
  let F : T.clSub A →+ ZMod 2 :=
    { toFun := fun u => f (S.cl (lift u))
      map_zero' := by
        have h1 := key _ (hliftA 0) 1 A.one_mem (by rw [hliftcl, T.cl_one]; rfl)
        rw [h1, S.cl_one, map_zero]
      map_add' := fun u u' => by
        have h1 := key _ (hliftA (u + u')) _ (A.mul_mem (hliftA u) (hliftA u'))
          (by rw [hliftcl, T.cl_mul (hAT (hliftA u)) (hAT (hliftA u')), hliftcl, hliftcl]; rfl)
        change f (S.cl (lift (u + u'))) = f (S.cl (lift u)) + f (S.cl (lift u'))
        rw [h1, S.cl_mul (hA.le_QG (hliftA u)) (hA.le_QG (hliftA u')), map_add] }
  obtain ⟨φ, hφ⟩ := LinearMap.exists_extend (F.toZModLinearMap 2)
  have hφx : ∀ x ∈ A, φ (T.cl x) = f (S.cl x) := fun x hx => by
    have h1 := LinearMap.congr_fun hφ ⟨T.cl x, T.cl_mem_clSub hx (hAT hx)⟩
    change φ (T.cl x) = f (S.cl (lift ⟨T.cl x, T.cl_mem_clSub hx (hAT hx)⟩)) at h1
    rw [h1]
    exact key _ (hliftA _) x hx (hliftcl _)
  set wt := (LinearMap.BilinForm.toDual T.q.polarBilin T.q_nondegenerate).symm φ with hwtdef
  have hwt : ∀ u, QuadraticMap.polar T.q wt u = φ u := fun u => by
    rw [← QuadraticMap.polarBilin_apply_apply]
    exact LinearMap.BilinForm.apply_toDual_symm_apply _ u
  obtain ⟨w, hwQ, hwcl⟩ := T.exists_cl wt
  have hpol : ∀ x ∈ A, QuadraticMap.polar T.q (T.cl w) (T.cl x) = f (S.cl x) :=
    fun x hx => by rw [hwcl, hwt, hφx x hx]
  have hwz : w * S.z = S.z * w := by
    have h0 := hpol _ hA.z_mem
    rw [S.cl_z, map_zero] at h0
    exact (T.polar_cl_eq_zero_iff hwQ (hAT hA.z_mem)).mp h0
  have hwM : w ∈ S.M := S.mem_M_iff.mpr hwz
  refine ⟨⟨w, hwM⟩, ⟨hwQ, hwM⟩, fun v hv => ?_⟩
  obtain ⟨x, hx, hxQ, rfl⟩ := S.mem_clSub_iff.mp hv
  rw [S.ρ_cl ⟨w, hwM⟩ hxQ]
  have hpx := hpol x hx
  rcases CFSG.RankThree.Literature.FSmith.zmod2_cases (f (S.cl x)) with h0 | h1
  · rw [h0] at hpx
    rw [h0, zero_smul, add_zero]
    have hc := (T.polar_cl_eq_zero_iff hwQ (hAT hx)).mp hpx
    change S.cl (w * x * w⁻¹) = S.cl x
    rw [hc, mul_inv_cancel_right]
  · rw [h1] at hpx
    rw [h1, one_smul]
    have hc := (T.polar_cl_eq_one_iff hwQ (hAT hx)).mp hpx
    rcases T.mul_comm_or hwQ (hAT hx) with e | e
    · exact absurd e hc
    · change S.cl (w * x * w⁻¹) = _
      have e' : w * x * w⁻¹ = k * S.z * k⁻¹ * x := by
        rw [e]
        change k * S.z * k⁻¹ * (x * w) * w⁻¹ = k * S.z * k⁻¹ * x
        group
      rw [e', S.cl_mul (hA.le_QG hk) hxQ, add_comm]

theorem Lbar_inf_le_Lbar_mul {k k' k'' : G} (hk'Q : k' * S.z * k'⁻¹ ∈ S.QG)
    (hk'z : k' * S.z * k'⁻¹ ≠ S.z) (hkz : k * S.z * k⁻¹ ≠ S.z) (hkk' : k * S.z * k⁻¹ ∈ S.Qa k')
    (hne : k' * S.z * k'⁻¹ ≠ k * S.z * k⁻¹) (hne' : k' * S.z * k'⁻¹ ≠ k * S.z * k⁻¹ * S.z)
    (hk'' : k'' * S.z * k''⁻¹ = k * S.z * k⁻¹ * (k' * S.z * k'⁻¹)) :
    S.Lbar k ⊓ S.Lbar k' ≤ S.Lbar k'' := by
  set T := S.conjBy k' with hT
  have hzT : S.z ∈ T.QG := S.z_mem_Qa hk'Q hk'z
  have hzα : S.z ≠ k * S.z * k⁻¹ * T.z := by
    intro h
    apply hne'
    have hαα : k * S.z * k⁻¹ * (k * S.z * k⁻¹) = 1 := (S.conjBy k).z_mul_z
    calc k' * S.z * k'⁻¹
        = k * S.z * k⁻¹ * (k * S.z * k⁻¹) * (k' * S.z * k'⁻¹) := by rw [hαα, one_mul]
      _ = k * S.z * k⁻¹ * (k * S.z * k⁻¹ * T.z) := mul_assoc _ _ _
      _ = k * S.z * k⁻¹ * S.z := by rw [← h]
  obtain ⟨w, hwQ, hwz, hwα⟩ :=
    T.exists_conj_eq_mul_z_of_commute hkk' hzT (conj_z_ne_one S k) hne.symm hkz.symm hzα
  have hwM : w ∈ S.M := S.mem_M_iff.mpr hwz
  rintro s ⟨hsk, hsk'⟩
  have hwL : S.ρ ⟨w, hwM⟩ ∈ S.Lbar k' := ρ_mem_Lbar S (y := ⟨w, hwM⟩) ⟨hwQ, hwM⟩
  have hcomm : S.ρ ⟨w, hwM⟩ * s = s * S.ρ ⟨w, hwM⟩ :=
    congrArg Subtype.val ((S.isElementaryAbelian_Lbar hk'Q).is_comm.comm ⟨_, hwL⟩ ⟨s, hsk'⟩)
  have hs' := conj_mem_Lbar_mul S ⟨w, hwM⟩ hsk
  rw [hcomm, mul_inv_cancel_right] at hs'
  have e : (w * k) * S.z * (w * k)⁻¹ = k'' * S.z * k''⁻¹ := by
    rw [hk'', mul_conj_z S, hwα]
    rfl
  rwa [Lbar_eq_of_conj_eq S e] at hs'

end CFSG.LargeExtraspecial.S11
