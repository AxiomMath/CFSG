module

public import CFSG.LargeExtraspecial.AS35DFourFiveA
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem fixSpace_le_orthogonal_commSpace_of_isometry {g : S.Qt ≃ₗ[ZMod 2] S.Qt}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup S.q) :
    fixSpace g ≤ LinearMap.BilinForm.orthogonal S.q.polarBilin (commSpace g) := by
  intro v hv
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro u hu
  obtain ⟨w, rfl⟩ := mem_commSpace.mp hu
  rw [mem_fixSpace] at hv
  change polar S.q (g w - w) v = 0
  rw [QuadraticMap.polar_sub_left]
  nth_rewrite 1 [← hv]
  rw [TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg, sub_self]

theorem fixSpace_eq_orthogonal_commSpace_of_isometry {g : S.Qt ≃ₗ[ZMod 2] S.Qt}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup S.q) :
    fixSpace g = LinearMap.BilinForm.orthogonal S.q.polarBilin (commSpace g) := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  refine Submodule.eq_of_le_of_finrank_eq (S.fixSpace_le_orthogonal_commSpace_of_isometry hg) ?_
  rw [LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate]
  have := finrank_commSpace_add_finrank_fixSpace g
  omega

theorem orthogonal_fixSpace_of_isometry {g : S.Qt ≃ₗ[ZMod 2] S.Qt}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup S.q) :
    LinearMap.BilinForm.orthogonal S.q.polarBilin (fixSpace g) = commSpace g := by
  rw [S.fixSpace_eq_orthogonal_commSpace_of_isometry hg,
    LinearMap.BilinForm.orthogonal_orthogonal S.q_nondegenerate S.polarBilin_isRefl]

section OrderThree

variable {x : G} (hxM : x ∈ S.M) (hx3 : x ^ 3 = 1)
include hxM hx3

omit [Finite G] in
theorem conj_ne_mul_z_of_pow_three (y : G) : x * y * x⁻¹ ≠ y * S.z := by
  intro h
  have hxz : x * S.z * x⁻¹ = S.z := by rw [S.z_comm hxM]; group
  have hxxx : x * x * x = 1 := by rw [← hx3, pow_three, mul_assoc]
  have h3 : x * x * x * y * (x * x * x)⁻¹ = y * S.z := by
    calc x * x * x * y * (x * x * x)⁻¹ = x * (x * (x * y * x⁻¹) * x⁻¹) * x⁻¹ := by group
      _ = x * (x * (y * S.z) * x⁻¹) * x⁻¹ := by rw [h]
      _ = x * ((x * y * x⁻¹) * (x * S.z * x⁻¹)) * x⁻¹ := by group
      _ = x * (y * S.z * S.z) * x⁻¹ := by rw [h, hxz]
      _ = x * y * x⁻¹ := by rw [mul_assoc y, S.z_mul_z, mul_one]
      _ = y * S.z := h
  rw [hxxx, one_mul, inv_one, mul_one] at h3
  apply S.z_ne_one
  calc S.z = y⁻¹ * (y * S.z) := by group
    _ = 1 := by rw [← h3]; group

omit [Finite G] in
theorem conj_eq_of_cl_conj_eq_of_pow_three {y : G} (hy : y ∈ S.QG)
    (h : S.cl (x * y * x⁻¹) = S.cl y) : x * y * x⁻¹ = y := by
  rcases (S.cl_eq_cl_iff hy (S.conj_mem_QG hxM hy)).mp h.symm with h1 | h1
  · exact h1
  · exact absurd h1 (S.conj_ne_mul_z_of_pow_three hxM hx3 y)

theorem cqxSub_eq_fixSpace_of_pow_three : S.cqxSub x = fixSpace (S.rhoL hxM) := by
  refine le_antisymm (S.cqxSub_le_fixSpace hxM) fun v hv => ?_
  obtain ⟨y, hy, rfl⟩ := S.exists_cl v
  rw [mem_fixSpace, S.rhoL_cl hxM hy] at hv
  exact S.cl_mem_clSub (S.mem_inf_centralizer_iff_conj.mpr
    ⟨hy, S.conj_eq_of_cl_conj_eq_of_pow_three hxM hx3 hy hv⟩) hy

theorem rhoL_rhoL_rhoL_of_pow_three (v : S.Qt) :
    S.rhoL hxM (S.rhoL hxM (S.rhoL hxM v)) = v := by
  obtain ⟨y, hy, rfl⟩ := S.exists_cl v
  have h1 := S.conj_mem_QG hxM hy
  have h2 := S.conj_mem_QG hxM h1
  rw [S.rhoL_cl hxM hy, S.rhoL_cl hxM h1, S.rhoL_cl hxM h2]
  congr 1
  have hxxx : x * x * x = 1 := by rw [← hx3, pow_three, mul_assoc]
  calc x * (x * (x * y * x⁻¹) * x⁻¹) * x⁻¹ = x * x * x * y * (x * x * x)⁻¹ := by group
    _ = y := by rw [hxxx]; group

theorem commSpace_inf_fixSpace_of_pow_three :
    commSpace (S.rhoL hxM) ⊓ fixSpace (S.rhoL hxM) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hvc, hvf⟩ := Submodule.mem_inf.mp hv
  obtain ⟨w, rfl⟩ := mem_commSpace.mp hvc
  rw [mem_fixSpace, map_sub] at hvf
  set σ := S.rhoL hxM
  have h2 : σ (σ w) = w := by
    have h := congrArg (· + σ w) hvf
    simp only [sub_add_cancel] at h
    rw [h, sub_eq_add_vec (ZMod 2), add_right_comm, add_self_vec (ZMod 2), zero_add]
  have h3 : σ w = w := by
    have := S.rhoL_rhoL_rhoL_of_pow_three hxM hx3 w
    rwa [h2] at this
  rw [Submodule.mem_bot, h3, sub_self]

theorem fixSpace_inf_orthogonal_of_pow_three :
    fixSpace (S.rhoL hxM) ⊓
        LinearMap.BilinForm.orthogonal S.q.polarBilin (fixSpace (S.rhoL hxM)) = ⊥ := by
  rw [S.orthogonal_fixSpace_of_isometry (S.rhoL_mem hxM), inf_comm]
  exact S.commSpace_inf_fixSpace_of_pow_three hxM hx3

theorem mem_zpowers_of_commute_cqx {y : G} (hy : y ∈ S.QG ⊓ centralizer ({x} : Set G))
    (hc : ∀ w ∈ S.QG ⊓ centralizer ({x} : Set G), y * w = w * y) : y ∈ zpowers S.z := by
  have hyQ := (mem_inf.mp hy).1
  have h1 : S.cl y ∈ fixSpace (S.rhoL hxM) := by
    rw [← S.cqxSub_eq_fixSpace_of_pow_three hxM hx3]
    exact S.cl_mem_clSub hy hyQ
  have h2 : S.cl y ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin
      (fixSpace (S.rhoL hxM)) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    rw [← S.cqxSub_eq_fixSpace_of_pow_three hxM hx3] at hu
    obtain ⟨w, hw, hwQ, rfl⟩ := S.mem_clSub_iff.mp hu
    change polar S.q (S.cl w) (S.cl y) = 0
    exact (S.polar_cl_eq_zero_iff hwQ hyQ).mpr (hc w hw).symm
  have h3 : S.cl y = 0 := by
    have := S.fixSpace_inf_orthogonal_of_pow_three hxM hx3
    rw [eq_bot_iff] at this
    exact (Submodule.mem_bot _).mp (this (Submodule.mem_inf.mpr ⟨h1, h2⟩))
  rcases (S.cl_eq_zero_iff hyQ).mp h3 with rfl | rfl
  · exact one_mem _
  · exact mem_zpowers _

theorem isExtraspecialPGroup_cqx (hfix : fixSpace (S.rhoL hxM) ≠ ⊥) :
    IsExtraspecialPGroup 2 ↥(S.QG ⊓ centralizer ({x} : Set G)) := by
  have hE2 : IsPGroup 2 ↥(S.QG ⊓ centralizer ({x} : Set G)) :=
    S.isPGroup_QG.to_le inf_le_left
  have hK := S.cqxSub_eq_fixSpace_of_pow_three hxM hx3
  refine (CFSG.LocalAnalysis.GorensteinLyons.isExtraspecialPGroup_two_of_forall hE2
    (S.z_mem_cqx hxM) S.orderOf_z (fun y hy => ⟨S.mem_zpowers_of_commute_cqx hxM hx3 hy,
      fun hyz w hw => ?_⟩) (fun y hy w hw => ?_) (fun y hy => ?_) ?_).1
  · obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hyz
    exact ((Commute.zpow_left (S.z_comm_QG (mem_inf.mp hw).1).symm k)).eq
  · rw [commutatorElement_def]
    rcases S.commutator_eq_one_or_z (mem_inf.mp hy).1 (mem_inf.mp hw).1 with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact mem_zpowers _
  · rcases S.sq_eq_one_or_z (mem_inf.mp hy).1 with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact mem_zpowers _
  · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hfix
    have hv' : v ∉ LinearMap.BilinForm.orthogonal S.q.polarBilin (fixSpace (S.rhoL hxM)) := by
      intro h
      have := S.fixSpace_inf_orthogonal_of_pow_three hxM hx3
      rw [eq_bot_iff] at this
      exact hv0 ((Submodule.mem_bot _).mp (this (Submodule.mem_inf.mpr ⟨hv, h⟩)))
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv'
    push Not at hv'
    obtain ⟨u, hu, hvu⟩ := hv'
    rw [← hK] at hv hu
    obtain ⟨y, hy, hyQ, rfl⟩ := S.mem_clSub_iff.mp hv
    obtain ⟨w, hw, hwQ, rfl⟩ := S.mem_clSub_iff.mp hu
    refine ⟨w, hw, y, hy, fun h => hvu ?_⟩
    change polar S.q (S.cl w) (S.cl y) = 0
    exact (S.polar_cl_eq_zero_iff hwQ hyQ).mpr h

theorem card_cqx_of_pow_three :
    Nat.card ↥(S.QG ⊓ centralizer ({x} : Set G)) =
      2 * 2 ^ finrank (ZMod 2) (fixSpace (S.rhoL hxM)) := by
  rw [← S.clPre_cqxSub hxM, S.card_clPre, S.card_submodule,
    S.cqxSub_eq_fixSpace_of_pow_three hxM hx3]

theorem sup_fixSpace_commSpace_of_pow_three :
    fixSpace (S.rhoL hxM) ⊔ commSpace (S.rhoL hxM) = ⊤ := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  apply Submodule.eq_top_of_finrank_eq
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (fixSpace (S.rhoL hxM))
    (commSpace (S.rhoL hxM))
  rw [inf_comm, S.commSpace_inf_fixSpace_of_pow_three hxM hx3, finrank_bot] at h1
  have h2 := finrank_commSpace_add_finrank_fixSpace (S.rhoL hxM)
  omega

theorem commSpace_eq_image_fixSpace_of_pow_three {g : S.Qt ≃ₗ[ZMod 2] S.Qt}
    (hcomm : ∀ v, g (S.rhoL hxM v) = S.rhoL hxM (g v))
    (hfix : commSpace g ≤ fixSpace (S.rhoL hxM)) {v : S.Qt} (hv : v ∈ commSpace g) :
    ∃ c ∈ fixSpace (S.rhoL hxM), g c - c = v := by
  obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
  have hw : w ∈ fixSpace (S.rhoL hxM) ⊔ commSpace (S.rhoL hxM) := by
    rw [S.sup_fixSpace_commSpace_of_pow_three hxM hx3]
    exact Submodule.mem_top
  obtain ⟨c, hc, u, hu, rfl⟩ := Submodule.mem_sup.mp hw
  have hu0 : g u - u = 0 := by
    have h1 : g u - u ∈ fixSpace (S.rhoL hxM) := hfix (sub_mem_commSpace g u)
    have h2 : g u - u ∈ commSpace (S.rhoL hxM) := by
      obtain ⟨u', rfl⟩ := mem_commSpace.mp hu
      rw [map_sub, hcomm u']
      exact Submodule.sub_mem _ (sub_mem_commSpace (S.rhoL hxM) (g u')) hu
    have h3 := S.commSpace_inf_fixSpace_of_pow_three hxM hx3
    rw [eq_bot_iff] at h3
    exact (Submodule.mem_bot _).mp (h3 (Submodule.mem_inf.mpr ⟨h2, h1⟩))
  refine ⟨c, hc, ?_⟩
  rw [map_add, add_sub_add_comm, hu0, add_zero]

end OrderThree

end Setting

end CFSG.LargeExtraspecial
