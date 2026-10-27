module

public import CFSG.LargeExtraspecial.AS35QIxP
public import CFSG.LargeExtraspecial.AS35QIxTr

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QIx

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.Blueprint.Fischer (K)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace IxSetup

variable (T : IxSetup S)

theorem tb_mem_O : (T.tb : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ TauCeti.QuadraticMap.orthogonalGroup S.q :=
  T.tb.2

theorem isConj_of_mul_mem_QG (hS : S.SixHyp) {u : G} (hu : u ∈ S.QG)
    (h : (T.t * u) * (T.t * u) = 1) : IsConj T.t (T.t * u) ∨ IsConj (T.t * S.z) (T.t * u) := by
  have htt := T.t_mul_self
  have htinv : T.t⁻¹ = T.t := inv_eq_of_mul_eq_one_right htt
  have h1 : T.t * u * T.t⁻¹ = u⁻¹ := by
    rw [htinv]
    calc T.t * u * T.t = (T.t * u) * (T.t * u) * u⁻¹ := by group
      _ = u⁻¹ := by rw [h, one_mul]
  have h2 : T.t * u * T.t⁻¹ = u := S.conj_eq_of_cl_conj_eq hS.sixFour hS.weak T.t_mem_DSet
    T.t_mem_M hu (by rw [h1, S.cl_inv hu])
  have huu : u * u = 1 := by
    calc u * u = u * (T.t * u * T.t⁻¹) := by rw [h2]
      _ = u * u⁻¹ := by rw [h1]
      _ = 1 := mul_inv_cancel u
  have hfix : (T.tb : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl u) = S.cl u := by
    rw [show (T.tb : S.Qt ≃ₗ[ZMod 2] S.Qt) = S.rhoL T.t_mem_M from rfl, S.rhoL_cl T.t_mem_M hu]
    exact congrArg S.cl h2
  have hq : S.q (S.cl u) = 0 := (S.q_cl_eq_zero_iff hu).mpr (by rw [pow_two]; exact huu)
  have hmem := mem_commSpace_of_singular S.q_nondegenerate T.finrank_Qt T.hζ2 T.qζ T.tb_mem_O
    (coe_mul_self T.tb_mul_self) (T.apply_comm_of_comm T.tb_comm_zeta)
    (coe_ne_one T.tb_ne_one) hfix hq
  obtain ⟨v, hv⟩ := mem_commSpace.mp hmem
  obtain ⟨w, hw, rfl⟩ := S.exists_cl v
  obtain ⟨hcQ, hccl⟩ := S.cl_conj_mul_eq T.t_mem_M htt hw
  rw [show (T.tb : S.Qt ≃ₗ[ZMod 2] S.Qt) = S.rhoL T.t_mem_M from rfl, ← hccl] at hv
  have hwM := S.QG_le_M hw
  have htwM : T.t * w ∈ S.M := S.M.mul_mem T.t_mem_M hwM
  have hconj : (T.t * w) * T.t * (T.t * w)⁻¹ = T.t * (w * T.t * w⁻¹ * T.t) := by
    calc (T.t * w) * T.t * (T.t * w)⁻¹ = T.t * (w * T.t * w⁻¹ * T.t⁻¹) := by group
      _ = T.t * (w * T.t * w⁻¹ * T.t) := by rw [htinv]
  rcases (S.cl_eq_cl_iff hcQ hu).mp hv with h3 | h3
  · left
    refine isConj_iff.mpr ⟨T.t * w, ?_⟩
    rw [h3, hconj]
  · right
    refine isConj_iff.mpr ⟨T.t * w, ?_⟩
    have hz' : (T.t * w) * S.z * (T.t * w)⁻¹ = S.z := by
      rw [S.mem_M_iff.mp htwM]
      group
    rw [h3]
    calc (T.t * w) * (T.t * S.z) * (T.t * w)⁻¹ =
        ((T.t * w) * T.t * (T.t * w)⁻¹) * ((T.t * w) * S.z * (T.t * w)⁻¹) := by group
      _ = T.t * (w * T.t * w⁻¹ * T.t) * S.z := by rw [hz', hconj]
      _ = T.t * (w * T.t * w⁻¹ * T.t * S.z) := by group

theorem isConj_t : IsConj S.z T.t := isConj_iff.mpr ⟨T.g, rfl⟩

theorem exists_u₀ (hS : S.SixHyp) :
    ∃ u₀ ∈ S.QG, IsConj (S.z * T.t) u₀ ∧ u₀ * u₀ = 1 ∧ u₀ ≠ 1 ∧ u₀ ≠ S.z := by
  obtain ⟨h, hh⟩ := S.exists_conj_of_mem_DSet T.t_mem_DSet
  obtain ⟨p, -, hpH, hpz, hpt, -⟩ := S.exists_two_mem_delta_J T.t_mem_DSet hh
  obtain ⟨k, hk, hkQ⟩ := S.exists_conj_mem_QG_J hS T.t_mem_DSet hh hpH hpz hpt
  have hztt : (S.z * T.t) * (S.z * T.t) = 1 := by
    calc (S.z * T.t) * (S.z * T.t) = S.z * (T.t * S.z) * T.t := by group
      _ = S.z * (S.z * T.t) * T.t := by rw [T.t_comm_z]
      _ = (S.z * S.z) * (T.t * T.t) := by group
      _ = 1 := by rw [S.z_mul_z, T.t_mul_self, one_mul]
  refine ⟨k⁻¹ * (S.z * T.t) * k, hkQ, isConj_iff.mpr ⟨k⁻¹, by group⟩, ?_, ?_, ?_⟩
  · rw [show k⁻¹ * (S.z * T.t) * k * (k⁻¹ * (S.z * T.t) * k) =
      k⁻¹ * ((S.z * T.t) * (S.z * T.t)) * k by group, hztt]
    group
  · intro h1
    have : S.z * T.t = 1 := by
      calc S.z * T.t = k * (k⁻¹ * (S.z * T.t) * k) * k⁻¹ := by group
        _ = 1 := by rw [h1]; group
    apply T.t_ne_z
    calc T.t = S.z⁻¹ * (S.z * T.t) := by group
      _ = S.z := by rw [this, mul_one, S.z_inv]
  · intro h1
    apply T.not_isConj_zt
    refine isConj_iff.mpr ⟨k, ?_⟩
    calc k * S.z * k⁻¹ = k * (k⁻¹ * (S.z * T.t) * k) * k⁻¹ := by rw [h1]
      _ = S.z * T.t := by group

theorem isConj_mul_z {y : G} (hyQ : y ∈ S.QG) (hy0 : S.cl y ≠ 0) : IsConj y (y * S.z) := by
  have : ∃ w, polar S.q (S.cl y) w ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hy0 (S.q_nondegenerate.1 _ fun w => by
      rw [QuadraticMap.polarBilin_apply_apply]
      exact hall w)
  obtain ⟨w, hw⟩ := this
  obtain ⟨c, hc, rfl⟩ := S.exists_cl w
  have hne : y * c ≠ c * y := by
    rw [← S.polar_cl_eq_one_iff hyQ hc]
    rcases AS35QTh.zmod2_cases (polar S.q (S.cl y) (S.cl c)) with h | h
    · exact absurd h hw
    · exact h
  rcases S.commutator_eq_one_or_z hc hyQ with h | h
  · exfalso
    apply hne
    calc y * c = (c * y * c⁻¹ * y⁻¹)⁻¹ * (c * y) := by group
      _ = c * y := by rw [h]; group
  · refine isConj_iff.mpr ⟨c, ?_⟩
    calc c * y * c⁻¹ = (c * y * c⁻¹ * y⁻¹) * y := by group
      _ = S.z * y := by rw [h]
      _ = y * S.z := (S.z_comm_QG hyQ).symm

theorem isConj_of_mem_QG (hS : S.SixHyp) {y : G} (hyQ : y ∈ S.QG) (hyy : y * y = 1)
    (hy1 : y ≠ 1) : IsConj S.z y ∨ IsConj (S.z * T.t) y := by
  by_cases hyz : y = S.z
  · left
    rw [hyz]
  right
  have hy0 : S.cl y ≠ 0 := fun h => by
    rcases (S.cl_eq_zero_iff hyQ).mp h with h | h
    · exact hy1 h
    · exact hyz h
  have hqy : S.q (S.cl y) = 0 := (S.q_cl_eq_zero_iff hyQ).mpr (by rw [pow_two]; exact hyy)
  obtain ⟨u₀, hu₀Q, hu₀c, hu₀u₀, hu₀1, hu₀z⟩ := T.exists_u₀ hS
  have hu₀0 : S.cl u₀ ≠ 0 := fun h => by
    rcases (S.cl_eq_zero_iff hu₀Q).mp h with h | h
    · exact hu₀1 h
    · exact hu₀z h
  have hqu₀ : S.q (S.cl u₀) = 0 :=
    (S.q_cl_eq_zero_iff hu₀Q).mpr (by rw [pow_two]; exact hu₀u₀)
  obtain ⟨ξ₁, hξ₁, e₁⟩ := T.exists_mem_X_apply hu₀0 hqu₀
  obtain ⟨ξ₂, hξ₂, e₂⟩ := T.exists_mem_X_apply hy0 hqy
  obtain ⟨⟨m, hmM⟩, hm⟩ := T.hXM (T.X.mul_mem hξ₂ (T.X.inv_mem hξ₁))
  have hcl : S.cl (m * u₀ * m⁻¹) = S.cl y := by
    rw [← S.rhoL_cl hmM hu₀Q, Setting.rhoL, hm, apply_O, ← e₁, ← e₂]
    congr 1
    rw [← apply_O, inv_mul_cancel]
    rfl
  have hc1 : IsConj (S.z * T.t) (m * u₀ * m⁻¹) :=
    hu₀c.trans (isConj_iff.mpr ⟨m, rfl⟩)
  rcases (S.cl_eq_cl_iff (S.conj_mem_QG hmM hu₀Q) hyQ).mp hcl with h | h
  · rw [h]
    exact hc1
  · have h2 : y * S.z = m * u₀ * m⁻¹ := by
      rw [h, mul_assoc, S.z_mul_z, mul_one]
    exact hc1.trans (h2 ▸ (isConj_mul_z hyQ hy0).symm)

theorem isConj_of_involution (hS : S.SixHyp) {y : G} (hyM : y ∈ S.M)
    (hyζ : S.ρ ⟨y, hyM⟩ * T.ζ = T.ζ * S.ρ ⟨y, hyM⟩) (hyy : y * y = 1) (hy1 : y ≠ 1) :
    IsConj S.z y ∨ IsConj (S.z * T.t) y := by
  by_cases hyQ : y ∈ S.QG
  · exact T.isConj_of_mem_QG hS hyQ hyy hy1
  set σ := S.ρ ⟨y, hyM⟩ with hσdef
  have hσσ : σ * σ = 1 := S.ρ_mul_self_eq_one hyM hyy
  have hσ1 : σ ≠ 1 := fun h => hyQ ((S.ρ_eq_one_iff _).mp h)
  obtain ⟨v, hv, hv0⟩ := exists_ne_zero_mem_commSpace (coe_ne_one hσ1)
  have hqv : S.q v = 0 := (T.isTypeA_O hyζ hσσ hσ1).2.2.2.2 v hv
  obtain ⟨ξ, hξX, hξ⟩ := T.exists_mem_X_apply hv0 hqv
  have hξζ : Commute ξ T.ζ := (T.hζc ξ hξX).symm
  have htζ : Commute T.tb T.ζ := T.tb_comm_zeta
  set τ := ξ * T.tb * ξ⁻¹ with hτdef
  have hτζ : τ * T.ζ = T.ζ * τ := ((hξζ.mul_left htζ).mul_left hξζ.inv_left).eq
  have hττ : τ * τ = 1 := conj_mul_self_of ξ T.tb T.tb_mul_self
  have hτ1 : τ ≠ 1 := fun h => T.tb_ne_one (by
    calc T.tb = ξ⁻¹ * (ξ * T.tb * ξ⁻¹) * ξ := by group
      _ = 1 := by rw [← hτdef, h]; group)
  have hw₀ : T.l ![0, 1, 1] ∈ commSpace (T.tb : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    (T.mem_commSpace_tb_iff).mpr ⟨1, rfl⟩
  have hvτ : v ∈ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    obtain ⟨u, hu⟩ := mem_commSpace.mp hw₀
    refine mem_commSpace.mpr ⟨(ξ : S.Qt ≃ₗ[ZMod 2] S.Qt) u, ?_⟩
    rw [← hξ, ← hu, map_sub, hτdef, apply_O, apply_O]
    congr 2
    rw [← apply_O ξ⁻¹ ξ, inv_mul_cancel]
    rfl
  have hA1 := T.commSpace_eq_span_O hyζ hσσ hv hv0
  have hA2 := T.commSpace_eq_span_O hτζ hττ hvτ hv0
  have hστ : σ = τ := Subtype.ext (OrthoF2.eq_of_commSpace_eq S.q_nondegenerate
    (T.isTypeA_O hyζ hσσ hσ1) (T.isTypeA_O hτζ hττ hτ1) (hA1.trans hA2.symm))
  obtain ⟨⟨m, hmM⟩, hm⟩ := T.hXM hξX
  have hsM : m⁻¹ * y * m ∈ S.M := S.M.mul_mem (S.M.mul_mem (S.M.inv_mem hmM) hyM) hmM
  have hρs : S.ρ ⟨m⁻¹ * y * m, hsM⟩ = T.tb := by
    have e : (⟨m⁻¹ * y * m, hsM⟩ : S.M) = (⟨m, hmM⟩ : S.M)⁻¹ * ⟨y, hyM⟩ * ⟨m, hmM⟩ := rfl
    rw [e, map_mul, map_mul, map_inv, hm, ← hσdef, hστ, hτdef]
    group
  have huM : T.t * (m⁻¹ * y * m) ∈ S.M := S.M.mul_mem T.t_mem_M hsM
  have hu : T.t * (m⁻¹ * y * m) ∈ S.QG := by
    refine (S.ρ_eq_one_iff ⟨_, huM⟩).mp ?_
    have e : (⟨T.t * (m⁻¹ * y * m), huM⟩ : S.M) = ⟨T.t, T.t_mem_M⟩ * ⟨m⁻¹ * y * m, hsM⟩ := rfl
    rw [e, map_mul, hρs, ← tb_eq]
    exact T.tb_mul_self
  have hts : T.t * (T.t * (m⁻¹ * y * m)) = m⁻¹ * y * m := by
    rw [← mul_assoc, T.t_mul_self, one_mul]
  have hss : (T.t * (T.t * (m⁻¹ * y * m))) * (T.t * (T.t * (m⁻¹ * y * m))) = 1 := by
    rw [hts, show m⁻¹ * y * m * (m⁻¹ * y * m) = m⁻¹ * (y * y) * m by group, hyy]
    group
  have hsy : IsConj (T.t * (T.t * (m⁻¹ * y * m))) y := by
    rw [hts]
    exact isConj_iff.mpr ⟨m, by group⟩
  rcases T.isConj_of_mul_mem_QG hS hu hss with h | h
  · exact Or.inl (T.isConj_t.trans (h.trans hsy))
  · right
    rw [← T.t_comm_z]
    exact h.trans hsy

end IxSetup

end CFSG.LargeExtraspecial.AS35QIx
