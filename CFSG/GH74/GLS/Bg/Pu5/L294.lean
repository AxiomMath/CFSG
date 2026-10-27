module

public import CFSG.GH74.GLS.Bg.Pu5.Assembly
public import CFSG.GH74.GLS.Bg.Pu5.L293Step0
public import CFSG.GH74.GLS.Bg.Pu5.BalStatements

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.ABGLocalTools CFSG.GH74.GLS.Bg.Iii2 CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec6

variable {G : Type} [Group G] [Finite G]

theorem Cfg.z_mem_S {z t : G} {S : Subgroup G} (hC : Cfg G z t S) : z ∈ S :=
  mem_sylow_of_forall_comm hC.sylow (Subgroup.mem_centralizer_singleton_iff.2 rfl) hC.hz fun _ hy =>
    Subgroup.mem_centralizer_singleton_iff.1 hy

theorem not_inducesFAut_of_bal1 (h44 : II4_44) (hBal1 : Bal1S) (h293 : L293) {z t : G}
    {S : Subgroup G} (hC : Cfg G z t S) {K : Subgroup G} (hK : IsRigidRankOneComp z K) :
    ¬ InducesFAut t K := by
  intro hf
  have hx : t ∈ normalizer (K : Set G) := hf.fst
  obtain ⟨y, hyK, hy2, hyC, hyL⟩ :=
    hBal1 G hC.simple z t hC.hz hC.t_orderOf hC.tC K hK hx hf
  have hyz : y ∈ centralizer ({z} : Set G) := (rr_pcomp hK).1 hyK
  obtain ⟨L, hL⟩ := rigid_nonempty hC.t_orderOf hC.t_mem_rigidProduct
  exact h293 G z t S hC y hy2 hyz hyC K hK (rr_inv_mem_cSec h44 hC.simple hK hyK hy2) L hL (hyL L hL)

theorem l294a_of (h44 : II4_44) (hquat : II4_4_quat) (hBal1 : Bal1S) (h293 : L293) : L294a := by
  intro G _ _ z t S hC
  refine ⟨fun K hK => not_inducesFAut_of_bal1 h44 hBal1 h293 hC hK, fun L hL => ?_⟩
  obtain ⟨S', hC'⟩ := cfg_swap h44 hquat h293 hC
  exact not_inducesFAut_of_bal1 h44 hBal1 h293 hC' hL

theorem l294b_of (h44 : II4_44) (hquat : II4_4_quat) (hBalSwap : BalSwapS) (h293 : L293) : L294b := by
  intro G _ _ z t S hC ⟨K, hK, hnK⟩
  have hK' : IsRigidRankOneComp z (cmap t K) := isRigidRankOneComp_cmap hK hC.tC
  have hne : K ≠ cmap t K := fun h =>
    hnK (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
  have hle := rr_ncard_le_two hquat hC.simple hC.gen4 hC.hz
  have hge : 2 ≤ Set.ncard {K : Subgroup G | IsRigidRankOneComp z K} := by
    have hfin : {K : Subgroup G | IsRigidRankOneComp z K}.Finite := Set.toFinite _
    exact (Set.one_lt_ncard_iff hfin).2 ⟨K, cmap t K, hK, hK', hne⟩
  refine ⟨le_antisymm hle hge, ?_⟩
  by_contra hZ
  obtain ⟨z₁, z₂, q₁, q₂, hZs⟩ := zStar_two hquat hC.simple hC.gen4 hK hK' hne hC.sylow
  have hz₁2 : orderOf z₁ = 2 := qdata_orderOf q₁
  have hz₂2 : orderOf z₂ = 2 := qdata_orderOf q₂
  have htz₁ : t * z₁ * t⁻¹ = z₂ := by
    have hmem : t * z₁ * t⁻¹ ∈ S ⊓ cmap t K :=
      ⟨S.mul_mem (S.mul_mem hC.tS q₁.mem.1) (S.inv_mem hC.tS), conj_mem_cmap' q₁.mem.2 t⟩
    have hsq : t * z₁ * t⁻¹ * (t * z₁ * t⁻¹) = 1 := by
      have : z₁ * z₁ = 1 := q₁.sq
      calc t * z₁ * t⁻¹ * (t * z₁ * t⁻¹) = t * (z₁ * z₁) * t⁻¹ := by group
        _ = 1 := by rw [this]; group
    rcases q₂.unique _ hmem hsq with h | h
    · exfalso
      have : z₁ = 1 := by
        have h' : t * z₁ * t⁻¹ = 1 := h
        simpa using h'
      exact q₁.ne this
    · exact h
  have hz₁₂ : z₁ ≠ z₂ := by
    intro heq
    apply hZ
    apply le_antisymm
    · intro c hc
      have hc' := hZs c hc
      have hzc : z ∈ S ⊓ zStar (rigidProduct z) := ⟨hC.z_mem_S, hC.z_mem_zStar⟩
      have hz1 : z = 1 ∨ z = z₁ ∨ z = z₂ ∨ z = z₁ * z₂ := hZs z hzc
      have hzne : z ≠ 1 := fun h => by
        have := hC.hz
        rw [h, orderOf_one] at this
        exact absurd this (by norm_num)
      have hzz₁ : z = z₁ := by
        rcases hz1 with h | h | h | h
        · exact absurd h hzne
        · exact h
        · rw [h, heq]
        · exfalso
          rw [← heq] at h
          have : z₁ * z₁ = 1 := q₁.sq
          exact hzne (h.trans this)
      rcases hc' with h | h | h | h
      · rw [h]; exact one_mem _
      · rw [h, ← hzz₁]; exact Subgroup.mem_zpowers z
      · rw [h, ← heq, ← hzz₁]; exact Subgroup.mem_zpowers z
      · rw [h, ← heq]
        have : z₁ * z₁ = 1 := q₁.sq
        rw [this]; exact one_mem _
    · exact (Subgroup.zpowers_le).2 ⟨hC.z_mem_S, hC.z_mem_zStar⟩
  have hcomm₁₂ : z₁ * z₂ = z₂ * z₁ :=
    rr_sylow_comm hK hK' hne hC.sylow z₁ q₁.mem z₂ q₂.mem
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [hC.t_orderOf, sq] at this
  have htz₂ : t * z₂ * t⁻¹ = z₁ := by
    rw [← htz₁]
    calc t * (t * z₁ * t⁻¹) * t⁻¹ = (t * t) * z₁ * (t⁻¹ * t⁻¹) := by group
      _ = z₁ := by
        have : t⁻¹ * t⁻¹ = 1 := by rw [← mul_inv_rev, ht2, inv_one]
        rw [ht2, this]; group
  have hu2 : orderOf (z₁ * z₂) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h1 : z₁ * z₁ = 1 := q₁.sq
    have h2 : z₂ * z₂ = 1 := q₂.sq
    refine orderOf_eq_prime ?_ ?_
    · calc (z₁ * z₂) ^ 2 = z₁ * z₂ * (z₁ * z₂) := sq _
        _ = z₁ * (z₂ * z₁) * z₂ := by group
        _ = z₁ * (z₁ * z₂) * z₂ := by rw [← hcomm₁₂]
        _ = (z₁ * z₁) * (z₂ * z₂) := by group
        _ = 1 := by rw [h1, h2]; simp
    · intro h
      apply hz₁₂
      have : z₁ = z₂⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [this]
      exact inv_eq_of_mul_eq_one_right h2
  have huz : z₁ * z₂ ∈ centralizer ({z} : Set G) :=
    mul_mem ((rr_pcomp hK).1 q₁.mem.2) ((rr_pcomp hK').1 q₂.mem.2)
  have hut : z₁ * z₂ ∈ centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : t * (z₁ * z₂) * t⁻¹ = z₂ * z₁ := by
      calc t * (z₁ * z₂) * t⁻¹ = (t * z₁ * t⁻¹) * (t * z₂ * t⁻¹) := by group
        _ = z₂ * z₁ := by rw [htz₁, htz₂]
    have : t * (z₁ * z₂) = (z₁ * z₂) * t := by
      calc t * (z₁ * z₂) = t * (z₁ * z₂) * t⁻¹ * t := by group
        _ = (z₂ * z₁) * t := by rw [h1]
        _ = (z₁ * z₂) * t := by rw [hcomm₁₂]
    exact this.symm
  have hzK : z₁ * z₂ ∈ cSec K :=
    mul_mem (rr_inv_mem_cSec h44 hC.simple hK q₁.mem.2 hz₁2)
      (le_cSec_of_ne (rr_pcomp hK') (rr_pcomp hK) hne.symm q₂.mem.2)
  have hzL := hBalSwap G hC.simple z t hC.hz hC.t_orderOf hC.tC K (cmap t K) hK hK' hne rfl S
    hC.sylow hC.tS z₁ z₂ q₁.mem q₂.mem hz₁2 hz₂2 hz₁₂
  obtain ⟨L, hL⟩ := rigid_nonempty hC.t_orderOf hC.t_mem_rigidProduct
  exact h293 G z t S hC (z₁ * z₂) hu2 huz hut K hK hzK L hL (hzL L hL)

end CFSG.GH74.GLS.Bg.Pu5
