module

public import CFSG.LargeExtraspecial.AS35CS63Hat
public import CFSG.LargeExtraspecial.FS65Transfer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

namespace S63

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace Pair

variable (P : Pair S)

theorem exists_commutator_eq_gen (hn : 3 ≤ S.width) :
    ∃ c ∈ S.QG, c * P.t = P.t * c ∧ P.x * c * P.x⁻¹ * c⁻¹ = P.t * S.z := by
  by_contra hno
  push Not at hno
  have hxM : P.x ∈ S.M := P.x_mem_M
  have hfix : ∀ c ∈ S.QG, c * P.t = P.t * c → rhoG S hxM (S.cl c) = S.cl c := by
    intro c hc hct
    have hcl0 : S.cl (P.x * c * P.x⁻¹ * c⁻¹) = 0 := by
      rcases P.commutator_mem hc hct with h | h | h | h
      · rw [h, S.cl_one]
      · exact absurd h (P.commutator_ne_t hc)
      · rw [h, S.cl_z]
      · exact absurd h (hno c hc hct)
    rwa [cl_commutator hxM hc, sub_eq_zero] at hcl0
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hle : LinearMap.BilinForm.orthogonal S.q.polarBilin ((ZMod 2) ∙ S.cl P.t) ≤
      fixSpace (rhoG S hxM) := by
    intro v hv
    obtain ⟨c, hc, rfl⟩ := S.exists_cl v
    rw [mem_fixSpace]
    refine hfix c hc ?_
    have h1 := LinearMap.BilinForm.mem_orthogonal_iff.mp hv (S.cl P.t)
      (Submodule.mem_span_singleton_self _)
    change S.q.polarBilin (S.cl P.t) (S.cl c) = 0 at h1
    rw [polarBilin_apply_apply, S.polar_cl_eq_zero_iff P.htQ hc] at h1
    exact h1.symm
  have hcomm : commSpace (rhoG S hxM) ≤ (ZMod 2) ∙ S.cl P.t := by
    rw [commSpace_eq_orthogonal_fixSpace_of_mem S.q_nondegenerate (rhoG_mem hxM)]
    calc LinearMap.BilinForm.orthogonal S.q.polarBilin (fixSpace (rhoG S hxM))
        ≤ LinearMap.BilinForm.orthogonal S.q.polarBilin
            (LinearMap.BilinForm.orthogonal S.q.polarBilin ((ZMod 2) ∙ S.cl P.t)) :=
          LinearMap.BilinForm.orthogonal_le hle
      _ = (ZMod 2) ∙ S.cl P.t :=
          LinearMap.BilinForm.orthogonal_orthogonal S.q_nondegenerate S.polarBilin_isRefl _
  have hxQ : (⟨P.x, hxM⟩ : S.M) ∉ S.Q := fun h => P.x_not_mem_QG ⟨⟨P.x, hxM⟩, h, rfl⟩
  have h2 := S.two_le_finrank_commSpace_of_conj (by omega) (x := ⟨P.x, hxM⟩) P.x_def.symm hxQ
  have h3 := Submodule.finrank_mono hcomm
  rw [finrank_span_singleton P.cl_t_ne_zero] at h3
  change 2 ≤ finrank (ZMod 2) (commSpace (rhoG S hxM)) at h2
  omega

theorem conj_eq_or_gen (hn : 3 ≤ S.width) {c : G} (hc : c ∈ S.QG)
    (hct : c * P.t = P.t * c) : c * P.x * c⁻¹ = P.x ∨ c * P.x * c⁻¹ = P.t * S.z * P.x := by
  rw [P.conj_eq_commutator_mul hc]
  rcases P.commutator_mem hc hct with h | h | h | h
  · left
    rw [h, one_mul]
  · exact absurd h (P.commutator_ne_t hc)
  · exfalso
    obtain ⟨c₀, hc₀, -, h₀⟩ := P.exists_commutator_eq_gen hn
    apply P.conj_ne_t_mul_x (c₀ * c)
    calc c₀ * c * P.x * (c₀ * c)⁻¹ = c₀ * (c * P.x * c⁻¹) * c₀⁻¹ := by group
      _ = (c₀ * S.z * c₀⁻¹) * (c₀ * P.x * c₀⁻¹) := by
          rw [P.conj_eq_commutator_mul hc, h]; group
      _ = S.z * (P.t * S.z * P.x) := by
          rw [S.z_comm_QG hc₀, P.conj_eq_commutator_mul hc₀, h₀]; group
      _ = (S.z * P.t) * S.z * P.x := by group
      _ = (P.t * S.z) * S.z * P.x := by rw [P.t_comm_z]
      _ = P.t * (S.z * S.z) * P.x := by group
      _ = P.t * P.x := by rw [S.z_mul_z, mul_one]
  · right
    rw [h]

theorem exists_conj_eq_gen (hn : 3 ≤ S.width) :
    ∃ c ∈ S.QG, c * P.t = P.t * c ∧ c * P.x * c⁻¹ = P.t * S.z * P.x := by
  obtain ⟨c, hc, hct, h⟩ := P.exists_commutator_eq_gen hn
  exact ⟨c, hc, hct, by rw [P.conj_eq_commutator_mul hc, h]⟩

theorem exists_conj_z_eq_gen (hn : 3 ≤ S.width) :
    ∃ c ∈ S.Qa P.g, c * P.t = P.t * c ∧ c * S.z * c⁻¹ = P.t * P.x * S.z := by
  have h := P.swap.exists_conj_eq_gen (by rw [S.width_conjBy]; exact hn)
  rwa [swap_x] at h

theorem x_mem_Hhat_gen (hn : 3 ≤ S.width) : P.x ∈ Hhat S P.htQ P.t_mul_t := by
  refine ⟨P.x_mem_M, P.t_comm_x.symm, fun e he het => ?_⟩
  have hc := P.conj_eq_commutator_mul he
  refine mem_Z2_of P.htQ P.t_mul_t ?_
  rcases P.conj_eq_or_gen hn he het with h | h
  · left
    rw [h] at hc
    exact (mul_eq_right.mp hc.symm)
  · right; right; right
    rw [h] at hc
    exact (mul_right_cancel hc).symm

end Pair

end S63

end CFSG.LargeExtraspecial
