module

public import CFSG.LargeExtraspecial.S3Eight
public import CFSG.RankThree.Literature.FSmithTransfer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith
open scoped commutatorElement

namespace Sm77

variable {G : Type*} [Group G] [Finite G] (S : Setting G)

theorem finrank_le_width_of_isotropic {U : Submodule (ZMod 2) S.Qt}
    (hU : ∀ u ∈ U, ∀ v ∈ U, polar S.q u v = 0) : finrank (ZMod 2) U ≤ S.width := by
  have hle : U ≤ LinearMap.BilinForm.orthogonal S.q.polarBilin U := by
    intro v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    rw [polarBilin_apply_apply]
    exact hU u hu v hv
  have h1 := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate U
  have h2 := Submodule.finrank_mono hle
  have h3 := Submodule.finrank_le U
  rw [S.finrank_Qt_eq_two_mul_width] at h1 h3
  omega

theorem exists_polar_eq_one_of_width_lt {U : Submodule (ZMod 2) S.Qt}
    (hU : S.width < finrank (ZMod 2) U) : ∃ u ∈ U, ∃ v ∈ U, polar S.q u v = 1 := by
  by_contra h
  push Not at h
  exact absurd (finrank_le_width_of_isotropic S fun u hu v hv =>
    (zmod2_cases _).resolve_right (h u hu v hv)) (not_le.mpr hU)

theorem q_add (u v : S.Qt) : S.q (u + v) = S.q u + S.q v + polar S.q u v := by
  unfold QuadraticMap.polar
  ring

theorem finrank_orthogonal_span_singleton {v : S.Qt} (hv : v ≠ 0) :
    finrank (ZMod 2) (LinearMap.BilinForm.orthogonal S.q.polarBilin (ZMod 2 ∙ v)) =
      2 * S.width - 1 := by
  rw [LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate, finrank_span_singleton hv,
    S.finrank_Qt_eq_two_mul_width]

theorem polar_eq_zero_of_mem_orthogonal {v w : S.Qt}
    (hw : w ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin (ZMod 2 ∙ v)) :
    polar S.q v w = 0 := by
  have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hw) v (Submodule.mem_span_singleton_self v)
  rwa [polarBilin_apply_apply] at h

theorem exists_polar_eq_one_q_eq_zero (h2 : 2 ≤ S.width) {v : S.Qt} (hv : v ≠ 0) :
    ∃ w, polar S.q w v = 1 ∧ S.q w = 0 := by
  obtain ⟨w₀, hw₀⟩ : ∃ w₀, polar S.q w₀ v = 1 := by
    by_contra h0
    push Not at h0
    apply hv
    refine S.q_nondegenerate.1 v fun w => ?_
    rw [polarBilin_apply_apply, polar_comm]
    exact (zmod2_cases _).resolve_right (h0 w)
  rcases zmod2_cases (S.q w₀) with hq | hq
  · exact ⟨w₀, hw₀, hq⟩
  set U := LinearMap.BilinForm.orthogonal S.q.polarBilin (ZMod 2 ∙ v) with hU
  have hUdim : S.width < finrank (ZMod 2) U := by
    rw [hU, finrank_orthogonal_span_singleton S hv]
    omega
  obtain ⟨w, hwU, hw⟩ : ∃ w ∈ U, S.q w + polar S.q w₀ w = 1 := by
    by_contra h
    push Not at h
    have h' : ∀ w ∈ U, S.q w = polar S.q w₀ w := fun w hw => by
      have e := (zmod2_cases (S.q w + polar S.q w₀ w)).resolve_right (h w hw)
      have key : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
      exact key _ _ e
    obtain ⟨u₁, hu₁, u₂, hu₂, h12⟩ := exists_polar_eq_one_of_width_lt S hUdim
    have e := q_add S u₁ u₂
    rw [h' _ (U.add_mem hu₁ hu₂), h' _ hu₁, h' _ hu₂, polar_add_right, h12] at e
    have key : ∀ a b : ZMod 2, a + b ≠ a + b + 1 := by decide
    exact key _ _ e
  refine ⟨w₀ + w, ?_, ?_⟩
  · rw [polar_add_left, hw₀, polar_comm, polar_eq_zero_of_mem_orthogonal S hwU, add_zero]
  · rw [q_add, hq, add_assoc, hw]
    decide

end Sm77

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G)

theorem transfer_M_eq_one (ϕ : S.M →* Multiplicative (ZMod 2)) (g : G) : ϕ.transfer g = 1 := by
  have := (ϕ.transfer).normal_ker
  rcases Subgroup.Normal.eq_bot_or_eq_top (ϕ.transfer).ker with h | h
  · exfalso
    obtain ⟨x, -, y, -, hxy⟩ := S.exists_not_commute
    apply hxy
    apply (MonoidHom.ker_eq_bot_iff _).mp h
    rw [map_mul, map_mul, mul_comm]
  · have hg : g ∈ (ϕ.transfer).ker := by
      rw [h]
      exact mem_top g
    exact hg

omit [Finite G] [IsSimpleGroup G] in
@[expose] noncomputable def fixHom {c : G}
    (hc : ∀ m ∈ S.M, m * c * m⁻¹ = c ∨ m * c * m⁻¹ = c * S.z) :
    S.M →* Multiplicative (ZMod 2) :=
  open Classical in
  { toFun := fun m => Multiplicative.ofAdd (if (m : G) * c * (m : G)⁻¹ = c then 0 else 1)
    map_one' := by simp
    map_mul' := fun m₁ m₂ => by
      have hcz : c * S.z ≠ c := fun h => S.z_ne_one (by simpa using h)
      have hz₁ : (m₁ : G) * S.z * (m₁ : G)⁻¹ = S.z := by
        rw [S.z_comm m₁.2]
        group
      have e : ((m₁ * m₂ : S.M) : G) * c * ((m₁ * m₂ : S.M) : G)⁻¹ =
          (m₁ : G) * ((m₂ : G) * c * (m₂ : G)⁻¹) * (m₁ : G)⁻¹ := by
        simp only [Subgroup.coe_mul]
        group
      have e' : (m₁ : G) * (c * S.z) * (m₁ : G)⁻¹ =
          (m₁ : G) * c * (m₁ : G)⁻¹ * ((m₁ : G) * S.z * (m₁ : G)⁻¹) := by group
      rw [← ofAdd_add, e]
      congr 1
      rcases hc m₁ m₁.2 with h1 | h1 <;> rcases hc m₂ m₂.2 with h2 | h2
      · rw [h2, h1, ite_eq_left rfl, add_zero]
      · rw [h2, e', hz₁, h1, ite_eq_left rfl, ite_eq_right hcz, zero_add]
      · rw [h2, h1, ite_eq_left rfl, ite_eq_right hcz, add_zero]
      · rw [h2, e', hz₁, h1, mul_assoc, S.z_mul_z, mul_one, ite_eq_left rfl, ite_eq_right hcz]
        decide }

omit [Finite G] [IsSimpleGroup G] in
theorem fixHom_apply {c : G} (hc : ∀ m ∈ S.M, m * c * m⁻¹ = c ∨ m * c * m⁻¹ = c * S.z)
    (m : S.M) : fixHom S hc m = open Classical in
      Multiplicative.ofAdd (if (m : G) * c * (m : G)⁻¹ = c then 0 else 1) := rfl

theorem eq_one_or_z_of_forall_conj (h2 : 2 ≤ S.width) {c : G} (hcQ : c ∈ S.QG)
    (hc : ∀ m ∈ S.M, m * c * m⁻¹ = c ∨ m * c * m⁻¹ = c * S.z) : c = 1 ∨ c = S.z := by
  by_contra hne
  push Not at hne
  obtain ⟨hc1, hcz⟩ := hne
  have hv : S.cl c ≠ 0 := fun h => by
    rcases (S.cl_eq_zero_iff hcQ).mp h with h | h
    exacts [hc1 h, hcz h]
  obtain ⟨w, hwv, hwq⟩ := Sm77.exists_polar_eq_one_q_eq_zero S h2 hv
  obtain ⟨a, haQ, rfl⟩ := S.exists_cl w
  have ha2 : a ^ 2 = 1 := (S.q_cl_eq_zero_iff haQ).mp hwq
  have hac : a * c ≠ c * a := (S.polar_cl_eq_one_iff haQ hcQ).mp hwv
  have haca : a * c * a⁻¹ = c * S.z := by
    rcases S.mul_comm_or haQ hcQ with h | h
    · exact absurd h hac
    · calc a * c * a⁻¹ = S.z * (c * a) * a⁻¹ := by rw [h]
        _ = S.z * c := by group
        _ = c * S.z := (S.z_comm (S.QG_le_M hcQ)).symm
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact hac (by rw [one_mul, mul_one])
  have haz : a ≠ S.z := by
    rintro rfl
    exact hac (S.z_comm (S.QG_le_M hcQ)).symm
  have hva : S.cl a ≠ 0 := fun h => by
    rcases (S.cl_eq_zero_iff haQ).mp h with h | h
    exacts [ha1 h, haz h]
  obtain ⟨c₁, hc₁Q, hc₁a, c₂, hc₂Q, hc₂a, h12⟩ : ∃ c₁ ∈ S.QG, c₁ * a = a * c₁ ∧
      ∃ c₂ ∈ S.QG, c₂ * a = a * c₂ ∧ c₁ * c₂ ≠ c₂ * c₁ := by
    obtain ⟨u₁, hu₁, u₂, hu₂, h⟩ := Sm77.exists_polar_eq_one_of_width_lt S
      (U := LinearMap.BilinForm.orthogonal S.q.polarBilin (ZMod 2 ∙ S.cl a))
      (by rw [Sm77.finrank_orthogonal_span_singleton S hva]; omega)
    obtain ⟨c₁, hc₁, rfl⟩ := S.exists_cl u₁
    obtain ⟨c₂, hc₂, rfl⟩ := S.exists_cl u₂
    refine ⟨c₁, hc₁, ?_, c₂, hc₂, ?_, (S.polar_cl_eq_one_iff hc₁ hc₂).mp h⟩
    · exact ((S.polar_cl_eq_zero_iff haQ hc₁).mp
        (Sm77.polar_eq_zero_of_mem_orthogonal S hu₁)).symm
    · exact ((S.polar_cl_eq_zero_iff haQ hc₂).mp
        (Sm77.polar_eq_zero_of_mem_orthogonal S hu₂)).symm
  have hcomm : ⁅c₁, c₂⁆ = S.z := by
    rw [commutatorElement_def]
    rcases S.commutator_eq_one_or_z hc₁Q hc₂Q with h | h
    · exfalso
      apply h12
      calc c₁ * c₂ = c₁ * c₂ * c₁⁻¹ * c₂⁻¹ * (c₂ * c₁) := by group
        _ = c₂ * c₁ := by rw [h, one_mul]
    · exact h
  refine smith_transfer (fixHom S hc) S.z_ne_one S.z_mul_z (F := S.QG) S.QG_le_M S.isPGroup_QG
    ?_ haQ (by rw [← pow_two]; exact ha2) ?_ (transfer_M_eq_one S _ a) ?_
    (S.exists_conj_eq_mul_z haQ ha1 haz) ⟨c₁, hc₁Q, c₂, hc₂Q, hc₁a, hc₂a, hcomm⟩
  · intro c' hc'
    have hc'M : c' ∈ S.M := S.mem_M_iff.mpr (hc' S.z S.z_mem_QG)
    exact S.eq_one_or_z_of_commute (S.mem_QG_of_commute hc'M hc') hc'
  · rw [fixHom_apply]
    have hne : a * c * a⁻¹ ≠ c := by
      rw [haca]
      exact fun h => S.z_ne_one (by simpa using h)
    rw [ite_eq_right hne]
    decide
  · intro f hf
    rcases S.mul_comm_or hf haQ with h | h
    · left
      rw [h]
      group
    · right
      calc f * a * f⁻¹ = S.z * (a * f) * f⁻¹ := by rw [h]
        _ = S.z * a := by group
        _ = a * S.z := (S.z_comm (S.QG_le_M haQ)).symm

theorem eq_zero_of_forall_ρ_apply_eq (h2 : 2 ≤ S.width) {v : S.Qt}
    (hv : ∀ m : S.M, (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) : v = 0 := by
  obtain ⟨c, hcQ, rfl⟩ := S.exists_cl v
  have hc : ∀ m ∈ S.M, m * c * m⁻¹ = c ∨ m * c * m⁻¹ = c * S.z := fun m hm => by
    have h := hv ⟨m, hm⟩
    rw [S.ρ_cl ⟨m, hm⟩ hcQ] at h
    exact (S.cl_eq_cl_iff hcQ (S.conj_mem_QG hm hcQ)).mp h.symm
  rcases eq_one_or_z_of_forall_conj S h2 hcQ hc with rfl | rfl
  · exact S.cl_one
  · exact S.cl_z

end CFSG.LargeExtraspecial.DW
